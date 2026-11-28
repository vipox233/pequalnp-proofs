import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_52586.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_52586
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffeefffffffefffffffe,0xfefefefcfefaee00ffff,0xffffffffffffffffffff,0xffffffeefffffffeffff,0xfffefefefefcfefaee00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[7,6]⟩,⟨.or,[2,7]⟩,⟨.or,[6,4]⟩,⟨.or,[1,0]⟩,⟨.or,[11,4]⟩,⟨.or,[0,9]⟩,⟨.or,[3,12]⟩,⟨.and,[3,11]⟩,⟨.and,[8,14]⟩,⟨.or,[1,9]⟩,⟨.and,[17,5]⟩,⟨.and,[10,13]⟩,⟨.or,[18,19]⟩,⟨.or,[16,20]⟩,⟨.or,[21,15]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 3, 4, 0, 0, 1, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 3, 4, 0, 0, 1, 0, 0] : List Nat).getD i.val 0))

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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low9 : Lower true (varsX 9) (graphGoal 9) 1 := by
  have q := @lower_count true (vars 9) (graphGoal 9) (proper_of _ (by decide +kernel)) (graphPairs 9 3) (by decide +kernel)
  exact q
def K9 := extendKnown [] 1 [(36,[32,16,83,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V9 : Known true K9 := extend_ok (m:=9) baseKnown low9 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low11 : Lower true (varsX 11) (graphGoal 11) 2 := by
  have q := @lower_count true (vars 11) (graphGoal 11) (proper_of _ (by decide +kernel)) (graphPairs 11 51) (by decide +kernel)
  exact q
def K11 := extendKnown K9 2 [(52,[64,81,32,50,49]),(100,[80,97,32,50,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V11 : Known true K11 := extend_ok (m:=11) V9 low11 (by decide +kernel)
def g73Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0)]
def g73C : List ColumnInfo := []
def g73A : List (List Nat) := [[],[99],[48],[48,96],[96,48],[96]]
def g73D3 (j : Nat) := if j=0 then 0x7 else 0
def g73L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g73D3)
  | _ => emptyPacking
def g73I (_ _ : Nat) : Option (Nat × Nat) := none
def g73 : Forest := ⟨73,3,fun i => g73Y[i]?.getD (0,0),g73C,g73A,g73L,g73I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73P3_0 : block g73 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g73B3 : block g73 3 0 1=true := g73P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73T : checkedTables g73 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g73 0 0 0 = true)
  · exact (rfl : block g73 1 0 0 = true)
  · exact (rfl : block g73 2 0 0 = true)
  · exact g73B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73G : graphValid g73 (boundsBefore K11) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low73 : Lower true (varsX 73) (graphGoal 73) 4 := lower_forest (g:=g73) (i:=0) (hints:=3) (before_sound K11 V11) g73G g73T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K73 := extendKnown K11 4 [(73,[]),(74,[16]),(81,[67]),(84,[32,16,67]),(137,[118]),(193,[99,67,84,117]),(200,[48,16,33,98,66,84,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V73 : Known true K73 := extend_ok (m:=73) V11 low73 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf71fc7ff03fffff8f7,0x1fc7ff03fffff8f71fc7])),(BitVec.ofNat 152 (word80 [0x710490a2850401207,0x10490a28504012071049]))),((BitVec.ofNat 152 (word80 [0xbe838fffc07e3ff0b,0xe838fffc07e3ff0be838])),(BitVec.ofNat 152 (word80 [0x4368db4c3260892043,0x68db4c326089204368db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xeee63ffffff803ffee,0xe63ffffff803ffeee63f])),(BitVec.ofNat 152 (word80 [0x88724904085124008,0x87249040851240088724]))),((BitVec.ofNat 152 (word80 [0x193dc0fffffffc0019,0x3dc0fffffffc00193dc0])),(BitVec.ofNat 152 (word80 [0x982db6e08306038498,0x2db6e083060384982db6]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[48,65]]
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
theorem g27G : graphValid g27 (boundsBefore K73) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=51) (before_sound K73 V73) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K73 4 [(27,[]),(29,[33,67]),(43,[16,84]),(46,[16,32,83,67]),(53,[32,16,67,83]),(54,[32,83]),(99,[16,99,84,67]),(101,[32,16,99,84,67]),(108,[32,49,97,84,65]),(114,[16,64,32,99,82]),(150,[64,32,115,83,101]),(156,[112,33,16,67,81,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V73 low27 (by decide +kernel)
def g75Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0),(0x0,0x0)]
def g75C : List ColumnInfo := [(1,0,74,0,4)]
def g75A : List (List Nat) := [[],[99],[16],[16,99]]
def g75D4 (j : Nat) := if j=0 then 0x1f else 0
def g75L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g75D4)
  | _ => emptyPacking
def g75I (_ _ : Nat) : Option (Nat × Nat) := none
def g75 : Forest := ⟨75,4,fun i => g75Y[i]?.getD (0,0),g75C,g75A,g75L,g75I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75P4_0 : block g75 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g75B4 : block g75 4 0 1=true := g75P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75T : checkedTables g75 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g75 0 0 0 = true)
  · exact (rfl : block g75 1 0 0 = true)
  · exact (rfl : block g75 2 0 0 = true)
  · exact (rfl : block g75 3 0 0 = true)
  · exact g75B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75G : graphValid g75 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low75 : Lower true (varsX 75) (graphGoal 75) 5 := lower_forest (g:=g75) (i:=0) (hints:=51) (before_sound K27 V27) g75G g75T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K75 := extendKnown K27 5 [(75,[]),(85,[33,67]),(89,[48,65,33]),(139,[118]),(212,[32,113,67,49,83]),(216,[48,65,32,98,82,117]),(226,[80,97,32,49,66,67,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V75 : Known true K75 := extend_ok (m:=75) V27 low75 (by decide +kernel)
def g77Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0)]
def g77C : List ColumnInfo := [(4,0,73,0,4)]
def g77A : List (List Nat) := [[],[48]]
def g77D4 (j : Nat) := if j=0 then 0x1f else 0
def g77L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g77D4)
  | _ => emptyPacking
def g77I (_ _ : Nat) : Option (Nat × Nat) := none
def g77 : Forest := ⟨77,4,fun i => g77Y[i]?.getD (0,0),g77C,g77A,g77L,g77I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77P4_0 : block g77 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g77B4 : block g77 4 0 1=true := g77P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77T : checkedTables g77 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g77 0 0 0 = true)
  · exact (rfl : block g77 1 0 0 = true)
  · exact (rfl : block g77 2 0 0 = true)
  · exact (rfl : block g77 3 0 0 = true)
  · exact g77B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77G : graphValid g77 (boundsBefore K75) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low77 : Lower true (varsX 77) (graphGoal 77) 5 := lower_forest (g:=g77) (i:=0) (hints:=1539) (before_sound K75 V75) g77G g77T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K77 := extendKnown K75 5 [(77,[]),(78,[16]),(83,[33,67]),(86,[32,16,67]),(90,[16,66]),(92,[32,16,49,65]),(106,[48,16,82,97,66]),(116,[64,16,82,99,50]),(166,[16,115,67,84,101]),(178,[16,66,83,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V77 : Known true K77 := extend_ok (m:=77) V75 low77 (by decide +kernel)
def g201Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g201C : List ColumnInfo := [(1,0,200,0,4),(8,0,193,0,4),(64,0,137,0,4),(128,0,73,0,4)]
def g201A : List (List Nat) := [[],[118],[99],[99,115],[115,99],[115],[48],[48,118],[48,96],[48,96,112],[48,112,96],[48,112],[96,48],[96,48,115],[96],[96,112],[96,115],[96,115,48],[112,48,99],[112,48],[112,96],[112],[112,99,48],[112,99]]
def g201D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g201D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g201H4 (j : Nat) := if j=0 then 0x37c0 else 0
def g201D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g201H5 := limbs80 #[#[0xb20000000000000000,0xc500580017c8c003cc,0x688016100000]]
def g201D6 (j : Nat) := if j=0 then 0x3904f else 0
def g201H6 := limbs80 #[#[0x280000000,0x8800002c4000000000,0x582880000528]]
def g201L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g201D3)
  | 4 => (3,2,2,0,0,5,0,g201D4)
  | 5 => (1,1,2,0,0,0,0,g201D5)
  | 6 => (1,0,2,0,0,0,0,g201D6)
  | _ => emptyPacking
def g201I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 5 0 5 1 0 g201H4
  | 5 => lookupWord 2 23 0 9 2 3 g201H5
  | 6 => lookupWord 1 23 0 9 0 5 g201H6
  | _ => fun _ => none
def g201 : Forest := ⟨201,6,fun i => g201Y[i]?.getD (0,0),g201C,g201A,g201L,g201I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P3_0 : block g201 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B3 : block g201 3 0 2=true := g201P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P4_0 : block g201 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B4 : block g201 4 0 3=true := g201P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P5_0 : block g201 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B5 : block g201 5 0 1=true := g201P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201P6_0 : block g201 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g201B6 : block g201 6 0 1=true := g201P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201T : checkedTables g201 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g201 0 0 0 = true)
  · exact (rfl : block g201 1 0 0 = true)
  · exact (rfl : block g201 2 0 0 = true)
  · exact g201B3
  · exact g201B4
  · exact g201B5
  · exact g201B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g201G : graphValid g201 (boundsBefore K77) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low201 : Lower true (varsX 201) (graphGoal 201) 7 := lower_forest (g:=g201) (i:=0) (hints:=3) (before_sound K77 V77) g201G g201T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K201 := extendKnown K77 7 [(201,[]),(202,[16]),(209,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V201 : Known true K201 := extend_ok (m:=201) V77 low201 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ffc07ffffffe00,0x3fffff80ffd386b20f0f])),(BitVec.ofNat 152 (word80 [0x41a8128d052280541a,0x82502916291304a21111]))),((BitVec.ofNat 152 (word80 [0xfffc00007ff01fffff,0xc007ffff01a37d4800f0])),(BitVec.ofNat 152 (word80 [0x81311b160644c89893,0x136232244d835c485555]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,0xfff80000003f407df000])),(BitVec.ofNat 152 (word80 [0x5c05c18178702e01c,0x380bc38703340753333]))),((BitVec.ofNat 152 (word80 [0x1fffff,0xfffffffffe663f7600ff])),(BitVec.ofNat 152 (word80 [0x160260205808130120,0x2404c00000642314aaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1803800060001c01c0,0x38070040808c9308cccc]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := []
def g31A : List (List Nat) := [[],[33,67]]
def g31D4 (j : Nat) := if j=0 then 0x1f else 0
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
theorem g31G : graphValid g31 (boundsBefore K201) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 5 := lower_forest (g:=g31) (i:=0) (hints:=1075) (before_sound K201 V201) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K201 5 [(31,[]),(47,[16,84]),(55,[32,16,67,83]),(59,[48,65,82]),(61,[64,49,82,16,33]),(62,[80,49,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V201 low31 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ffc07fe03fff,0xe00ffffe07f469d401c7])),(BitVec.ofNat 152 (word80 [0xa0a86a128d0a458a05,0x46a250a4b29029d49249]))),((BitVec.ofNat 152 (word80 [0xfffff00007fffc07f,0xfff007fff813a68c0e38])),(BitVec.ofNat 152 (word80 [0xc1304c1b160c891309,0x84c360c924d1a28c9249]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000007f,0xfffff800000bc8b47000])),(BitVec.ofNat 152 (word80 [0x5c1705c182f0e1c2e,0x70382f1c70bc8b5b6db]))),((BitVec.ofNat 152 (word80 [0xf0000000000000007f,0xffffffffffe6fe67803f])),(BitVec.ofNat 152 (word80 [0x60180602030102030,0x8040300000654212492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x80200800040000040,0x10080400000000024924]))),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(1,0,78,0,5)]
def g79A : List (List Nat) := [[],[16]]
def g79D5 (j : Nat) := if j=0 then 0x3f else 0
def g79L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g79D5)
  | _ => emptyPacking
def g79I (_ _ : Nat) : Option (Nat × Nat) := none
def g79 : Forest := ⟨79,5,fun i => g79Y[i]?.getD (0,0),g79C,g79A,g79L,g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5_0 : block g79 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B5 : block g79 5 0 1=true := g79P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0 = true)
  · exact (rfl : block g79 1 0 0 = true)
  · exact (rfl : block g79 2 0 0 = true)
  · exact (rfl : block g79 3 0 0 = true)
  · exact (rfl : block g79 4 0 0 = true)
  · exact g79B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 6 := lower_forest (g:=g79) (i:=0) (hints:=1587) (before_sound K31 V31) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K31 6 [(79,[]),(87,[33,67]),(199,[115,67,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V31 low79 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc3fe00ff87f87ffc0,0x7fffffe3dba15000ff0f])),(BitVec.ofNat 152 (word80 [0x288140a05101100285,0x502004842a141111111]))),((BitVec.ofNat 152 (word80 [0x3ffff0007ff87fff,0x807f1ffc2adc600f00f0])),(BitVec.ofNat 152 (word80 [0x310984c26212011306,0x260444812acc43333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff80007fff,0xff801fff949db0f000ff])),(BitVec.ofNat 152 (word80 [0x421209048024222408,0x82889001410b4444444]))),((BitVec.ofNat 152 (word80 [0xffc000000000007fff,0xffffe0000b66bf000f00])),(BitVec.ofNat 152 (word80 [0x801c0e070438443810,0x30300e120946b6666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x2010080040004020,0x40401000000008888888]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(1,0,90,0,5),(2,0,89,0,5),(8,0,83,0,5),(16,0,75,0,5)]
def g91A : List (List Nat) := [[],[48,65]]
def g91D6 (j : Nat) := if j=0 then 0x6c09f else 0
def g91L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I (_ _ : Nat) : Option (Nat × Nat) := none
def g91 : Forest := ⟨91,6,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : block g91 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B6 : block g91 6 0 1=true := g91P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact (rfl : block g91 4 0 0 = true)
  · exact (rfl : block g91 5 0 0 = true)
  · exact g91B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=51) (before_sound K79 V79) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K79 7 [(91,[]),(93,[33,67]),(155,[118]),(214,[64,32,115,83]),(220,[112,33,16,67,81]),(227,[16,99,84,67,116]),(242,[16,64,32,99,82,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V79 low91 (by decide +kernel)
def g94Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0),(0x0,0x0)]
def g94C : List ColumnInfo := [(2,0,92,0,5),(4,0,90,0,5),(8,0,86,0,5),(16,0,78,0,5),(10,0,84,0,4),(20,0,74,0,4)]
def g94A : List (List Nat) := [[],[66],[33,67],[33,49,65],[49],[49,66],[65,33,50],[65,50]]
def g94D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g94D5 := limbs80 #[#[0x7c54443f280885bd4940,0xfea8885f95110beaa221,0xbd4940bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201141080d176b,0xc110204810001]]
def g94H5 := limbs80 #[#[0x88c900000010000032,0x21]]
def g94D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g94H6 := limbs80 #[#[0x5b44010868781100d023,0x4e244800357d0fc2b1a0,0x1138641]]
def g94D7 (j : Nat) := if j=0 then 0x1605f else 0
def g94H7 := limbs80 #[#[0x14a0000f88039460,0x52000000000005200000,0xc1000033400007e7,0x4153001d4000]]
def g94L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g94D4)
  | 5 => (10,2,3,0,0,7,0,g94D5)
  | 6 => (3,1,3,0,0,6,0,g94D6)
  | 7 => (1,0,3,0,0,0,0,g94D7)
  | _ => emptyPacking
def g94I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 13 0 8 2 2 g94H5
  | 6 => lookupWord 4 17 4 10 4 2 g94H6
  | 7 => lookupWord 3 31 3 9 2 3 g94H7
  | _ => fun _ => none
def g94 : Forest := ⟨94,7,fun i => g94Y[i]?.getD (0,0),g94C,g94A,g94L,g94I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P4_0 : block g94 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B4 : block g94 4 0 3=true := g94P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5_0 : block g94 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P5_1 : block g94 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B5 : block g94 5 0 10=true := (@block_merge g94 5 0 1 9 g94P5_0 g94P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P6_0 : block g94 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B6 : block g94 6 0 3=true := g94P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94P7_0 : block g94 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g94B7 : block g94 7 0 1=true := g94P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g94 0 0 0 = true)
  · exact (rfl : block g94 1 0 0 = true)
  · exact (rfl : block g94 2 0 0 = true)
  · exact (rfl : block g94 3 0 0 = true)
  · exact g94B4
  · exact g94B5
  · exact g94B6
  · exact g94B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 8 := lower_forest (g:=g94) (i:=0) (hints:=16913456) (before_sound K91 V91) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K91 8 [(94,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V91 low94 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff80ffe03ffff0,0x1ff80ffc0009ede81c0])),(BitVec.ofNat 152 (word80 [0x45a8a51a2a458a12a2,0xd4251a148b009e8eb6db]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffc07fff,0xfe0000fffff8da218e07])),(BitVec.ofNat 152 (word80 [0x8130362c0c891304c0,0x98362c191248d2019249]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xffffff00000ff10e7038])),(BitVec.ofNat 152 (word80 [0x1c038300f0e1c0700,0xe038301e1c0ad10a1249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff,0xffffffffff99af6d003f])),(BitVec.ofNat 152 (word80 [0x1602c040b01020580b,0x14000a000112c646db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x18030000c00000600c,0x18040c0202500704924]))),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := [(2,0,101,0,4)]
def g103A : List (List Nat) := [[],[33]]
def g103D4 (j : Nat) := if j=0 then 0x3f else 0
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
theorem g103G : graphValid g103 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=1049942) (before_sound K94 V94) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K94 5 [(103,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V94 low103 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe007fe1ff0fffc01f,0xffe1ff0ff92b0a00f00f])),(BitVec.ofNat 152 (word80 [0x942509442220128941,0x4044222099220a333333]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffe0,0x1ffffff01c56b90f0ff0])),(BitVec.ofNat 152 (word80 [0x180601880402030181,0x80800402084609111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe001ffff239766f000ff])),(BitVec.ofNat 152 (word80 [0x204812004844240202,0x5084800201164444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffe00001369f8000f00])),(BitVec.ofNat 152 (word80 [0xc1705c117088b82c14,0x160170441329f0eeeeee]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0x18060018000c03018,0x18118088468880888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(0,32,73,2,5),(1,0,106,0,5),(32,0,75,0,5),(2,32,73,0,4),(8,0,99,0,4),(64,0,43,0,4)]
def g107A : List (List Nat) := [[],[99]]
def g107D4 (j : Nat) := if j=0 then 0x5ed4142 else 0
def g107D5 (j : Nat) := if j=0 then 0x108404fd42 else 0
def g107H5 (j : Nat) := if j=0 then 0xb0 else 0
def g107D6 (j : Nat) := if j=0 then 0x2c458bf else 0
def g107H6 (j : Nat) := if j=0 then 0x3 else 0
def g107L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g107D4)
  | 5 => (1,1,3,0,0,0,0,g107D5)
  | 6 => (1,0,3,0,0,0,0,g107D6)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g107H5
  | 6 => lookupWord 1 2 0 4 0 0 g107H6
  | _ => fun _ => none
def g107 : Forest := ⟨107,6,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P4_0 : block g107 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B4 : block g107 4 0 1=true := g107P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 1=true := g107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P6_0 : block g107 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B6 : block g107 6 0 1=true := g107P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact g107B4
  · exact g107B5
  · exact g107B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=1048627) (before_sound K103 V103) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K103 7 [(107,[]),(117,[33,67]),(157,[48,65,33,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V103 low107 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(0,32,73,4,5),(32,0,77,0,5),(1,0,108,0,4),(4,32,73,0,4),(8,0,101,0,4)]
def g109A : List (List Nat) := [[],[48]]
def g109D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g109D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g109H5 (j : Nat) := if j=0 then 0xe else 0
def g109D6 (j : Nat) := if j=0 then 0x18989f else 0
def g109H6 := limbs80 #[#[0x1580001a010007200000,0x44000000]]
def g109L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g109D4)
  | 5 => (3,1,3,0,0,5,0,g109D5)
  | 6 => (1,0,3,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g109H5
  | 6 => lookupWord 1 19 0 7 2 1 g109H6
  | _ => fun _ => none
def g109 : Forest := ⟨109,6,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P4_0 : block g109 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B4 : block g109 4 0 1=true := g109P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P5_0 : block g109 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B5 : block g109 5 0 3=true := g109P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6_0 : block g109 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B6 : block g109 6 0 1=true := g109P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0 = true)
  · exact (rfl : block g109 1 0 0 = true)
  · exact (rfl : block g109 2 0 0 = true)
  · exact (rfl : block g109 3 0 0 = true)
  · exact g109B4
  · exact g109B5
  · exact g109B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=2098435) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 7 [(109,[]),(115,[33,67]),(158,[16,66,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)
def g110Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xfff0fffff95e0200f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028281,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0x1fff0ff01c35b90f0f00])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0305,0x81402042183511333333]))),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb028160058442c0406,0x5844280213164666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02828,0x16000b040348e8cccccc]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x18088c08468880888888]))),(0x0,0x0),(0x0,0x0)]
def g110C : List ColumnInfo := [(4,0,106,0,5)]
def g110A : List (List Nat) := [[],[97,82]]
def g110D5 (j : Nat) := if j=0 then 0x3f else 0
def g110L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g110D5)
  | _ => emptyPacking
def g110I (_ _ : Nat) : Option (Nat × Nat) := none
def g110 : Forest := ⟨110,5,fun i => g110Y[i]?.getD (0,0),g110C,g110A,g110L,g110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P5_0 : block g110 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g110B5 : block g110 5 0 1=true := g110P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110T : checkedTables g110 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g110 0 0 0 = true)
  · exact (rfl : block g110 1 0 0 = true)
  · exact (rfl : block g110 2 0 0 = true)
  · exact (rfl : block g110 3 0 0 = true)
  · exact (rfl : block g110 4 0 0 = true)
  · exact g110B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110G : graphValid g110 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low110 : Lower true (varsX 110) (graphGoal 110) 6 := lower_forest (g:=g110) (i:=0) (hints:=17831216) (before_sound K109 V109) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K110 := extendKnown K109 6 [(110,[]),(118,[33,67]),(229,[16,112,48,67]),(236,[113,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V110 : Known true K110 := extend_ok (m:=110) V109 low110 (by decide +kernel)
def g122Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc007ff01ffe03fffff,0xffffffffff9ceb9d01ff])),(BitVec.ofNat 152 (word80 [0x809002040240800120,0x8090000800403851249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff80001ffffc07ff0,0x3ff80fffff19e0b0e07])),(BitVec.ofNat 152 (word80 [0xa215458548a150a43,0x50921a290a51980a2492]))),((BitVec.ofNat 152 (word80 [0xfffffffe0000007fff,0xfc0000ffc00f8a66f000])),(BitVec.ofNat 152 (word80 [0xcc198906713261382,0x60dc2c32130d8a46b6db]))),((BitVec.ofNat 152 (word80 [0x7fff,0xffffff000009f56c0038])),(BitVec.ofNat 152 (word80 [0x2f05e0e1781c385c0b,0x82e030bc1c09f4686db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x30060001800000600c,0x30040c0202244304924]))),(0x0,0x0),(0x0,0x0)]
def g122C : List ColumnInfo := [(16,0,106,0,5)]
def g122A : List (List Nat) := [[],[97,84]]
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
theorem g122G : graphValid g122 (boundsBefore K110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low122 : Lower true (varsX 122) (graphGoal 122) 6 := lower_forest (g:=g122) (i:=0) (hints:=18223152) (before_sound K110 V110) g122G g122T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K122 := extendKnown K110 6 [(122,[]),(124,[33,67]),(151,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V122 : Known true K122 := extend_ok (m:=122) V110 low122 (by decide +kernel)
def g203Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7f01fc7f01fc7e7fc,0x7f1f9fe7ea000f00f0f])),(BitVec.ofNat 152 (word80 [0x50a14290a142905028,0x50a414051ea111111111]))),((BitVec.ofNat 152 (word80 [0x7ffe007ffe007f9ff,0xf801fe7f8b700f00f0f0])),(BitVec.ofNat 152 (word80 [0x60c18320c183208430,0x60c821084b7111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8000007fffff801ff,0xfffe007fe640f00f00ff])),(BitVec.ofNat 152 (word80 [0x810204010204010040,0x81004010000222222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff800000001ff,0xffffff8001af000fff00])),(BitVec.ofNat 152 (word80 [0x20408020408020081,0x2008020000444444444]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x181ffff00000])),(BitVec.ofNat 152 (word80 [0x40810040810040102,0x4010040000888888888]))),(0x0,0x0)]
def g203C : List ColumnInfo := [(1,0,202,0,7)]
def g203A : List (List Nat) := [[],[118],[99],[99,115],[115,99],[115],[16],[16,118],[16,99],[16,99,115],[16,115,99],[16,115]]
def g203D7 (j : Nat) := if j=0 then 0x3f else 0
def g203L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g203D7)
  | _ => emptyPacking
def g203I (_ _ : Nat) : Option (Nat × Nat) := none
def g203 : Forest := ⟨203,7,fun i => g203Y[i]?.getD (0,0),g203C,g203A,g203L,g203I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203P7_0 : block g203 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g203B7 : block g203 7 0 1=true := g203P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203T : checkedTables g203 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g203 0 0 0 = true)
  · exact (rfl : block g203 1 0 0 = true)
  · exact (rfl : block g203 2 0 0 = true)
  · exact (rfl : block g203 3 0 0 = true)
  · exact (rfl : block g203 4 0 0 = true)
  · exact (rfl : block g203 5 0 0 = true)
  · exact (rfl : block g203 6 0 0 = true)
  · exact g203B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203G : graphValid g203 (boundsBefore K122) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low203 : Lower true (varsX 203) (graphGoal 203) 8 := lower_forest (g:=g203) (i:=0) (hints:=51) (before_sound K122 V122) g203G g203T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K203 := extendKnown K122 8 [(203,[]),(217,[48,65,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V203 : Known true K203 := extend_ok (m:=203) V122 low203 (by decide +kernel)
def g205Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff01ff1ffffc03f,0xe1fe1fffd19d300f00ff])),(BitVec.ofNat 152 (word80 [0x1440a140a408028281,0x44044008018931111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffe001fc7fffc0,0x1ffe1fc4d3aa0000f00])),(BitVec.ofNat 152 (word80 [0x5892c192c8514b2325,0x892805114d3aabbbbbbb]))),((BitVec.ofNat 152 (word80 [0x1ffffffe007fffff,0xfe0001ffbe1b40f0f00f])),(BitVec.ofNat 152 (word80 [0x6103020300620c0406,0x3088203e1002222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe0000000007fffff,0xfffffe000be08f00fff0])),(BitVec.ofNat 152 (word80 [0x800404040080100808,0x400040000004444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x1808180100603030,0x118111824046c8888888]))),(0x0,0x0)]
def g205C : List ColumnInfo := [(4,0,201,0,7)]
def g205A : List (List Nat) := [[],[115],[48],[48,112],[112,48],[112]]
def g205D7 (j : Nat) := if j=0 then 0x3f else 0
def g205L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g205D7)
  | _ => emptyPacking
def g205I (_ _ : Nat) : Option (Nat × Nat) := none
def g205 : Forest := ⟨205,7,fun i => g205Y[i]?.getD (0,0),g205C,g205A,g205L,g205I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g205P7_0 : block g205 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g205B7 : block g205 7 0 1=true := g205P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g205T : checkedTables g205 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g205 0 0 0 = true)
  · exact (rfl : block g205 1 0 0 = true)
  · exact (rfl : block g205 2 0 0 = true)
  · exact (rfl : block g205 3 0 0 = true)
  · exact (rfl : block g205 4 0 0 = true)
  · exact (rfl : block g205 5 0 0 = true)
  · exact (rfl : block g205 6 0 0 = true)
  · exact g205B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g205G : graphValid g205 (boundsBefore K203) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low205 : Lower true (varsX 205) (graphGoal 205) 8 := lower_forest (g:=g205) (i:=0) (hints:=1539) (before_sound K203 V203) g205G g205T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K205 := extendKnown K203 8 [(205,[]),(206,[16]),(233,[82,66,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V205 : Known true K205 := extend_ok (m:=205) V203 low205 (by decide +kernel)
def g211Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0)]
def g211C : List ColumnInfo := [(2,0,209,0,7)]
def g211A : List (List Nat) := [[],[118],[64],[64,118]]
def g211D7 (j : Nat) := if j=0 then 0x3f else 0
def g211L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g211D7)
  | _ => emptyPacking
def g211I (_ _ : Nat) : Option (Nat × Nat) := none
def g211 : Forest := ⟨211,7,fun i => g211Y[i]?.getD (0,0),g211C,g211A,g211L,g211I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211P7_0 : block g211 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g211B7 : block g211 7 0 1=true := g211P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211T : checkedTables g211 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g211 0 0 0 = true)
  · exact (rfl : block g211 1 0 0 = true)
  · exact (rfl : block g211 2 0 0 = true)
  · exact (rfl : block g211 3 0 0 = true)
  · exact (rfl : block g211 4 0 0 = true)
  · exact (rfl : block g211 5 0 0 = true)
  · exact (rfl : block g211 6 0 0 = true)
  · exact g211B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g211G : graphValid g211 (boundsBefore K205) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low211 : Lower true (varsX 211) (graphGoal 211) 8 := lower_forest (g:=g211) (i:=0) (hints:=100) (before_sound K205 V205) g211G g211T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K211 := extendKnown K205 8 [(211,[]),(213,[33,116,100]),(218,[16,64,32,50]),(234,[48,81,32,100,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V211 : Known true K211 := extend_ok (m:=211) V205 low211 (by decide +kernel)
def g230Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc3fe01ff0fffff00f,0xfff0fff0fe542f0071c7])),(BitVec.ofNat 152 (word80 [0x28814140a20400a0a0,0xa0220022081425049249]))),((BitVec.ofNat 152 (word80 [0x3fffe000fe1ffff0,0xfff0fff015971c00e38])),(BitVec.ofNat 152 (word80 [0x31218190c40850c8c8,0xc840284020587156db6d]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff001fffff,0xf0000ffff2a37683803f])),(BitVec.ofNat 152 (word80 [0x420a0a050050850101,0x284428002a102892492]))),((BitVec.ofNat 152 (word80 [0xffc0000000001fffff,0xfffff000013c8afc0fc0])),(BitVec.ofNat 152 (word80 [0x800c0c060861060202,0x300030441208a892492]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0xce2917ff000])),(BitVec.ofNat 152 (word80 [0x3010180080180c0c,0xc088c08844210724924]))),(0x0,0x0)]
def g230C : List ColumnInfo := [(4,0,226,0,5)]
def g230A : List (List Nat) := [[],[101],[113],[113,101]]
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
theorem g230G : graphValid g230 (boundsBefore K211) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low230 : Lower true (varsX 230) (graphGoal 230) 6 := lower_forest (g:=g230) (i:=0) (hints:=286262608) (before_sound K211 V211) g230G g230T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K230 := extendKnown K211 6 [(230,[]),(244,[65,82,49,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V230 : Known true K230 := extend_ok (m:=230) V211 low230 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe0001ffffffff001ff,0xc7447c36a8a740007c1f])),(BitVec.ofNat 152 (word80 [0x420d42094205202c05,0x740543288a21294a529]))),((BitVec.ofNat 152 (word80 [0xffffe0001ffffffe00,0x18dfc238d4e081f003e0])),(BitVec.ofNat 152 (word80 [0x8049804d8046404809,0x88c4c230d0608a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffffffe000000000,0x2761e3d10b58be0f8000])),(BitVec.ofNat 152 (word80 [0xe000e001780700e,0x5416390085886318c63]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xe819257c4e4f400003ff])),(BitVec.ofNat 152 (word80 [0x1490149014980500a0,0x2019214c060d65294a52]))),(0x24569a07773c000ffc00,(BitVec.ofNat 152 (word80 [0x18e018e018e0098130,0x201688057704294a5294]))),(0x13aa5dc49781bff00000,(BitVec.ofNat 152 (word80 [0x1f001f001f000e01c0,0x122a1c440781318c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(8,0,55,0,5),(9,0,54,0,4),(10,0,53,0,4),(17,0,46,0,4),(20,0,43,0,4),(34,0,29,0,4),(36,0,27,0,4)]
def g63A : List (List Nat) := [[],[33,67],[16,84],[16,32,83,67],[32,16,67,83],[32,83],[48,65,82],[48,81,66,16,32],[64,49,82,16,33],[64,81,50],[80,49,66],[80,65,50]]
def g63D5 (j : Nat) := if j=0 then 0xb7d8d10 else 0
def g63D6 (j : Nat) := if j=0 then 0x683faa1fd10 else 0
def g63H6 (j : Nat) := if j=0 then 0xf0 else 0
def g63D7 (j : Nat) := if j=0 then 0x335611bf else 0
def g63H7 := limbs80 #[#[0xc9000012e00003c4002,0x1650029941e900486580]]
def g63L : Nat → Packing
  | 5 => (1,2,3,0,0,0,0,g63D5)
  | 6 => (2,1,3,0,0,4,0,g63D6)
  | 7 => (1,0,3,0,0,0,0,g63D7)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g63H6
  | 7 => lookupWord 2 17 2 9 1 4 g63H7
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
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
theorem g63P6_0 : block g63 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 2=true := g63P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 1=true := g63P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 7 := by
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K230) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := lower_forest (g:=g63) (i:=0) (hints:=1049651) (before_sound K230 V230) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K230 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V230 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffe001ffffff01fc,0x5eab85c0600001f07c1f])),(BitVec.ofNat 152 (word80 [0x500540d40940522c50,0x5e8300c0610842108421]))),((BitVec.ofNat 152 (word80 [0x3fffffe001ffffe01,0x9993613740003e0003e0])),(BitVec.ofNat 152 (word80 [0x988984984d84644899,0x9993013545294a5294a5]))),((BitVec.ofNat 152 (word80 [0x3ffffffffe0000002,0x54dc3874c007c00f8000])),(BitVec.ofNat 152 (word80 [0xe02e00e00e017870e0,0x548c3874c318c6318c63]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffffffe,0xa08ef66320f8000003ff])),(BitVec.ofNat 152 (word80 [0x13009009009800002,0x200cf6020a5294a5294a]))),((BitVec.ofNat 152 (word80 [0xfc0000000000000002,0x4970938fdf00000ffc00])),(BitVec.ofNat 152 (word80 [0x1c00e00e00e008102,0x170830b0c6318c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [1,0x37050a181ffffff00000])),(BitVec.ofNat 152 (word80 [0x20010010010000000,0x108421084210]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(1,0,94,0,8),(2,0,93,0,7),(4,0,91,0,7),(8,0,87,0,6),(16,0,79,0,6),(6,0,89,0,5),(9,0,86,0,5),(10,0,85,0,5),(12,0,83,0,5),(18,0,77,0,5),(20,0,75,0,5),(64,0,31,0,5),(11,0,84,0,4),(14,0,81,0,4),(22,0,73,0,4),(66,0,29,0,4),(68,0,27,0,4)]
def g95A : List (List Nat) := [[],[33,67]]
def g95D4 := limbs80 #[#[0x32a87993746007154d43,0x81dc16550f1c304c0ae0,0x75c830db92a921e38e0b,0xaa74e39259170185538,0xf624c3021e730b22e03]]
def g95D5 := limbs80 #[#[0x5d9544c7955915354531,0x4c63de0576551318fb80,0xe0576d51318ef825d954,0x507318ef825d2654c63d,0x9e7825d351cc67560e75,0xdc554cc67560f7155331,0xcc63ee017655331cb564,0xe0974997318ef825d954,0xd4d41f155350d515063b,0xa9f8654d43d063be0976,0xdc553d073558f7154f41,0xd07275d163d4f419b584,0xe095458f41a5f8558f53,0x58f41ad9801d563d07a3,0xacd821d563d06b560475,0x9d563d06b5e057558f41,0x54679e0974d4551c5f75,0x54f7150f518ef825d363,0x50f51cd563dc543d4755,0x97585dc543d472d59371,0x5d943d463ee017650f51,0x50f0fd977454d438ef82,0x6046554d43a798019553,0x54d438fb805d95350e9d,0xd97741c55350ef460071,0x1955350f351db7154d43,0x50ed56046554d43b5980,0xe1d6519543c79655c065,0x59543cf1815c06550e1f,0xcf371dc16550f3c1c770,0xdc16550f3c2077059543,0x50f39dc87159543cf381],#[0xdd37359543ce772dc565,0x58a43ec78154d6290f27,0x8ed86dc95490eb360f54,0x5516014fb4e055358053,0x14f35e1d5358453aeb82,0xe055358853ae78255161,0x54c538ef875516214fb1,0xcd776dc55314fa559371,0x5c06154f35e077654c53,0x54f3cd917018553cf164,0xe096418553af38059061,0xd85538f7875906154eb9,0xae7825936154ebce0164,0x5d36154e3ee0174d8553,0x54eb9e0954d85538ef82,0x60c74d8553e375495361,0xd8553cb5741d36154eb5,0xae7825d36154ebce0174,0x5906454e73e0974d4d53,0x94e73e0974d4e538bf87,0xe0576d4e53b4f825d353,0x3c00ae9801c964d4f95,0xfc390cc2d09c2106c15,0x1e0721b06615c5112c45,0x2a0a2270962408a2107e,0x360d2330c6300ba2d0ae,0x4450b414f63c0ea390de,0x5053b4d52f4a52347517,0x5c56b5955f5655353547,0x6859b6558f625835f577,0x7b1e6781da751ce721b9,0x872168420a811fe7e1f2],#[0x2418d22e8a222,0x1020800000000000,0x0,0x90400000000000,0x0,0xe2300400000000000000,0x6182]]
def g95H5 := limbs80 #[#[0x1e0000,0x6a0000000000000,0xe2,0x500000000980000,0x168]]
set_option maxRecDepth 16000 in
def g95D6 := limbs80 #[#[0x67bb8aca98f555354531,0x1baae7a8e63d554f51cc,0x677b92caa0e7565d473,0x439dee4b26a3a755163d,0x50e7ab88caa1cf970195,0xa439eee2b2a873edc165,0x114f6ca9ac029ecd5358,0x4c53d9aa6b10a7b554d6,0x6154e6fbb2a629e9d645,0x59353cbaeda9ca77c5c0,0xd514c7f2a92a290cef72,0x154d31deac8a8a63f554,0xc9544c76eb22a698fd77,0x7655131d7ac8aa2637bd,0x5c7544c67fbb2a898cfd,0xd76d5131bbae7aa2637d,0xfdd5644c77bb8ac898cf,0xff7459531deee2b2a633,0xf554d41cc67eba4ca98c,0xef56550731f6aa8a0e63,0x3f554f51cc6fb3aa8398,0x8df574d4731faae7a8e6,0x63bd5db51cc77ab2ea39,0x98edd6454f31faee2a9e,0x6637bdc954cc6fbb8aa9,0x998cfd7655331d7ac8aa,0xa663775cf54cc67fbb2a,0xcb98cff75593319faeda,0x32e633fdd165cc77bb8a,0xaa2a0fb543545419fae9,0x8a8a83ddd4d51507baa9,0x9a86a0fb77150d41f6aa],#[0xeaa1a83af59543507cea,0xb8aa6a0dbf7550d41b7a,0xae3a9a833fdd953506fb,0xebb6a6a0dbd74d4d41be,0x5ee4aa283eddc5545067,0x7bb8acaa0dbf7355141f,0x9fee6b2a83bbdc965507,0x7cea9a87a0cfd7399541,0x1b7aeaa1e83af59543d0,0x6fbb8aa7a0dbf7550f4,0x419faeca9e83b758d53d,0xd076eb1ea7a0cff7654f,0xf419faeda9e836f5d353,0x3d067fbaac7a0ebd5458,0x8f41dbaeab1e83b71d56,0x54d076fbaac7a0ede755,0x59741b7ee6aa683ebdc9,0xf515467eb9ccba0cff73,0x4d4551beae7a8aa3dd54,0x8d43547aea9a86a8df57,0x7154d519feeca1aa3b7d,0x5d363547bbb8aa6a8df7,0xf7255151beee2aa2a33f,0xf5cf64546f7b92c8a8de,0x5d5350f51beee2a1ea33,0xaf59143d476eb1a87a8f,0xcff7650f519faeca1ea3,0x3bddc563d47bbb8aa7a8,0x8def72553519fee8b1ea,0xa3bbdc964d46f7b92c9a,0xa1edd53d85439fee6b26,0xa873f5d76150f5eaa6c2],#[0x6a1dbf7454d43beee2a9,0x9a879fd955350f3e32aa,0xa6a1fd47154d439faeca,0xa9a8777dc95350febb8a,0x2a6a1f9e5454d43f3aa8,0xaa9a87e7dd15350fce3a,0xb2a6a1f5f6554d43eb8c,0xeb29a87e79525350f6e3,0xba6a6a1dde7694d43bba,0x2e032a879fd975350ede,0xeb28caa1df57119543bf,0xf6e0b2a873f9d86550f3,0x3fb2acaa1df77159543b,0xde8e2b2a87bedc16550f,0xe7fb8acaa1ef77159543,0x39fee6b2a87b7dcd6550,0xe7eb9ccaa1e7f659954,0x43ddaa8b14873f5c7655,0x90febb8aa721eef5458a,0x243bdee4aa487b7dd953,0x490f3eb2aa921ddf7355,0x5243bbae7aa4879f9955,0x6014f7caa2c029e7d65d,0x58453deaa8b08a7be951,0x16214f76aa2c429ef654,0x454c53faee2a98a7bb95,0xc95414f6fbb2a629edd6,0x64950539feecaa0a77bd,0x5906154e7ebb4a829ebd,0x67618553deec830aa7bd,0xdd8b6154f7ab16c2a9df,0xf763d8553faea7b0aa7b],#[0xbd1936154febb9ec2a9e,0xef664d8553deac9b0aa7,0x73f5d36154f7bb26c2a9,0x9ef772d8553deae5b0aa,0xa7bd5536154f7bb9ec2a,0xa9ef754d8553deca9b0a,0xaa7bd5d36154f7a3a6c2,0x4a9ef774d8553dece9b0,0x9aa73f5d36254efbb8ac,0xa8a9ddf7355153bbae9a,0x2a2a7cfd525454eeeb9c,0x2c8a9ebd6419153d7ec9,0x4b22a77ddc56454efdb8,0x24c8a9df57199153bdee,0xe5b22a73f5c76454f5fb,0xba6a729f5e54d4e539fa,0xce9a9ca7d75d35394eee,0x7b92c9a9ddd7395253eb,0xd8e4b26a73fdc564d4ef,0x7fb92c9a9eef7259353d,0x101d81801280b0078002,0x83c03883703182c02682,0x6685d05785204c847041,0x508187c07887506f86c0,0x89809489108f88a08688,0xaa8a70a38a209e89d099,0xf0bb8ba0b68b30b18b00,0x8d40ce8cd0cb8c80c28b,0xe68e50e18e00de8db0d9,0xf0fb8f80f48f10ed8ea0,0x91210e90d1099081048f,0x2a92712191e11a919115],#[0xd13993813493112d92c1,0x95415094f14b94614293,0x6c96b169966162959155,0x317f97e17897316f96e1,0x99a19699318d98a18698,0xb09a91a59a21a099d19b,0x71c39c01be9bb1b79b61,0x9d81d69d51d19ce1ca9c,0xf29ef1eb9e81e09dd1db,0x9205a04202a011ff9fa1,0xa2221ea1b217a1220ca0,0x30a2d229a28226a25223,0x7243a42240a3d23ba362,0xa5c258a55251a4c248a4,0x74a7126da6a264a6325f,0x9285a84282a7f27ba782,0xaa62a2a9d299a98292a8,0xbcabb2b5ab22aeaad2a9,0x32cface2ccac72c5ac42,0xae42e2add2d9ad82d6ad,0xf6af32efaec2eaae92e5,0x7305b02300afd2fbafa2,0xb1a316b1330fb0c30ab0,0xe00d0f27b24322b1f31d,0x83f8020f07e00f8010b,0xb078020ae00b80107e0,0x7e00b80103802c2100f,0xe0081f80207e0081c182,0x8020f090d0c101f80207,0x82c10b0408042e0041f,0x400200082c1002410341,0x81001c1001c100041030],#[0x4107040001004209040,0x81043d04281041c102,0x10400200080e8820,0x10904241230408101041,0x41034209041410424,0x4100081010410100101,0x504100002043c2420107,0x4104810a0c100041030,0x101000c100101030108,0x4105041046260071,0x41002d0c20b430804100,0x2042d042830410104050,0xc1014104001040003c10,0x1041c100080020342c10,0x21040410207041c10404,0x4003000400004002841,0x8a842c30404841090408,0x20b0424100000004a109,0x2c103048810321081084,0x17802000400100000000,0x1000410000004001e008,0x6101030484144030820,0x588104040c8420000103,0xb048810b058810b0,0xc0828442c1c0101c1,0x14160050c16260080c1,0x89803010c84243050c10,0x2041c100002000800025,0x8410006260090c10006,0x4000101c107041000400,0xc10b0400304021040210,0x400304003042c162040],#[0x2]]
def g95H6 := limbs80 #[#[0x1c380062c0861c1800b,0x58002084023c2651c0,0x621e4424eb2a5543a82e,0x8004088b092963f,0xf000850b27806d112450,0x4db17e410000000008a,0x52637c4ba828b1b15000,0x8043c32305000c040123,0xd01000a2bf36b4900011,0x31b14000000d1010e81c,0x8b48835007000953000b,0x74a00072f00033ac0f33,0x28cad000e4c024519d88,0xcc3d902c0c484703c097,0x31ed55342a1f34682293,0x3902dcb211a0004a3913,0x14f00a000f231511a2a,0x4333348a942000023b00,0x90d000f40b1b000c3e,0x511d72cd3010b0000000,0xe2ed26fae000000047c2,0x16]]
set_option maxRecDepth 16000 in
def g95D7 := limbs80 #[#[0xb58a43b798f41b758f41,0x58453be58053e7d0e43b,0x9053af59053bb58853bd,0x521d7d4e53bdd8553af9,0x31bf99521bf59521fd54,0x1bf59131f754d31fd545,0xfd50731bf99531bf5953,0xf59331f754f31fdd4731,0x54541bf99731bf59731b,0x9541ef55141ef50d41fd,0xf41ef50f41bf99541bf5,0x41bf59741ef55341bf58,0x1bfd8951fdd4551bf997,0xbfd8d51dfd4d51df54d5,0xf54f51bf58b51bfd9151,0x59351bf58f51dfd4f51d,0x8543bf99443bf59443bf,0x543f794d43f754d43bfd,0x43bf99543bf59543bf19,0x3bf59243f754e43bfd95,0xf754c53bf99643bf5964,0xd18553bf99453bf59053,0xd8953bfd8553fdd8553f,0x4e53bfd9153f7d4d53bf,0x753bf59653bf59253f7d,0x31bf59353bf58b53bf58,0x1ff55331ffd5131ff551,0xffd4d41ff54d41ffd533,0xf54951ffd4f41ff54f41,0x54d51ff50d51ff58951f,0x9151ff55151ff58d51ff,0xf51ff54f51ff50f51ff5],#[0x43ff59351ff55351ff58,0x3ff54d43ffd8543ff585,0xff59543ff19543ffd4d4,0xf55243ffd9543ff99543,0x95053ff55053ffd5243f,0x8953ffd8553ff58553ff,0x153ffd4d53ffd8953ff5,0x53ffd5153ff95153ff55,0x3ff99153ff59153ff191,0xffd5253ff95253ffd915,0x1b000ff99353ff59353,0x90e70c50a308105f03d,0x1d51b318a16814612b1,0x2a728c27124f22d20b1f,0x8e37335833630d2eb2c9,0xc45343140f3ed3d23b03,0x53a5184f64db4c049e47,0x1a5f85d65b459257755c,0xb7026e76cc69566c63c6,0x8137ea7c879f77d75472,0x18d88b689b88085e83c,0x69db9b299096e9459239,0xa98a7da62a4ea33a119f,0x55b33b1fb0bae9aceab3,0x4bf0bd5bbaba6b92b70b,0xcb4ca7c85c55c3ac18c0,0x94d79d65d3cd13cf1ccf,0x5e21e0ddf2dd0dbcda8d,0xec2ea7e9ae86e6be57e3,0x803890426010241c0283,0xb101c308202600e24411,0xe20b11803882c4600e20],#[0xc8c018809803882c4600,0x1478ec03441623007110,0x6863b00b1a2101e3b00d,0x82c4e01a20bc03431f80,0x64061300d1620f098068,0x83f04110201c1203c02,0x2058a130411020bc0244,0x12343463f00e10241c0,0xc2c41e0f00e105e01c1e,0xbc028389805070c1e01,0x162838380509047e0142,0xe12181c0404070700a,0xd107e01a18fc03431e37,0x80d1018ec03c4083f00,0xd105e00e18bc03431d8,0x1300710583c038416130,0x6162700d10404c01c410,0x588c01c5c42d0830980,0x38032004104078078e1,0x28202101e0148601e182,0x82c208c01c516104600e,0xc4082300716284118038,0x16284162300714588c01,0x1e010789c034408203e0,0xf102601a184c0343c486,0x5880808b07805200f00,0x118038a103e0102080f8,0x26020344098078d10584,0x70c2220e18104105e014,0x85890618444041882c48,0x307042062c3890c1890,0x88407850e0901e18b0e1],#[0x1e20f0e10f0e10407047,0x203170441e8848611141,0x4862d1090c5870858708,0x1080c4068420e2421688,0xd121401018c0c5840c5a,0xb080c31608b44850082,0x802c2161018812122062,0x3842c242830050909141,0x21634220342160d0863c,0x5042030d141080c4820c,0x210444850080c4850458,0x618b0420308584061a11,0xb042221]]
def g95H7 := limbs80 #[#[0x80520914050946f1a8c7,0x8c4c2ba632026403043,0x5405bc8001ada219037,0x58001980814002038494,0x6d6f3216602c2458401,0x2346fd80000001e9400,0x791e70a74000889e0400,0xfa10000000a,0xa4e000000148692f8,0x20c4000c300000000000,0x66ac196870000000108,0x3a04b5a1d1cb21964d17,0x9a542c2c15ecdca1763,0x22bc4e08e9b61625db,0x868e4d00a989916c0910,0xba9c9bcd080001740003,0x2d80000000000098f680,0xda000000,0xe8000000000000371f40,0x92255f28b8000461d1,0x87800000064400000000,0x1eb00007,0xf83c000a1a7701c24000,0xc19f151966cd88ecd51,0x3c80001c2b3d043a800,0x2b5400135400,0x6f86190a4c460004a500,0x15a0000000000c,0x45de328,0xb5b2c091720000000000,0xff140e6258c000f1122f,0x1f3e3d9bc800023573a],#[0xc1b6e3000000016d80,0x2ec7e6d000784c0000,0x6e6628603b56200061f0,0x1324b4be58d414032f4c,0x4a10000003b76000167,0x65cfbac00,0xc79430007004000aa900,0x3a58b400000044c0b150,0x5ac00043b2add5ce6373,0x2478001c627038b46,0x2599a95146800377be1d,0xd6ee20f4e200044f000,0x27866a1f9451dc3ac400,0x4e0007aa33226648b589,0x38460007562b87e176,0x28be203090d5a44ab4b0,0xb9de52744b83f8c74001,0x162700000001828bff39,0xfc1d691c681000013000,0x88000dce4155a6cc0201,0x3de896adecaa9572ccaa,0x10de0004968001edc4,0x48d5687cd00000002c7c,0xb8c4535c846858595,0x5af409581a991bf50398,0x19a488f3dd1a7c8cbae,0x38d17da8b298c7ca2780,0x1151b1c1b0003d363440,0x63c20b52d7262835743a,0x32c9d4c000000738fcc3,0x524324a99e00a000,0x880038ba83d355d80c00],#[0x1a69669800104000002,0x70e800027850a00000,0xb42ca970b64990,0x54d306000000035d68ec,0x30fc0002c080b89212a4,0xfa5800,0x588086a710681794e400,0x67598000000000710de,0x106c172390331b2c0008,0x4b5c0007e4e4de,0xd91fb58abd55e714c452,0x2464389fb52cd93e,0x1242076800000]]
def g95D8 := limbs80 #[#[0xf41fea0ffcc7fa63fd21,0x87fd43fe21ffd47faa3f,0x3fea7fe53fea9ff14ffc,0x3a998a8421989c300c00,0x3433a0343cc5eab92c84,0xa10780e0c9060204260,0x3a034504f3a03451c18,0x1c528980d1081201c405,0x4410204b2201c7084220,0x43e03451088071011203,0x40]]
def g95H8 := limbs80 #[#[0x2000131e0c4850801702,0xc1871e00c0e00141002,0x98000058281025802812,0xc74dc000000003c59080,0xc5a42b0f00031dd90fa,0x58c5cc0024d,0x10dd38a000000114d4fc,0xc0035e40034bc3a26404,0xc012b08742477a6cad9,0x2800307db99850001ca4,0xa9314e698904a17e0797,0x8c8ced04001539d11c1,0x945bc000ced035472da3,0x677ce3b640000020,0xb73800db4780881d8000,0x27271cb53311b0cd815f,0x61217a584446b1c31639,0x4f8cb0002093c1780995,0x43b9f35d6c0000857350,0xb77de6de69e8240f72ed,0xd4a03e4c753d95000355,0xa952c0027c54b8001e7a,0x5cf78380019a40740994,0xd039a8000003d87dbbd3,0x8559b85d9c400042dbc0,0xd685d800000201f089b,0x2dadc20d679e357000,0x77465c4d3ddd1c443334,0x7060002d95cd5d6f516d,0xc6f03149fd90508000d4,0xad62f9d44e95cac04002,0x38c800000257bd180034]]
def g95D9 (j : Nat) := if j=0 then 0x8200ff else 0
def g95H9 := limbs80 #[#[0x326c56d958009378021,0x3940db4b1ddd684003b0,0xbf9000038174c1a730cf,0xcc001ab2247b214a2]]
def g95L : Nat → Packing
  | 4 => (6,5,5,0,0,5,0,g95D4)
  | 5 => (86,4,5,0,0,10,0,g95D5)
  | 6 => (238,3,5,0,0,12,0,g95D6)
  | 7 => (122,2,5,0,0,12,0,g95D7)
  | 8 => (14,1,5,0,0,9,0,g95D8)
  | 9 => (1,0,5,0,0,0,0,g95D9)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 53 0 7 3 0 g95H5
  | 6 => lookupWord 24 127 7 12 7 1 g95H6
  | 7 => lookupWord 74 443 5 13 8 1 g95H7
  | 8 => lookupWord 38 191 7 12 7 1 g95H8
  | 9 => lookupWord 6 31 5 9 4 1 g95H9
  | _ => fun _ => none
def g95 : Forest := ⟨95,9,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P4_0 : block g95 4 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B4 : block g95 4 0 6=true := g95P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 86=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B5 : block g95 5 0 86=true := g95P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 21=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_21 : block g95 6 21 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_117 : block g95 6 117 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P6_213 : block g95 6 213 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B6 : block g95 6 0 238=true := (@block_merge g95 6 0 117 121 (@block_merge g95 6 0 21 96 g95P6_0 g95P6_21) (@block_merge g95 6 117 96 25 g95P6_117 g95P6_213))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_11 : block g95 7 11 63=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_74 : block g95 7 74 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : block g95 7 0 122=true := (@block_merge g95 7 0 11 111 g95P7_0 (@block_merge g95 7 11 63 48 g95P7_11 g95P7_74))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B8 : block g95 8 0 14=true := g95P8_0
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
theorem low95 : Lower true (varsX 95) (graphGoal 95) 10 := lower_forest (g:=g95) (i:=0) (hints:=1075) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 10 [(95,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff5,0xb361d03e280001f0001f])),(BitVec.ofNat 152 (word80 [0x42a135092845216141,0xb261d01428294a5294a5]))),((BitVec.ofNat 152 (word80 [0xffffff8003fffff002,0x16e8554587003e007fe0])),(BitVec.ofNat 152 (word80 [0x4c02601b006424262,0x10605505810842108421]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000009,0xd8c2c299d107c00f8000])),(BitVec.ofNat 152 (word80 [0x17003801c017838381,0x98c24019d118c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffa,0x4fe283ab8f8000003ff])),(BitVec.ofNat 152 (word80 [0x980240120098000008,0x48a282a105294a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [9,0x1711a3877600000ffc00])),(BitVec.ofNat 152 (word80 [0xe00b805c02e0040408,0x711a28226e739ce739c]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300080804,0x41140240048421084210]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7),(4,0,107,0,7),(0,32,73,6,6),(1,0,110,0,6),(32,0,79,0,6),(8,0,103,0,5),(33,0,78,0,5),(64,0,47,0,5),(10,0,101,0,4),(65,0,46,0,4)]
def g111A : List (List Nat) := [[]]
def g111D5 := limbs80 #[#[0x31fb2aa8987595354130,0xeb2a7a86613edc1654c,0x4f3cb2ea1985d973d433,0x53d72a9b02a77c5c4605,0xe35cafb299a06ba54d81,0x183b]]
def g111D6 := limbs80 #[#[0xb58853bd58453be58053,0x54130d7d4e53bed8153b,0x5130f794d30f754d30fe,0x330bfd9530bf59530ef5,0x30ef55330f754f30fed4,0xdf54f50df54d50bf597,0xfed8153fe18153bf58f5,0xf95153ef55153bfd8153,0x95253ef55253bf58253e,0x481e0a83000bf59653ef,0x509c4b241147e3c1b0c0,0xf1d4e46c34998c05a2b9,0x39010b80e1c9a350e843,0x608e08a3e01e008f804,0x60860800060800003820,0x38204608f18400608000,0x182382]]
def g111H6 := limbs80 #[#[0x2100000000000000002,0x8300000065000000000,0x87000,0x921866000000c400000,0xe00]]
def g111D7 := limbs80 #[#[0xd50ff987f4c37ca9bd54,0xa7fe53fea9ff14ffea1f,0xd0bf4d9f0ba3e0f803fe,0x478c0c291228c059d445,0x82453c60628a72c60614,0x828c1239451818e314d1,0x8a3028e410ce58c07194,0xa41460918e41]]
def g111H7 := limbs80 #[#[0x800e0c2334000020420c,0xc6002e65af1ba,0x6b80000d600000000000,0xccd4800b4000000000,0x93122ebd0f2cbc00,0x388880001c900000,0x179dd600000000000000,0x708000000000000000d,0x29c0]]
def g111D8 (j : Nat) := if j=0 then 0x3421017f else 0
def g111H8 := limbs80 #[#[0x10003d80000007,0x2162401c400cc000001a,0x21c00000000014b9]]
def g111L : Nat → Packing
  | 5 => (9,3,4,0,0,6,0,g111D5)
  | 6 => (27,2,4,0,0,9,0,g111D6)
  | 7 => (10,1,4,0,0,9,0,g111D7)
  | 8 => (1,0,4,0,0,0,0,g111D8)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 47 2 8 4 0 g111H6
  | 7 => lookupWord 6 71 4 9 5 0 g111H7
  | 8 => lookupWord 2 29 3 8 4 0 g111H8
  | _ => fun _ => none
def g111 : Forest := ⟨111,8,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_0 : block g111 5 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B5 : block g111 5 0 9=true := g111P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_0 : block g111 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_5 : block g111 6 5 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B6 : block g111 6 0 27=true := (@block_merge g111 6 0 5 22 g111P6_0 g111P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_2 : block g111 7 2 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 10=true := (@block_merge g111 7 0 2 8 g111P7_0 g111P7_2)
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
  · exact g111B5
  · exact g111B6
  · exact g111B7
  · exact g111B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 9 := lower_forest (g:=g111) (i:=0) (hints:=1049907) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 9 [(111,[]),(119,[33,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ffffffffffff00ff5,0x30e690b8f80001f07c1f])),(BitVec.ofNat 152 (word80 [0x408502080010202001,0x30241090c8294a5294a5]))),((BitVec.ofNat 152 (word80 [0xe0007ffc03fffff00a,0x6a955c7c2003e0f83e0])),(BitVec.ofNat 152 (word80 [0x802600100802400022,0xa05506c018c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff800003fffffffb,0x497889211e07c00003ff])),(BitVec.ofNat 152 (word80 [0x50814a0b0a4828288,0x9588821124210842108]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000008,0x94d06b1ab3f800007c00])),(BitVec.ofNat 152 (word80 [0x63018c120c704c4c8,0x84d04b0a325294a5294a]))),((BitVec.ofNat 152 (word80 [9,0x1717a2877400000f8000])),(BitVec.ofNat 152 (word80 [0x17c05f01c2f8070709,0x1717a28134e739ce739c]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0x180060020300080804,0x40032040058421084210]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(8,0,115,0,7),(16,0,107,0,7),(32,0,91,0,7),(0,32,89,2,6),(1,0,122,0,6),(2,0,89,0,5),(2,32,89,0,5),(64,0,59,0,5)]
def g123A : List (List Nat) := [[]]
def g123D5 := limbs80 #[#[0x26fb9aca884ef7259510,0xd3aa9b1aa1a7d8e4154,0x26fb9ac1a8cbd769075,0xf624c3]]
def g123D6 := limbs80 #[#[0xe54110af59641b7d8d50,0xd9510bf59510fd54510f,0x8d50bfd8550ef90550bf,0x750ef90750ef55150f7d,0xbf58351bfd8151bf58,0xaa9a8f7f74644a352010,0x7a49c32e02d602d0caba,0x4144118821882010c450,0x4100620a830a9108208c]]
def g123H6 := limbs80 #[#[0xd80,0x74000000000000009000,0x2c01000360000]]
def g123D7 := limbs80 #[#[0xf50fea87f4437aa9be41,0x38291a0b007fd47faa3f,0xc33964c30d930a25849,0xa69350e3bad24c0ce953,0x8530ec33a54c30c]]
def g123H7 := limbs80 #[#[0x32c00000001280000030,0xd7400025002800001f00,0x400d40000000000025b4,0x35c03a286c802a]]
def g123D8 (j : Nat) := if j=0 then 0x685017f else 0
def g123H8 := limbs80 #[#[0x78000000000d8580,0x29000,0x40000000011000020000,0x13]]
def g123L : Nat → Packing
  | 5 => (6,3,3,0,0,5,0,g123D5)
  | 6 => (14,2,3,0,0,8,0,g123D6)
  | 7 => (7,1,3,0,0,8,0,g123D7)
  | 8 => (1,0,3,0,0,0,0,g123D8)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 31 0 7 3 0 g123H6
  | 7 => lookupWord 3 37 2 8 4 0 g123H7
  | 8 => lookupWord 1 37 0 7 3 0 g123H8
  | _ => fun _ => none
def g123 : Forest := ⟨123,8,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 6=true := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_2 : block g123 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 14=true := (@block_merge g123 6 0 2 12 g123P6_0 g123P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_2 : block g123 7 2 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 7=true := (@block_merge g123 7 0 2 5 g123P7_0 g123P7_2)
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
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 9 := lower_forest (g:=g123) (i:=0) (hints:=1048627) (before_sound K111 V111) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K111 9 [(123,[]),(125,[33,67]),(159,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V111 low123 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffe01fffff7,0x22ca982eb80001f07c1f])),(BitVec.ofNat 152 (word80 [0x25002800404022003,0x2080180ca8294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfff8003ffffffff00b,0x942915d9c2003e0f83e0])),(BitVec.ofNat 152 (word80 [0x600b002800004023,0x802815094018c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffffa,0xd9dc81211e07c000001f])),(BitVec.ofNat 152 (word80 [0x28814c0ab058548288,0x995c8121125294a5294a]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000008,0x4f46b1ab3f8000003e0])),(BitVec.ofNat 152 (word80 [0x3301900cc0906704c8,0x4d40a12b36318c6318c]))),((BitVec.ofNat 152 (word80 [9,0x1713a2877400000ffc00])),(BitVec.ofNat 152 (word80 [0xbc05e02f00e1780708,0x1713a28214c6318c6318]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300101800804,0x40036040048421084210]))),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(32,0,94,0,8)]
def g126A : List (List Nat) := [[],[33,67]]
def g126D8 (j : Nat) := if j=0 then 0x7f else 0
def g126L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g126D8)
  | _ => emptyPacking
def g126I (_ _ : Nat) : Option (Nat × Nat) := none
def g126 : Forest := ⟨126,8,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8_0 : block g126 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B8 : block g126 8 0 1=true := g126P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g126 0 0 0 = true)
  · exact (rfl : block g126 1 0 0 = true)
  · exact (rfl : block g126 2 0 0 = true)
  · exact (rfl : block g126 3 0 0 = true)
  · exact (rfl : block g126 4 0 0 = true)
  · exact (rfl : block g126 5 0 0 = true)
  · exact (rfl : block g126 6 0 0 = true)
  · exact (rfl : block g126 7 0 0 = true)
  · exact g126B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 9 := lower_forest (g:=g126) (i:=0) (hints:=17962032) (before_sound K123 V123) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K123 9 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V123 low126 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x807ffff800fffffe03,0xfc8f2a513a000f000f0f])),(BitVec.ofNat 152 (word80 [0xb0a01506a0940a458,0xa48b0a50321111111111]))),((BitVec.ofNat 152 (word80 [0xff807fffff001ffffc,0x39b89984500f000f0f0])),(BitVec.ofNat 152 (word80 [0x121302604c0d80c891,0x339b8810411111111111]))),((BitVec.ofNat 152 (word80 [0x7fffffffe00000,0x6b760e4a500000f0000])),(BitVec.ofNat 152 (word80 [0x1c1c4b84708e12f0e1,0xc6b760e4a5bbbbbbbbbb]))),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf9627987230f00f000ff])),(BitVec.ofNat 152 (word80 [0x20200c008010030000,0x207183002222222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c46290f000ffff00])),(BitVec.ofNat 152 (word80 [0x10010020040000,0x4444444444]))),(0x665163c4cffff000000,(BitVec.ofNat 152 (word80 [0x4040600600c0180102,0x44042c0c8888888888]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(1,0,206,0,8)]
def g207A : List (List Nat) := [[],[115],[16],[16,115]]
def g207D8 (j : Nat) := if j=0 then 0x7f else 0
def g207L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g207D8)
  | _ => emptyPacking
def g207I (_ _ : Nat) : Option (Nat × Nat) := none
def g207 : Forest := ⟨207,8,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P8_0 : block g207 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B8 : block g207 8 0 1=true := g207P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : checkedTables g207 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g207 0 0 0 = true)
  · exact (rfl : block g207 1 0 0 = true)
  · exact (rfl : block g207 2 0 0 = true)
  · exact (rfl : block g207 3 0 0 = true)
  · exact (rfl : block g207 4 0 0 = true)
  · exact (rfl : block g207 5 0 0 = true)
  · exact (rfl : block g207 6 0 0 = true)
  · exact (rfl : block g207 7 0 0 = true)
  · exact g207B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 9 := lower_forest (g:=g207) (i:=0) (hints:=1587) (before_sound K126 V126) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K126 9 [(207,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V126 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x807ffff800fff01fff,0xfd8f23511a000f000f0f])),(BitVec.ofNat 152 (word80 [0xb0a01506a04a34148,0xa58b2250121111111111]))),((BitVec.ofNat 152 (word80 [0xff807fffff00001ffc,0x3bbc1984500f000f000])),(BitVec.ofNat 152 (word80 [0x12130a604c16c58191,0x33bbc190413333333333]))),((BitVec.ofNat 152 (word80 [0x7fffffffffe000,0x69728e4a500000f00f0])),(BitVec.ofNat 152 (word80 [0x1c1c438470870611e1,0xc6972864859999999999]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf9627987230f00f000ff])),(BitVec.ofNat 152 (word80 [0x20200c008018000200,0x205183202222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c46290f000ffff00])),(BitVec.ofNat 152 (word80 [0x10010020000400,0x4444444444]))),(0x665163c4cffff000000,(BitVec.ofNat 152 (word80 [0x4040600600c0081802,0x44042c0c8888888888]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(2,0,213,0,8)]
def g215A : List (List Nat) := [[],[33,116]]
def g215D8 (j : Nat) := if j=0 then 0x7f else 0
def g215L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g215D8)
  | _ => emptyPacking
def g215I (_ _ : Nat) : Option (Nat × Nat) := none
def g215 : Forest := ⟨215,8,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P8_0 : block g215 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B8 : block g215 8 0 1=true := g215P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 8 := by
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
  · exact g215B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 9 := lower_forest (g:=g215) (i:=0) (hints:=1124) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 9 [(215,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf87ffe01fffffff1e6,0x3147300000f8000ffc1f])),(BitVec.ofNat 152 (word80 [0x110014140a02002420,0x11463084210842108421]))),((BitVec.ofNat 152 (word80 [0xff87fffe00ff1ffe1a,0xfec10001f0001f003e0])),(BitVec.ofNat 152 (word80 [0x201098184c0442409a,0x5ec118c6318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffff001fffc4,0xead8a003e0003e0003ff])),(BitVec.ofNat 152 (word80 [0x422120201028848004,0xea108210842108421084]))),((BitVec.ofNat 152 (word80 [0x7ffffffffe00013,0x6c0fc07c0007c0007c00])),(BitVec.ofNat 152 (word80 [0x8441c0406030070913,0x6c09c318c6318c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff800000000000029,0x84009f800007ffff8000])),(BitVec.ofNat 152 (word80 [0x200808040080000,0x421084210842108]))),((BitVec.ofNat 152 (word80 [0x10,0x51304ffffff800000000])),(BitVec.ofNat 152 (word80 [0x401010080100000,0x842108421084210]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,8),(2,0,217,0,8),(8,0,211,0,8),(16,0,203,0,8),(64,0,155,0,7),(128,0,91,0,7)]
def g219A : List (List Nat) := [[],[118],[48,65],[48,65,118]]
def g219D8 (j : Nat) := if j=0 then 0x2a5cd40dfd54 else 0
def g219D9 (j : Nat) := if j=0 then 0x2c6501bf else 0
def g219H9 (j : Nat) := if j=0 then 0x7 else 0
def g219L : Nat → Packing
  | 8 => (1,1,3,0,0,0,0,g219D8)
  | 9 => (1,0,3,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 2 0 4 0 0 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 1=true := g219P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_0 : block g219 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B9 : block g219 9 0 1=true := g219P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact (rfl : block g219 5 0 0 = true)
  · exact (rfl : block g219 6 0 0 = true)
  · exact (rfl : block g219 7 0 0 = true)
  · exact g219B8
  · exact g219B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 10 := lower_forest (g:=g219) (i:=0) (hints:=51) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 10 [(219,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffffe1ffff32,0x82cb330000f8000f83ff])),(BitVec.ofNat 152 (word80 [0x2814050044002012,0x28b1004210842108421]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffe007ffe1ff059,0x29c78a80000001f07c00])),(BitVec.ofNat 152 (word80 [0x50b219164280504259,0x9c78a4e739ce739ce73]))),((BitVec.ofNat 152 (word80 [0x1fffffff80001fffed,0xb0415c001f003e00001f])),(BitVec.ofNat 152 (word80 [0x82c020180b0882802d,0xb0404c18c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xfe246883e007c0007fe0])),(BitVec.ofNat 152 (word80 [0x30040200c00030400,0xf0206090842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x1132807c0007ffff8000])),(BitVec.ofNat 152 (word80 [0x40080401000040000,0x21084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x459c477ffff800000000])),(BitVec.ofNat 152 (word80 [0x1803018060111808c0,0x5140342108421084210]))),(0x0,0x0)]
def g221C : List ColumnInfo := [(4,0,217,0,8),(8,0,213,0,8),(16,0,205,0,8),(1,0,220,0,7),(64,0,157,0,7),(128,0,93,0,7),(0,4,137,80,6),(5,0,216,0,5),(64,4,137,16,5),(129,0,92,0,5),(65,0,156,0,4),(192,0,29,0,4)]
def g221A : List (List Nat) := [[],[112]]
def g221D5 (j : Nat) := if j=0 then 0x2f8e097550110 else 0
def g221D6 := limbs80 #[#[0x379b2a80887b15450110,0x9dee4b2a81ce5515050,0x2f7b92caa07f1755011,0x471eda965201bbdc9655,0x2d43f211a8ae22390b53,0x42ab8f97010471e4244e,0x1040622]]
def g221H6 (j : Nat) := if j=0 then 0x90 else 0
def g221D7 := limbs80 #[#[0xdd9510bd59510fc50110,0x55140fe54140fd55110b,0x9540bfd9540bf59540ef,0xa3a9688a331205400ff5,0xc79102141eb8e440d388,0x232b8c79102e2ae4388a,0x50986392b19054846391,0xe18e450a595813962316,0x16522488a]]
def g221H7 := limbs80 #[#[0x4518600d250d30000658,0x83]]
def g221D8 := limbs80 #[#[0x88aeb807f543fa81f510,0x2aa41c6121c07356838c,0x10708c923]]
def g221H8 := limbs80 #[#[0xd00000908000000,0x0,0x18400d980c00e6c3800,0xc5000000000000,0x0,0x2480,0x21000200000]]
def g221D9 (j : Nat) := if j=0 then 0x5431201bf else 0
def g221H9 := limbs80 #[#[0x20006200036000000000,0x1a000700]]
def g221L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g221D5)
  | 6 => (7,3,4,0,0,8,0,g221D6)
  | 7 => (9,2,4,0,0,9,0,g221D7)
  | 8 => (3,1,4,0,0,7,0,g221D8)
  | 9 => (1,0,4,0,0,0,0,g221D9)
  | _ => emptyPacking
def g221I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g221H6
  | 7 => lookupWord 2 11 2 8 3 1 g221H7
  | 8 => lookupWord 2 59 0 9 4 1 g221H8
  | 9 => lookupWord 1 19 0 7 2 1 g221H9
  | _ => fun _ => none
def g221 : Forest := ⟨221,9,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P5_0 : block g221 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B5 : block g221 5 0 1=true := g221P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_0 : block g221 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_4 : block g221 6 4 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B6 : block g221 6 0 7=true := (@block_merge g221 6 0 4 3 g221P6_0 g221P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_0 : block g221 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_3 : block g221 7 3 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_8 : block g221 7 8 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B7 : block g221 7 0 9=true := (@block_merge g221 7 0 3 6 g221P7_0 (@block_merge g221 7 3 5 1 g221P7_3 g221P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_0 : block g221 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_1 : block g221 8 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B8 : block g221 8 0 3=true := (@block_merge g221 8 0 1 2 g221P8_0 g221P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P9_0 : block g221 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B9 : block g221 9 0 1=true := g221P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221T : checkedTables g221 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g221 0 0 0 = true)
  · exact (rfl : block g221 1 0 0 = true)
  · exact (rfl : block g221 2 0 0 = true)
  · exact (rfl : block g221 3 0 0 = true)
  · exact (rfl : block g221 4 0 0 = true)
  · exact g221B5
  · exact g221B6
  · exact g221B7
  · exact g221B8
  · exact g221B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 10 := lower_forest (g:=g221) (i:=0) (hints:=1027) (before_sound K219 V219) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K219 10 [(221,[]),(235,[48,33,81,65,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g222Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff801ffffe1fff94a6,0x1d94b00003f00003f03f])),(BitVec.ofNat 152 (word80 [0x450940500441101486,0xc80b145145145145145]))),((BitVec.ofNat 152 (word80 [0xffffe007fffff83a0a,0x978b5000000000fc0fc0])),(BitVec.ofNat 152 (word80 [0x164191642810213a02,0x978948e38e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xfffffff8001ffff968,0x38516000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x98020180b082406928,0x3051028a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000063f,0xa863103f000fc0000fc0])),(BitVec.ofNat 152 (word80 [0xe00c0200c00382043c,0x2862130c30c30c30c30c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x984,0x66280fc0000ffffff000])),(BitVec.ofNat 152 (word80 [0x1004010004000000,0x410410410410410]))),((BitVec.ofNat 152 (word80 [0x6651,0x43c4cffffff000000000])),(BitVec.ofNat 152 (word80 [0x6018060118040241,0x43044820820820820820]))),(0x0,0x0)]
def g222C : List ColumnInfo := [(4,0,218,0,8),(16,0,206,0,8),(128,0,94,0,8),(2,0,220,0,7),(8,0,214,0,7),(64,0,158,0,7),(10,0,212,0,5),(66,0,156,0,4),(72,0,150,0,4)]
def g222A : List (List Nat) := [[],[49]]
def g222D6 := limbs80 #[#[0xe3c1243e437a94250120,0x5]]
def g222D7 := limbs80 #[#[0xf50940bf59120fe50120,0x42a00ff58940bfd8940e,0xc32187c70572186ae8a5,0x481c5c705328c82071b1,0x81c60d4c31c871]]
def g222H7 (j : Nat) := if j=0 then 0x20 else 0
def g222D8 := limbs80 #[#[0xa38c2461a403fa81fd20,0x1e851c6121c]]
def g222H8 (j : Nat) := if j=0 then 0x44f3f1e00092000000f8 else 0
def g222D9 (j : Nat) := if j=0 then 0x5431021bf else 0
def g222H9 (j : Nat) := if j=0 then 0x653 else 0
def g222L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g222D6)
  | 7 => (5,2,4,0,0,8,0,g222D7)
  | 8 => (2,1,4,0,0,6,0,g222D8)
  | 9 => (1,0,4,0,0,0,0,g222D9)
  | _ => emptyPacking
def g222I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g222H7
  | 8 => lookupWord 1 11 0 8 3 1 g222H8
  | 9 => lookupWord 1 3 0 6 1 1 g222H9
  | _ => fun _ => none
def g222 : Forest := ⟨222,9,fun i => g222Y[i]?.getD (0,0),g222C,g222A,g222L,g222I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P6_0 : block g222 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B6 : block g222 6 0 1=true := g222P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P7_0 : block g222 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P7_4 : block g222 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B7 : block g222 7 0 5=true := (@block_merge g222 7 0 4 1 g222P7_0 g222P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P8_0 : block g222 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B8 : block g222 8 0 2=true := g222P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P9_0 : block g222 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B9 : block g222 9 0 1=true := g222P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222T : checkedTables g222 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g222 0 0 0 = true)
  · exact (rfl : block g222 1 0 0 = true)
  · exact (rfl : block g222 2 0 0 = true)
  · exact (rfl : block g222 3 0 0 = true)
  · exact (rfl : block g222 4 0 0 = true)
  · exact (rfl : block g222 5 0 0 = true)
  · exact g222B6
  · exact g222B7
  · exact g222B8
  · exact g222B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222G : graphValid g222 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 10 := lower_forest (g:=g222) (i:=0) (hints:=285348912) (before_sound K221 V221) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K221 10 [(222,[]),(243,[32,16,81,67,49,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V222 : Known true K222 := extend_ok (m:=222) V221 low222 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffff8003ffc03ffc0,0x28e1a490ae7000f00f00])),(BitVec.ofNat 152 (word80 [0x1409505a8128681485,0xa841a4908e5333333333]))),((BitVec.ofNat 152 (word80 [0xffffffc00003ffff,0xdb59298254c00f00f00f])),(BitVec.ofNat 152 (word80 [0x2602601301b0b01909,0x1941088054c111111111]))),((BitVec.ofNat 152 (word80 [0xfffffffffffc0000,0x7638e0d9940000f00f0])),(BitVec.ofNat 152 (word80 [0x3883841c21c0c21e0e,0x3638e08914999999999]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffff,0xc8137847ab90f00000ff])),(BitVec.ofNat 152 (word80 [0x402c01600a0000a000,0x1070072a1666666666]))),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c463c762f000fff00])),(BitVec.ofNat 152 (word80 [0x3001800c0100c010,0x41c4004202444444444]))),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x80c006003002030020,0x2a00360010888888888]))),(0x0,0x0)]
def g231C : List ColumnInfo := [(4,0,227,0,7)]
def g231A : List (List Nat) := [[]]
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
theorem g231G : graphValid g231 (boundsBefore K222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low231 : Lower true (varsX 231) (graphGoal 231) 8 := lower_forest (g:=g231) (i:=0) (hints:=1049942) (before_sound K222 V222) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K231 := extendKnown K222 8 [(231,[]),(252,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V231 : Known true K231 := extend_ok (m:=231) V222 low231 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff7224,0xa70baa00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403200,0x25032a05145145145145]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff800ffffffe03d48,0x8e6630c0000000fc0fc0])),(BitVec.ofNat 152 (word80 [0x20642c828080823d08,0x8e4210638e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad86,0xb058468003f03f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0409000506,0x9058048a28a28a28a28a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc0fc0000000fc0])),(BitVec.ofNat 152 (word80 [0xb01402c002e048045,0x2114ad9c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088071,0x20c010410410410410]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104880,0x4a800060820820820820]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(4,0,233,0,8)]
def g237A : List (List Nat) := [[],[82,118],[48],[48,82,118]]
def g237D8 (j : Nat) := if j=0 then 0x7f else 0
def g237L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g237D8)
  | _ => emptyPacking
def g237I (_ _ : Nat) : Option (Nat × Nat) := none
def g237 : Forest := ⟨237,8,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 1=true := g237P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g237 0 0 0 = true)
  · exact (rfl : block g237 1 0 0 = true)
  · exact (rfl : block g237 2 0 0 = true)
  · exact (rfl : block g237 3 0 0 = true)
  · exact (rfl : block g237 4 0 0 = true)
  · exact (rfl : block g237 5 0 0 = true)
  · exact (rfl : block g237 6 0 0 = true)
  · exact (rfl : block g237 7 0 0 = true)
  · exact g237B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 9 := lower_forest (g:=g237) (i:=0) (hints:=2098435) (before_sound K231 V231) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K231 9 [(237,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V231 low237 (by decide +kernel)
def g238Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf801fffff83fffffc8,0xd40ac1c0007c00f83ff])),(BitVec.ofNat 152 (word80 [0x5014028010800103c0,0x8400014210842108421]))),((BitVec.ofNat 152 (word80 [0xfffe003fffc1ff81d7,0x214153a8000001f07c00])),(BitVec.ofNat 152 (word80 [0x64190b20a0050209d6,0x2141430a739ce739ce73]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffc97,0xc5b4444400f83e00001f])),(BitVec.ofNat 152 (word80 [0x80200c02c108140007,0x45a44400c6318c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2edc7a201f0000007fe0])),(BitVec.ofNat 152 (word80 [0x140500b0000581021,0x49c38218c6318c6318c]))),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x180600c0210602000,0x901888a1084210842108]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x60180300421804018,0x202034a108421084210]))),(0x0,0x0)]
def g238C : List ColumnInfo := [(4,0,234,0,8)]
def g238A : List (List Nat) := [[],[113]]
def g238D8 (j : Nat) := if j=0 then 0x7f else 0
def g238L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g238D8)
  | _ => emptyPacking
def g238I (_ _ : Nat) : Option (Nat × Nat) := none
def g238 : Forest := ⟨238,8,fun i => g238Y[i]?.getD (0,0),g238C,g238A,g238L,g238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238P8_0 : block g238 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g238B8 : block g238 8 0 1=true := g238P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238T : checkedTables g238 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g238 0 0 0 = true)
  · exact (rfl : block g238 1 0 0 = true)
  · exact (rfl : block g238 2 0 0 = true)
  · exact (rfl : block g238 3 0 0 = true)
  · exact (rfl : block g238 4 0 0 = true)
  · exact (rfl : block g238 5 0 0 = true)
  · exact (rfl : block g238 6 0 0 = true)
  · exact (rfl : block g238 7 0 0 = true)
  · exact g238B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238G : graphValid g238 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low238 : Lower true (varsX 238) (graphGoal 238) 9 := lower_forest (g:=g238) (i:=0) (hints:=286266672) (before_sound K237 V237) g238G g238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K238 := extendKnown K237 9 [(238,[]),(245,[16,64,82,48,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V238 : Known true K238 := extend_ok (m:=238) V237 low238 (by decide +kernel)
def g246Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf800fffff83fff83ce,0xd40e8180007c00f83e0])),(BitVec.ofNat 152 (word80 [0x502a02809080010bc6,0xd4000106318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffff003fffc1fffdd1,0x214117ac000001f07c1f])),(BitVec.ofNat 152 (word80 [0x640c832020050201d0,0x2041030e318c6318c631]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffc00001fffc97,0xc5b4444400f83e00001f])),(BitVec.ofNat 152 (word80 [0x80300402c108140007,0x45a44400c6318c6318c6]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2edc7a201f0000007fe0])),(BitVec.ofNat 152 (word80 [0x140280b0000581021,0x9c78218c6318c6318c]))),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x180300c0210602000,0x901888a1084210842108]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x600c0300421804018,0x202034a108421084210]))),(0x0,0x0)]
def g246C : List ColumnInfo := [(4,0,242,0,7),(32,0,214,0,7),(16,0,230,0,6),(20,0,226,0,5),(68,0,178,0,5),(80,0,166,0,5),(130,0,116,0,5),(96,0,150,0,4),(132,0,114,0,4)]
def g246A : List (List Nat) := [[],[65,82,118]]
def g246D5 := limbs80 #[#[0x7cab2286a8f155450d51,0x232080d18179dc96454]]
def g246D6 := limbs80 #[#[0xd55151f550d51e750d40,0xf0f00fd59151fd58951d,0x22304ca883e02cc266b4,0x890418246232a]]
def g246H6 (j : Nat) := if j=0 then 0x40000720068a else 0
def g246D7 := limbs80 #[#[0xf80feaa7f503fa41f551,0x91818a201158985a6e4,0x11818a246053]]
def g246H7 := limbs80 #[#[0x1ac4000000000000,0x88005200006100007000,0x730000]]
def g246D8 (j : Nat) := if j=0 then 0x651013f else 0
def g246H8 := limbs80 #[#[0x600a00f2000000000000,0x6000cbb007]]
def g246L : Nat → Packing
  | 5 => (3,3,4,0,0,5,0,g246D5)
  | 6 => (5,2,4,0,0,7,0,g246D6)
  | 7 => (4,1,4,0,0,7,0,g246D7)
  | 8 => (1,0,4,0,0,0,0,g246D8)
  | _ => emptyPacking
def g246I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 7 0 7 2 1 g246H6
  | 7 => lookupWord 1 29 0 8 3 1 g246H7
  | 8 => lookupWord 1 17 0 7 2 1 g246H8
  | _ => fun _ => none
def g246 : Forest := ⟨246,8,fun i => g246Y[i]?.getD (0,0),g246C,g246A,g246L,g246I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_0 : block g246 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_1 : block g246 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B5 : block g246 5 0 3=true := (@block_merge g246 5 0 1 2 g246P5_0 g246P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_0 : block g246 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_3 : block g246 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B6 : block g246 6 0 5=true := (@block_merge g246 6 0 3 2 g246P6_0 g246P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_0 : block g246 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_1 : block g246 7 1 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B7 : block g246 7 0 4=true := (@block_merge g246 7 0 1 3 g246P7_0 g246P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_0 : block g246 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B8 : block g246 8 0 1=true := g246P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246T : checkedTables g246 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g246 0 0 0 = true)
  · exact (rfl : block g246 1 0 0 = true)
  · exact (rfl : block g246 2 0 0 = true)
  · exact (rfl : block g246 3 0 0 = true)
  · exact (rfl : block g246 4 0 0 = true)
  · exact g246B5
  · exact g246B6
  · exact g246B7
  · exact g246B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246G : graphValid g246 (boundsBefore K238) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low246 : Lower true (varsX 246) (graphGoal 246) 9 := lower_forest (g:=g246) (i:=0) (hints:=286393424) (before_sound K238 V238) g246G g246T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K246 := extendKnown K238 9 [(246,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V246 : Known true K246 := extend_ok (m:=246) V238 low246 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1c000007c0000fc0fc,0x60d11cb9824fcfa43c93])),(BitVec.ofNat 152 (word80 [0x1414a5290924924924,0x20101cb9806483c41082]))),((BitVec.ofNat 152 (word80 [0x440000f800fc003f00,0x8111e301ed8c30c04359])),(BitVec.ofNat 152 (word80 [0x40463088514514514,0x8810d500858c90c00110]))),((BitVec.ofNat 152 (word80 [0x80801f003f03f00000,0x61e005e11f03f008366])),(BitVec.ofNat 152 (word80 [0xc2118430c30c30c,0x23c184810f03a000140]))),((BitVec.ofNat 152 (word80 [0x6a83e0000000003fff,0x7e000601e003ff7049d])),(BitVec.ofNat 152 (word80 [0x68a908525249249248,0x26800401a002c110405]))),((BitVec.ofNat 152 (word80 [0x91fc00000003ffc003,0xf80003801fffc01800e6])),(BitVec.ofNat 152 (word80 [0x80a14a429451451450,0x880083000f0900180024]))),((BitVec.ofNat 152 (word80 [0xc10000003ffc000000,0x3ffe000001ff704])),(BitVec.ofNat 152 (word80 [0xc1739ce738e38e38e0,0x2b32000001ff604]))),((BitVec.ofNat 152 (word80 [0x277fffffc000000003,0xfffffc000000001ff800])),(BitVec.ofNat 152 (word80 [0x34210842082082082,0x5581000440020022e000]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(32,0,95,0,10),(1,0,126,0,9),(2,0,125,0,9),(4,0,123,0,9),(8,0,119,0,9),(16,0,111,0,9),(33,0,94,0,8),(64,0,63,0,8),(0,32,89,6,7),(10,0,117,0,7),(12,0,115,0,7),(18,0,109,0,7),(20,0,107,0,7),(34,0,93,0,7),(36,0,91,0,7),(2,32,89,4,6),(3,0,124,0,6),(4,32,89,2,6),(5,0,122,0,6),(8,32,81,6,6),(9,0,118,0,6),(16,32,73,6,6),(17,0,110,0,6),(40,0,87,0,6),(48,0,79,0,6),(6,0,89,0,5),(6,32,89,0,5),(10,32,81,4,5),(11,0,116,0,5),(12,32,81,2,5),(18,32,73,4,5),(20,32,73,2,5),(21,0,106,0,5),(24,0,103,0,5),(41,0,86,0,5),(65,0,62,0,5),(66,0,61,0,5),(68,0,59,0,5),(72,0,55,0,5),(80,0,47,0,5),(96,0,31,0,5),(13,0,114,0,4),(14,0,81,0,4),(14,32,81,0,4),(16,8,36,67,4),(19,0,108,0,4),(22,0,73,0,4),(22,32,73,0,4),(26,0,101,0,4),(28,0,99,0,4),(73,0,54,0,4),(74,0,53,0,4),(81,0,46,0,4),(84,0,43,0,4),(98,0,29,0,4),(100,0,27,0,4),(80,8,36,3,3),(19,8,36,64,2),(27,0,100,0,2),(75,0,52,0,2),(82,8,36,1,2)]
def g127A : List (List Nat) := [[],[33,67]]
def g127D5 := limbs80 #[#[0x21e305d98358d2148110,0x443a60bb326b1a42902,0xa40886560a95d9654852,0x2148110cac153bb2ca90,0xaae4b02211d8ee996e55,0x965e01744c2a2cd992dc,0xd0329c0ac6b0d871b121,0xb55273c6c90900c4e2cb,0x300102e101184046101]]
set_option maxRecDepth 16000 in
def g127D6 := limbs80 #[#[0x20443661965952148110,0xd21481109d82a565485,0x86a54348520443bc1835,0x443bc18358d21481109f,0x2148110df064d6348520,0x9d6348520443ce17658d,0x2be1a858d2148110b78e,0x481109f86a5634852044,0x6348520443ce176d8d21,0xe1a8d8d2148110b7869f,0x1109f86a76348520442b,0x485204439e17660d2148,0xa660d2148110cf865983,0xe785db8348520442be3,0x5204433e196e0d214811,0x64d2148110af869b8348,0xf861993485204435e176,0x4433e38664d2148110c,0xd2148110d785db934852,0xe1b93485204433e186e4,0x427e1a6e4d2148110cf8,0x148110f585d965485204,0x96548520443d63765952,0xd6176e552148110dd865,0x8110f58ddb9548520443,0x54852044376196e55214,0x3a35d92148110bd869b9,0x10f7028d7648520442fc,0x8520443dc3a35d921481,0x79d92148110b78e91764,0xaf86a27648520442de1a,0x204427e1a99d92148110],#[0x592148110b7869376485,0x8e9596485204427e3a36,0x4427e1a9a592148110dd,0x4148110f345d9634c520,0x916250520443f81434c9,0x3b918350d4148110fa85,0x48110eac619645052044,0x9258520443e616558961,0xd18358d6148110f98595,0x110cf4e4f8358520443a,0x585204427e1a2e4d6148,0x8659561481109f868b94,0xe9ce196558520443a71,0x9204438d97660d634811,0x58d214c110d7224f925d,0xc45954350530443cd176,0x443d917650d414c110f,0xd414c110ee4619435053,0x69943505304437919650,0x42f93a650d414c110be4,0x14c110f345d963505304,0x56358530443e516550d6,0xa7186595614c110f9459,0x8110f165d96558d30443,0x248560443ec1634c9215,0x19358d2158110f985956,0x10af868b83485604436d,0x85604433d393e0d21581,0x45912158110f2c5d1644,0xd9c65965485604436b19,0x60442770a95952158110,0x8d3158110f94595634c5],#[0xc651644c5604436d1945,0x442ed1a3d913158110da,0x4158110d9c659654c560,0x937250560443cb1645c9,0x3ab164e094158110f2c5,0x58110fa458d435056044,0x6350560442eb1a650d41,0x31655914158110bac693,0x110bace8d6450560443e,0x58560443671965954158,0x65dc96158110f1c59572,0xe9c5978258560443c71,0x56044367165e49615811,0x58d6158110f345cd6358,0xb4e4d6358560443ad383,0x443c71655cd6158110d,0xd6158110f1c597735856,0x59783585604433d393e0,0x4367165e4d6158110e9c,0x158110f2c5d164585604,0x574585604436b3945916,0xc7165dd16158110f1c59,0x8110d9c5979458560443,0x2589604434d99758d325,0xb93d8d7258110e9a5978,0x10d1e25b955c9604434d,0xc960442cd9a325972581,0x45938258110d2e65164d,0xf265d16350d604438b97,0x604434d99758d4358110,0x914358110f265937350d,0xe6597450d604434b9975],#[0x443c59655cd6358110d2,0x6358110d3665373d8d60,0x5174d8d60442cdba35d3,0x2cd9a3d917358110d2e6,0x58110b36e8d64dcd6044,0x74591604434b99459373,0xb974e4d6458110f0e595,0x110b2ee8974591604434,0x4c921442cbba35d16458,0x7658d3248510f615d143,0xf985959058921443cc5,0x9214427e1a0e4d624851,0x5916248510f295d16458,0x195d96558921443aa584,0x1443c67765956248510f,0xd6348510ad92a1655892,0x26176595214438d57660,0x4317498dd96548510c5d,0x548510e9ce8186595214,0x586e1521443a67a26196,0x5c493e4976485108ddea,0xc510e355d98458d31443,0x24c941443c5576595634,0x5645c96250510f6150d7,0x10dac59190d8941443ca,0x9141443c957658d43505,0x560b8058510f0d5d9655,0xd9c59592e0161443a716,0x61443a71656138058510,0xc96258510d3565d634c9,0x95978258961443c65655,0x442674a95957258510e9],#[0x7258510d35e4f635c961,0x8c965c961442c74a9595,0x367165e418258510b356,0x58510db458f9050d6144,0x6350d6144367165e4143,0xd59758d4358510f255d1,0x510f155977350d614434,0x50d61443c35655d14358,0x655cd6358510d1d65d65,0xb35e8d74d8d61443c55,0xd61443c5565e0f735851,0xe416458510d1d59594dc,0xd595745916144367165,0x144347565e4d7458510f,0x38458510d9c597906116,0xe99985d1324436716564,0x421dfa3661764c91083f,0x5891086fe91985d9324,0x198dcd62443a71656058,0x1dfa365f845891086fe9,0x8910b1be897659562442,0x659562442c5fa35d9655,0xfa361d6558910b1b68b7,0x10b17e8d875956244295,0x1d62442c3fa461d65589,0x4e4d8758910c67e50936,0xc57e579361d6244319f9,0x624438b97459180d8910,0x6174d8910877e8d985cf,0x7e8d76e15724421dfa36,0x44217da99db855c910a5,0x855c91086fe9198d8d72],#[0x5886e157244295da321b,0x295fa361b855c910c1f6,0x5c91085f6a686e157244,0x862197244307d96e1b85,0x7fa661d6550d1083fea5,0xd1087ee81985d9434428,0xe11634421dfa36617650,0xa361d6558d10877e8d97,0x87e6a687e016444295f,0x5644421dfa365f825911,0xe418759110a57e8d8759,0x67e5083609764431d893,0x64421dea920d825d910c,0xd825d910c67e53836097,0xe818420d7644315f95e0,0x421dfa9610835d910a76,0x35d91086fe9192e0d764,0x592e0d7644299fa464b8,0xcd163dc52158130a57e9,0x8130d96e5563485604c3,0x2dc5604c2e99a650d415,0x99458f7158130d3658d9,0x30d2e65164dc5604c34d,0xc9604c3c996450f72581,0x458f7258130b3669943d,0xd2e65164dc9604c34d99,0x604c369b9458d8258130,0x954358130f865956450d,0x66929650d604c3659965,0x4c26d9a9a594358130ba,0x6358130f265d16458d60,0x857458d604c3c59655d1],#[0x2cdba25d16358130b36e,0x58130e362a17458d604c,0x43585414c2cd9a2dd163,0x7f985957458530f85595,0x530b17e8d87595614c30,0x5d3614c38d97458d80d8,0xa066174d8530c1fe6165,0x87ee8198593714c21fb,0x1624c307f9659584dc53,0xdd96558930d1b59592dd,0xfe9187595624c2c6da2,0x24c3a996450d80d8930b,0x96450d30c1fe59656137,0x68886591434c2e99a021,0xc32d9866408650d30ba3,0x259130b35684965d1634,0x187595644c21fba065f8,0x87fa661d6559130a5ee8,0xd13087ee8198dd9644c2,0x5e01744c307f86656765,0x1a121b805d130e1e2196,0x30c3e65886e01744c29f,0x95744c2c75a1219655d1,0x618865d130a1f687865,0x83fea586219744c28fba,0x764c307f86656865d130,0x637348560877e8d91e11,0x7e8d87e15215821bfa46,0x58217fa961f8548560a5,0x854856085f6a687e1521,0x93905854158295fa365f,0x34756564b7158560dac5],#[0x50d60c67e53835c97158,0x90e0543582ad9a3a1980,0xb9646438150d60cb658d,0xd60da65939058d435832,0xdcd6358259fa464b7358,0x65e5182dcd609a7e9192,0xf295917250521d8313d,0xd21d838d58358d714876,0x58d714c76085f69f9560,0xb6e818458d31d838d584,0x1d82abba0611644c760a,0x1435c760f2558d435c54,0xe5f9061943d834d963e4,0x8707d96e1b755c121c3e,0x250521f615d9434c9414,0x9434c941487b858650d3,0xf87a650d3250521be169,0x8521da95939058941486,0x260161487a6565e09805,0x565e4d8058521d995979,0x21e9959562e016148765,0x89614878d57358f80585,0x358d6258521f315cd635,0xd9959590e09614876c79,0x614876c563e494358521,0x1b7550d21d3565d6350d,0xee81985d94348697ba06,0x4863f3a06538158d2187,0x7659521b1de85905d965,0x83915d965486c5fa3641,0x7c6792e457659521b1d6,0xdd521c1fe59866037548],#[0x936017648695fa364186,0x5565e0d8058531c57e17,0x531d9559793601614c7a,0x58d614c78d57458f8058,0x655d16358531f255d164,0x1b35e817458d614c7c55,0xd614c6cd7a25d1635853,0x5d38358531bb4e819458,0xd59574591614c7c5565,0x14c747565e417458531f,0x174d8931d95597936116,0xe8197e09644c61fba066,0xc697ba061d655913187e,0x58541c76e4c9061d644,0x7846016150765565e4d8,0x63565e518058541e8d59,0x8541ea558d43e0161507,0x258961507a3565593805,0x56558d4358541ea95938,0x41f855978350d61507e1,0xd615076359659543585,0x35916358541d8de59655,0xd8d5979359161506e97a,0x705861fba064f825d941,0xd725c161e9559783e05,0x7e57835c97058785d65e,0x58785d65e0f725c161c5,0x835c161c9765783d8d70,0x8565e0d70587a5565e47,0x74d963e4143dc161e95e,0xdc961c9d59590e056258,0x91e01435861fba066143],#[0x75656478050d61cb558d,0xd61cb558d91e09435872,0xdcd43586e97a15916350,0x65e456450d618776a787,0x1a9ee818659543587635,0x543586a77a16196550d6,0x61d6550d61a9d6878659,0xfce8194e0563586a7ba0,0x3587275656538158d618,0xf81591619bce8194e056,0xe9192e0d70d872756564,0x8743d65e51805cb6186f,0x35c14387ee8193e0974d,0x9959d97050ecd5a11d96,0x7f9659580dc543c1fe1,0x8d43ae6e8164e016350f,0x1d96350f31d95653825,0xda6a5f8059543da66919,0x43d1ee58905d96550e47,0x7650f8d97664d801d9,0x95d9801d943c3e2a5766,0xc3ee60905d87650f0fba,0x7650f0fb98e41761d943,0x61761d943c3e283985d8,0x6e8d812017650f0fba0e,0x50e1fba9604805d943a7,0x84dc563d36e5b93e0176,0x17905d37258f17965e41,0x32db96e4f805d163c5e6,0x35030c2c82581e812000,0x4bc4a446041c3d8394,0x466c6285e45cc5885445],#[0x7c47ac76872470c6c868,0x489048ec8a886484c808,0xca88a44a2c9e89d098c9,0xc64c20bb0b40b28b10ac,0xe8dd0d60d1ccd8c94c7c,0x4efceb8ea0e5ce44e00d,0x55010ff8fe0f9cf58f1,0x8116912510d0f50b1099,0xd23d22520d1f51b11991,0x3ed3a936534d3352f12a,0x455014bd479461449431,0x162d6155fd5e55a155d5,0x72d7156fd6e56a168967,0x598157fd7e57a1789745,0xd9158fd8e58a18898718,0xa6da55a119cd98997192,0xc5badb69b25b0dac9a85,0xdd05cedc7dc39bf5bddb,0xe31dedda9d91d79d35d1,0xb5f71f59f41efdeb9e49,0xa0f608604202a011ff9f,0x22220a1f21da19615213,0xf62de2c628226a25223a,0xa3b239a38236a32630e2,0x48646e42a4123fa3e23c,0xb259a58256a5524b649e,0xa64262a6125fa5e25ca5,0x7166fe6e66ce6b669e65,0xbe7a678e77675e74672e,0x684e83681e8067ee7d67,0x8f68de8c68ae89687e86,0xca9b296e95693e92690e],#[0x2a5aa42a2aa129fa9e29,0xbb2b6eb2ab12aceab6a7,0x86c6ec56c3ec26c0ebf6,0xed16cfece6ccecb6c9ec,0xdbeda6d8ed76d5ed46d2,0x66e4ee36e1ee06deedd6,0xeef6edeec6eaee96e7ee,0xf9ef86f6ef56f3ef26f0,0x7305b042ffefe6fcefb6,0x315b1170ff0e70cf0b70,0x2031eb1d31bb1a318b17,0x5b3172ff2e72cf28b21b,0xf4173ff3bb3a338b3733,0x4eb4d34bb4a348b44742,0x175d35bb5a358b54752f,0x36ff6e76cf68b64762f6,0x7ff7e77cf7b779f75b74,0xa788f87785f84782f817,0xf93791f9078ef8d78bf8,0xa0b9f39db9c397f96794,0xb3a9ba83a6ba53a3ba23,0xbb43b2bb13afbae3acba,0xbebbd3bbbba3b8bb73b5,0x93c7bc63c4bc33c1bc03,0xbd23d0bcf3cdbcc3cabc,0xdcbdb3d9bd83d6bd53d3,0x405fc06e002b1bdfbde3,0x142e8be1060019101282,0x608030401a8a30028205,0x840460025141d8009840,0xac130808c004a28201,0xd1413080800ac130808],#[0xe101034080d14130808,0x20641032080e10118008,0x25141308080610103600,0xd0c0080c8c008000600,0x4102114108a080008404,0xa28200c004000e00240b,0x10830401208080028101,0x501040020081004000,0x4000014504000040808,0x20080041004600280460,0x2040100000138280410,0x2805008204100408,0x8000000070400003820,0xe080000704000e,0x201c100038200007c004,0x1c100e080000704080,0x101408000001c100e08,0x708080001714128421,0x1049b00202c20202810,0x420a0404000200209,0x40048082438012050400,0x4000000000005008070,0x500800000402,0x81380180001008100000,0x362c,0x1c1,0x0,0x28082000000000,0x4101008205010400000,0x70403820,0x0,0x0],#[0x8200000000000000,0xe0800000023040,0x281056414200000000,0x1c1000000d8808000,0x81d00100000000e0800,0x100e0800484040000e80,0x1c103810200001c,0x0,0x16002000000]]
def g127H6 := limbs80 #[#[0x2e8e6c714028,0x3380003538803b400000,0x26c020c0001de8000200,0x1d800000]]
set_option maxRecDepth 16000 in
def g127D7 := limbs80 #[#[0x90a40886f860d2148110,0x217e193485204437c706,0x952148110bf1c9a42902,0x443ec72a90a40887d85,0x1bb24290221de1764852,0xa40885f86592148110ef,0xe716558520442fc72c90,0x614c110fc8a1a8298221,0x43ce2cab0a60887b458d,0x1a62b0221cd97658d304,0x887ac5914158110f68b,0x97358d60443ce2cab0ac,0x58110e6db9ec6b0221cd,0xccacab12428872e5d164,0xca90a21a758659521443,0x87355d9634c5109ba4c2,0x55c961443ce2cbc02c28,0x510e3ab2ee4b0a21c756,0xae6b1ac28869d5978258,0xb0a21cd773d8d614439a,0x1d5957358510b3acaec6,0xd1614438eacbb9ac2887,0xe3ab2ee8b0a21c75655,0xeb2ac28871d25d655851,0x2211df9361d624438ef2,0xe4d87d8910d3ab2b03b1,0x724422f930b2ae488477,0xefc9b0eb1a2117d96e15,0x3ec888477e4d87591108,0x155f935d9654423bf26c,0xf8158130e6cb1ee2b026,0x4c39b2c7b92c0986b658],#[0xcb286b0261e996450d60,0xc0987965956358130b6c,0xdb7458d604c39b2e8b1a,0x458130b6dca2c6b0261c,0x35b2c6c06c2985b664f6,0x2caba2611fb9061d644c,0xb071d5977158560c3fc3,0x9460b735823eb2243a86,0xc7608becbf0a90ec11bf,0xb2c7c0287b073558d714,0x4a0a43f85434c9414875,0xf995956258521f52b22c,0x58d61487ccacbc12c290,0x21aba4bacab0a43cd573,0x2dc2ae690c5f66375d8d,0x2a43c77915d9654862fb,0xfe6176dd5218becb50eb,0x1614c62fb313b6ea90c5,0xf2ab2ac6b0a63ad563e0,0xc1ac298f355d16358531,0x63c75655d1614c7caacb,0x8d43585418fdc830eb22,0x1507c6acaa1ac2a0fa55,0xab2f08b0a83e35655916,0xac4b0e97597835c161f1,0xa7565e05635874eacbc0,0x8750f61d3ab2f02b22c3,0xedb3203b2c6a1c7ee41,0x82ecb2a876d5911d9635,0xca1e3e5d9801d943abdc,0xb906137158e1ff30bb0e,0x48110ff0a1a42902211f],#[0xfc6c690a40887f858d21,0x4290221fe18348520443,0x87f89d92148110ff0bb2,0x648520443fc32c90a408,0x110ff0a126290221fe29,0x2c698a40887f85893148,0x902217f1944c520443fa,0xfc6193148110ef8bb262,0xc5204437e70c98a40886,0xff099282902217f1964,0x6a0a40887f8589414811,0x221bf18350520443f628,0x5d94148110fd8b228290,0x20443be6eca0a408877c,0xf8cb28290221bf186505,0xa40887f85896148110b,0x1ef16358520443fc324b,0xd6148110f79b1ac29022,0x4437e706b0a40886fc60,0xba2c2902217f39358520,0x408877cdd16148110ef8,0x716558520442fe728b0a,0x148110df8c32c290221f,0x37b306a1a40886fce196,0x2c690221bd98358d2044,0x8857ee5d6348110e7cbb,0x91d8d204427f330b1a40,0x8110bf4c96c6902217f1,0xf32fb1a408873e5db634,0x6902213f998d8d20442b,0x4fee598348110cfcbb30,0xe0d204433f2edc1a4088],#[0x10ebcbb2ca902213f996,0x22bb2408875edd965481,0x2217eb925d920442fe7,0xce457648110bedc9aec9,0x920443bd724bb2408877,0xeedc9aec90221dd8935d,0x3b2408857ee517648110,0x217e9929d920442fe323,0x627648110afccbcec902,0x442bf329bb240884fe6,0x8a1a4298221fe1624853,0xa60887f458d214c110fe,0xdf17648530442fe32890,0x214c110df8c324298221,0x43fa2c6a0a60885fc659,0x2a8298221fb164505304,0x8877c5d9414c110fb8b,0x196505304437e30ca0a6,0x4c110bf9c92c2982217f,0xfa2c6b0a60887f450d61,0xc2982217f39458530443,0x86fc619614c110fb8b2a,0x3d8930442fe323b12608,0x110afccbec4982217d99,0x322a1a60884fe663624c,0x98221f996450d30443fa,0x765d9434c110facb2a86,0xd304437b30ca1a60887,0xbedcb286982217d9965,0x8b1a60887f4645634c11,0x221f596558d30442fb72,0xe61644c110eecbb2c698],#[0x30442fe323b2260884fe,0xfccbec8982217d993d91,0x2a60884fe663644c110a,0x1b798659530443af2ecb,0x9864c110eedc9aec9822,0x4437b726c3260884fee4,0xb1242b0221fe13248560,0xc0887f86092158110ff0,0xf36348560443de2c690a,0x158110df9c1a42b0221e,0x2fe72690ac0885fc64d2,0x242b0221ef1644856044,0x8877c5d12158110f79b2,0x9448560443be6e890ac0,0x8110bf9ca242b02217f1,0xe72a90ac0887dc595215,0x2b02217f19648560443e,0x6fce093158110bf9cb24,0x4c560443fa2c698ac088,0x10f79b2262b0221ef164,0xca98ac0885fc65131581,0x2217f1964c560443ee2,0xcdc94158110ef8b9282b,0x5604437e704a0ac08877,0xf78b1a82b0221fb14350,0xa0ac0887bcd8d4158110,0x21fb164505604437e706,0x594158110fb8b2a82b02,0x443be2e4b0ac0885fc6,0x9c12c2b0221df3725856,0xac0885fce496158110df,0xdf17358560443de2c6b0],#[0x6158110ef9b9ac2b0221,0x42fe726b0ac0886fce0d,0xa2c2b0221ef164585604,0x8877cdd16158110ef8b,0x182e0560442fe728b0ac,0x58110bf8c9702b0221bf,0xbb6e6992c0887b658d32,0x64b02215f9974c960443,0x87ae59142581109fd4c2,0x5589604437d704b12c08,0x110bbdcaae4b0221e796,0x2c6b92c0885bee597258,0xb0221cfb635c9604439f,0x5e5957258110afdc9ae4,0xc960443af72ab92c0887,0xe7dcb2e4b0221cf8965,0x9b92c08873e593725811,0x2215f994dc9604439f6c,0xe458258110ebcb2ee4b0,0x60442f7728c12c0885fc,0x7cb2704b02213f993e09,0x12c0886bed938258110d,0x19fb74e09604433f2e9c,0xd4358110dbcb2f04b022,0x443bb6e6a1ac0887b658,0xba286b0221eb96450d60,0xc0885be6594358110edc,0xd97358d60442bf32ea1a,0x358110dedc1ac6b0221d,0x3de322b1ac08879e5956,0x2c6b0221edb8358d6044,0x885bee516358110e7cba],#[0x94d8d604439f2e9b1ac0,0x8110e7cb22e6b02216f9,0xf2cab9ac08873ed91735,0x6b02215f992dcd60443a,0x73e5937358110eedc1ee,0xdcd604439f6c9b9ac088,0x10ebcb2ee6b02215f994,0xcbc1ac0884fe64b83581,0x221db974591604436f2,0xc6456458110f3cb2ac8b,0x160442df726b22c0887b,0xf5dc22c8b0221eb97459,0xba2c0885be64f6458110,0x215fb935d160442bf724,0x4b7458110ebcb2ae8b02,0x443af2cbba2c08857e6,0x2a1a6490a21f73915956,0x242887f158d3248510fe,0xde5764c921443bcae899,0x3248510df2c326490a21,0x43fc320b1242885f9659,0x1ac490a21be583589214,0x2885f9e4d6248510df3c,0x76458921443dcac8b124,0x48510ef2ba2c490a21ee,0x7cb08b124288779dd162,0xc490a21be78458921443,0x87d9e156248510fb2b2a,0x658921443bcaecb12428,0x510bf9c828690a21de77,0xae8a1a42885f9e494348,0x90a213f59850d21443b6],#[0x3d5d96348510deac1ac6,0x8d21442bef2eb1a42887,0xbf8c86c690a213f5985,0xdb1a42885f964b634851,0xa215f597d8d214439eae,0x5d983485109facc6c690,0x214433eaedc1a428867d,0xf9c82c890a213f596e0d,0x2242885f9e496448510b,0x1bb58459121443b6ae8b,0x16448510afacbac890a2,0x442fe321b2242884fd66,0xcbec890a217e592d9121,0x42884fd6636448510afa,0xf7965d1214433eb0cba2,0x448510cfac36e890a215,0x33eaecc22428857d65b7,0x70890a219f7766112144,0x8867dddb8448510cfabb,0x76595214427eb2dc2242,0x8510ebbbb2ca90a21d75,0xeaedc2a42886dd619654,0xa90a21d7776e1521443a,0x5dd65b8548510dbac370,0x5d921442fe720bb24288,0x10bebc9aec90a217e792,0x24bb2428877ce4176485,0xa21dd4935d921443bcf,0xde517648510eebc9aec9,0x921442fe3213b2428857,0xafacbcec90a217e5929d,0xbb242884fd6627648510],#[0x217f39061921442beb29,0x418648510bf3c930c90a,0x14437cf24c3242886fce,0xbca30c90a213f7936192,0x242886dde5586485109f,0x7e592a1921442fe32143,0x8648510afacbd0c90a21,0x42fe321b1262884fd662,0xbec498a217d593d89314,0x2884fd663624c510afac,0x58458d31443fa320b1a6,0x4c510faab2ac698a21bd,0xfe720b2262887755d963,0xc898a21bb58459131442,0x85fc643644c5109facc2,0x7d9131442fab27b22628,0x5109facc6c898a215f59,0xacac2262884fde49844c,0x98a219f576611314436e,0x5d5d9654c5109fbcb308,0xd9314436eb0cb2a62887,0x9fbc930c98a21dd7935,0x8c3262886f5e4d864c51,0xa21de5724c9414427ef2,0x5c96250510fcaa1a64a0,0x41443d6ac8b128288779,0xf8c86c4a0a215f597589,0x1282887ad5936250510b,0x15f597d8941442f6b29b,0x172505109facc6c4a0a2,0x443b6a86b9282885ede5,0xca2e4a0a21db5645c941],#[0x828867d6197250510edb,0xb564dc941442bef2cb92,0x250510cfac36e4a0a21d,0x3f2ac6a1a828857d65b7,0x286a0a21f356550d4144,0x886ed6194350510edabb,0x9650d41442f6b2ca1a82,0x510e7abb2c6a0a217b7,0x6b29b1a82885fc643635,0x6a0a21cf576d8d41442f,0x4fd6636350510afacbec,0x59141443f6720b228288,0x10f9ab2ac8a0a217b793,0xecb22828876d5d964505,0xa21d757659541443b6e,0xd6196550510ebbbb2caa,0x941442fe720bb282886d,0xbdbca2eca0a217d7935d,0xbb2828877ce417650510,0x21dd4935d941442bef24,0x517650510eebc9aeca0a,0x1442fe3213b2828876de,0xacbceca0a217b5949d94,0x282884fd6627650510af,0xbf39061941442beb25bb,0x86505109fbc930ca0a21,0x4376f28c3282884fde4d,0x9700b0a21bf182e01614,0x2886fc6138058510bf8c,0x7734c961443daac6992c,0x58510afacba64b0a21dd,0xbeb2ea12c2884fda6132],#[0xc4b0a213f69850961442,0x86f9e096258510ef2b92,0x55c961443ceacab12c28,0x510bbbcaae4b0a21e756,0xac6b92c2885bde597258,0xb0a21cf7635c9614439e,0x7de117258510afbc9ae4,0xc961442bef28b92c2886,0xebbcaae4b0a21d75655,0xcb92c28873d259725851,0xa219f784dc9614439ef2,0x5977258510afaca6e4b0,0x61442fe720c12c28875d,0xbbcab04b0a21e7565609,0x12c28879d5978258510b,0x19f574e09614427eb27c,0x38258510cfbba704b0a2,0x4436eacbc12c2884fd65,0xb1a86b0a217f39050d61,0xc288775dcd4358510f6a,0xb57450d614437af06a1a,0x358510f3ab2a86b0a21d,0x27ed30a1ac28857d65d4,0xac6b0a21dd57358d6144,0x8879d5956358510debc1,0x8358d61443de320b1ac2,0x8510e7aba2c6b0a21ed7,0xeacab9ac28873d5d3635,0x6b0a215f592dcd61443a,0x57d6537358510eebc1ee,0x60d61443aeacbb9ac288,0x10f3ab2f06b0a21e7565],#[0x29c1ac2884fd64b83585,0xa21b7565e0d614427eb,0xd5d16458510bf9c82c8b,0x16144376f08b22c28876,0xf3ab2ae8b0a21e756559,0xba2c28857de497458510,0x21d75655d161442bef26,0x977458510afac96e8b0a,0x1442fe720c22c28875d5,0x8c8708b0a21e75656116,0x2c28879d5978458510bf,0x3f592e11614437e321c2,0x84585109fac9f08b0a21,0x43cef2eb2ac2886dd597,0xbac499221dcf73589324,0x4887675d1434c910af7c,0xd8758d324439baecb1a6,0x4c910ceec26e6992219d,0xbbb2db9a648857765373,0xe8992215df935d132442,0x84fee41844c9108fecc2,0x85d932442bbf26bb2648,0x9108ffcc2ec992211fd9,0xf26c3a648847fe5d864c,0x992211ff9461d324433b,0xab59162509108ffcb30e,0xd9424423fb31b9a84887,0x8ffcc2eca12215df935,0xc32848847f663765091,0x221bf181601624427f72,0x5958158910f3cb2b00b1,0x62443cdacab92c48879d],#[0xefc1ee6b12215ed92dcd,0x1ac48847f6637358910c,0x13f591e0d624427f321c,0x164589108fecbf06b122,0x442bdb25ba2c48872f5d,0xcc6e8b12219bf84dd162,0xc4884fe64384589108fe,0xfd97e11624427eb23c22,0x558910e3ebb2cab12211,0x32fb0eb2ac48871fdd96,0xacab1221c7d875956244,0x8857be497658910e3f43,0x92dd962442bbf26bb2c4,0x89108fecc6ecb12215ed,0x7f28c3ac488577e4d875,0xeb12214ff9661d62442b,0x4fde4587589109fdc830,0x61d624427bf26c3ac488,0x10cfdc830eb12213bf94,0x26c3ac48867de4587589,0x12219df9361d624433b9,0xfe5587589108ffc9b0eb,0xd624431ff2cc3ac48865,0xa7ecb50eb12211ff9661,0xc3ac4884fe6438758910,0x211fd93e1d624427eb23,0xcd80d8910cfcb9b01b12,0x24427f726c06c48867ed,0xcba301b1221af9646036,0xec48867edd180d8910cf,0x9f773607624433eae6c0,0x81d89109fbc9b03b1221],#[0x433eee8c0ec48867d5d1,0x1ae7b12213f794607624,0x48847f66173d8910ceec,0xd74593624423fb31b9ec,0xd8910cdec22e9b1221cb,0x3fb31ba6c48847f66174,0xfb12213fb9061362442,0x867724d87d89109efc9b,0x361f624433bf26c3ec48,0x9108ffca30fb12211ff9,0x930b2ae48866fe11745c,0xb922197d76e15724426f,0xdf65b855c910cbf3b70a,0xd972442bdf24bb2e4884,0xc7fc32ecb92215df935,0x33b2e48857e642765c91,0x2215ed929d972442beb2,0xe41435c910c7fc34ecb9,0x724433bf06a1ae48857e,0xff4c2c6b92211fe9850d,0x1ae48857e643635c9108,0x15ed92d8d72442beb23b,0x3635c910cefc1ec6b922,0x4423fd31b1ae48847f66,0xcb706b92211fd94e0d72,0xe48865fe19655c9108fe,0x7c86e1572442af930b2a,0x55c910cbec370ab92219,0x32ff0dc2ae48865fa1b8,0x90cb922157d96e157244,0x8863f618865c910aeec9,0x9361972442bf720c32e4],#[0xc910afcc850cb92215df,0xfb27c32e48863fe1a865,0x9b922197f95e19724423,0x47f66164dc910cdec22c,0xd9372442bf321b26e488,0x108fecc6c9b92215f591,0x28c36e48865f61965dc9,0x1a213f992e01434423ff,0xe5938050d10decb1f00a,0x1434436f2cbc0286886e,0x9fac8f04a1a213f996e0,0xc128688677dcf8250d10,0x21d9d7458d434423fb2f,0x1d6350d10e6ebb2c6a1a,0x34433bf0eb1a86886776,0xeb26e6a1a215dd92dcd4,0xa86887575977350d10ec,0x7bb9059143442bbb2db9,0x6450d10cdec3ac8a1a21,0x42b7b2eb22868866fe1d,0x2ae8a1a215bf97591434,0x68866f6197450d10e9eb,0xf965d14344337f0cba28,0x50d10cbec3acaa1a215b,0xbbf26bb2868865fe1d65,0xeca1a211fd985d943442,0x84fee418650d108ffcc2,0x1e19434423ff2ec32868,0xd108fecbf0ca1a213f59,0xf24c3a868867de458750,0xa1a211ff9661d434423f,0xfc6058058d108fecb70e],#[0x9634427f321c12c6886,0x8fecbf04b1a213f591e,0x1c22c6887575957358d1,0xa213f591e11634427f32,0x5d96558d108fecbf08b1,0x634432fb0eb2ac68871f,0x6fc9aecb1a215df935d9,0x3ac68847fe498758d10e,0x11ff9461d634433bf26c,0x38758d108fec970eb1a2,0x4427f724c06c68847f65,0xc9303b1a219f97460363,0xc68867d5d181d8d109fb,0xdf7360b634427ef28c0e,0x4d8d10ceec26e7b1a219,0x337b08ba6c688577e4d7,0x309b1a211fd985d36344,0x88737e4d76d8d109fdc8,0x9361f634423ff24c3ec6,0xcd108ffca30fb1a219df,0xeb23b22e68857e643645,0x8b9a215dd93d9173442b,0x47fe5182dcd108fecc6c,0x593734423ff2cc16e688,0x10cdec22c9b9a215df93,0x21b26e68847f66164dcd,0x9a215f591d9373442bf3,0xf59584dcd108fecc6c9b,0xb734432fb0cb2ee68865,0xcefc9b0db9a211ff9261,0xc02c88847fe5186dcd10,0x21db974e01644437e303],#[0x1f8059110cfcc3f00b22,0x44437e323c02c88867ea,0xcc9f00b22213f992e016,0x2c8886de59780591109f,0x9fb76e01644433f2edc0,0x82591109fac8f04b2221,0x427eb23c1ac88847f65f,0xbf06b22219bd74e0d644,0x88856fe4974591108fec,0xd655d164442b7f26ba2c,0x59110e3ebb2cab2221d3,0xbbf26bb2c88865f61d65,0xecb22215bf945d964442,0x847f6637659110adeca6,0x61d64442bbf26c3ac88,0x1109efc9b0eb22213fb9,0xf24c3ac88867ee418759,0xb22219dc9361d644423f,0x7fe4d8759110cefc9b0e,0x1d6444337f28c3ac8884,0x9fcc870eb22214fd96a,0x7c3ac8884fd647875911,0x2213fb92603644423fb2,0xe4981d91109fdc9b01b2,0x644427ef26c0ec8884fd,0xffc930fb22213df9361f,0x3ec88867724d87d91108,0x11ff9361f644433bf26c,0x1765d110aefc9aecba22,0x442bf3213b2e88856fe5,0xca4ecba2215f5919d974,0xe88847f64f825d110ade],#[0xf79160d744423fb2dc12,0x35d1108fec9706ba2215,0x23fb2dc1ae88865f5978,0x30cba22197f865957444,0x88577e4d865d110afdc8,0x91a1974442bf321432e8,0xd1108fec970cba2215f5,0xff2cc16e88847f64f865,0xdba22197d86597744423,0x75d5db81595108ffc930,0x5d965443aeeedc0aca88,0x10abfc92ecb2a2175f93,0x26bb2ca8875724d76595,0x2a2157f935d965443abf,0xf64b7659510abfca2ecb,0xd65442afb29bb2ca8855,0xdf9c0f00bb22177591e1,0xc02ec886f6e0f805d910,0x21bd783e05764427f325,0x43835d9109fac9702bb2,0x64437af23c1aec886f6e,0xcc9700bb221df381e017,0xaec88776e0f805d910af,0xdd783e0576442beb25c0,0x825d910afdc8304bb221,0x433b906c12ec8857de45,0x9b04bb2219df83609764,0xc8856fe51825d910aefc,0xc83e0976442aff2ac12e,0x5d910cefc1f04bb2219d,0x3fb29c12ec8847f64f82,0x6bb2219dd8420d76442],#[0x8577a60835d910cefc21,0x1e0d76443bb721c1aec8,0x910ceec2706bb221dd79,0xb25c1aec88677e13835d,0xbb2211fd94e0d764423f,0x77e4b835d910ceec9706,0xd764433bb29c1aec886,0xafdc8308bb2219df94e,0x5c22ec88577e4d845d91,0x2211fd93e11764423fb2,0xe49819d9109fdc93013b,0x764427ef28c0cec884fd,0xffca30f3b2211ff9261e,0x16ec8847fe5182dd9108,0x1df371485604c32ff2ac,0x52158130f6cb1a42b026,0x4c3f3286a0ac0985dee5,0xb2282b0261ed96350560,0xc0987b658d6158130f5c,0xf992dc5604c3cf2cab0a,0x158130e7cb26e2b02615,0x3db2c6c0ac09857e6537,0xb02b0261bdb83605604c,0x986f650f8158130bedc9,0x64509604c3db2c6a12c0,0x8130f6cb1ac4b0261eb9,0xb2c6b92c09879e595625,0x4b0261dd943dc9604c3d,0x57e6537258130e7cb26e,0x609604c3db2c6c12c098,0x30bddca304b02617db93,0x8a1ac0987e659143581],#[0x261f596550d604c3f33,0x66594358130f6ccb286b,0xd604c3db52ca1ac0985f,0xf6cb22c6b02617db9650,0xb1ac0987765d16358130,0x61ed99258d604c3db322,0x116358130f6cba2c6b02,0x4c3db328b1ac0987b66,0xcc9ac8b0261e79655916,0x2c0987ae5d16458130f6,0x5fb915d1604c2df72cba,0x7458130ebcb2ae8b0261,0xc39f72cba2c09873e259,0x96e8b02619f8985d1604,0x2987e550d4148530afcc,0x562dc5214c3daac6b0a4,0x48530eeab1ee290a61de,0xbeb2db8a429857d65371,0x8690a615ef97589214c2,0x86d7e156348530dafc2a,0x55d1214c2bef22ba2429,0x5308ffcc2e890a6197f8,0xb2dc2a429865f5db8548,0x90a615f7915d9214c26f,0xe550d61505308ffcbb0c,0x85414c3daac6b0a82987,0xfcbc8a86a0a61e75655,0xca1a82987c7595435053,0xa61b9d8650d414c3b3ae,0xe594350530bcecb286a0,0x614c23ff2ec3282985e7,0x3cb2b00b0a61ed963601],#[0x12c2984fe6438258530f,0x1e5d6550d614c23fb2fc,0x56358530cefc3a86b0a6,0x4c39bae8b1ac29879759,0xcc2e8b0a61c7d655d161,0xc2984fe64384585308ff,0x7d76595614c23fb2fc22,0x758530e3ec3acab0a61c,0x23fb25c3ac298577e4d8,0xb01b0a611fd94e1d614c,0x9867e5d180d8530deca1,0x6550f614c373b08a1ec2,0x8530daec2a87b0a61e5d,0xbb30a1ec29867761d43d,0x7b0a613df9850f614c27,0x6775d183d8530e6eba2c,0x5d3614c337b08ba6c298,0x30cbec2ae9b0a61c7d65,0x30ba6c29847f66174d85,0x8a611fd9850b714c23ff,0xf66162dc530cf6c12c5b,0xf714c33bac6c16e29847,0xcdec22c9b8a619dd8458,0xc26e29847f66164dc530,0x6197d65613714c23ff24,0x9162509308ffcb309b8a,0x24c3cdacab1284987ab5,0xecbf02b12611fd98dd94,0xac49879b59572589308f,0xb9f8450d624c3d3ac8a1,0x6358930f2eb2a86b1261,0xc2bdb25ba2c498797595],#[0x2ee8b12619bf84dd1624,0x49847f6637458930e3eb,0xd76595624c23fb2fc22c,0x58930e3fbb2cab1261c7,0x8fd0eb2ac49871f61d65,0xeb12615ed92dd9624c3,0x84fee418758930adfca3,0x461d624c27bf26c3ac49,0x930a7ecb50eb12613bf9,0xb27c3ac4984fe6438758,0xb12611fd91e1d624c27b,0xbe59180d8930deca1b01,0xf624c3d3ac8a1ec4986,0xf2eb2a87b1261b9d845,0xea1ec4986d761543d893,0x2613dd9850f624c33bb0,0xe41765c9309efcc287b1,0x724c2bf3213b2e49857e,0xceb2287b92615dd939d9,0x1ee49875759543dc930e,0x15dd9650f724c33bb0ca,0x163dc930aefcb287b926,0x4c337b08b26e49867761,0xb2b09b92611fd9859372,0x869847fe5984dc930cbe,0x5965e01434c3f32c9c02,0x50d30decc3700a1a61f,0x2f3f22b2286985f665b8,0x2c8a1a61f1d65591434c,0x98767dd96450d30ecebb,0x86591434c3d390cb2286,0xd30eaebb2caa1a61e9f],#[0xbb0cb2a8698757dd9655,0xca1a61b5f86595434c36,0x776e417650d30bedc82e,0x9d9434c2bbf24bb28698,0x30bceca4eca1a617d990,0x2f3b286985d76567650d,0x1a613dd989d9434c2bbb,0x66408650d30aeec96eca,0x9434c2fab2243286985f,0xbaeca90ca1a617cd9221,0x43286986b76188650d30,0x617db90619434c27bd30,0x418650d30d6fc330ca1a,0x34c2fb32143286986f6e,0xecad0ca1a6179d94a194,0x2869857765e8650d30ba,0xbd984e01634c27bb3143,0x6458d30bedc8304b1a61,0xc2fb720ba2c6987675d1,0x82e8b1a616df965d1634,0x698577e457458d30eedc,0xd655d1634c2bbf24ba2c,0x58d30e6e4b2e8b1a61d5,0xbbb25ba2c698737e5974,0x8b1a617db90611634c2,0x84f764f8159130b6fcb3,0x3e09644c23fb2fc0ac89,0x1308fecbf04b22613dd9,0x720ba2c8985b7e598359,0xb226197d87595644c2f7,0x7f6637659130adeca6ec,0x1d644c2bf720c3ac8984],#[0x9fdc830eb22614ff966,0x2c3ac89867ee41875913,0x2618ff9661d644c23ff2,0x65a87591308ffcb30eb2,0x644c27f321c3ac89853f,0xfec8f0eb22613dd93e1d,0x2e8986de597805d1308,0x13f996e01744c33f4edc,0x9765d130d3fc32caba26,0x4c2bf3213b2e89863fe1,0xca4ecba2615dd939d974,0xe89855f656765d130ade,0x7965e01744c31ff0d3b2,0x5d130cfc43700ba261d,0x2bf32dc02e89867ea1b8,0xf02ba2611fd92e05744c,0x9847f65b815d130cbeb2,0x86595744c38f90cb2ae8,0xd130cbfc32caba261c7f,0xfb2a432e89857d644865,0xcba2618fd86219744c2a,0x57e642865d130afdc830,0xa19744c2afb2b432e898,0x308fec8f0cba2618ff86,0x25bb2ca9865f59582dd1,0x2a6157d94dd9654c2afb,0x764f8759530abeca10eb,0x5764c2afb29c3aca985d,0x8fec9702bb2615df9360,0xc12ec9847f653815d930,0x615df93609764c2bf720,0x47825d930adfca304bb2],#[0x64c23fb29c12ec9847f6,0xec8f08bb2615fb906117,0x6ec9847f64b845d9308f,0xb7b85601215823ff24c2,0x6148560f5ab228290ac1,0x83ceacab0a42b05fce41,0x1ac690ac1de5725c5215,0x2b069fe156348560d6ec,0x591dcd215834ff0bb1a4,0x48560af6c96e690ac15f,0x2ff0bb9a42b0677e0f73,0x690ac11fd98dcd21583,0x4fe64383485609bfcab,0x6595215823fb2fc1a42b,0x5609be4c2ca90ac1a7d8,0xb0fc2a42b04dfa616548,0x90ac197e87e15215832f,0xdf65b8548560dbcc870a,0x15215832fb2fc2a42b04,0x9fdc830c90ac197e97e,0x1c3242b04dfe55864856,0xac15f79161d215827f32,0xe4d8748560aefc9b0e90,0x215826ff2ac3a42b04f7,0xfac8d0e90ac12ff9661d,0xa62b04bf65b8748560a,0x1e756558531583daac6b,0x7724c560f6ab1ae298ac,0x5823fb31b9262b057d64,0xc22c698ac1e5d6558d31,0x62b06af611644c560d6e,0xf591dd131582dbb27b22],#[0x54c5608fecc6e898ac15,0x27bf26c3a62b069f6196,0x2c2a0ac11fd92a1d3158,0xb07ad5916150560bf9c8,0x645c541583ceacab0a82,0x560afac8ee4a0ac1eb5,0xfb31b9282b072f593725,0x6a0ac1e9d6350d415823,0x5af6536350560b5ecb28,0xdcd41582beb23b9a82b0,0x60f1eb2ac8a0ac11fd98,0x26b2282b07aee4164505,0xac1a7d8659541582d7f,0x7e4d87505609fdc830ca,0x1615823fb2543a82b04f,0xd7cb2700b0ac13f992e0,0xb8ac2b04fe6538058560,0xc1c7d65dc961582beb25,0xcd6358560d3eb2f04b0a,0x15835bf06b1ac2b0737d,0xeb2ee6b0ac19df83dcd6,0x2c2b069f5978358560e3,0xc7d65dd16158357f08b2,0x6558560d3eb2f08b0ac1,0x837b707c02e2b079de45,0x1ee4b8ac19df835c9715,0x2b0737dcd635c560cefc,0xf83d8d715835bf06b1ae,0x5c560dedc8706b8ac1ad,0x5bec9c1ae2b06b759383,0x6b8ac19dd74e0d71583,0x6d7597835c560cefba7],#[0x360b7158357f08b22e2b,0x5608ffca305b8ac11ff9,0xac6a1ee2b065f59582dc,0xb8ac19dd8350f715839b,0x7f66143dc560cdec2287,0x143583db2c6c0286b04,0xd7d43300a1ac1af9866,0x7c0a86b04fe6438150d6,0xac1abd64e05435835bac,0x65f8150d6097ecb702a1,0x43582fb720b1a86b047f,0x2eb2ac6a1ac1e9d6458d,0x1a86b07b6e416350d60f,0x1d9d745cd43583d3ae8b,0xd6550d60d3ec32caa1ac,0x5827f720c3286b065fe1,0xc9d0ca1ac1afb9061943,0x86b04bf6628650d60b6e,0xfb9061d435827f321c32,0x750d6097fcb30ea1ac15,0x23fb2343a86b057764e8,0x70ea1ac12fd96e1d4358,0xb04fe64b8058d608fecb,0x94e01635835f2c9c02c6,0x8d60aeec8ee6b1ac13f9,0xf720b2ac6b057764b735,0xb1ac1e5f9359563583c,0x6be6138058d60b7cc970,0x60963582df329c02c6b0,0x60b6ec8ee6b1ac16fb90,0x20c22c6b05b764b7358d,0x9ac13bf9460b73582df7],#[0xfe5181dcd608ffc9303b,0xb735832facac0ee6b047,0x8ffc8b05b9ac15bf9460,0xc16e6b066f25182dcd60,0xc11ff9460b7358337f28,0x4d65dcd60cbeb2b05b9a,0x55836f307c02cab07576,0xdc8306b2ac177993e016,0xa43b05dde458359560bb,0xeb56450521d83bcae4a0,0x4148760edaba28290ec1,0x82beb2ea0a43b067d61d,0x1ae290ec1cf5635c521d,0x3b067de0d7148760cfac,0x7845c521d833eb08b8a4,0x48760afbca2e290ec19f,0x5bb06b1a43b075de1571,0xe690ec1a7f8558d21d83,0x67760d7348760afbc8a,0x85cd21d832ff0ab9a43b,0x7609bfcab0690ec11fd9,0xb0fc2a43b047f65f8348,0x90ec157d97e1521d832f,0x7fe4d8748760cbecbf0a,0xc531d832ff2ac3a43b04,0xd6ec22c698ec19f5845,0x8b2263b0677611734c76,0xec19bd845d131d8357b0,0xe41844c7608fecc2e898,0x41d82bef24b8a83b04fe,0x7ab1ae2a0ec1db5435c5,0x1a83b072f5917250760e],#[0x1d9d7350d41d83d3ac6a,0xd4350760b5ecb286a0ec,0xd82b7b2ea1a83b066f61,0xc9ae8a0ec16bf9359141,0x83b047fe498750760adf,0x7f9560971d823ff26c3a,0x35c7608feca704b8ec15,0x39bac6a1ae3b057ee414,0x706b8ec19df8350d71d8,0xb047f653835c7608fec9,0x63e0143d823fb25c22e3,0xf60eecb9f00a1ec1ed9,0xf30fc0287b06be61b805,0xa1ec1af996e0143d833,0x6b758f8150f60cfccbf0,0xe0543d833bae7c0a87b0,0x60cdeba702a1ec1abd64,0x2fc0a87b04bf65b8150f,0x1ec15df925cd43d823fb,0xfe5d8650f60d7dc830ca,0xd43d833f720c3a87b063,0xb7dc8308b1ec11ff9161,0xc0ae7b053fe5d8458f60,0xc11fd94e0573d823fb25,0x41845cf608feca704b9e,0x4863fb25c22e7b057ee,0xbc32c2b8243d77755857,0xae090e5fe1b755c121d7,0x8ff865d970486afb2dba,0x765c121afac8cecb8243,0x87bcac4b0ee090e3fe1a,0xb264a0a43fc5634c9414],#[0x290ef96193250521ef2b,0x54358941486fcf20b128,0x50521bf3c9ac4a0a43fa,0x7cb0cb128290fe959162,0x86a0a43f956350d41487,0xeed6194350521edabb2,0x650d41486f6b2ca1a829,0x5219fbcc2c6a0a437b79,0xb29b1a8290df964b6350,0xa0a435f597d8d41486f6,0xe9e4964505219facc6c6,0x9141486f6f26b228290f,0x1afbc82eca0a43db5765,0x8bb28290f79e49765052,0xa433f79061941487b6f2,0xe518650521df3c930ca0,0x614877cf04c02c290eed,0xebc9b00b0a437e792601,0x2c290f9d5958058521b,0x3be562e0161487ceacbc,0xf8058521d7ab1f00b0a4,0x4873eae7c02c290ebdd8,0xba700b0a439f773e0161,0xc290e7ddd38058521cfa,0x7565e01614867eb29c02,0x258521dbbbaf00b0a43b,0x7bcae6b12c290fb958d6,0xac4b0a43de7735896148,0x90fd9dd56258521bf3c9,0x84e0961486fcb21c12c2,0x8521fb3baf04b0a43be5,0xaac6a1ac290df9e49435],#[0x6b0a435f59750d61487d,0xfb96496358521eeab9ac,0x58d61487daf06b1ac290,0x21e7aba6c6b0a43cf574,0x24b22c290d7d64373585,0xa43db57459161486fcf,0xd6437458521ddbc22c8b,0x161486fcf24c22c290d7,0x9fac8708b0a437e592e1,0xbaac290ef964b8458521,0x4397f75e0143486eeb2d,0x438150d218fecbf00a1a,0x34877aac7c0a8690cfd6,0xacb702a1a43bb564e054,0xa8690f57dd56350d219f,0x9df8758d434873bb0eb1,0x7550d21cbec36eaa1a43,0x86afb2dbaa8690e5fe1b,0xc2eca1a435df935d9434,0x690c7fe617650d218fec,0x791619434867f720c328,0x50d218ffcbb0ca1a433f,0x3ff20c3a8690c7f65f86,0xea1a431ff9661d43486,0xc7f65b8750d218fec87,0x5e01634867db25c02c69,0xd218fecbf00b1a4397f7,0xae7c0ac690ef960b8158,0xb1a439f587e0563487ba,0xf964b8158d219fac8702,0x5634867eb29c0ac690e,0x19f6c9708b1a439f576e],#[0xfc22c690e5fdd78458d2,0xa4357d96dd5634863fb2,0xe418758d21aefc9aecb1,0x634873ef22c3ac690c7f,0xffca30eb1a439df9361d,0x6c690c7f6538758d218,0x33f790607634872feeac,0x181d8d21cfaba303b1a4,0x4867df20c16c690cfde5,0xc22e9b1a439ed7460b63,0xc690c7f66174d8d21cde,0x7f75613634867df24c26,0x7d8d218ffc830fb1a439,0x63ff2cc06e690c7fe518,0x2ecb2a431ff9061b7348,0x90f1f6417659521abfc8,0x905db754878ff20bb2ca,0xd521ebbc8aedbaa4357f,0xfb213b6ea90e5fe6176d,0x1baa43b779161b75486a,0xd5fe5980dd521cbec330,0x61b75486aff20c36ea90,0x21cbfc830dbaa4397d90,0x26c36ea90e5f64d86dd5,0xb24357d90a1b754872ff,0xd643815d921df3c1702b,0x176486bef22c02ec90cf,0xcbfc2b00bb2435df9360,0xc02ec90e5fe17805d921,0x435f590e05764863fb27,0x17815d921ef3c1702bb2,0x6486bef22c1aec90f5de],#[0xeca706bb2431fd90e0d7,0xcec90cfde41819d9218f,0xed563601614c63ff20c3,0x8058531debc1b00b0a63,0xc7ceacac02c298df5e4d,0x1a84b0a639f574e01614,0x298fb558d6258531f6ab,0x793609614c7daac6c12c,0x58531f6ab22c6b0a637d,0xdab20b1ac298f755d163,0xc6b0a63ed59258d614c7,0x8fb56516358531f6ac22,0x4591614c7baae9c1ac29,0x531f3ab2ac8b0a63db57,0xf24ba2c298d7de417458,0xb0a63d75655d1614c6be,0x9d5958458531bebc9b08,0x91624c63fb2fc02c498f,0x18fecbf08b1263cbd745,0x8c0ec498c7f643875893,0x2639dd7460f624c73eae,0x61174d8931e5eba2c9b1,0x634c63fb30ba6c498e6f,0xceba2c8b1a637d791609,0xa2c698d77e417458d31e,0x35df925d1634c7baf22b,0x18458d31eaeb2ae8b1a6,0x4c6faf22c22c698df6e4,0xcbf04b22631fd97e0164,0xc898d6fe4174591318fe,0xbf925d1644c7b6f22ba2,0x559131e9eb2ae8b22635],#[0x6bf720c3ac898e5f61d6,0x30eb22639f89061d644c,0x98c7fe418759131cfdc8,0x9261d644c73ef22c3ac8,0xd131cefc9b0eb22631ff,0xfb25c02e898d7de45805,0xba26397d65e01744c63,0xd7d643815d1318fecb70,0xe05744c7aeacbc0ae898,0x318fec8704ba2635f596,0xcb2ae898c7f65b825d1,0xa2635fb90619744c72ff,0x7e4d865d131afbc8b0cb,0x9744c6beb23432e898d7,0xadeca50cba2635dd93a1,0xc32e898c7f662865d131,0x631fd92e19744c63fb21,0x4b805d931aefc9b00bb2,0x64c63fb29c02ec98c7f6,0xfc9b04bb2635f7916097,0x2ec98c7f643825d931ae,0x9dd84e0d764c63fb29c1,0x845d931afdc8308bb263,0xc6bbf26c22ec98d7de45,0x9708bb2631fd90e11764,0x2a0df5e4d80585418fec,0x7946016150776f08c02c,0x58541f3ab2b00b0a837b,0x7eb25c02c2a0f9d59780,0xb0a83bb543e0161506,0xebdd8f8058541d7ab1f,0x5e016150776ac9c02c2a],#[0x541fcaa1a64b0a83b756,0xf04b12c2a0fb558d3258,0xb0a83eb564589615077c,0xede518258541ddbc2304,0x9615067eb21c12c2a0d,0x1ddab2704b0a83bb543e,0x6a1ac2a0fe558d435854,0xa83f356550d61507f2f0,0xe594358541bdacb286b0,0x61507d6ac8b1ac2a0ded,0x6bc1ac6b0a83e756558d,0x1ac2a0fad6516358541f,0x3e7565e0d61507ceacac,0x9434c941bdbc9ac8b0a8,0x506f3b2ca1a64a0f675d,0xcc2ec9928379f9650d32,0xc4a0cfd64780589418ff,0xfd97e016250757ac9c02,0x358941f5ab2302b12831,0x67eb23c1ac4a0e6fe1d4,0x2c8b12831fd97e0d6250,0xa0d7be497658941f57c9,0x93e1d625063fb21c3ac4,0x8941d5eb2301b12831fd,0x6a86c0ec4a0cfde4181d,0x7b1283b9d8350f625077,0xcef66143d8941cdec3a8,0x61f6250677f26c26c4a0,0x418ffc9b0fb12831ff90,0x21c0a86a0dede458050d,0x1a83f9563e0543506f6b,0xd61b8150d41f9ab2f02a],#[0xd43506f6b2dc0a86a0ee,0xbcfc92c6a1a8379f9058,0xb1a86a0fc75956350d41,0x83d3d7659543507b3aec,0x196550d41d9ec32caa1a,0x3506b7f20bb286a0ecfe,0xfc9aeca1a83db7915d94,0x286a0deee418650d41ec,0x79f9361943506f6f22c3,0x8650d41ddc4830ca1a83,0x776f22c3286a0eeee41,0x8d0ca1a83b9f93619435,0x6a0de764e8650d41bdac,0xd98a1943506b7b2f4328,0x58d419deca700b1a833b,0x77b29c12c6a0c7f65f80,0xc8b1a831fd97e0963506,0xd77e4d7658d41bcfc9a,0x2e1d63506bf720c3ac6a,0xd419fbc8303b1a831fd9,0xf20c3ec6a0cfde4981d8,0xb22831ff9261f635063f,0xeee418359141ddac1f02,0xd64506f6f22c1ac8a0d,0x1abfc82ecb2a83b3d65e,0x6c02eca0d5fe4d765954,0x2835bf9460176506bbf2,0x64f805d9418fec9700bb,0x76507b6f09c0aeca0c7f,0xfec8704bb2835bf94609,0x1aeca0c7f64f825d9418,0x35f79160d76506bf720c],#[0xb835d9418fec8706bb28,0x5877af07c0ae0b0c7f64,0xc1ae4b82c3e7565e0570,0xe0b0f1f595725c161cef,0xdf83dc970586aff2ab92,0x25c161e3eb2ee4b82c39,0x79bee6b1ae0b0e9f5978,0xec6b82c3adf8358d7058,0xb0d9f657635c161d6fc1,0x65dcd705878facab9ae0,0xc161f2eb2906b82c3c7d,0xfacbc1ae0b0f97597835,0x6b82c3bd791e0d705874,0xe77dd3835c161ceeba70,0x5d1705876bacbc1ae0b0,0x61e3eb2ee8b82c3c7d65,0x22b2ae0b0e9f597845c1,0x82c3c7d655cb70587cef,0xf59582dc161abfcaae5b,0x3705878facaba6e0b0e9,0xe3eb2ac5b82c3a7d6561,0xc16e0b0c7fe4d82dc161,0xc397d6560b705863ff28,0x8d43dc161afdc8287b82,0x58737b08a1ee0b0f375,0xeb2ac9b82c31fd9850f7,0x6e0b0c7fe4984dc161e3,0x97d65613705863ff26c2,0x81589619fac8702b12c3,0x867eb27c0ac4b0ebd58f,0x2f00b92c3adf8358d625,0x4b0f9d597815c961d3eb],#[0xf8358d725876ef0bc0ae,0xdc961d3eb2b01b92c3ad,0x3ff26c06e4b0f1f59580,0x1b92c31ff9460372586,0xe6f61143dc961cbeb2b,0x613725863fb30a1ee4b,0xd618ffc9b09b92c31ff9,0xac7c0286b0cfd6478050,0xa1ac3a7d65e01435875b,0xb558d8150d618fecbf00,0x943587ceacac0a86b0f,0x1d6eb1f04a1ac33f591e,0x8b1a86b0c7f65f8250d6,0xac3e5d6558d43587d3ac,0x5d16350d61f6bc8ac6a1,0x43587b3ae9b9a86b0fa7,0xefc3ee6a1ac3e5d65dcd,0x9a86b0d776437350d61c,0x3d9d64dcd43586bbb25b,0x77350d61ececa6e6a1ac,0x5873bb0db9a86b0f5759,0xc8ac8a1ac39df86dcd43,0x86b0f8f5956450d61bdb,0x7d8659543587c7acaba2,0x550d61d3fc32caa1ac3a,0x74fb0eb2a86b0e5fe1d6,0x30ca1ac3a7f875954358,0xb0cfde458650d619fdc8,0x9021d435867eb23c3286,0xd61afdc830ea1ac31fd,0xf720c3a86b0d77e4d875,0xea1ac35dd93a1d435867],#[0xc7f6428750d61adeca50,0xe1d435863fb2543a86b0,0x618fec870ea1ac32fd96,0x25c0ac6b0c7f65b8750d,0x1ac33f594e05635867eb,0x764b7358d61aeec86e6b,0x163586bbb29b9ac6b0d7,0xb6fc9ac8b1ac36f79159,0xc0ac6b0dbd64b8158d61,0xc36f79160963586deb29,0x4b7358d61b6ec86e6b1a,0x3586dbb29b9ac6b0db76,0xdc8308b1ac36df935d16,0x6e6b0dbde458458d61b7,0xa7d65613735874facac0,0x80dcd618ffc9301b9ac3,0x872facac06e6b0c7fe51,0xa305b9ac31ff9060b735,0x6b0c7fe4184dcd618ffc,0xd65613735863ff24c26e,0x59161d3eb2f00b22c397,0x4facbc1ac8b0cfd64f81,0xe8b22c35bd90dd164587,0xe9f597805d161adec96,0x5e0d74587ceacbc0ae8b,0x161d3eb2b01ba2c3a7d6,0xf26c06e8b0c7fe4980dd,0xba2c397d65603745863f,0x7fe4d82dd1618ffc8305,0xd70d86b7f28c12e1b0c,0x18fec9706b86c3cdd635,0x8c02e5b0c7f64b845c36],#[0x6c3c7d6560172d86b7f2,0xe11435cb618fec9f00b9,0x72d863fb21c1ae5b0e6f,0xfec9f08b96c31fd90e11,0x287b0eb758f8050f618,0x39bd74e0143d873bae7c,0x78050f61d3eb2f00a1ec,0xd863fb2fc0287b0e5f5d,0xb9f04a1ec3add63e0943,0x87b0e6f5d38250f61cee,0xdf905cd43d863fb2fc12,0x450f61aefc92e6a1ec35,0x6bf720c3a87b0d6fe417,0x30ea1ec39f89061d43d8,0xb0c7fe418750f61cfdc8,0x90e1d43d863ff24c3a87,0xcf61b7dc8308b1ec31fd,0xfb29c02e7b0c7f64b805,0x8b9ec31fd94e0973d863,0xc7f64b845cf61afdc830,0xe0974d863fb27c02e9b0,0x43afdc8306ba6c31fd93,0xecb1ae0a1f371d9635c1,0x8287adf8658d7050f9be,0xd644765c143d3fc32cab,0x97050eafb2a3b2e0a1d7,0xc7fc32ecb82871fe981d,0x3b2e0a1d7764e765c143,0x878ff869d97050eafb2b,0x4e76dc143bedc82c7b82,0x50eafb2b3b6e0a1d776,0xeb1b03b82871fd989db7],#[0xee0a1e6f59181dc143ce,0xddb9058f7050f2facac0,0x63dc143eceb22c7b8287,0xfaf720b2ee0a1f57595,0x830db828797d86597705,0xa1c7fe4586dc143cfdc,0xd95a1b7050ebbb27436e,0x5c543afdc82ecb8a8757,0xb7b293b2e2a1d7764e76,0xedb8a873df9858f7150e,0x1d7764e76dc543afdc82,0x89db7150eb7b293b6e2a,0x5438ffc9301b8a871fd9,0xac8c06e2a1e7758d80dc,0xb8a8797d656037150f37,0x7758d82dc5438ffcb301,0x8f7150f37ac8c16e2a1e,0x3eaeb2ac7b8a87d9d645,0xab26e2a1d77e6163dc54,0xa8797d865977150fa7ac,0xe4986dc5438ffc830db8,0x7150ebbb27436e2a1c7f,0xeec9700b1a875bd94a1b,0x2c6a1ee75938058d439,0x7b9f846096350f6bacbc,0x38258d43bcfca304b1a8,0x50eebb2bc12c6a1de765,0xb2704b1a873dd90e0963,0xc6a1ee76538258d43dce,0x5d95e096350f6bacbc12,0x458d43f4fbb2c8b1a87b,0xfcbeecb2ac6a1fa7ddb8],#[0xecb1a876dd901d96350,0xa1db76437658d43b6f4c,0x97e016550eebb27c02ca,0x9543abf4bf00b2a8757d,0xfeecbb2caa1ddee41765,0xcb2a87d78905d96550f8,0xd5fe417659543ebdc82e,0xdd96550eaff22bb2caa1,0x43abec8eecb2a8757d90,0x21c3acaa1d5f64087595,0xb2878fd766007650eafb,0xe241761d943decc9b003,0x87650f9f720bb0eca1f3,0x8fec850e3b2878ff985d,0xc02eca1f3edd8805d943,0x87cfb76e017650f7b707,0xdb805d943dedc9f00bb2,0x650f73f09c1aeca1e7ed,0xec86ecbb287cdf76e0d7,0x2eca1e7e604805d943a7,0x9fb862017650f3f70240,0x805d943afd4c100bb287,0xf3f703c02eca1e7e607,0x9f00bb287ddb83e01765,0xca1f3ee5b805d943eedc,0x991e017650e3fb23c02e,0x5d943cfdc8f00bb2879f,0xbf720c0aeca1e7ee5b80,0x2bb2875df936057650e,0x1c7f64b815d9438fec87,0x60e7650fb3f09c1aeca,0x9439efc93073b2873df9],#[0x120c3ceca1d3f643769d,0x3b2871ff9061e7650f3f,0x7fe4580dd9438ffc8b0f,0xb7058e3ff22c16e0b1c,0x3cbeb2b05b82c71ff946,0x2c26e0b1d7ee4164dc16,0x2c71ff926137058e3ff2,0xe41745c563cbeb2b09b8,0x7158ebf720ba6e2b1d7e,0xffc8305b8ac73fb90613,0x26e2b1c7fe5182dc5638,0x79f8906137158ebf720c,0x184dc563cfdc8309b8ac,0x58e3ff24c26e2b1c7fe4,0xc82e8b92c797d6561371,0xe4b1d7ee4174dc963afd,0x7d856137258f2fb0aba6,0x4dc9638ffc8309b92c79,0xf2facac26e4b1c7fe458,0x100ba2c73dd91e0d6458,0xb1ef6e0f805d163d7dc3,0x93e017458f5f70dc02e8,0xd163dbcb2f00ba2c7bdb,0xbf0dc1ae8b1ebee5b805,0xcba2c7a7f865957458f5,0xc7fe4182dd16397ec870,0x60b7458e3ff22c16e8b1,0x63aefc9b02b86c797d65,0x28c12e1b1c7f64b815c3,0x86c71fd91e0970d8eb7f,0xf64b845c3638fec8f08b,0x171d8ebbf26c02e3b1c7],#[0x8feca700b8ec71fd92e0,0xc12e3b1c7f643825c763,0xc71fd90e1171d8e3fb29,0x51805cb638fec9708b8e,0x2d8e3fb23c02e5b1d6fe,0xec8708b96c71fd90e057,0x2e9b1c7f647845cb638f,0x1fd91e0974d8e3fb23c0,0x83dc165cbec26e7b82cb,0x4f0038001c00004dfe51,0xc700b0008f0078006100,0x3f012d011600ff00e300,0xb20196017f016d015601,0x1b01ff01e801cc01bf01,0x930281026a024e023202,0xed02db02c402b702aa02,0x5b033f0323031102ff02,0x92038a037d0375036303,0xc903b703aa03a2039a03,0x2d041b03ff03e803d603,0x7d04700463045b044404,0xc804bb04a4048d048504,0x1d050b04f404e704d004,0x6d056505530541052f05,0xb805ab0594058c057505,0x805f605e905d205c505,0x58064b063e062c061006,0xb206aa06980686066f06,0x11070906ed06e006c906,0x8e07770756073a071e07,0x107f407e207c607af07,0x2e0826081e0811080908],#[0x51084908410839083108,0x6f086708640861085908,0x92088a08870875087208,0xb508ad08a508a2089a08,0xec08da08d708ca08c208,0x140911090408fc08f408,0x410939092c0924091c09,0x5f095c094f094c094409,0x87097f0977096f096709,0xaa09a709a4099c098f09,0xe109cf09c709c409b709,0x180a0b09fe09f609ee09,0x270a240a210a1e0a1b0a,0x4f0a470a3a0a320a2a0a,0x770a6f0a670a5f0a570a,0xa40a9c0a8f0a870a7f0a,0xcc0ac90ac10ab90ab10a,0xf90af10aee0ae10ad40a,0x260b190b110b090b010a,0x530b410b390b360b290b,0x760b730b6b0b630b5b0b,0x990b910b8e0b8b0b830b,0xcb0bc30bb60bae0bab0b,0xe90be60be30bdb0bce0b,0xfd0bfa0bf70bf40bec0b,0x1b0c0e0c060c030c000b,0x340c310c2e0c260c1e0c,0x570c540c4c0c440c370c,0x7a0c720c6f0c670c5a0c,0xa20c9a0c970c8f0c870c,0xc00cb80cab0ca80ca50c,0xe80ce00cd80cd00cc80c],#[0x60d030d000cf80cf00c,0x240d1c0d140d110d090d,0x330d300d2d0d2a0d270d,0x5b0d530d500d480d3b0d,0x8d0d850d7d0d750d630d,0xba0db20daa0da20d9a0d,0xe70ddf0dd70dca0dc20d,0xf0e070dff0df70def0d,0x410e390e310e290e170e,0x6e0e660e630e5b0e530e,0x9b0e8e0e860e7e0e760e,0xbe0ebb0eb30eab0ea30e,0xf50eed0ee00ed80ed00e,0x220f1a0f120f050efd0e,0x4f0f420f3f0f320f2a0f,0x860f7e0f760f690f5c0f,0xb80fb00fa80fa00f930f,0xe50fdd0fd50fcd0fc00f,0x12100510020fff0ff20f,0x441037102a1027101f10,0x6c1064105c1054105110,0x99108c107f1077106f10,0xc610b910b610a9109c10,0xf810f010e310db10ce10,0x25111d11151108110010,0x52114511421135112811,0x84117c1174116c115f11,0xc511b311a6119e119611,0xe811e011d811d011c811,0xb1208120011f311eb11,0x2e1226121e1216121312,0x4c124412411239123112],#[0x74126c12641261125412,0x97128f128c1284127c12,0xb512ad12a5129d129a12,0xdd12d512cd12c512bd12,0xf112ee12eb12e812e512,0x14130c1304130112f912,0x2d13251322131a131713,0x5013481340133d133513,0x781375136d1365135d13,0x96138e138b1388138013,0xb913b113a913a6139e13,0xd713cf13cc13c913c113,0xf513f213ef13e713da13,0x22141a140d140a13fd13,0x5e145114441432142f14,0x7c147914711469146614,0xb314ab14a31496148414,0xe514ce14cb14be14b614,0x17150f150714ff14f214,0x3f153c15341527151a15,0x6c1564155c154f154c15,0xa3159b15931586157e15,0xd515cd15c515ae15a615,0x215fa15ed15e515d815,0x20161d16151612160516,0x5c164a1647163f163216,0x93168616791676166416,0xca16bd16b516ad16a516,0xfc16f416ec16e416d716,0x24171c1714170c170416,0x5b17581746173e173617,0x7e177617691766175e17],#[0xa6179e1791178e178b17,0xf617e917dc17ca17bd17,0x1e181b1813180b17f917,0x41183918361833182618,0x8c1875186d1860184e18,0xb918b118ae18a618a318,0xe618de18d618d318d018,0x418fc18f418f118ee18,0x40193819261923191619,0x681965195d1955194d19,0x86197e197b1973197019,0xb319a6199e1996198919,0xdb19d819cb19c319bb19,0xfe19f619f319eb19e319,0x121a0f1a0c1a041a0119,0x301a2d1a251a1d1a1a1a,0x581a501a481a401a381a,0x7b1a731a6b1a631a601a,0x991a961a8e1a861a7e1a,0xcb1ac31ac01ab81aab1a,0x111b091b061af41ad31a,0x341b2c1b241b211b191b,0x5c1b541b4c1b3f1b3c1b,0x6b1b681b651b621b5f1b,0x891b811b7e1b711b6e1b,0xa71ba41b9c1b941b8c1b,0xd91bcc1bbf1bb71baf1b,0x11bf91bf11be41be11b,0x291c261c1e1c161c091c,0x561c491c411c391c2c1c,0x791c6c1c641c611c591c,0xa11c941c911c841c811c],#[0xce1cc61cb91cb11ca91c,0x51cfd1cf01ce81cd61c,0x321d2f1d2c1d1a1d171d,0x4b1d431d401d381d351d,0x641d5c1d591d561d531d,0x821d7f1d7c1d741d671d,0xaa1d9d1d951d8d1d851d,0xc81dc51dbd1dba1dad1d,0xd71dd41dd11dce1dcb1d,0xf01de81de01ddd1dda1d,0x91e061e031e001dfd1d,0x311e291e211e1e1e111e,0x4a1e471e3f1e3c1e391e,0x721e6a1e671e5f1e521e,0x901e8d1e851e821e7a1e,0xa91ea61e9e1e9b1e981e,0xcc1ec91ec11eb91eb11e,0xe51ee21eda1ed71ecf1e,0xf91ef61ef31eeb1ee81e,0x261f191f111f091f011e,0x491f461f431f311f291f,0x671f5f1f571f541f4c1f,0x8a1f871f841f811f741f,0xb21faf1fa71f9f1f971f,0xd01fcd1fc01fbd1fba1f,0xf31feb1fe81fe01fd81f,0x16201320061ffe1ff61f,0x39203120292021201e20,0x75206d206a205d204b20,0x98209520922085208220,0xc520bd20b020a3209b20,0xf220ea20dd20da20c820],#[0xb2108210020f820f520,0x1f211c21142111210e21,0x422130212d2125212221,0x6f215d215a214d214a21,0xa1218a2182217f217c21,0xd321d021be21bb21ae21,0x5220221ff21e821db21,0x3c22342227221f220822,0x6e226b225e224c224922,0xb422a22290227e227122,0xe230122f922e222cb22,0x402333232b2328231b23,0x682365235d2355235223,0x86237e237b2373237023,0xae23a1239e2396238e23,0xc723c423c123b423b123,0xe023dd23da23d223ca23,0xfe23ec23e923e623e323,0x302428241b2413240b23,0x4e24462443243b243824,0x71246e246b2459245124,0x8a2482247f2477247424,0xa824a524a2249a249224,0xc624c324c024b824b024,0xe924e124de24d124c924,0xc24ff24fc24f424ec24,0x3425312524251c250f25,0x66255e25512549254125,0x7f257c25792571256e25,0xa7259f259c258f258725,0xc525bd25ba25b225aa25,0xde25db25d825d525cd25],#[0xfc25f425ec25e425e125,0x1f2617260f2607260425,0x3d263a2637262f262726,0x562653264b2648264026,0x832676266e2661265e26,0xa1269926962693268626,0xc926c126b926b126a926,0xe726df26dc26d926d126,0xa270226fa26f726ef26,0x282720271d271a271227,0x4b27432740273d273027,0x78276b2763275b275327,0xa0279d279a278d278527,0xc327b627b327ab27a827,0xe127de27d627d327cb27,0xfa27f727ef27ec27e427,0x182815280d280527fd27,0x40283828302828282528,0x542851284e284b284328,0x7c2874286c2864285c28,0xa4289c28992887287f28,0xbd28b528b228af28a728,0xd128c928c628c328c028,0xf428f128e428e128d928,0x1c29192911290428fc28,0x3f2937292f2927292429,0x62295029482945294229,0x7b297829752968296529,0xb729af29a7299f298829,0xe429d229cf29cc29bf29,0x1b2a0429f729f429ec29,0x482a402a332a302a232a],#[0x702a682a602a582a552a,0x982a902a882a802a782a,0xd92ac72abf2aa82aa02a,0xf72aef2aec2ae92ae12a,0x1f2b172b0f2b022afa2a,0x422b3a2b322b252b222b,0x5b2b582b552b522b4a2b,0x742b6c2b692b662b5e2b,0x922b8f2b872b7f2b772b,0xb52bad2baa2ba22b952b,0xf12be42bdc2bcf2bc22b,0x1e2c162c0e2c062bfe2b,0x4b2c3e2c312c2e2c262c,0x732c702c682c602c532c,0x912c8e2c862c7e2c762c,0xb42cac2ca42c9c2c992c,0xe62ce32cdb2cd32cc62c,0xe2d062cf92cf62cee2c,0x3b2d332d262d1e2d162d,0x682d602d5d2d4b2d432d,0x862d832d7b2d732d702d,0xae2da62d942d912d8e2d,0xd12dc92dc12db42db12d,0x122e0a2dfd2df02de32d,0x302e2d2e2a2e272e1f2e,0x442e412e392e362e332e,0x6c2e642e5c2e592e4c2e,0x852e7d2e7a2e772e742e,0xa32e9b2e982e902e8d2e,0xc62ec32ebb2eb32eab2e,0xf32eeb2ede2edb2ed32e,0xc2f092f062efe2ef62e],#[0x2f2f272f1f2f1c2f142f,0x432f402f3d2f3a2f372f,0x572f542f512f4e2f462f,0x702f6d2f6a2f672f5f2f,0x7f2f7c2f792f762f732f,0xa22f9f2f9c2f992f8c2f,0xbb2fb82fb52fad2fa52f,0xd42fd12fc92fc12fbe2f,0xfc2ff92fec2fe42fd72f,0x10300d300a30022fff2f,0x2e302630193016301330,0x603058304b3043303630,0x8d308a30823075306d30,0xba30b230aa309d309530,0xe730df30dc30d430c730,0x530fd30f530ed30ea30,0x23311b31133110310831,0x3c3139312c3129312631,0x7331703168315b314431,0x87317f317c3179317631,0xaf31a7319a3197318a31,0xdc31d431c731bf31b731,0x13320131f431ec31e431,0x36322e32263223321b32,0x59325132493246323e32,0x86328332713269326132,0xa432a1329e3296329332,0xc732c432bc32b432ac32,0xef32e732e432d232ca32,0x2633193316330932fc32,0x4e3341333e3336332933,0x763373336b335e335633],#[0xa833963393338b337e33,0xc633be33b633b333ab33,0xda33d233cf33cc33c933,0x233f533ed33e533e233,0x1b341834153412340f34,0x5c345934423426341e34,0x843477346f346c346434,0xb634ae34a63494348c34,0xd434cc34c934bc34b934,0xf734f434f134ee34dc34,0x24351c3519350c350434,0x5b354e3541352a352735,0xab358f35823570356d35,0xfb35e435d235c035b335,0x41363936313629361235,0x78366b365e364c364436,0xa0369336903683367b36,0xcd36c036b836b036a836,0xf036e836e536dd36da36,0x1837103708370536f836,0x363733372b3723371b37,0x4f374c37443741373937,0x6837653762375f375737,0x7c377937763773376b37,0x9a3792378a3782377f37,0xcc37bf37b237aa37a237,0xea37e237da37d737d437,0x8380037fd37f037ed37,0x26381e38163813381038,0x4e384b3848383b382938,0x67385f38573854385138,0x99389138893877386f38],#[0xbc38b438ac38a4389c38,0xee38e138cf38cc38c438,0x11390e390638fe38f638,0x2a3922391f391c391939,0x4d3945393d3935393239,0x6b39683965395d395539,0x893981397e3976397339,0x9d399a39973994399139,0xb639ae39ab39a839a039,0xe339db39ce39cb39be39,0xfc39f939f639ee39eb39,0x1a3a123a0a3a073a0439,0x2e3a263a233a203a1d3a,0x4c3a493a413a3e3a363a,0x603a5d3a5a3a573a4f3a,0x743a6c3a693a663a633a,0x833a803a7d3a7a3a773a,0xa13a993a913a8e3a8b3a,0xbf3abc3ab43ab13aa43a,0x53af33aeb3ad93ad13a,0x3c3b2f3b1d3b103b0d3b,0x733b663b5e3b4c3b493b,0xaa3ba73b9a3b8d3b803b,0xcd3bc03bbd3bb53bad3b,0x93c063bf43bf13bdf3b,0x363c2e3c2b3c233c163c,0x4a3c473c443c3c3c393c,0x5e3c563c533c503c4d3c,0x9a3c8d3c7b3c6e3c663c,0xc23cbf3cbc3cb43ca23c,0xe53ce23cdf3cd23cca3c,0x83cfb3cf83cf03ced3c],#[0x3a3d2d3d2a3d223d153d,0x713d643d5c3d4f3d473d,0x8a3d873d843d773d743d,0xb73daa3da73da43d973d,0xe93de13dd93dd13dc43d,0xc3e043dfc3df43df13d,0x2a3e223e1a3e173e0f3e,0x3e3e3b3e383e303e2d3e,0x523e4f3e4c3e493e463e,0x7a3e723e6a3e623e5a3e,0xa73e9f3e973e8f3e873e,0xcf3ecc3ec93ebc3eaf3e,0xde3edb3ed83ed53ed23e,0x13ef93ef13ee93ee13e,0x383f2b3f1e3f163f093f,0x473f443f413f3e3f3b3f,0x603f5d3f553f4d3f4a3f,0x883f803f7d3f753f723f,0x9c3f993f963f933f8b3f,0xb53fb23faa3fa23f9f3f,0xd83fd53fcd3fc03fb83f,0xec3fe93fe63fe33fdb3f,0xfb3ff83ff53ff23fef3f,0xf400c400940013ffe3f,0x234020401d401a401740,0x464043403b4033402b40,0x64406140594056404e40,0x8c40844077406f406c40,0xaa40a2409f409c409440,0xcd40c040b840b040ad40,0xe640e340e040d840d540,0xff40f740f440ec40e940],#[0x2c411f4117410f410240,0x4a4142413f4132412f41,0x634160415d4155414d41,0x9a419241804178417041,0xd141c941c141af41a741,0xfe41f641e941e141d941,0x1c421442114209420641,0x3f4237422f4227421f42,0x5d425a4257424f424242,0x76427342704263426042,0x8f428c42844281427e42,0xa842a042984295429242,0xc142be42b642ae42ab42,0xda42d242ca42c742c442,0xfd42f042e842e042dd42,0xc430943064303430042,0x1b431843154312430f43,0x2a432743244321431e43,0x3e433643334330432d43,0x5c435443514344434143,0x7f4377436a4367436443,0x984390438d438a438243,0xb143ae43a643a3439b43,0xc543c243bf43b743b443,0xd943d643ce43cb43c843,0xe843e543e243df43dc43,0xfc43f443f143ee43eb43,0x62c412440f440c440943,0x80090562825e028a0e05,0x787a2f800e0562038a2f,0x423810085e1589e00381,0x20c2487e00c606021705],#[0xa0c825e00382048118,0xe005e158a128480d603e,0x38204908056178809021,0x588130480e0610f80458,0x19049e00382049a2c381,0x46138204588130460e06,0x38381181a28514160228,0xc087040580e282923840,0x702178bc084a17856202,0x2f8a2070215081285760,0x2e0066286611821c0c12,0x70805e03856258b0150,0x10561270217881205f0e,0x3c0d4382013238403838,0x24201586038570e06120,0xa1243817870800e17861,0x2200d8a1203c0d834880,0x178481587e0036003c0d,0xf800810083414052382,0x5840a07a048e148e0f80,0x825860e06418640e0412,0x4e10d8b808a138461082,0xb0280388144021906190,0x4190213046e283820420,0x3e002038381002190,0x801186220681201a1908,0xc0892230e0e89e004a5f,0x80858562028c3840a00f,0x385e15861384a178610f,0x7e280e15861784815860,0x17880402a383e286c150,0x7c16802680085612e80],#[0x158560866121e638487f,0x4904840480fe00602066,0xe04162f800c160385618,0x5e104905856184c12043,0x3e82e070420661784038,0x819056185e1204a1588c,0x60250e084817868184,0xe104de1f80180813787e,0x21384dc2f09e00ba048,0x60062180562f81a105e0,0x34303409020c2580285f,0x28050809020c2580e00,0x2046e258021820302560,0x3e00342821603800d081,0xd081203e0034184a1220,0x80a8a008408021582a2,0x2178322820082028a09,0x22820008902228289,0x85608340800d3801206,0x824a284178217820056,0xc2022a04180a28041686,0x8022804100609080c200,0x222804100609080d080,0x18203088184010808005,0x18211821183810211821,0x200610006860909a185a,0x2015861582008a01044,0x80120809800821600560,0x8000000000566004015,0xe020a020878012020856,0x10202020802158201030,0x420e05080581020e020],#[0x800e020802080222a041,0x206080105e000814200,0x4810282020102020208,0x8780820029c1040020a2,0x36003600360020938a11,0x200160036038a100600,0x80118008011a8a410660,0x808208780101e002009,0x16080000000000208000,0xe08020800878015,0x100048e080e0c0500840,0x1b8a102c080038300a02,0x4000000e080880211821,0xe084c080e0c200c21810,0xe0f8008340850080e080,0x200e0e0800382000000,0x40861238488020000000,0xc1780038603820802070,0xc201184808308030803,0x8380820080e0820084c,0x803808203820e00e100e,0x1022282a3820382a3820,0x380830803c17800387c,0x80211820b08e080608,0x80080e080e080e080e08,0x24202050288028838a11,0x408560824e284a180158,0x17820d02e28208308103,0xf020834085e084a1784,0x80418680100c20061032,0x20080220044220610041,0x802200401e8011080c],#[0x880100609080d080e8,0x1005a0040d0242020502,0x8801108018400001680,0x2200442006101a0020,0x180806085e0801782c1,0x20610340085010301020,0x840308818420702100c2,0x412021268010320832c0,0x61686084808480e03a00,0x42006101a003a1824268,0x20341049e00400022004,0xf020f0208480849e0041,0x210340f800833c08801,0x808200800d0022006420,0x205080200380802080,0x80820080008206080f8,0xa0808010830082000208,0x8020f020800828812020,0x282005e0a200a0a0,0x10820282008202820802,0x282090202821382,0x2008200801083080200,0x22820082028200200800,0x828202f80100a0c20080,0xa0e8a08080828282,0x820282000a0e8a0e8a08,0x101c0820000282008202,0x3841582000120212380,0x80e1002085e03840056,0x850803416054084a181c,0x8015820d02001e081f80,0x20d4241587c0850185e0],#[0x3f02105e0800d020d0,0x101fc0841281e6070220,0x10017821782080361848,0x84058a08048085c0d86,0x802080e0d8b0804058b4,0x21350214200f03e000e1,0x9c080e203c0801202810,0xc0a8e101810215820e58,0xc08400800f0212041983,0x104f62d0218003820405,0xd8bc080e180178308416,0x4f4084000f01702185e0,0x8362d0212060130210,0x801e1403628400820082,0x81408140808084a15848,0x806080608060818080e0,0x180608040810038001,0x11e00400000800010028,0x10000400004000109808,0x12856290440b80200408,0x840d424104a607021d8a,0x201020400a0006005603,0x20001780e104a080008,0x61010020001802200401,0x1082a0800088182c220,0x200000804430ac21002,0x10080001002808000800,0x80008000800000080009,0x18002780104209f801,0x2040001000082a098,0x1c102000e08000020002,0x2085608560384000e08],#[0x40382008217821780e17,0x202038203820010000,0x5a0800008080000408,0xe800800080a182e202,0x20c8200000806080e080,0xe080e080e0800c82028,0x6081000040400a000600,0xe21800d0c04036002000,0x20050e2b881a248838a,0xf800800081e002600360,0xe080008100004000e0,0x20120c3840000000000,0x20200060d86080208101,0x88811100284130203820,0x82038382704101028202,0x200c0809100204020202,0x4028282820405010000,0x10020800102001000,0x10210004000100000204,0x38038401820082010241,0x80810020001802080408,0x2046a206000204000120,0xe0800000076198381801,0xe08000000820382000,0x38200000380e0801040,0x40010000403820382,0x3820010,0xc2004108a0820080,0x2008203080105010200,0x100e0800382000008202,0x8000800080820282e02,0x8080000008000020008],#[0x200020002168200,0x2020000702081c1020,0x84038202820382168200,0x400800060002000400,0x400020382000008000,0x20101000000400010100,0x1080804183c083a002c,0x82009200800401c100,0x2013020b040810802058,0x2000308020580080190,0x558b600609d8b600600,0x5054084098200096184,0x6204e00200000040084,0x2800180108288188122,0x8003860b8ae0040010,0x20800000188080,0x60e082880d801800002,0x90419602120600288084,0x30808064204608006081,0x21800860e1012420412,0x8242982041282002961a,0x42024200000090142382,0x7800e0fc204090212d8a,0x801064808421800b0461,0xbe000e1864138400000f,0x4a05602184804e021b8,0xe282d42081082c238282,0x850a021384219602204e,0x2002c03840b028106413,0x2c0a00e182c0a04038,0x182005608121820382,0x400060d020d02080408],#[0x8000001e80100001000,0x10818000000000420c16,0x40102020219438106412,0x12020502080a0e05408,0x1911040061902000808,0xd020d02080038200000,0xe080e080e0800002080a,0x82005603840082000000,0xf00840002080e08003,0x40001418081821840,0x8740854082a183094141,0x9020010182000e0d020e,0x8000020064c28481821,0x20002000200000800,0x80a0d020d02080000000,0x38203820382018200020,0x2000e080000028302821,0x42084240840042080038,0x8200002f801000a02610,0x83c0828083a282828210,0x28380820000283a283a2,0xf020f020b0208000820,0x10b0210420b020800702,0x2408200820083c082000,0x108210a0217800384050,0x1082000e08000420b04,0x20800082108210b0210,0x20000002002808000,0x801a06410000020002,0x80000000200000800080,0xe0800080a080e08640,0x1020800b3800a0600020],#[0x2000000038200003820,0x80040001000382038200,0x8000020c00e138a09060,0x19021902008205840,0xe1000010020001d8a080,0x21884204781840000350,0x183408340821182e2d88,0x81002800180010a01040,0x88020808084000e0f020,0x4030ac205c08381e05c0,0x2080c2b0817020810c38,0x20f80080008020f02080,0x62002080008020f020f0,0x8462486118219885c084,0x8011820000082020219,0x1c0828082040001008,0x80a0896084608162284,0x4e080000a0800000016,0xb04001c082008280820,0x16050084118200020848,0xe8415020849408411c84,0x2084608480d09c08411,0x462204058a0d0208500c,0x20a20c38540821250210,0x408480f0208003020b0,0x8020808080a081010200,0x20382439021028438421,0x47828400020d84080038,0x881046084c0846084608,0xcc0860083c0828082228,0x20082000208020801384,0x4c0b30a1800002080000],#[0x8214028a050100000208,0x2104e13041302c408612,0x3b02104a084811841280,0x800282000000001c0821,0x9020e0e080e1044140a0,0xe0800182028200007020,0x30182018221020382000,0x100038201e80100038,0x80010008500800402040,0x38203820382000e08000,0x20200000160800000000,0x8400000000000001020,0x118200000004000100b4,0x1610361020000001182,0x1384c1002091002840,0x332384000000004c0800,0x48782a388c148c081e08,0x1820d00e121e0834008,0x5821582001408568285,0x580a1606085e085fe004,0x1820004088881841,0x2005e080228201820282,0x80125881000001782178,0x2120411d8960d0627060,0x100810200000005820d8,0xd021583012041001b582,0x85e084808040c8215820,0x861580e1056085608320,0x340801203810203f8015,0x820d02005e085e083408,0x6600601820182178217,0x8000560800400010007e],#[0x8002820808080e0c8a0,0x5c002001000800180a,0x400100004040001007c,0x40004081000040011e0,0x201b0010880832081000,0x102c00561006081c00,0x80080000200100200018,0x6080e08000000000f,0x17001010000403820382,0x8e0e802b820800000000,0x8012849a0382221ee2b8,0x98e60840c82003208320,0x820b8ae23821b820d820,0x800081e003410000260b,0x4000000d62d881f800,0x608015f8010340835e,0x2842041182019b082000,0x418011d8342060830810,0x5800d8a8104a101361a0,0xe1c04138415821283281,0xe0420460a6041b8be000,0x204e05b8b420812814e1,0x820383010213842e0e04,0x8158bc200e185608013,0x41282004f4204058,0xe080e080e08560384001,0x7800384050041002080,0x108041704080e0801082,0x203820382000e0802080,0x200000800082000808,0x200000000020,0x8000800080008000800],#[0x8100004040001002080e,0x21000000080008000660,0xa0800000080008002b8,0x2120411d894286002c0f,0x58215836082000000058,0x82178205a0a810617838,0xa040f80085e085608017,0x8405a0a810600040d880,0x4808660a160848084d42,0x16080a080000050200,0x13820182028202024582,0x2005608005820001782,0x42080000000010202,0x80100478161616084208,0x80068808081028202027,0x7040f0408007040,0x10200040804080408,0x60e08000000000000020,0x2058200000020000000,0x600000800100210000,0x219049a0876002040080,0x2101a203a21812087600,0x48220411c05a087a248,0x8208472268218011d041,0x226821065a0852268214,0xc382000881881047c105,0x2091600611c041012082,0x4a12682180126826007a,0x8212604104f208400,0x8080068208,0x612d82104a0856084a08,0x184a0832600412032e00],#[0xc060800582084701582,0x40800382000010021008,0x38505c1210121084040,0x10481504120405860856,0xd0410420d04120413034,0x2d041000110028400122,0x205c1048100000aa0850,0x82828281028128217041,0x808000800080a282a0,0x800000080008000020,0x84e0800000056080000,0x2046104a084e084a084e,0x383c1021382138212821,0x13c04104701041,0x82138383821382000000,0x41048084f2085838383,0x47010413c,0x4762d82180e1820282,0xc38203820800202,0xa168a08005860d860800,0x82001a2024400,0x8200000820000000000,0x20082000200820000001,0x806382018e0a82080038,0x98e0f806384a082000e0,0x4080018e080018e08100,0x4081a10224084100e080,0x1000382000e080000068,0xfa1042782038203f80,0xe0020684080040001000,0xa084c0b0a6184001c283,0x2c08100a082a06780180],#[0x83428203c0b0207c2830,0x26428410838202108203,0x10208013020102081008,0x100a3024102e08241020,0x81904000000c283c2f08,0x680800182080006,0x82098208000200b80080,0x40800000080208000001,0x24008170a086,0x0,0xe8008101402100000208,0x8101820400010005820,0x4c080608201820800064,0x86080000000c38200000,0x38208000000000000003,0x40001]]
set_option maxRecDepth 16000 in
def g127H7 := limbs80 #[#[0x2031020100001000220,0x110310140000a2011001,0x30130232000050121200,0x30100004310021004104,0x314543b0300001103111,0x210110000a0011801510,0x50910255420130010,0x307a00024020000,0x2d2a00000,0x657800,0xa2140000000000,0x3c000728400000000000,0x18d6000000000018f991,0xb927ca700028c23b4,0x86000000000000000000,0x900000000000000d65ec,0xf530000365821,0x1c200000d39,0x806ac2400000000000,0x15540000000193800000,0x4500000000a0e,0x6d000000074880000000,0xd7278000f31658100001,0x193abc54a08207e4b,0xd28000d22d0ae58d3c11,0x51938e4f800000008ab7,0xc0000bc400000036c7f4,0x97d0003019362b50bb57,0x53100000001243,0x10b9000000000000,0x2d4000000000,0x418000f1600000000000],#[0x2560280800000000005,0x632047200028cb00,0xec5e5f8000a518000000,0x860002c404bf8000d122,0xa0000000db5800000029,0x934cc5,0x1cdc6615592,0x101a0000000895ba040,0xd23604158e000000,0x96800000000000000c57,0x664400043ccc562ced,0x650000c1500,0x9454000000000,0x1ff8f70000000db08d55,0x114a0000000000054f5,0x10e000000000000f2200,0xe5c40000002e87000,0xf2000000000000000000,0xe414000e8a9a119640c,0x64348c6000000,0x86c8440002c320000ca6,0x5,0x381b0000000000114300,0x52c00038a20000000000,0x10ca0001,0x0,0xa3fc000000000,0xe620000f164000,0x2c3e000061a0,0x183d00,0x91700000000000000000,0x34344400039d0000e8de],#[0x90000000000345ce3a79,0xd9fd12,0xd8774600000004360000,0xa,0x5a9800000,0x8848156015b4d4000861,0x82fa8400000000002,0x14e400000,0x414c5d40fa000000,0x2805,0x4f18d000000000028fc0,0x2c9781bc000000008092,0x4d215dc0000002778000,0x41e3d8000958c000c9c4,0x32dc0000564919993df,0x0,0xcf4e2d00000000000000,0xfab07457934000a,0x80000000000000000000,0x24c00000000000756,0x21000000000000000000,0xd00018b20000000b1880,0xf394a8d194346,0x5aac6000033710000000,0x98000000152800015454,0x212b9597c3ae0d800034,0x1f29000,0x147e0000,0x30300,0x0,0x5c9c28000252733ec000,0xb8964304915],#[0x6ab8000000000000,0x58200000000000000a06,0x305c00000037400002,0x989c0000000c51cbd00,0xb5b8c120000000ea2800,0x48dc95000000000014ec,0x5000059dd434000360cf,0xdd00000000000000a2,0xdf0000000a364000000,0x48e38d40b54b80000003,0xada840ee0001e8c00022,0x1c73000000022ebce,0x8c48c9000367a0000000,0x2f993000000003380b45,0xbc30000000348815,0xb87c0004438000000,0x90a505370c4,0xbcf90ad000252f00000,0xd090000108c00,0x2a8000c11accf4494000,0x1080003d4900038a90,0x34f0000384e000000000,0x0,0xa60c00000000000000,0x296f72940004a0c0,0x2e2f0000cc3000000,0x8c3ef9000308e0001239,0x4b1670003487c8500005,0xa59a8ccea68000cc,0x615000248f0000000000,0x337800000000000001,0x2558000000157900000],#[0x83040000544000000000,0x11882a0e12,0x25c7c000000000000000,0x81d0000000da,0x52100000000000000000,0x3700016945601c0ef270,0x4800c00000008b80003d,0x51f4000b02400,0x7211d0003a060000000,0x147900000000003000d,0x400021e0000000220a00,0x5ae90d495fca13d27,0x9a4c000e46c0004584,0x633f40000000000a0dc0,0x2b2a4d2c863000106,0x56c00000000000000000,0xbc000d0f22760002cf4d,0x1001e43c000000000080,0x48a00000000000000000,0xb26bb14dc18,0x639b400098354d700000,0xf40466b000182d000182,0x0,0x20f800000000,0x2c760000000000000000,0x18c40000000000,0x926c,0x527c00000000,0xc44c0000001ef8000000,0x0,0x313d000197c0,0xf1efc42a20629100],#[0x4dbfde457635e196c000,0xc43e2261694137,0xa50000000000,0x313c0002d6b000000,0x0,0x9046700000000002ccd0,0x205b24cc07052,0x1e952838000747,0x2074a17a8bfda2c,0x847b61c0,0x0,0x54c57a35200000000000,0x3c0001c6c0000000000b,0x1e1732600007a,0x512c0250000000000,0x84ec0000863509d300,0x9543cd5f02000000000,0xfa200000002903000000,0x5080927e54000000113f,0xde0578282cb10002910a,0x439c000987a57bb1,0xf0a00020451184000000,0x207b50283c6,0xdc640,0x0,0xbc0000920c000b534000,0x3c6a00000000003c6c5,0x40004a8c3760001ef600,0x93661d400053d,0x328f4650000,0xd41a58be000000000000,0x2192d41000345],#[0x2c390000000517c000,0x0,0x30b300,0xbaf,0x6b000000000000000128,0xb3f8000309d0,0xd47c000000000,0xc710000000,0xe1a000070a80000,0x0,0x0,0x8000318c00000000000,0x1f,0x5028000000000,0x54a53200000000000000,0x304910cc00048580005,0x636daae8bc00,0x7e300000088000000,0x6ef3b40000001e5f0000,0xc0000000653ac0f00000,0x8bce0e6f9ec564849173,0x7abca077400000,0x0,0xf31e00000da000000000,0x24ef0000000762,0x8200020eb00000000000,0x8000000012ec000d2c34,0x1a7,0x0,0x1cd1f341d58fcd00000,0x188c0000000000000000,0x20c00006043195000],#[0xaf684259800000000000,0x82b282ccad5a1cd01e8,0x463e90a0001775ee0000,0x0,0x90af8e800000000,0x3d1600,0x51a0003e090000000000,0x36240005481,0x392d80000bf25748c940,0x641c0000000e3a0001d7,0x3544038ad5d,0x30000931c000d5880000,0x2104000200de51c00031,0x1e050002d2d000,0x1e000281318d5c3f0000,0x35c000000025,0x1b22e33000000,0xd1e416e0ec0000000000,0x62580002,0xb11280d6852000202e00,0x8cdc0007385270863,0xce0003e0f00000000000,0xef20000000b266a,0x0,0x21570000000]]
set_option maxRecDepth 16000 in
def g127D8 := limbs80 #[#[0xe756558510fe12148110,0x9df835d91097f855c910,0xe756558521ed96358130,0xc7d765952197f855cd21,0x97e875952197c8759521,0x97f855d92197d86dd521,0xe756558531ed56358531,0xc7d65dc961e756558541,0xe778159561a7d85d8d61,0x9fb805d943c7d655cb61,0xb77815cd6597d85dc963,0xff13148110a7f865cd65,0xff16148110ff14148110,0xbfb8348110bf98348110,0xdf97648110f796548110,0xff1214c110dfb7648110,0xff1614c110ff1414c110,0xfd9634c110fd9434c110,0xdf9764c110f79654c110,0xff12158110bf9864c110,0xff14158110ff13158110,0xff38158110ff16158110,0xdfb7258110df97258110,0xef96358110bfb8258110,0xdf97358110efb6358110,0xbfb8358110dfb7358110,0xefb6458110ef96458110,0xdfb7458110df97458110,0xfe53248510f796558110,0xbf58348510fe56248510,0xdf57448510bf78348510,0xbf58448510df77448510],#[0xf756548510bf78448510,0xdf57648510f778548510,0xbf58648510df77648510,0xfd5634c510bf78648510,0xf75654c510bf5844c510,0xbf5864c510df5764c510,0xdf77250510df57250510,0xfb56450510fb54350510,0xdf57650510f756550510,0xbf58650510df77650510,0xdf57258510ff38058510,0xbf78258510df77258510,0xef76358510ef56358510,0xdf77358510df57358510,0xdf57458510bf78358510,0xbf78458510df77458510,0xddf734c910f756558510,0xe7d65589109fd874c910,0x9ff87589109fd8758910,0xbf581d8910bf980d8910,0xb7d85d8910e7d65d8910,0xb7f855c9109fd87d8910,0xd7d655c9109ff835c910,0x9ff865c910d7f855c910,0xd7d65dc9109fd84dc910,0xbfb8050d109fd86dc910,0xdbd7450d10ddf7350d10,0x9ff8750d109fd8750d10,0xcfd7658d10ddd7358d10,0x9ff8758d109fd8758d10,0xbf581d8d10bf980d8d10,0xb7d85d8d10ddf73d8d10],#[0x9fd87d8d10cfd76d8d10,0x9fd82dcd10d7d655cd10,0xd7d65dcd109fd84dcd10,0xbfb80591109fd86dcd10,0x9fd8759110dbd7459110,0xbf980d91109ff8759110,0xb7d85d9110bf581d9110,0x9ff825d1109fd87d9110,0xd7d655d1109ff835d110,0x9fd82dd1109ff865d110,0x9fd86dd110d7d65dd110,0xd7d7659510f778159510,0xd7c8759510d7f7659510,0xbfb805d910d7f8759510,0xbdf835d910bf7815d910,0xdf7815d910dfb805d910,0xddc835d9109ff825d910,0x9ff835d910ddf835d910,0xbf9809d9109ff845d910,0xb7d859d910bf5819d910,0x9fd82dd9109fd879d910,0xdfb71581309fd84dd910,0xdfb7258130bfb8158130,0xfd96358130fd94358130,0xef96458130fdb8358130,0xdf97458130efb6458130,0xf796558130dfb7458130,0xb7f8548530df77148530,0xedd6358530f9d4350530,0x9ff8758530e7d6558530,0xedd63d8530bf980d8530,0xe7d65d8530bdd83d8530],#[0x9fd87d8530b7d85d8530,0xddd63dc5309fd82dc530,0xd7d65dc5309fd84dc530,0xe7d65589309fd86dc530,0xbf980d89309ff8758930,0xe7d65d8930bdd83d8930,0x9fd87d8930b7d85d8930,0xddd63dc930ddd43dc930,0xd7d65dc9309fd84dc930,0xfdb8050d309fd86dc930,0xf5d6550d30f9d6450d30,0xddf7650d30ddd7650d30,0xbdf8650d30bdd8650d30,0xddd7458d30fdb8058d30,0xbdf8458d30ddf7458d30,0x9fd8759130f5d6558d30,0xbf980d91309ff8759130,0xb7d85d9130bdd83d9130,0xbfb805d1309fd87d9130,0x9ff815d130dfb805d130,0x9ff865d130d7d655d130,0xd7d65dd1309fd82dd130,0xd7d76595309fd86dd130,0xd7c8759530d7f7659530,0xbfb805d930d7f8759530,0xdfb805d930bdf835d930,0x9ff825d9309ff815d930,0x9ff845d930ddf835d930,0xbdd839d930bf9809d930,0x9fd879d930b7d859d930,0x9fd84dd9309fd82dd930,0x9fe8748560b7f8548560],#[0x9fe874c560edd634c560,0x9fe8750560ebd6450560,0xdf77158560bfb8058560,0xbdf835c560e7d6558560,0xcfd63dc5609fd82dc560,0x9fd83dc560cff63dc560,0xd7d65dc5609fd84dc560,0xafd8650d60edd6350d60,0x9fe8750d609fc8750d60,0xbfb8058d609ff8750d60,0xe7d6558d60ddf7358d60,0xedf7358d60efb8058d60,0xafd84d8d60aff8458d60,0x9fd82dcd609fd81dcd60,0xd7d65dcd609fd84dcd60,0xdf57148760f7b8059560,0x9fd8748760b7f8548760,0xedd634c760df5714c760,0x9fd874c760ddd734c760,0xebd6450760df57150760,0x9fd8750760dbd7450760,0xcfd635c7609ff825c760,0x9ff845c7609ff835c760,0xedd6350f60bfb8050f60,0xd7d7550f60ddd7350f60,0x9fd8750f60afd8650f60,0xaff8458f609ff8750f60,0x9ff825cf609ff815cf60,0xd7f755c1219ff845cf60,0x9fd86dc121df561dc121,0xfe56250521fe53250521,0xfb56450521fb54350521],#[0xbf58650521df57650521,0xfe56258521bf78058521,0xef56358521fe78258521,0xdf57358521ef76358521,0xdf57458521df77358521,0xbf78458521df77458521,0xf777558521f756558521,0xd7f7550d21bf78150d21,0x9ff8750d219fd8750d21,0xddd7358d21bf78158d21,0x9fd8758d21d7f7558d21,0xbf581d8d219ff8758d21,0xd7f75d8d21bed82d8d21,0x9fd80dcd219fd87d8d21,0xd7d76595219fd86dcd21,0xd7e76dd521d7d76dd521,0xd7d80dd521b7d86dd521,0xd7e86dd521d7d86dd521,0x9ff805d921bf7815d921,0x9ff835d921df7815d921,0xbf5819d921d7f855d921,0x9fd80dd9219fd879d921,0xfd56358531bf78058531,0xdf57458531fd78358531,0x9ff8758931f756558531,0xbdd83d8931bf581d8931,0xfd78158d319fd87d8931,0xf5d6558d31ddd7458d31,0x9fd8759131dbd7459131,0xbf581d91319ff8759131,0x9fd87d9131bdd83d9131,0xdf7815d1319ff805d131],#[0xd7d655d1319ff825d131,0xd7d76595319ff865d131,0xdf7815d9319ff805d931,0xddf835d9319ff825d931,0xbf780585419ff845d931,0xfb54358541bf78258541,0xef76358541ef56358541,0xfb78458541fb56458541,0xf9d434c941f756558541,0x9ff8758941ebd6458941,0xebd64d8941bf581d8941,0x9fd87d8941bbd84d8941,0xf9d6350d41fb78150d41,0xdbd7650d41f3d6550d41,0xbbf8650d41bbd8650d41,0xbf581d8d419ff8758d41,0x9fd87d8d41bbd84d8d41,0xbbf8359141fb78159141,0xd7d7659541f3d6559141,0xdf7815d9419ff805d941,0x9ff835d9419ff825d941,0xbdf835c161dbf845d941,0xe7d65dc161e7d655c161,0xcfd63dc1619fd82dc161,0x9fd83dc161cff63dc161,0xd7d65dc1619fd84dc161,0xe7d6558961bf78158961,0xb7f855c961e7d655c961,0x9fd80dc961e7d65dc961,0x9fd84dc9619fd83dc961,0xedd6350d61d7d65dc961,0xe7d6550d61ddf7350d61],#[0x9fe8750d619fc8750d61,0xbf78158d619ff8750d61,0xe7d6558d61ddf7358d61,0xedf7358d61ef78158d61,0xe7d65dcd61e7d655cd61,0x9fd82dcd619fd80dcd61,0xd7d65dcd619fd84dcd61,0xdbf7459161bf78159161,0xe7d655d161e7d6559161,0x9fd80dd161e7d65dd161,0x9fd83dd1619fd82dd161,0xf778159561d7d65dd161,0x9ff825c361e7f8059561,0x9ff835c361cfd635c361,0x9ff805cb619ff845c361,0x9ff845cb619ff835cb61,0xddd7350f61edd6350f61,0xe7d6550f61dbd7450f61,0x9fd8750f61d7d7550f61,0x9ff805cf619ff8750f61,0x9ff845cf619ff825cf61,0x9ff825d3619ff805d361,0xe7f80597619ff835d361,0x9fd81dc143d7f805d761,0xd7d65dc143ddd63dc143,0x9fd80dc5439fd86dc143,0xddd63dc5439fd82dc543,0xd7d65dc543dbd64dc543,0xbdf8058d439fd86dc543,0xf9d6458d43bdf8258d43,0xf5d6558d43f9f8458d43,0xedf7658d43edc7658d43],#[0xd7f7659543d7d7659543,0xd7f8759543d7c8759543,0xbf5811d943bf9801d943,0xcfd761d943b7d851d943,0xbfb805d9439fe871d943,0xcff765d943bdf835d943,0xdfb805d943df8805d943,0x9ff815d9439ff805d943,0xbdd839d943ddf835d943,0xcff769d943b7d859d943,0x9fd80dd9439fd879d943,0x9fd81dc1639fd81dd943,0x9fd84dc1639fd82dc163,0x9fd80dc563d7d65dc163,0x9fd84dc5639fd82dc563,0xb7d85dc963d7d65dc563,0x9fd81dc9639fd80dc963,0xd7d65dc9639fd84dc963,0xbdf8359163d7d85dc963,0xaff865d163bfb805d163,0x9fd81dd1639fd80dd163,0xd7d65dd1639fd82dd163,0x9ff815c363f5f8359563,0x9ff845c3639ff825c363,0x9ff825c7639ff805c763,0x9ff805cb639ff845c763,0x9ff845cb639ff815cb63,0x9ff815d3639ff805d363,0xd7f805d7639ff825d363,0xd7d73dc165b7d81dc165,0xb7d83dc165d7f73dc165,0xb7f805cd65b7f805c565],#[0xd7f74dcd65b7f865cd65,0xff96348110ff94348110,0xff98348110ffb6348110,0xffa7648110ff97648110,0xff9624c110ff9424c110,0xff9644c110ffb624c110,0xff93258110ffb644c110,0xff96258110ff94258110,0xff98258110ff97258110,0xff94358110ffb8258110,0xff98358110ff96358110,0xff96458110ffb8358110,0xff98458110ff97458110,0xff54348510ffb8458110,0xff76348510ff56348510,0xff76448510ff56448510,0xff57648510ff57448510,0xff58648510ff67648510,0xff5424c510ff68648510,0xff7624c510ff5624c510,0xff7644c510ff5644c510,0xff56250510ff53250510,0xff57250510ff76250510,0xff76350510ff56350510,0xff67650510ff57650510,0xff54258510ff53258510,0xff57258510ff56258510,0xff78258510ff58258510,0xff56358510ff54358510,0xff78358510ff58358510,0xff57458510ff56458510,0xff78458510ff58458510],#[0xfdd434c910fed624c910,0xdfd744c910fdd634c910,0xdfd764c910bfd844c910,0xfed6250910bfd864c910,0xdff7350910dfd7350910,0xdfd7650910fbd6450910,0xbfd8650910dff7650910,0xff98058910bfd8750910,0xfed7258910ff58158910,0xdff7358910dfd7358910,0xefd6458910bff8358910,0xdfd7458910eff6458910,0xbff8458910dff7458910,0xdfd7658910f7d6558910,0xdfd8758910dff7658910,0xdfe8758910bfd8758910,0xdfd73d8910bff8758910,0xbfd83d8910dff73d8910,0xdfd74d8910efd64d8910,0xbfd84d8910dff74d8910,0xdfd745c910bfd87d8910,0xf7d655c910bff845c910,0xdfd765c910f7f855c910,0xbff865c910dfe765c910,0xdfd635c910dfd435c910,0xdfd835c910dff635c910,0xdfc865c910dff835c910,0xdfe865c910dfd865c910,0xdfd64dc910dff865c910,0xff58150d10dff64dc910,0xfdd6350d10bff8250d10,0xf7d6550d10fbd6450d10],#[0xbfd8650d10dfd7650d10,0xdfd8750d10bff8650d10,0xff58158d10ff98058d10,0xdfd7458d10bff8258d10,0xf7d6558d10bff8458d10,0xdfd8758d10dfd7658d10,0xdfd74d8d10bfd82d8d10,0xdfd645cd10bfd84d8d10,0xdfd64dcd10dff645cd10,0xffb8059110dff64dcd10,0xbff8259110ff58159110,0xfbd7459110bff8359110,0xdfd7659110f7d6559110,0xdfd8759110dff7659110,0xdfe8759110bfd8759110,0xbfd82d9110bff8759110,0xbfd87d9110bfd83d9110,0xdfd765d110f7d655d110,0xdfd825d110dfe765d110,0xdfd865d110dfd835d110,0xf7d7659510dfe865d110,0xffb805d910f7f8759510,0xbff825d910ff7815d910,0xbff845d910fdf835d910,0xdff825d910dfd825d910,0xdff835d910dfd835d910,0xdff845d910dfd845d910,0xbfd849d910bfd829d910,0xff94158130ff92158130,0xff98158130ff96158130,0xff96258130ff94258130,0xff98258130ff97258130],#[0xff97458130ff96458130,0xff54148530ff98458130,0xfed6248530ff56148530,0xfdd6348530fdd4348530,0xbfd8448530dfd7448530,0xbfd8648530dfd7648530,0xfdd6350530ff56150530,0xf7d6550530fbd6450530,0xbfd8650530dfd7650530,0xbff8258530ff98058530,0xfdd6358530fdd4358530,0xbff8458530dfd7458530,0xdfd7658530f7d6558530,0xbfd82d8530dfd8758530,0xdfd74d8530fdd43d8530,0xdfd42dc530bfd84d8530,0xdfd64dc530dfd62dc530,0xfdd6350930fed6250930,0xf7d6550930fbd6450930,0xdff7650930dfd7650930,0xbfd8750930bfd8650930,0xfed7258930bff8158930,0xfdd6358930fdd4358930,0xeff6458930efd6458930,0xbff8458930dff7458930,0xdfd7658930f7d6558930,0xdfd8758930dff7658930,0xdfe8758930bfd8758930,0xbfd81d8930bff8758930,0xefd64d8930fdd43d8930,0xfdd435c930bfd84d8930,0xdfd745c930fdd635c930],#[0xdfd765c930f7d655c930,0xdfd64dc930dfe765c930,0xfdf8150d30fdd8150d30,0xfdf8250d30fdd8250d30,0xfde7650d30fdd7650d30,0xfdd8650d30fdc8650d30,0xfdf8650d30fde8650d30,0xfdd8258d30fdd8158d30,0xfdd7458d30fdd6458d30,0xbff8159130fdd8458d30,0xfdd8359130bff8259130,0xf7d6559130fbd7459130,0xdff7659130dfd7659130,0xbfd8759130dfd8759130,0xbff8759130dfe8759130,0xbfd82d9130bfd81d9130,0xbff825d130ffb805d130,0xdfd765d130f7d655d130,0xbff865d130dfe765d130,0xdff815d130dfd815d130,0xdfd865d130dfc865d130,0xdff865d130dfe865d130,0xf7f8759530f7f8459530,0xdfd825d930dfd815d930,0xbfd829d930dfd845d930,0xff98048560bfd849d930,0xff56148560ff54148560,0xefd6348560ff57148560,0xdff7348560eff6348560,0xbff8348560bfd8348560,0xf7f8548560f7d6548560,0xbff8648560bfd8648560],#[0xbfd8748560dfd8748560,0xbff8748560dfe8748560,0xff5714c560ff5614c560,0xfdd634c560dff724c560,0xeff644c560efd644c560,0xbfd844c560dff744c560,0xbfd864c560f7d654c560,0xff56150560bfd874c560,0xdff7250560ff57150560,0xefd6350560fbd4350560,0xdff7350560eff6350560,0xf7d6550560fbd6450560,0xbfd8750560bfd8650560,0xbff8258560dff7258560,0xdff7358560efd6358560,0xefd6458560bff8358560,0xbff8458560dff7458560,0xdfd725c560ffb805c560,0xbff825c560dff725c560,0xeff635c560efd635c560,0xdff735c560dfd735c560,0xfdf835c560fdc835c560,0xefd645c560bff835c560,0xdfd745c560eff645c560,0xbff845c560dff745c560,0xbfd82dc560f7d655c560,0xdfd43dc560dfd82dc560,0xbff8150d60ff98050d60,0xfdd7350d60fdd6350d60,0xefd8650d60f7d6550d60,0xefe8650d60bfd8650d60,0xdfd8750d60bff8650d60],#[0xdfe8750d60bfd8750d60,0xefd6458d60bff8750d60,0xefd8258d60efd8158d60,0xefd8458d60efd7458d60,0xbfd81dcd60dfd745cd60,0xdfd81dcd60bfd82dcd60,0xf7d8159560dfd82dcd60,0xf7d8359560f7f8159560,0xff54148760f7f8359560,0xdfd7348760efd6348760,0xbff8348760bfd8348760,0xdfd8748760f7f8548760,0xefd644c760dfd724c760,0xbfd844c760dfd744c760,0xfbd4350760dfd7250760,0xdfd7350760efd6350760,0xdfd435c760dfd825c760,0xffb8050f60dfd845c760,0xefd8650f60bff8150f60,0xefd8258f60dfd8750f60,0xdfd825cf60efd8458f60,0xff5615c121dfd845cf60,0xdfe765c121dfd765c121,0xff56350521bff865c121,0xff58058521ff76350521,0xff54358521ff78058521,0xff58358521ff56358521,0xff56458521ff78358521,0xff78458521ff58458521,0xfdd6350d21bff8050d21,0xbfd8650d21dfd7650d21,0xdfd8750d21bff8650d21],#[0xff78158d21bff8058d21,0xdfd7458d21fed8258d21,0xdfd7658d21bff8458d21,0xbfd80d8d21dfd8758d21,0xbfd84d8d21dfd74d8d21,0xff7815d921bff805d921,0xdff805d921dfd805d921,0xdff835d921dfd835d921,0xff58058531bfd809d921,0xff56258531ff54258531,0xff56458531ff58258531,0xfdd6350931ff58458531,0xbff8058931dfd7650931,0xefd6458931fdd6358931,0xdfd7458931eff6458931,0xdfd7658931bff8458931,0xbfd80d8931dfd8758931,0xdfd74d8931efd64d8931,0xfdd8058d31bfd84d8931,0xfdd6458d31fdd8258d31,0xbff8059131fdd8458d31,0xf7d6559131bff8259131,0xdfd8759131dfd7659131,0xbfd82d9131bfd80d9131,0xdfd825d131dfd805d131,0xdfe865d131dfd865d131,0xdfd825d931dfd805d931,0xff58058541dfd845d931,0xff53258541ff78058541,0xff58258541ff56258541,0xff56358541ff78258541,0xff78358541ff58358541],#[0xdfd764c941fdd634c941,0xff58158941bff8058941,0xbff8358941fbd4358941,0xdfd7658941fbd6458941,0xbfd80d8941dfd8758941,0xbfd83d8941fbd43d8941,0xfbd8250d41fbd8050d41,0xfbe8650d41fbd8650d41,0xbff8258d41bff8058d41,0xfbd8458d41fbd6458d41,0xdfd7658d41f7d6558d41,0xbfd80d8d41dfd8758d41,0xfbd8059141bfd82d8d41,0xfbd8259141fbf8059141,0xfbd8359141fbf8259141,0xdfd805d941fbf8359141,0xdfd825d941dff805d941,0xdfd835d941dff825d941,0xff7815c161dff835d941,0xdff725c161dfd725c161,0xefd635c161bff825c161,0xdfd735c161eff635c161,0xfdc835c161dff735c161,0xbff835c161fdf835c161,0xdff745c161dfd745c161,0xf7d655c161bff845c161,0xbfd82dc161dfd72dc161,0xbfd84dc161dfd74dc161,0xdfd82dc161dfd62dc161,0xdfd64dc161dfd43dc161,0xefd6358961dfd84dc161,0xbff8358961dff7358961],#[0xff7815c961bff805c961,0xeff635c961efd635c961,0xdff735c961dfd735c961,0xdfd745c961bff835c961,0xbff845c961dff745c961,0xf7f855c961f7d655c961,0xdfd74dc961bfd80dc961,0xdfd80dc961bfd84dc961,0xdfd64dc961dfd43dc961,0xbff8050d61dfd84dc961,0xbff8250d61ff58150d61,0xfdf7350d61fdd6350d61,0xfbd7450d61fbd6450d61,0xbfd8650d61f7d6550d61,0xdfd8750d61bff8650d61,0xdfe8750d61bfd8750d61,0xefd6458d61bff8750d61,0xefd8258d61efd8058d61,0xefd8458d61efd7458d61,0xdfd745cd61efd74d8d61,0xbfd82dcd61bfd80dcd61,0xbfd84dcd61dfd74dcd61,0xdfd82dcd61dfd80dcd61,0xdfd84dcd61dfd64dcd61,0xbff8259161bff8059161,0xbff805d161bff8359161,0xbff825d161ff7815d161,0xf7d655d161bff835d161,0xbfd82dd161bfd80dd161,0xdfd82dd161dfd80dd161,0xdfd435c361dfd825c361,0xdfd435cb61dfd805cb61],#[0xbff8050f61dfd835cb61,0xdfd8750f61bff8250f61,0xefd8458f61efd8258f61,0xdfd845cf61dfd825cf61,0xdfd715c143dfd835d361,0xbff815c143dff715c143,0xf7d655c143fdd635c143,0xdfd765c143dfc765c143,0xdff765c143dfe765c143,0xfdd63dc143bff865c143,0xdfd76dc143f7d65dc143,0xbfd86dc143dfe76dc143,0xdfe86dc143dfd86dc143,0xfdd635c543dfd725c543,0xf7d655c543fbd645c543,0xdfe765c543dfd765c543,0xfdd63dc543bfd80dc543,0xf7d65dc543fbd64dc543,0xdfe76dc543dfd76dc543,0xdfd80dc543bfd86dc543,0xdfe86dc543dfd86dc543,0xfdf8058d43fdd8058d43,0xfdf8158d43fdd8158d43,0xfdf8258d43fdd8258d43,0xf7f8059543fdf7658d43,0xf7f7659543f7d7659543,0xf7f8759543f7c8759543,0xff8805d943bfd801d943,0xbff805d943ffb805d943,0xfdf835d943bff815d943,0xdfd805d943dff765d943,0xdfd815d943dff805d943],#[0xbfd809d943dff815d943,0xbfd879d943bfd819d943,0xdfd80dd943bfd80dd943,0xdfd725c163dfd715c163,0xdfd72dc163dfd745c163,0xdfd74dc163bfd82dc163,0xdfd82dc163bfd84dc163,0xdfd84dc163dfd64dc163,0xdfd745c563dfd725c563,0xbfd82dc563dfd72dc563,0xbfd84dc563dfd74dc563,0xdfd64dc563dfd82dc563,0xbff805c963dfd84dc563,0xfdf835c963bff815c963,0xdff745c963dfd745c963,0xf7d655c963bff845c963,0xbfd84dc963dfd74dc963,0xdfd84dc963dfd64dc963,0xffb805d163ff8805d163,0xbff815d163bff805d163,0xfdf835d163bff825d163,0xeff865d163f7d655d163,0xbfd82dd163bff865d163,0xf7f8059563dfd82dd163,0xdfd815c363f7f8459563,0xdfd805c763dfd825c363,0xdfd845c763dfd825c763,0xdfd815cb63dfd805cb63,0xf7d83dc165dfd815d363,0xe700a2006f003c0000,0x1e601b301890156012c,0x31b02e802a302670222],#[0x41a03e703ab036f0345,0x52b04f804ce04890456,0x63305f705cd05910555,0x70e06e406c30699066f,0x7fb07bf0795076b074a,0x8f108c70894086a0837,0x9f009c6099c09600936,0xb010abc0a800a440a11,0xc2d0be80bbe0b700b46,0xcf60cd50cb40c780c57,0xe070dd40d8f0d5c0d29,0xef40eca0ea00e760e43,0xfe10fb70f960f630f30,0x10bc10921071103e1014,0x11c411911155112b10e6,0x12c31287124b121811f7,0x13ef13b31380132012ed,0x150914cd1491145e1422,0x161a15e715bd15661533,0x173d171316e0169b165f,0x187b182417d617911767,0x19b01974192618d818b7,0x1a8b1a581a2e1a1619e3,0x1bae1b7b1b481b151ae2,0x1ce31ca71c591c1d1bea,0x1e0f1dd31d7c1d491d16,0x1f051edb1eb11e871e42,0x203120071fcb1f6b1f2f,0x210c20eb20a62085205b,0x2265221721d2217b2136,0x23882343231022dd22aa,0x24512427240f23ee23bb],#[0x2547251d24e124c9248d,0x263d260a25e025b6258c,0x2733270926cd269a2670,0x27f327c02796276c2754,0x28d728a42883283e2826,0x29a929882967293d290a,0x2a8d2a5a2a392a0629d3,0x2ba72b622b142aea2ab7,0x2caf2c8e2c5b2c1f2bec,0x2d782d452d1b2d0c2ceb,0x2e532e202ded2dd52dab,0x2f912f552eec2ea72e74,0x30ab306f303c30092fc4,0x3174314a312930ff30d5,0x3258322e320431d131a7,0x3333330932d632a33270,0x344d341a33e733b43378,0x3579352b34dd34aa3480,0x36663633360035df35c7,0x37e337a7373e36f036ab,0x38d0389d38733840380d,0x39fc39ae3960392438fa,0x3b1f3ada3a953a743a2f,0x3c4b3c183be53bb23b7f,0x3d653d323cdb3ca83c75,0x3e883e3a3e103ddd3da1,0x3fc63f933f3c3f003ecd,0x40ce4092405f40233fe7,0x41a04176414c412b4101,0x429f425a420c41e241c1,0x43714347431d42f342c9,0x4431441043dd43bc4392],#[0x4539451844dc448e4452,0x4638460e45d2459f4563,0x4740471646e3469e4662,0x4851480c47d947af4785,0x4962494148fc48db4896,0x4a464a1c49e049b6498c,0x4b334b004acd4aac4a67,0x4c054be44bb14b7e4b66,0x4d0d4cd14c8c4c594c38,0x4de84dc74d944d614d37,0x4ed54ea24e784e4e4e1b,0x4f8c4f6b4f414f204ef6,0x50675046500a4fd74fa4,0x515d512150ee50bb5088,0x525c523b51e451b1517e,0x532e531652e352b0528f,0x5436540c53be53945361,0x551a54f954b454785457,0x564f55f855aa5592554d,0x5757572456fa56d9568b,0x58835847580257d857a5,0x599d596a594058f258bf,0x5ac05a845a485a0c59c7,0x5b925b685b505b2f5afc,0x5c885c3a5c075bdd5bbc,0x5d7e5d5d5d2a5d005cbb,0x5e985e655e175ded5dba,0x5fa05f6d5f285eec5ecb,0x60a860756042600f5fdc,0x61cb61a16165612960e4,0x630062c46288625561fe,0x641163d563a263666333],#[0x656a651c64c564896456,0x66846651661e65eb65b8,0x67cb6798675c671766c9,0x691b68cd686d68436819,0x6a1169de69ab6978694e,0x6b226b016ac56a806a4d,0x6c606c3f6bfa6bac6b70,0x6d956d506d026cd86ca5,0x6edc6e976e496dfb6dc8,0x6fdb6fb16f906f426f0f,0x70da70b070867038700e,0x71d971a6717371497104,0x72f372c0728d726c7227,0x741673e373a7736b732f,0x752774f474b874857449,0x763875f375d27596756c,0x772576fb76d176a77662,0x77f777d677ac778b774f,0x78c0788d786378397821,0x799b795f792c790b78e1,0x7a5b7a3a7a2279e679b3,0x7b247af17ad07aaf7a8e,0x7c237bf97bc67b937b57,0x7cf57ccb7caa7c807c56,0x7da37d827d587d2e7d0d,0x7e637e397e187ddc7dbb,0x7f2c7f0b7ee17eb77e8d,0x80077fcb7faa7f927f5f,0x80ac808b806a8049801f,0x81638139810680dc80cd,0x820881d581c681ae8184,0x82a4828c826b82418232],#[0x836d8343832282f882ce,0x840083df83c783af838e,0x84ae849f847e844b8421,0x85538520851a851484e1,0x85f885ce85a48595857d,0x869d867c8664863a8619,0x878a8760872486f186c7,0x8880883b881a87f087b4,0x8949891f890788d488b3,0x89f789cd89ac898b896a,0x8a8a8a728a3f8a278a0f,0x8b148afc8ae48acc8aa2,0x8bdd8bb38b808b5f8b3e,0x8caf8c8e8c648c438c07,0x8d5d8d3c8d128ce88cd0,0x8df08dd88dc08d9f8d7e,0x8e7a8e598e388e208e08,0x8f4c8f2b8ef88ec58e9b,0x8fd68fc78fb88fa08f6d,0x907b905a903090188ff7,0x91329123910b90e190a5,0x91c5919b917a91629141,0x92739249921691f591e6,0x930692f792df92be929d,0x93ab938a936093489327,0x942c941493fc93e493cc,0x94bf9495947494539444,0x95499531951094f894e9,0x960995f195be95949573,0x969c967b9663964b962a,0x972f971796f696d596b4,0x97d497c5979b977a9759],#[0x9882984f982e980d97f5,0x98e898e298ca98a9989a,0x996099489939990f98ee,0x99fc99e499c399a29981,0x9aa19a899a569a3e9a26,0x9b589b379afb9ada9ac2,0x9be29bc19ba09b889b70,0x9c7e9c669c4e9c249c03,0x9ced9cde9ccf9cae9c96,0x9d419d299d119d029cfc,0x9dd49db39d9b9d719d59,0x9e9d9e859e499e319e07,0x9f429f189f009edf9eb5,0x9fde9fab9f9c9f8d9f6c,0xa095a074a04aa020a008,0xa167a146a125a0f2a0c8,0xa21ea206a1d3a1a0a188,0xa2d5a2aba28aa257a22d,0xa38ca362a341a320a2ff,0xa428a410a3e6a3c5a3a4,0xa4cda4a3a48ba473a452,0xa569a548a527a506a4ee,0xa632a611a5f0a5bda58a,0xa6f2a6d1a6a7a674a653,0xa7c4a791a75ea73da71c,0xa88da86ca842a821a7ee,0xa956a93ea90ba8d8a8ae,0xaa1fa9f5a9c2a998a96e,0xaac4aab5aa9daa73aa49,0xab2aab12aafaaaf4aadc,0xababab93ab69ab51ab39,0xac6bac41ac20ac08abd5],#[0xad2bad13ace9acbfac95,0xadfdadd3adb2ad88ad55,0xaea2ae8aae57ae36ae1e,0xaf47af1daef3aedbaecc,0xb007afe6afb3af80af68,0xb0beb08bb061b040b01f,0xb1b4b18ab160b124b0f1,0xb262b24ab220b1ffb1e7,0xb2feb2cbb2b3b29bb27a,0xb3c7b38bb361b340b31f,0xb46cb44bb421b400b3e8,0xb535b50bb4cfb4aeb484,0xb5f5b5d4b5aab577b55f,0xb67fb667b658b62eb616,0xb71bb6fab6d9b6b8b6a0,0xb7c0b79fb77eb754b73c,0xb853b83bb81ab7f9b7e1,0xb901b8d7b8b6b89eb87d,0xb9afb997b976b94cb92b,0xba81ba45ba12b9f1b9d0,0xbb53bb29baf6bac3baa2,0xbbefbbcebbb6bb95bb7d,0xbc94bc6abc49bc31bc07,0xbd15bcfdbce5bccdbcb5,0xbd9fbd7ebd66bd4ebd3f,0xbe4dbe23bdf9bde1bdb7,0xbef2bedabeb9be8fbe65,0xbf7cbf5bbf43bf2bbf13,0xc021c009bfd6bfb5bf9d,0xc0d8c0aec096c063c04b,0xc186c16ec144c11ac0f0,0xc246c21cc1e9c1d1c1b0],#[0xc2f4c2dcc2bbc29ac267,0xc3bdc39cc384c35ac330,0xc462c44ac429c3ffc3e7,0xc4fec4d4c4bcc4a4c48c,0xc5b5c59dc57cc55bc528,0xc648c630c5fdc5e5c5cd,0xc6e4c6c3c6abc68ac67b,0xc777c756c735c714c6fc,0xc849c816c7f5c7cbc7aa,0xc8cac8c4c8a3c88bc873,0xc966c945c924c90cc8e2,0xca14c9eac9c9c9b1c987,0xcac2ca98ca6eca56ca35,0xcb55cb3dcb1ccb04cada,0xcbf1cbd0cba6cb85cb6d,0xcc84cc6ccc42cc2acc12,0xcd3bcd11ccf0cccfccae,0xcde9cdbfcd9ecd7dcd5c,0xce97ce6dce43ce2bce13,0xcf57cf36cf15cefdcec1,0xd005cfe4cfc3cfa2cf81,0xd0aad092d071d050d02f,0xd14fd125d0fbd0dad0c2,0xd1e2d1c1d1a0d188d170,0xd290d26fd245d224d203,0xd33ed314d2f3d2d2d2ba,0xd3f5d3d4d3b3d389d35f,0xd4acd479d461d449d416,0xd563d527d506d4e5d4c4,0xd5edd5c3d5b4d5a5d58d,0xd677d65fd647d626d60e,0xd725d70dd6e3d6b9d698],#[0xd7dcd7bbd79ad779d761,0xd88ad869d851d81ed7fd,0xd926d905d8edd8ccd8ab,0xd9c2d9a1d977d956d93e,0xda82da4fda37da16d9f5,0xdb1edb06dadcdabbdaa3,0xdbe7dbbddb93db72db48,0xdcb9dc98dc65dc3bdc11,0xc0100ac6dd37dd16dce3,0x8ac8f1c430bc517c0439,0xe21c01e87820ae04262,0xc30e700643e0b0347e2f,0x5140fc1178ac48081f8b,0x6802f1589c1a260f041,0xf04131a8fc1000b8542f,0x5e270707821e8fc10ae0,0x1f83830ae082630218fc,0xc503f1787c119f00123d,0x7e27045e201c67c5e08a,0xf510343093822b17880,0xb83400f0683630900fc1,0x9c0184a07e08bc5628d,0x7d0c6415168fc3e1617,0x30f80e08568811078e17,0x81450e0ac50a8442e0f1,0x7c0080dc0080805e204b,0x97008a1c158c24095168,0x8bc56307380201588290,0x84c170286344a20c080,0x1c158812a1f003820902,0x5e00704e022c381f1780,0xc43c3817018a1c18494],#[0xe09456047056209b801c,0x8a14a27030430c849c00,0x2288c33c561f002030c8,0x1f00208b104745e00411,0x70064251603c00811c51,0x41a61e082007e00e101a,0xc3e060866188f801c102,0xc108fc01907041191420,0x80a07e0070311f008e1,0x620c4e0608611d1f80c4,0x723f002034c131461191,0x168e230805b81826291c,0x18a1c102c10c13178007,0x600a28b01c111c811f0,0xc08687e0714382b10471,0x7801c158825086138bc0,0x5a84c08bc6e00705e1f1,0x1811787c00e0bc308700,0x2f158a10e0317022b178,0xc408181170a858830302,0x70511f142084c0f02863,0x1aa1f030230678b43e00,0xc1021c015e045e28978a,0x10600be0070413717801,0xc2181e04246e2b02382b,0x5e2f1467c004e0451988,0x82700382f0c2410c0f00,0x38438181058a3005f003,0x607810b1620c0c08bc41,0x178113810b0e062308,0xfc01d8a10e00cc413f,0x31270038206824c3c084],#[0xe0bc51230c21c0c08cc,0x38bc023870523f1467c0,0x8fc062040503f0038189,0x637144910e0313023092,0x2f00382043022d03f001,0x91ca810418bc0c08a246,0x1244389c3147141ec0c0,0x2f0056351f8bc0480ac5,0x8e25c08bc5628a438070,0x35141143c101409c018,0x2d0f8182238c04c16078,0x89c51250f8181238c232,0x21ea191c362e045e4715,0x181702470260b8143270,0xe0456287a861b8808241,0x1816001c5e2b1f800702,0x3c4a2181600bc56344a2,0x8b45040140981a1e0b80,0x807604705e201f801c17,0x87e007060201687c00e0,0x4206044e1d1f8145480f,0x709180585a83c0f00174,0x30e8602d045140e03e00,0x1c38181c0b82c0f0062,0x6320811f8181c15108e0,0xd8cc64080280c39c0206,0x870501f170581e009861,0x9c5e011c38288c8bc023,0x50f11c351c112147084,0x7c170288489047c02387,0x571c1448230280f024,0x450801c0bc0158a0782b],#[0x63c4056281c07c0a20b,0x158e0501f0021441a0ac,0x41607c08c81c27028b82,0xd01e0b0204e01016e00b,0x200982c0f006a30d28a2,0x30247144745e06088e28,0x9c086e8a470d0a24a2f0,0x904603238130581e0514,0x5a28e40e04e00b45e30,0x16001e082f1c0e036270,0x17880401f005a245a218,0xe0807604705e27000e1c,0x3d400d60436300e8bc00,0x42a0d0981a011f045240,0x10a8323d013830904690,0x361a14081e0d86850202,0x1c1a0645e0070482078,0x1f0f0581a3f1781101f8,0x31c6810600c840870066,0x18848400a04c160780c,0xc01c6632887178781c17,0xf0188471787106260705,0x3c0628e10a3f178782c0,0x3917801c142004e1e0b0,0x4405e2a088fc00e0a812,0x20501f0038387836470d,0x28200ac3e0070523e0b0,0x20184320c0a030e7005a,0xa0cc340070642308641,0x80fc0190dc31188780c5,0x6434628c141a05c5e1f0,0xe381f00c5190814c0610],#[0x28c841085829c062e100,0xac4143000e3211001c6,0xb87c2d0c271c178bc04a,0x321987041850f804b0e0,0x1120c2423e16382b1780,0x8f00470e080501e13818,0x3c7040e0c821311c3818,0xc85c28748f1c130a2b2,0xe05e00ac52281407c0a1,0x701f0029421e8432080,0xa10c85828c85618c18a,0x148e25c2e0456281407c,0x28780190984016078035,0x985158c83a180464181,0xa0301700642e16861b19,0x1c190631a1f018a1c140,0xd1908c503f02861c1686,0x100a03e0070642c16381,0x88a14e06048180538031,0x26004f03451e082761e0,0xc90414c0f028a3c53878,0x70230878745e00705e18,0x10d170228c84f04e051,0xa6040e301066320c29c,0x20c8162870641b178016,0xc80602e00a2880b0064,0x1464200b09c0c08d451a,0x68a470d8a01190404c05,0x3818140602e00c85c087,0x438582831e00c05e00c4,0xa0b0380e8b84c0f018,0x68a01c1145c240e05816],#[0x148a03016068b84e00d1,0x606c08e0c87038728bc0,0x50280c39c0190a280451,0xa011d3832150682a00c8,0x408850e86c50202107c5,0x7c5e00983822143a1b1,0xc8519f1780321380340e,0x50170064201406c2e00,0x3e00c841a05385c0190a,0xe0c8240f008e1c1005c,0x70642f143a1b23c505,0x80501f003829140a03e,0xb84a1d0b02380d8bc00e,0x450e8434e00c860461f0,0x700682f006632c092450,0xa87e00d3024b168803a1,0x81e00cc4a280e85c0190,0x2c090341210b80321446,0xb0241004785c260c6d4,0xc0a111106261f8bc3e05,0xd0864108c25810281187,0x1407c0a10c85a1310461,0x284321c0803e05086828,0x1195170238360701600d,0x1f8145a2604843f0f802,0x118f0046302c683210a,0x7004630200e050200c04,0xb8718f0060251689c3e1,0x42e00d0519e1403c0190,0x3190a802040464209889,0x100fc01a0c8403805803,0x4e2362e046628078032],#[0xc081406c2e05108a270,0x48058102b0f814420461,0x868381007c2e00d05118,0x7408d830bc0e02c0a270,0x1f8a24426078143438e3,0x30256170808a1d0b0387,0x894480802812874243f0,0x50e49144981e021c922,0xc5136078087248a260a6,0x4e021c96201407c0c08c,0x4392c51385b0287258a2,0x74243f0302489f03c0,0x561e078033144e24a281,0x120dc01209b02c4a10c0,0xf8181198a0501b138181,0x287230145a261c46280,0xa2a1c71308787c00a517,0x702870d8bc31320b8181,0x91389a8b4443e046a287,0x9c4d45a200c0487e0604,0x702260d0e31e06046028,0x66301406c2c0f004c331,0xe06046628200ac3c0f00,0x62510a39185c2a198a03,0x822f158941e008c5e2b1,0xb44e00bc4e042c561f02,0x27e00bc3e00c0162b104,0x813f00882f104bc01786,0x1c49c50911204c1e060c,0x86627058b44817003447,0x56211f8a331588c5e006,0xe27178007158824e291c],#[0x2b1380071787c0123105,0x7158bc0220bc3e00918a,0x158747170a83127045e4,0x28f41a2e0f04131b8031,0x6188c05c07a2807802b2,0xe00ac30381403c015884,0x1e0826371780071589c5,0x660500f00562d1e8b41c,0xe2b101005c1e0b803218,0x47184a45238ac4127148,0x807802b1e8b41c1e0827,0x3c003d105e2894484702,0xc1178ac7e0006882f118,0x501822e1508251211e81,0x1e802e150ac1170a98e2,0x83c131d8215a004c7e0b,0x71f078263f042b40098f,0x94561e0f04c10a90026c,0x19028130583e03047178,0x4e0017822b1035c01a86,0x410bc8e2b1382c0178ac,0x78ac4c1e0803c0178ac6,0xf00663b0780330d83c01,0xa24e00243e2f0c05c103,0xc1158cc5058c00fc0048,0xb0b098200f006a281f8b,0x198a26a1f008e8914662,0x48bc0048c830280687c0,0x8a26238ac3628c00fc00,0x300f007c20c3800705,0x26086bc01a0d84c10cc6,0x11d12251409c0198808c],#[0xc050280c03c0198a26e0,0xc518f0060181c06c1e00,0xb03c0456281c03c0180a,0x158cc401807803011810,0x98603e2b078033150a81,0xcc30280456331065c01,0x216180c03c01989c100,0x42c4e002c5e00bc260f,0x8f0b188e33e031216289,0x61f008e0b0c481ee0024,0x289389c1238bc505f006,0xf02868b146230e022c56,0x604c10070bc0128c471a,0x27e00308e8b144847178,0x7e050c913d0f8047458a,0x62189c498502608024,0xc561e0c4c30e042c505f,0x16289107c005d1056042,0x32178030084c30a2702,0x25138047458b8501e0b8,0xe0b8144204fc023a2c41,0x35058d0413890060123,0xc61391c5e1b13810b0f8,0x4e03047138908e84408b,0x146a0b1a060b01e0b0bc,0xb83c0620e3ce0010022f,0x818220163308178501e0,0xc15049883130fc5e1d07,0x86631210e24a2d0e88c0,0x3c17028240d80f45a191,0x1381411986240c81408c,0x407c0a08cc5a0f018824],#[0x405b140803c170282401,0xe00d4482c0c6d41198a2,0x44807c0d045e2b1c4882,0x36321c48c0e08bc56309,0x17890562b030fc10f50c,0xa0460e0b8143200fc1,0x22f140a01158cc41204,0x43f045624178824e0010,0x1514643f0c43c019d170,0x4941a28ac62270e83c0c,0x381003c018890643e08,0xc45a2d100601e00906,0x8cc2197006618170401e,0xcb8033128b41198ac4a0,0x6822b198807e00cc3038,0x8144200f45e0890562d1,0xe00ac512043040501b07,0x78200f028838900a01,0x8034160bc1120ac40589,0x22f184e451986351220b,0x2512822f144e2403d128,0xf028a401e82331788871,0x801178a1012010078260,0x18100601e00cc5e00900,0xd003c1a0d8d86808cc5e,0xa9014306801e0d8687e0,0x82625046618cb05c01a0,0xb1007c0c10d05e008c4d,0xb8035158b82e1f00642,0x466200781821a8a0460e,0x4a1c70231705c0e089,0x30545438c2610f0e8bc],#[0x2741f030544438dc3137,0x5c121c3a2d068a871588,0x140687a2007818226834,0x8600a1f8182188a27135,0x2e00c8601f1704c1e009,0x140782e00c8504015878,0xb80341983c0e26086a2b,0x41af03043414700461e0,0x98f0d6087837070d0cc,0x28230170507608442b40,0x3e031c4385a08c0701f0,0x101103813005185a0922,0x8410e140602e0504863e,0x81c06c1c2e138142218f,0x1684281c03c0188ac510,0x85126138142144821e06,0x1e050876001e0385158a,0x983c0c29021c2e10060,0x4261f030a389b8616821,0xd090b04e011c60a83208,0x148e42158633e00c8561,0xc0180826e1b00514209e,0x7a0144718f0060209b87,0x27130210682c2e11024,0x28230883417068185239,0x8743628110a810e86c50,0x1c602b0463c0238c0540,0xc10e91c3621178231e01,0x180a271361709c0238d,0xf8585e061070091c63c,0x21421086bc01a0cc1a3f,0x4e1f0b80c12062c01806],#[0x98385c270061a0cb0b8,0x47c261787c2e03048e1f,0x8870b840180780c21c43,0x1085c023e1471ab00681,0x4e0e143a470d8a21e1a,0x7c280709c02063c0238c,0x98384e061471080c044,0xc50180803c0180a21018,0x30170282400f8bc0a08c,0x98bc0a090260501708c,0x93e2d046638984384018,0x81407c0a10c850340d80,0x78142204dc002804562,0x5190ac31308708c5018,0x2a1f00642f16861b1909,0xe050c8028045633100a0,0x45632104226c200802c5,0x834138a00158c840741,0xc3f0f85c0a2e1071a899,0x2f006428c44c871808c1,0x900300f028a33140602a,0x438284d840100587c0a2,0x406c30c5160903600cc6,0xd0501b0b81841a0a1d1,0x584e1f0046330c0584e0,0x301406c1c27004833140,0x7004830158601c270048,0x4c1c27006a2b140601c2,0x84128cc200f030835140,0x30781841a8ac50170383,0xd05043086bc0c20d0601,0x110ad001e38098784e00],#[0xf183c1b0d0d84c241d82,0x7436280d89410a888220,0x840be005045a08743638,0x40784582151c2a13088d,0x1408150883c44205f014,0x80943c10c46020742a1b,0x20848130034321204120,0x8c42184040a048521848,0xc341132082300201a0c4,0x8205020c01588141584,0xa04181040d8a4541052,0x1b0c204c8388c30841c3,0x6424c0238405c14044a,0xc461094250762b0f043,0x204718210723e08602b,0x2230c2832084d8280f0,0x2d0f8027c11148e2e0a,0x16288c30b3146818582,0xd040518d005e10158a,0x12034060040343212034,0x201a1603400d0418a2a,0x202842800b168901a030,0xa0300201a1046c4a010c,0x2207801a0c4a81e00684,0x15868115840961b3208,0x8206c404b15030411801,0x18405e130d030b0d8010,0x6824c0085146600405e,0x21050f088105c1430f,0x820c0a28823620428a23,0x870117882b61c0420207,0x4c0238405016044a1841],#[0x24084a1a61b030228682,0x1e00408e331602100d86,0xc0c0848202466109a058,0x1840162d0c4ec50806c4,0x41582c54089031382f02,0x23a4014431520c58850c,0x18c42018e45b43050887,0xf0606100a8702808284a,0xa183040e0468680060a2,0x1a12870206084c042044,0xf2008041a84020650c20,0xd094462e082425105c0,0xac4a206824100f02c0,0x2104a100c202b12861c4,0x178945a186a06140d8a1,0x28950b81080825080bc3,0x84108030c8f82c0c404a,0x200a1108215088016860,0x801587050001283c8a44,0x6080540158428e201e80,0xe10100f40178b4462822,0x4411862762840303d005,0x30931420f502862d1048,0x6244a20400d091288068,0xd01e80c0a18ac4a011c8,0x8440c81e86400784860,0x6860990e002610268180,0x1ce00ac440c018013038,0x408700343843802b0c52,0x680ec56270050901d8ac,0x80e10e006850d01f8018,0x61a03b0020209c20104],#[0x428a1b0c20300c160918,0x3054588090422608343a,0x84060151420160842141,0x84c1c08602d09a00382,0x689821303c8010104c1c,0x7e051041344021304021,0x8209420184d001c0c204,0x23142020780e04a00b45,0x3003830702b001388278,0x1c4081104e186c2a0780,0xc16191704810c36c0083,0x4e84a28404138402c089,0x74513c4030b11c161010,0x45a1c0781450d0810028,0x9002416042220d024260,0x2208c313040212840207,0x201d882d0e2d10858624,0xb43cc0100a1ea2b005a,0xd05a18c05a1e60070517,0x30223480a1e600b43620,0x30c38087014803c21231,0x11b142a391220189046c,0x209046c30d8ac46030c4,0x8430581620c33190ec38,0x8d8a10d05ac462882411,0x70828c08386c5058608,0x40841c6420ca02240c29,0x4141486250428c383862,0x842388250941d8b84142,0x51a06210b11c2827004f,0x60a5056140c86940c2cc,0x420a206801a06802b0c5],#[0x80190c5c13200504a006,0x42059142200505618ca,0x902c28a42c20591c20a2,0xb1205031909038185011,0x126048e211604810a082,0x471247031205021203c0,0x4a18c81e800e0832a104,0x7148a81a0050415850,0xc30606270a0445824068,0x8a10504e10ac28250c28,0x3030610c20a50d021830,0x2860c0c6543060714a1c,0x8631099004020d428105,0xd022048280a0c561412,0x184858190c312821422d,0x8950a140c284512861d8,0x406320a2847c26044a2,0xc0004a45086485148743,0x824540d002820ac48140,0x148614050a4313850242,0xa44a141d0c62290c280a,0x4083b43600a44190a428,0x228118421141230084e1,0x320b030561860a188490,0x16011428330028450c28,0x6060421909f021b0d858,0x25056043048cc2820842,0x218588e140f80321386,0xe14084e13200504138cb,0xc4f14082c14086427084,0x1a0232068a081780320,0xa04141284240a058404],#[0x145a2847a28805618416,0x502058503b028a181464,0x61042d1d0c03820840f4,0x9040761b0980160a0c30,0x8840e160a08076004341,0x1d87044a04c2628a02a1,0x93143190a58ac3106632,0x7e0040322b1416182341,0x1186820590f021a10248,0xa0680c41189430808c4,0x91285400c8b0140d0038,0xf0219144640c08a8411,0x302190f02230d0623421,0x7005e060420c90302190,0x2452260480288c1e8542,0xf0244198981041fc0083,0x84090c66230860492288,0x5014089c011d090e208e,0x23a10243a14050219168,0x284e0684231302301186,0x5811186331d870319e04,0xc41182c211843024b100,0x2111202810d0842c082,0x7c011d090e208e961405,0x3022d0c17810b030b118,0x86122109030ca0446191,0xa2304912858117023219,0x4580a0430a2130342120,0x20185a84240c16811186,0x223168981219085118cc,0xc4130224618619a208f0,0x2190624118703198c820],#[0xa10a2304912858117034,0x62044c0d084198ca2181,0x8b440806240850b02c41,0x744010d0316892888110,0x51260420c5101744118,0x3c0b0e842892898111c4,0x8211046210846c3084a2,0x871442c2c088c40b21c2,0x5170214118804e008e8a,0xd06421c0890582604462,0x8221c0842143f030220,0xf8108010e0421a0c82c,0x1a040ac084330468320b,0x20d06410d04232c088c5,0x9170212118a24c084046,0xc0882362b0c311b08212,0x880f610a28020d9844d,0x813620a28022118422c,0x1032250188110f000b0d,0x840d01f0040150a26a03,0x80261c80190c0e43c006,0xb4208134212862507893,0x700e0060282684270c8,0x10d90b0030104a0b0836,0x82512301862098161110,0x42138918a18910342108,0x2286d8580038845c380,0xa109f02260c4e2610a1f,0x2612b0c313a044c18a44,0x23f0034289c4c816288,0xa08b406011c344114241,0xe8212e0040603d01801a],#[0x161a1089034182c40781,0x8108c20c460e0c581b00,0xc0238ac4178c4561b044,0x8a2f0c482b08662b084d,0xc03228bc48109c5e109d,0xc421917002b0c6281c00,0x300c8841c00643400a,0x218b82680188a86030c7,0x82130283c00ac2136003,0x2136003218b826801309,0x6190c2782400a84400ac,0x20682607a02005c36004,0x978024608827c031432,0x1034c562307802f00341,0x58633e00ac31289380c1,0x84067841380c10849c01,0x12b005618945610ac111,0x4341062705e1038209c2,0x204e084a18ce860c0c13,0x7820d0b0321e084128ac,0x25c10243180ac4a186a0,0x46090c66801586331584,0x607a00ac602217041608,0x415820c2832081382138,0x4ec1c108c5817004e209,0xf821c024413e0b1218c0,0x460181466142704270c4,0x138212878211824319a0,0x30188c301686d801c14,0x300d823318062e1506d8,0x31466320db0038286d80,0xcc60c16288331506d80c],#[0x586c1120423083130a20,0x95802f0c4a2f0856c38,0x1985c0136148e20bc481,0x591c1443118902120609,0x517842505843ca18283c,0x4717882505840b15842,0xc460b09002f085e08978,0x307042098161500602b0,0xc04cc1c1080c1884160a,0x58826c584300db030420,0x8605a27004c20981e400,0x2f81440c4d0b08602645,0x189416108c1612046010,0xc1a84056089c30b30468,0x1341d8382140ac313860,0x10d05ac46088c4138430,0x3086a2e0f30186289d82,0x123102198c182c4104ec,0x23008641106424085044,0x41046c3082544410904a,0x1984241187031904066c,0x85044120508982a08b41,0x505882c4089410c66328,0x11041d108a410c4610c1,0xe2087a2504611b1420b5,0x87411025416009041208,0x8276289030b504212891,0x842209186104a0541120,0x48c50849020b062420e0,0xac2120ac22210e048210,0x481aa1f00412b042128,0x4a1b0d50050ca0a801b1],#[0x424a00ac319d005618a8,0x78540178540178425158,0x682128910e400d0a251,0xc5e0890461060d0c520,0x589042189182109c482f,0x1408903120bc2120bc21,0xe288456240c160910862,0x20128a820f8024a2a090,0x41688240586058260848,0x860841010887c1516882,0x2104601a046614130410,0x242c108882108b44080a,0x6c5a2060a61e083608c8,0x30138798a208583820c1,0x802b1046101206051984,0xe0b12062122090312890,0x41206d80c31048c1084,0x2271048c50842448109,0x427228243138bc208115,0x20627178424058427608,0x8903138910f0b104e0b6,0x848c1084a2417862320,0x188421288d8ac31048c3,0x89456210c4a2362b0441,0x10898010e1c313094561,0x2b0c313a044c181f002b,0x984ac30c602760862a1,0x9c4cc1620827133058a2,0xa5058420418415046010,0x11e8220508f410b08300,0x4c3611058085420d168a,0xc43840c0ec0a08647208],#[0x941108607a085828208,0x1c311886821c1609410c,0x442189c4c21a08821603,0x62c31806c06388430390,0xe170908163008123008,0x1081ba130060201d8230,0xd0820241442188428c1a,0x60062460d08382508210,0xd0982189843420c3742,0x86e84c010880710d0831,0xb0a046089840a304641,0x282b0a181184260c1233,0x70208470d0ac36009841,0x9c4cc12388810a8a0262,0x986280a84c342a108e18,0x4160a01d82211450150,0x170826608b4720843419,0x6211a300313308213e,0xe118230d064c10c4e26e,0x4331830584209c4c21c2,0x8850823081608226610,0x20c42c1082c141086852,0xc181464100c641504663,0xc5a08825050983091044,0x661842710b144c20982c,0x6284c5821078016130c2,0x181582330c0742198626,0x11306250509830c9084c,0x618427109058a261416c,0x189982c50c1704130626,0x60504250530831282982,0xac508188409824521862],#[0xca1b068020984b0a0c4,0x5820338026144ec51306,0xa10d065450c4dc062861,0xc20c4e21c25158229068,0x41a09a8a189d86109c42,0xa87104d45084e26a0d14,0xc30c5825218984137028,0x8a00894608a28020b04c,0x61882411a118420558a2,0x18a2411a1182209446c5,0x88271231431289036c06,0xa240eb0184289446c560,0x2250450189c48c20c4]]
set_option maxRecDepth 16000 in
def g127H8 := limbs80 #[#[0x1020e120418e0600000,0xcd000a0c00700100040,0x818c0804283100400300,0x600045c2880c08282021,0x84000c28302042810618,0x33c082881000c0410042,0x8087802e04882080008,0x20450202080001004000,0x40008500044800,0x28a0600281180800002,0x8400007931218491060,0x500000000c001820614,0x20400007080480102040,0xc080820404311102800,0xa20400160060e0828300,0x10023000000308201000,0xc08406009831e0030500,0x40000181030404001121,0xc500078104000020208,0x60214082060c5800e001,0x64408a0a240880800a0,0x404a8702001822424281,0x1000008e0006a11970,0x8880000410a02301070e,0x18c223c1023e1000a000,0x12e1400602045010030,0x180c1811600f81623c1,0x20c3091400600020000,0x2c60136009830200101,0x8a801e2c4070a7c30d0,0x810104000010e006a512,0xd800414606006c289161],#[0x22a0490108140010e0c,0xa020428e080008f04140,0x1a0010c0630016023c38,0x60818006681880600403,0x140c33c14386060cb002,0x40021498185020870000,0x105185c0850e0461b021,0x8d061068e20303811420,0x10e10009001011f0c000,0xcb0e3001b84082860,0x8a82041c190010c49900,0x45820a004091c080830,0xc28c22381020a0c50e14,0xa001c0060448020285,0xb0000418814547021220,0x214001321c10104205,0x21c6112001bbc061479,0x800d831c040070044488,0x20c800c1810000a00800,0x44140e10003040808108,0x7001c001860608102060,0x499204184810a24,0x20c041861a001045c101,0x10188921c117800a0491,0xa042ad5c04b9a0410084,0x5c5060404181580c5082,0x30414a00825e0400004,0xa200600b000200409720,0x9204000a260d618001c,0xa60594c9343c20018242,0x4ab4a9ff6808282ee037,0x779000058cfca0de0000],#[0xf20f714714ace8,0x84ef7b3bf002b8000000,0xe3b068e0000234ad508,0x162f100004,0x23c771ce40000000000,0x837ea261000000000000,0xb9800000000000000b76,0xebc74d17e0213380003c,0x103881e587a70150383,0x32ed36f074e0000412b,0xff00000000105011,0xc7d5000011971829000,0xef80000105570530000,0x20400000000000000267,0xff9571100f66c50c14cc,0xa39f209780000083a822,0xa0def8c5000015003,0xc66cb2dfd41c282ec0,0x6a76ca5af11290434800,0x9b0c0001b436b18718d0,0x95f8de0000123e82114f,0xeb0933c218000027b1b1,0x333310c279a34442ee64,0xf031980223421858dbd,0x347bf7570332c800036,0x1c912a245f12a000,0x6081a437400000000,0x38cbd84518d1501ef0,0x4435000000002240200,0x319f0000,0xb204329a49c000000000,0xa786ba705800007144c8],#[0xf884613780000007cd43,0x2e46b3100001a48361d5,0xfb250b00007a03000007,0x3c54450e3a1bd70128c5,0x122b000000000,0xb5883280001e4ac11ac8,0x167c9c0,0x233d000000001a11c000,0x2004800000000,0x9403a60055318bbc9e40,0x412600000c82900006a0,0x3e7a82f009c40000b350,0x50026b152d901603a26,0x114498a33f084f01d766,0x8000103c,0x130000000002a6c00000,0xd680c000000000f80a82,0x28e500000a5bd483,0x12b180000e65be24d,0x5e00000000000014c620,0x16249000000002e8,0x10070137c6070a03c,0xc780000000146fbdaed8,0x32cdc93740000c01fea,0x844e096e000034670000,0x521c3a0c40001,0xe2c85a000008ba00b6c0,0x80000000000000000447,0x483a5a0ecd27bb954,0x5b71000000001b0910,0xe0000000019d948f2000,0xc6b800000000681500c8],#[0x7430bfef5b2c31d3d621,0xf800024ebfc32319d6a8,0xc89fb9cf64ff00000e14,0x6943e9508a7bb4093,0x7a000000000048666920,0x14661616f13b40000160,0x3a0020000d41d8000,0xce0000000000000c8700,0x80000016c400000000b3,0x4fe308161b7542f075b,0x126ab61da80002c034,0x7c6a1474b13cd000000,0x41ac8000180040000784,0x34880000000000006a59,0xc1323469a0400000000d,0x8827e33500000000180,0xa269000000000000,0xd2586a4e272000028470,0x958247cf2e85a7394591,0x3ac0000181ca0000491,0x1b200002c34f6a040000,0x80000010148000000014,0x800000000000039ea96d,0x2074a0000000070a6,0x6e0bc0000000000000,0xc6066000000000431900,0x79d02466ce776a4b,0xce4e2a7ba32800020fc0,0xa40000c7f50000204136,0x48ce40001000d00004d9,0x392b135c00000000b8a5,0xbdc0a73a1b8888e73047],#[0x12094d37b0888fab84a3,0x322c000049e20000,0x3e4318480000040440,0xe1aa58da38448a1aa80,0x34224c41c47ffb645210,0x2a6d2b8000000001409c,0x123c1207648ec000000,0x287ea43ba31ab0000000,0x59980001c786d2e56d91,0x6d00000cb78026c002ff,0x41e01c4cbc39d40,0x8ba16334000,0x3b00000d42950e16872e,0x41eb851b2b71e14690,0x800020653a11a030c800,0x3d5668cc8a3a4417c,0xdc8167800028e9d45260,0x20000000019fc927e7e0,0x8886000070f108cd98dd,0x14018000002db00000,0x3a15ac0000000050c780,0x2997800000000000041c,0x306800018104c723,0x8464aa03914cefbc6be0,0x1e772d32b000040a440b,0xadc8000,0xbd199980000746f00000,0xf00003c811c1aa000063,0x443b0000181c00000c3a,0xff3c4a503ddf0833cc5f,0xc0000f05b0000549960,0x2cc00004013814c60c],#[0xb108c2d4c1400000000,0xb57b11a9e7e4aeed4f30,0x3604573b49c23f689a07,0x44ce803316508c30874,0x37c403627e750a2220c2,0x5e93138c58340601ff14,0x71152933aee9d40f112d,0x28621358d186a38ae74d,0xba400b5ae700ad9a1396,0x822b0872000004c974e0,0x8f47c88000002360a212,0x1d096bcff4a2a99410d,0xe82cb8b35850fc6a820,0x43278128101cc0000000,0x261828172e400001819f,0x580bae0000c3a400002c,0x800000f8227fb588e8d8,0x1c88000000010076b0ef,0x7e000000000e1100000b,0x2d064f1,0x4d48605bb29a00000000,0x83429ae27297ad739d04,0x209dc0000c1d2a037b5,0xf33421b020685e03b000,0x6ef01739bcba071c7d1,0x12843f0109287e4813d0,0x28f3d35e34290a086ccb,0xc408c90bc117f39708ff,0x87c0976065ca7e8e05ce,0x59283c0605610bd1c342,0x38c909153283684f,0x881159421020c124d46],#[0xe7506c73dcc32071f1c8,0x40f438afa8616d836690,0x584d9e16494308ab0d8,0x3352dce1698000007efb,0x6c728000000003cdad86,0x90d6d94f5059,0x3e201500000000019a60,0xf800000000000031b44d,0xe0f6827,0x7f0000000020cec0000,0x4a3405000000003856e9,0xb80813242703381a6580,0x202b893bb30a00005542,0x2bb15408665e58d03191,0x974044d067c862c58b84,0xc29790cae8c7d0779040,0xdd7c18718373140c027f,0x7e4990c40c0000000032,0x194ba0af200002a30283,0x3de4c19a4d0ac1094183,0x8971f5ab3,0x2e5b862820c248000000,0xad8a0000000000000c0d,0x4409d12244000000003,0xd114e580380000a34920,0x609ce0663450465e6d37,0x1110000304db070301a4,0x8036e60d10cb7fc57a2,0xc0001300200000000009,0xbf002b80000515a90f4,0x384ae0000e0cb0,0x1f035611a44121622c00],#[0xc241f3865c8fc0001a0a,0xde3c2e149300a0f40000,0xed4b078760b3032cf00c,0x3cedec8e60000783a5d1,0x267c9488494971b70000,0xfc2b6790b880000e27d1,0x1a0e301c5e921c0001e0,0x1f15d00006811c000,0x7a124ae0000e30790320,0x2d98618cda0000000038,0x5b359d7eb68080000309,0x773ff8000042dd13ca,0x17077a137000028e890,0xd004f44bd000060f7400,0xc1ed45d9e7ae5095e989,0x2c08c00001a739,0x3d8bde97a4c24f075b00,0x6073ac705cd1c77e,0x4f2054df84a15384cafe,0x6481508cd0400c5464,0xd044c000000006329000,0xdd800000000855b12e7,0x8de311cde56d02701412,0xca793726b000034bcbe3,0x2b66a119d182800030af,0x193889682da000018b39,0xe800020ede127800005c,0x981951435c19a653531a,0x4710000595d70bbfc859,0x95c69603a180d6841143,0x30982322028bad859cce,0xd4cc0000e81a6ac0603e],#[0x14303aa109a43ec90b00,0x7451d03ac041842,0x872db12600003cb0e000,0x51a220035d00003304d,0x20d3e0000000000000f,0x0,0x51e0543c9a0770000,0x219e8000120dd0,0xb070e000000000000000,0xd03ee0e0d29f99f1b43f,0x19188bc0000000000002,0x240526ba325a2519bf0,0xf3247921a4fb467c8000,0x61d0000794c800000000,0x1d14011d078638ade3a,0x2cec8872600003163000,0x166ec00000000,0x1b700d3480,0x750fa000000001e4eb00,0x475300005a144000080c,0xf2a0000a1c415b50c443,0xf7e5f240ac43bc,0x2d1f00000e85ae0eb800,0x68d5c0001c6f5e161,0x1a0e778ba4000000000,0x8248d55980001e8,0x1861a5429d8a84865,0x958c5bae2f4d280313d8,0x1b8b58cbfd41c190967c,0x1a94c75a04fc8b3,0x32ee5d70000006516,0x6dc31dc1a7b1c4ccc180],#[0x400000000e1ca8000330,0x1089a0288b115c02a,0xc5f0c1c87e484b2fb190,0x83aa80000cbe5d2dd80,0xba3c9cb83479e000,0x5481820680003cc78,0x915036000019ef800000,0xf97500000c86a000001e,0x846d11400000a588e3b0,0x3803f40cd254c00000,0xc000020f8695990aa600,0xc45a3b2c3bfd4259aef,0xcb3c3cf608e223340f8b,0x6f939869e1f14f51e390,0x1211c09a00000208dc3f,0x5b733186c043407c4,0x78a7670000000026eaa0,0x32238000083dfdd90b6e,0x182c41dee17b00000000,0x7a1cfc80000000000000,0x152530000000000000f2,0x839b3411a49400000107,0xbab636251a66840d4f53,0x93807c2334899099dd8c,0x78fc489869266a31cb8b,0x428000008f3b37dc0232,0x81e2a8b0c000000000,0x4000022e2b5d9c000000,0xb3800000000191084f1,0x633024585f51a5380000,0xceaea22853dbd0,0x73e1d1429483f26eac20],#[0x540b19d58b9d06d40000,0x980000a1200dab800002,0x80000000000004117709,0xa0d00000e57251f0f120,0x5,0x9ef0cd40000a37300,0x40c5ea1bb0cc4000104d,0x516d322b162683640001,0xe123f3bb800008,0xaa116810aa0af0000000,0x4008967ae00000263,0x3f400000,0x1631aa2418000110aa00,0x182d800001192c000,0x20b54,0x9cc488000156c81aec00,0x2262d4ac0e5d60000a18,0x7f0b08ab1f6f0aca0000,0xe60000c3990406800008,0x40dad7b2f31ff5aac04,0x3406e0000e3c28000,0x5028c000086803ac70,0x2a09d9042c0001910600,0x619f59e950b26009,0x5f4a77e0000588f3ccc2,0x618011ad84,0xb0a74000021618411000,0x14700001442847b4120c,0x45b37f4d69e8a57c19af,0x656ff50a1a1d3ccd5d27,0xbb00000f2f5921d4834,0x1e90a06d72056bd439],#[0xdf167f83256621d0ae80,0x23f000000000c2aef34,0x83763703517000016569,0xfde03500000000000010,0x142eb000000000c1,0x9c00001c75100000000,0x1c206d7e02f851218abb,0x814167cd5b0bc40000a4,0xa80d12eb0000203bda12,0x679c0ff017fd9dc4041c,0x53417c0000421800002c,0x1c4ad0000516,0x36680000000000000000,0x7ef35a71e6400000000a,0x80000000029c3cd07321,0xad5a000021b0990a8cd2,0xd80919610cf3ae09050,0x4d04a44b65c78202fc88,0xb36300000d066000011e,0x90f8c12ac000023ab,0x807fd433a8eab85de0,0x80000c0f9a35f00d2c00,0x1a1ea0000f431d13c,0x34c8c00640000686f0,0xc000000003440423f000,0xa06600002051deb86114,0x86c0020000000000001,0x530a180000a3aed9d41a,0x321274c0086ad0a3a098,0x51380479184ee126e,0x4f0000000004858d4620,0xca2ed0000000000001b6],#[0x1c28c00003901501b,0xb500000c4f0e17dad148,0x2d609a257251900000c,0x7449000000000000,0x7dd000041f5000000000,0x6fe638f34210e3e26520,0x1082024934276e496183,0xc1dc203ca2b40000,0x3cf220000e1648,0x7012fb830c0001a46d00,0xc3e410c8000000001469,0xd7683ca314a61ca80001,0x62816e441c302100001c,0x80003ca5e0000b353911,0xe229ee400000000b082,0x360000000000000609bc,0x3852c0000c6,0x83b255da63039a1cc000,0x1a026000058c42,0x14c1ca382000000,0x7031b0b4954e0000,0x146000021c51c03c0000,0x2766e34845995c786552,0x248b3f40700001873d47,0x945f6b33b4cb,0xf020d98000160c400000,0x90000000000000c56e71,0xf156416880003278de37,0x8220271dab4199dc0000,0x1f093406df905fc,0x800012bf086b7711b000,0x2ac58fbd8c820000726c],#[0xc,0x7546671adb82d7288c00,0xc0a6e5d20000589fc41e,0xa2400002034a0c369b88,0x84165400000000000001,0xd302000000000e650936,0x4f39059314c485240000,0xe7630000508cc0001e,0x286f66809905350f6400,0x1306dab685600000000,0x4b2cff1aba7623dd11fa,0xc32d316440000000041,0x27ef0b4800006b4c000,0x1e860036a80002a2b8,0xb820c0000203e800000,0x24fd3f10a00002a1,0xc0180000000000000000,0x59c1000000000b,0x8066b3104502ac000000,0x46ea000063d180001c9c,0x3bd6613e00a439bc966b,0xa0000083dd86ed328f25,0x727880000000163dab3b,0xe0c8d8e5a688a5665,0x1c7e300000000000000,0x80ac8000002288000000,0x1f488046829e20f1f20f,0x18f4950240000c2472,0x4000070edf0666707d00,0x67b0f2d1993440001e52,0x2e137f28b9ea40580001,0xc383040000a20d717f24],#[0x80000000000000000594,0x3d4f4000000bd2967,0x18a94301f63c719c08b0,0x342f2a3708927f652ce7,0x2aeb82f7000010c7062f,0xa13d05c8546000029a87,0x28,0x337380002aa700000000,0x6f800003c099efce0000,0xf80000026fe1778e5570,0x230b50116000000002d0,0x68e4000020e3f17a,0x78be32b6f83ce506a0,0xe2823800000000000000,0x80a220cf800004bc3d14,0x162240000355938724,0x1400000000f90b088ec0,0x80001a980000052ab9d3,0x8f880f9fc9f465a81357,0x46140078b8da68c00005,0x949b2314f8517421f82,0x2811a2a3017b306a0000,0x65820000fa5ea9baf,0xd0925ee32a0000102d00,0x21a1c20464284a537613,0x494f38ba60000,0x100000000010d52c0c20,0x5eab5e015e3f371113cc,0x80c0000508323f21912,0xfa000000001175300003,0xc40521839182f2a4e952,0x25aa9347f457a841e483],#[0xc83612af8fec04028a51,0x9ac0f4e6fd935af55f3a,0x29bbe0430f199926069a,0x39711b0a7b30211cb65,0x34a10f90f980caaa1641,0xfd3afc86a021c60da7b4,0x8f5e0000523d5438bee5,0xfa4cb6a0000133c51236,0x9e128c00016735ea23dd,0xd04f800000001400811a,0x24b20d8b54b7d02d82d4,0xb686f00000cef40000e,0x3446000001238a96b3c4,0x1c1bc50e58000,0x6ceb80000000000000,0x9e9dd000022890000000,0x3064c0001c36,0x1979428ce20ac80420,0x3c000000000000291ac0,0x15e0000122af000055d,0xf412,0x92ad000038f1f028d0,0x3520e11b780000ac7a00,0x655821346b6900003434,0xafac0e20000f275191ed,0xf000014a8ea308bac088,0xa933c00904b6f6364196,0xf4d1f9855734f4c4078,0x852424000059aaaaaeca,0x73d63217e8e,0x95780001e4fd00000000,0x505132cc57e0000c1d48],#[0x87a9cf1cec048e8663f0,0xa309a3e691e608b24248,0x287273a000025f2a802e,0x2c00000000a147a06266,0x15397a083c0bb0000490,0x19c01eea807ce0000,0x5cee0c3b400000,0x71c548d1144b800,0x478951ba825fa834c000,0xeb8ba5e3000000001,0x1125a0d780000000000,0x210a919f58ee524a8000,0x16ceacf18f350c02e67f,0x143d8988d81f4006d74,0x400000000ca1991fcc00,0x12a6268e45fd62be71ac,0x4a849ea864a0000786e4,0x55aad800002094912598,0xa5b3921e1903e8a92409,0x12052722ab9cfc0001,0x9c00017065d8bef0c840,0x1c00000000000302,0x18ae0000145da0000,0x720d4000000000,0xe41c3000069084000000,0x48c663c6d87580001e12,0x9d18ff8d13a000032017,0x163060000604649,0x213d9d7f800006408daf,0xd000000836000004820,0x40e80000c7ad4,0x36e04000000000000000],#[0x8af00000508900000000,0x4,0x50000000000000c47500,0xe46f029db1b500000c52,0x1343102b5387500001,0x30010e00000000000000,0x80003c916864f9994160,0x553c7445e0000e250,0x43811a800000000e20a0,0x209b6e6,0x65a2000060285513c000,0x65a00006aab65087,0xc5bfd7c9e43480,0x905600002eb820000000,0x398d257800000001a1e6,0x3aa08000347354,0xd04c0e4be00005caf800,0x9a19e2d7811243acf025,0xfb00efe462be562b162a,0x1636fadd48000182c060,0xb414306e144b2c55,0x36044561e1101b069f2,0x5046e9639ca32200003b,0x8056342f90258d395b14,0x751ea10e06517f02e,0xa3d104e0859252400000,0x32fc263,0x60ea13bc0000000024a9,0xa40bc9e26,0x0,0x50165cfee005c000,0x13200000000084a635d9],#[0xc8c541538ad91d8886fe,0x24e3c000002008000010,0x96818be125096253e842,0xa3800000001070b5365d,0xbd2884996005a40000a3,0x859e000000001433cf44,0xa87a87702e4e60c70063,0x3a4da4e363bad8494474,0x49564107a39933b6b20,0x11c4443a31469d367,0x36000000000cb5dc4330,0x80b1b1bb00003c11364,0x4d920000000000000000,0x281903c000010fa98050,0x37999400000000b2ac85,0xf117405f690ec35e22af,0xf2690197400006407,0x38a7348a60,0x9cce0e2783435b1e0c00,0x8ca0b2f01c50000081f,0xed80000000154687291d,0x80000000002518000022,0xc4990000000018278c85,0xc71900000000105e7,0x2505ee1fb00006923c0,0xa19bba6700000e12d800,0xb7080001cfa780638c3d,0xcef26504a510797643e5,0xe3b9e386a0a934945e5,0xa40868c0432f9a2c818,0x10c2a56126af5813ec,0x100000d0ba0000210e00],#[0xe02b0000010dae021290,0x3fb229f00000882d8295,0x8c290b233d1eeb0827c,0x90b3ae1592314000004f,0x2edd1e6ee000018fd,0x967700000,0xae03af95332a12000000,0x75b2c0001e09,0x126c84188d5b92264a,0xf382a20000d3b9d01200,0x800006c5fe0160000007,0xa2ae,0xe1af5c554000147b20,0x161f7000000002848600,0x88dc0000526980000000,0xcbea00002,0x1014d800000000000000,0xf40ccc97a2b7423c0421,0x8c109999ecba252a1,0xea32adf0e5785ff0cc00,0x4000042392272a8b8084,0x5c380001069ad227e5c0,0xda0126d00c060a500dca,0x8409b949332279470990,0x620f8b70000242a7a77,0x9c8000062e3000000e8c,0xcd9101a2,0x6810c0001e5faa1c8000,0x8c9820ba0000,0x2443efcc47c000061680,0xb46c2d324d980d88f3e7,0x670000206f],#[0xb640000000040b8f98a8,0x1a645000048,0x72e08000000000000000,0x4fa41b6c605fc4c2b4f7,0xe041991974683ed8d67b,0xc877001f25071059a345,0xfeac69282b490af597d,0x2c71200001c1f9,0x2837ff11968b60000000,0x26572884f9b6c2b6b679,0xb69b41a61dd800030393,0xb68d98e5730000684ba2,0x140580000b39c397,0x348e1443262c2,0x3d1f2f436c000000000,0x60000a283408640001e4,0x240a482e0e97,0x4000007661f8b600000,0x8a939c0000000012d6f8,0xd0ce695580000000032f,0x61c0,0x9c4441000079c1cc8fe0,0xdcf8a000063b528d82c4,0x95ec0000d12d0acb5452,0x186da00005,0xd209c000028dcc000000,0x976833aa68a28aacb077,0x9b576d3821d400480000,0xe80000900a0000000020,0x43d5f8b8e96,0x1fcbd4840000000073ab,0xec00000000000000000b],#[0x40000fa73060c9875125,0xca3200002a4d,0x68060000794700000,0xc018b9eb0780d2741f80,0x504080000000093c7a3d,0x8fc1df187cec05a0000,0xc504f8000059fba4e374,0x864be82e6fa3c3cb3740,0x3c5ca000000005043,0x3b68eb0c3db8826316f0,0x7888ca42410e032529c1,0xa4bbd3390419e4e6244b,0x97d9325a0000128bc,0x3c000005a172b0785580,0x2076d626ad01f901,0x34180000ed8e00007121,0x8221d898c04436600005,0x8a6020000781acebd8a5,0x20dae425000000001c59,0x56e2ec800000000618dd,0xb39f080000b80a29a42c,0x92cc00003a65c0000a3c,0x80b54946000000000,0xf28461941500002c9920,0x162ac000040fa590,0x2e406000010e68000,0x1209d00000,0x49bf38766000000,0x83d48250000000000000,0x5492cc3042291580001,0xdc08520183000000e0e8,0xc1fb2a57641eb535ec8f],#[0x1038df6089dea358d025,0x86000020f8fcaaa0712d,0x60000dab11092ac55620,0x86e20000e312a58e5508,0x52400000000000000002,0x901e000052ba3c,0x3f161b3fc7dc0000000,0x90d30000000000000,0xb800009362208d0d00c0,0x1837f0000621184d,0x9f7000000000ea398000,0x107fc000061cc60d7a,0xa42e000000000000000,0xe118f565da300000,0x24000006c1188aa3436c,0x21682a6609724ab15160,0x3215000000000aa0e41a,0xc3b3,0xb63f2e089c0001d2ae0,0x6e7eb000000000000102,0x43c2811b933a90aa8083,0x614604400004902c18f9,0x500000000000006363f8,0xa2f9b98d000000000d3f,0x7935400000000,0x10736f834001ec00000,0x443d80000dbb3690b800,0x1231b00007847,0xe632060000032d260fc0,0x87258e1cf0c01e00008b,0xe2b080002a5d2e84,0x7a0000b3981a1880000],#[0x8000012635d0d561d7bc,0x12c3f60c9d15ca91,0x141d8463017ea6870000,0x92f700001705b7326e,0x9e58ea3a921f02903800,0x82ad4c11192605e8c2a,0xe6f8bb221dc00347dab0,0x157aa8f2800002a0a79,0x100b0618d000,0x7ad62e22d71047e82157,0xe0000000020d1800002,0x30c39221eb18f0000182,0x9898ca3fa57a1b620000,0x24006274932fa,0xa0000104cc0000000000,0xa0b40000798c00000111,0xcd20000000019dac0000,0x480000000000003d129c,0x2557ce59dc56f0000192,0x69c9c4f7cd7c80000,0x9ecb39c85d52ed6064d0,0xdf1fe024541c7d0bc9e4,0x61c200000ca1,0xf700001c0d1c42000000,0xe8875e1ffa878000060,0x9ab50000000006264b97,0x83388000002e51193,0x980d83ff04b8d45620,0x4ec48000000000000000,0x8cbc000000006ad8da0b,0xe81cb990fbc236500005,0x9035cda1a384c7a1244b],#[0x42c0a99898ec5007,0x98c55e9a36c390740000,0x30,0x6443ca664e262a38e30e,0x30eb8000000000000,0x621300000000000000,0x600000000599cc000000,0xc4a2000000007052b22a,0xb1800008508e427e8f0d,0x34c940000026a20,0xa3b7084d4ac7c2367000,0x633ce1c5a43b78474,0x1000000137947d163080,0x1a6a20000594e2ce,0x153c4690a237717a8000,0x291f1c34f858a00005,0x252a700000a370976300,0x149d96da08e80000743,0x37c62c1c3d5845b4d0f6,0xeaee12b194a097b1a4e8,0xe9e324ca3220dc427414,0x14cc0a968681a1a5989e,0x10d213c1f874a5850273,0x275afa6b416f8897306,0xb2057fca0afc99f98ee,0x534000000000000741c9,0x7b47080000c478a3e618,0x21fc645200001d1c4d2c,0x63dea0ddc000161ea,0xac00000000000024df20,0x24196250522c000003cf,0x5576c07560edea1a8000],#[0x411dc0000a3b400004,0x5997b28a3805100,0x865b0000000000000000,0xb6a5c390ce800000000,0x3857483fdab68800035,0x495b7cbed9087e949800,0xa780003037e25a90000,0x50b311cd0000000007,0x783eba04b00000000000,0x629a626d00006dbc80b9,0x87c440950e1d25b480be,0xf9c1fa4311c457f337e1,0xe372a8b1e2c33032651c,0x7030bc9c2d046,0x7c0000000000000069c0,0x281fa0000922d1cfc602,0x3a100000000005113,0x4835800014005f2968,0xe96550b4c0000a6d900,0x27b602fc40708000001a,0x1300000000041529070d,0xc18f440000000008d450,0x50c600f40c3ed6308f1a,0xf4e813ac4cce2dc4111,0x33326685554a6690654f,0x4a5dd73f8f987a481420,0x8a05d833b3c5b47cfc21,0x54bcfb3173b00003995a,0x59178308682653e1ef61,0xe168121c800003622f21,0x821e8000000000000,0x1b327a8b948fa800000],#[0x64e300003095400,0x5fd54031416300000000,0xc2800019082630d00004,0x7433521e9c68a000062,0xa37c9189000010c2e000,0x2ded5f6a803312ea8d95,0xe0a65ea000008c3c2,0x800030e06000022a2000,0xda95,0x150000000000001074c0,0x93d4000000000c5,0x281aa2040000,0x1c847431de0b5c,0xe800000000c4b3ca9300,0x908f000000000442f931,0xea5f800000001a69e,0x80686c50570000000000,0x53098000070,0x144c000180e8d3810000,0xcb588b4000027f64a273,0x50730000280560000d2,0x18b78f6c0000000,0x76a015b0000312d44804,0xe50f6613d6708f800016,0xe1f5c0000535e00001d7,0x40f5c0000c2ade0aa,0x871315e1242073c23cc0,0x5a2b38383284ea8a54e7,0x58e348e,0xdc18d7f315070cba5a40,0x612b8469a0000431220,0xd9d8297ed10bc65ef000],#[0x1003289f3eda1a554,0xb81500000000000000,0xe0cf6121fd89de8a6c00,0xabcfa2930175003d,0xbf800000001e372424a0,0x30000093e6005086e89a,0xf3ba80000c501c6f,0x1c6464891d1bdda848,0x6400000000d0ad19b900,0x2505c0000a527f8b9c96,0x686b0c2ee00003800,0x511f00000000000000,0x0,0x43bb2225c3d080000000,0x1f50b4b5104a19df071a,0xe2979cec040000c0c501,0xb1b6086024e438285922,0x30a0000105d2e1b5e150,0x1f098e1917112a4e206,0xb4576646a00000000000,0x916c000000000000295d,0x2461ae22860000000001,0x48b820bf80000b181d1,0x293200002c2da000,0x21a0000000064a140000,0x97449fc7f45100593dd2,0x34c0b4072a4b01007687,0x3e580002480800000000,0x19000009908000000003,0x2000000000000382a400,0xb2afa94762be,0x280e8002000005171c],#[0x804400,0x51c5f40bd81c8000,0x46333c6e06ac6dd876c9,0x31e0d7834e2a0124e153,0xd4e8084ec000069a7522,0x84b400000000fa49e14c,0xa911849ad8c0000c8413,0xa00004a12f0b80034a38,0xf248438eda054000092d,0x21a40b6000045ebc0470,0xc00000c71a139611049c,0xa06a4cba1617343b641b,0x518b64ad9e320dabb,0x802480000a3ec00000,0xf73e740154213cb6800,0x8a40000726c49188000,0x3c28035616c04cc7e6,0x447d40000c6ac000000,0xec1740c0b403b9793000,0x5868341320af426207ca,0x1272f62e6a1ccc00016]]
set_option maxRecDepth 16000 in
def g127D9 := limbs80 #[#[0xd65586bfbaa435f5d760,0xaec75f5d761cfacbb0e7,0x10ff260887f920442beb,0x7f531443fa90a21fe581,0xeb9221fd58510fea8288,0xcd10bfae6885ff72442f,0x885ff74442feba2217fd,0x2ffbb2217f5d910efaca,0xfdc930bfee2987f9604c,0xe8987dd634c3eea1a617,0x4c3beb2a617fdd130bfa,0x17fdc560bfeec985fd76,0xfee6b06ff635837eb1ac,0x63d82feb8ec1df59560b,0xa437fdc121bfae7b06fd,0x1bfae690ff561487faa0,0x7f75487beb2a437fdcd2,0xb0a637fdd921bfaec90f,0x531bfae898fdd634c7fa,0xff561506febb263df59,0xbeb2a83ef59141f7a86a,0xdc961bfee0b0dfd76507,0x6b0eff635877eb1ac37f,0x87beb2ac37fdd161bfee,0xbf58f61bfae5b0dfd70d,0xee0a1dfd74d86feb9ec3,0x550feeb1a877fdc543bf,0xc77fdd943bfaeca1f7d6,0xbfee4b1dff7158effb82,0xd70d8fbeb2ac77fdd163,0xa6c77f5cb63bfae3b1df,0x65efee0b2f7d70596feb],#[0xf7d73597bfb8acbdf5c5,0xea1221ff4c910efee6b2,0xc910ffec4887fd62443f,0x887fd63443fea1a21ff5,0x3ffb2221ff59110ffec6,0xf9d910ffaec887fd7444,0xc2987fd414c3fe90a61f,0x4c3fea1261ffd8530ffa,0x1ff5c930ffec4987fd62,0xfae8987ff644c3feb226,0x21583ff3b261ff5d930f,0xac1ff50560ffa62b07fd,0xffee2b07fd71583feb0,0xfd73583feb1ac1ff50d6,0x98ec1ff48760ffee6b07,0x121ffa87b07fd41d83fe,0xffd63487fea1a43ff5c,0xff3b243ff5d921ffec69,0xd8931ffac498ffd424c7,0x4a0fff644c7feb2263ff,0x7ffb1283ff58941ffa6,0xff5c161ffec6a0ffd635,0xae4b0ffd62587ffb82c3,0x3587fea1ac3ffdc961ff,0xc3ffdcd61ffae6b0ffd6,0xffee8b0ffd74587feb22,0xf7050ffeb8287ff50f61,0xb287ffdc543ffae2a1ff,0x43ffceca1ffd7650ffe3,0xfff7058ffeb82c7ffdd9,0xeb92c7ffdc563ffae2b1,0xd163ffac8b1fff7258ff],#[0x1b003e0003ffba2c7ff5,0xa017a04f010603600a20,0x2c60a2025a08b01ee06,0x42a0ff03ae0de034a0c7,0x9e15a052a13904b611a0,0x21bb06a619c062217705,0x21c08321fb07a61d8073,0x7b09be264094a24108be,0xc0aea2b10a8e2980a322,0xc4e3060bda2e70b5e2c,0xd8a3550d2633c0cba321,0x63b20e8a3930e063720,0xa41710163f80f9a3d30f,0x48211c245f113e43e10a,0xe9135e4c612d24a51256,0x14f2531147650c13ea4,0x1676590160256f157e55,0x8425fd17a65da171a5b1,0xde66c197264d18de6201,0x26cd1ade6a81a5268519,0x7401cca71f1c1e6f81b9,0xaf1e567821db27591d36,0xc20327fb1fa67d41f127,0x21de868215a84320b681,0x35a8c522e68aa227288b,0x3693a24a291323f68ec2,0xa9a7266698425c295d25,0xa14281a9f5277e9d226f,0x8529bea5c293aa3f2896,0xc2b6aac72ac6aa42a52a,0x2cdeb282c6ab0b2beeae,0x7811a1ee06b6e2d52b47],#[0x4560c4e0851f1d1e1b0,0xc1cac60740c12f822b1b,0x6c11f07821d14360b04b,0xc0201c1c7f047a101c68,0x130f170070545844382,0xac70701c347c582c01c2,0xc5c01c14bc73150f0204,0x1c1f0e0700702c504c3,0xb020468a02c3c54781c,0x43c01c1448401f17110e,0x410181f170f0070507c5,0x130e07002c907c5c3c04,0x7c345c01c1458401cb7,0x2c02500ad1e0a0670bc7,0x705041047c5c4c3818,0xc5c31c84c032211f170f,0x81ccb170d0b005070107,0x1147073207c543c01c1,0xc31c81c03220120b0e07,0xf0f091612070090407c5,0x83207c345c01c1858501,0x3222701e11031604c8ac,0xf00705148481c5c3c2c0,0x481c334c04232211f170,0x1f170f09130204c88050,0x714c3c28107c0443420,0x781322416070f0b0110d,0x204cc8348440c5c3c20,0x7c081332013170d081f,0x30c1f0204cc814c5c344,0xbc507c0412f2b140b151,0xc547c0832b200f030710],#[0xf141f030714ac52f02c1,0x1f04bcac607c0c1442,0x60b0068800c12e2a111d,0x7c0c12f2b151f17120f0,0x91c1f170f04cf002474,0x42f0024707c5c3c133c0,0x24047c5c12b181cc30f0,0xc00b1b170f04cf002468,0x3070d13002c647c4c3c1,0x4bc547c4c3c1c00b18c,0x47c4c3c1c00b19011f13,0x331c13170e090700cc7,0x120b00cc804c582c143c,0xc3c107c0091c1f170f05,0xf170e0b04930110724c5,0x1cac804c3c182c045331,0xc0823224cd00da0b04bc,0xe0b00d483404c5c34107,0x307c032091817110f041,0x715130c1f0208c88c5c,0x350145c4c307c0823424,0x1c0c0a1214c70104c09,0x14707038584c1c042312,0xc1852b2013070d1f0b02,0xb06161300815c2404784,0x4c3c185c03024051f0f0,0x130f170104cc73102478,0x880184c5c3c042321c0a,0x5322008061314cf010cc,0x1cc8ac8020184c333c04,0x7c0843420ce05031610,0xf06101f0108805c3c241],#[0x3c2c107c084352093170,0x5170f081f0210d09054,0x904689131511060f14d4,0x342111c7c74de00786cd,0x600786c687870dc1151,0x4280c14415110f221d0b,0xb19121e031704746c787,0x104204bc98747c0c51c2,0x82c08143291d110f021e,0xf02051c92584441047c5,0x543c01c1d10421316090,0xc11f0d17007091a1247c,0x834347c5c01c261c1208,0x20d0f17011c707260704,0x483431047c08245812c1,0x120e091702051ca27844,0x470bc3c01c2d1d110c42,0xc160a051f0f170070716,0x1f031470ac6c3c5c0471,0x987478343c04b1c1e1d,0xc1c92160c09150d1f007,0x20530a85458343c0471,0x81432d1d0d08521e0a13,0x892585458242144784c0,0x91c1e15160908510f00c,0x120514b1247c50ac01c2,0x32249e0d0e0908511f02,0x70607834382421445c0,0x5c3c01c3218591f0d170,0x428127170f011c70507c,0x20524a231a87c5c443c0,0x14b248d150d0a160e1f0],#[0xa04c234443848387c08,0x908e151611120d0c1f01,0x238710c5c4c381c04228,0x1281e070f00d108c8744,0x807232187c3c2c045448,0x32201f15130f0a0700c8,0x110d071481c544c3c2c0,0x38142c087201f0e070b0,0xd0a07021d24a1ac5c44,0x4381c0874b246e15160d,0x9170205121c81e844483,0x21047c0412f2b1c870f0,0xc61e04c11d0700bcac91,0xc626814441c047c52b20,0x1c02f2b1e050703151ca,0x230700bd1cac5838247c,0xcaca8747828141c04c2b,0xb2096140e0a070115051,0x1624a854582814140472,0x47289e0e0a050d051f01,0xc81b834382814145c089,0x72f261d1d0e0507022ca,0x1cbc725840381c044414,0x47c0448b261112050501,0x513011e2c92683814341,0x4c38241c0287a0d0e050,0xf0104cc644248710c5c,0x8444c107c043822c1f17,0x306090f0068925248545,0x7c5c1c0433318921f171,0x8605061f0d17011208a0,0x7c544c3c182c0332090],#[0x442423170f042700cc6,0x1f011608c0702c5c3c1c,0xb1c9c9211120d0e0504,0x70114cc62487c4c3c1c0,0x1c34582c04487241f0f0,0x1e170b0e130104a21814,0x50431c041301c845851,0x1182d1f04270f00c0747,0xc51f00c0a4704c1c0423,0x8584c0250d0b04141104,0x613011c84121c147c3c2,0x18431c0301c87070f0a1,0x53170f090700c870547c,0xcc60704c3c5c041331c,0x5c3c042321f170f04270,0x9a1f170b07002870704c,0x11610c07c5c033433218,0x49c9a0d0e090a05041f0,0x6412687c3c2c1c084452,0x1f0f00cd14c8]]
set_option maxRecDepth 16000 in
def g127H9 := limbs80 #[#[0x50b8010440002810,0x10000d0040803023,0xb000020280b03403,0x9455010060140200000,0x382f058180982902020,0x34180340e0700b0501e,0x201e08c000100011000,0x1dc020003d0140515800,0x2800020300000000042,0x101400c38120000ec04,0xb0141800c7602415,0x14010d8020602507800,0xc25c362d40901c04,0x1981600445214020bc21,0xc0f0005300c190b812,0x124130900200c1a0c804,0x13ca302000000045a02e,0xa00302c001ac0200832,0x81202401050350640f,0x1c0802c0d03c0100452,0x942c0cc0203c050184c,0xa4030e0003940000003,0x680e08001048e80582f,0x8070c01a004610ac02,0x178920fc810981a00404,0x1201e034030140401c19,0x1641300c002540305c2f,0x2e000140a40461814,0x54160a8370c00a04c62,0x181a004d8034000bc07,0xd01c0340f04c1915d14,0xb601c030745c12c00],#[0x3c7b0301301c0b06805,0x4c15040010e8b908833,0x1519c0005c001a071,0x243a0002a1bc0002801,0x800493000af15c15,0x534000006710401,0x2a80101c0b0002f01044,0x24000380011816025a4,0x134d0030040d80d0a80d,0x27802088040040f31c3a,0x1a8110b01100400000a5,0xc170300a0000f0242d,0x4c60294da1005501c00,0x38562a41f00c0348802,0x18407050011340105417,0x40502806054060d1e7,0x802344070c44920c06,0x13413b6c1e0084812c06,0x4c281c02a669bb1f806,0x52c02030420000300014,0x1794b11ca60202b01401,0x8c002f02cbac4d4f403,0x204e7cc450002c12214,0xffe2b572fd080990f020,0x80e146e02453e468db40,0x7683e910be8bd3936ab2,0x60096462e54ac7986892,0xc88426d4a4c3bed4d4c4,0x9c34a65ca1d4bd8c5bb4,0x76d18300f194b0113f19,0xe8fac3d39c34c3206e18,0x27793fe4fd0247fb4ce2],#[0x255340fc4e51b483a9a4,0x9b00c84cca2432e11c54,0xd3b36008c96ad5fa9dc4,0x8832331855141e8350e8,0x27680581b58253f03813,0x8ea3619c44aa4f6aa329,0x13e4abf1fbc498702e83,0x1fa076b2cb9041f08811,0xf1734a305413d932dcf5,0xb10502544082c3f52cf1,0x43c0585ccc194ad83973,0xe4f26c000042a47496c8,0x75b223205902b93abf1c,0xa144b1430e94310000d1,0xa7090cce2d903d4add3,0x649469521f439a940b1a,0xf032de404fac40f2222a,0xe3c37992e9f2515c2f78,0xa113f7c301d0aa02c900,0x7440f063eb98b2e20522,0x3b38b1c36caa851449d9,0xa083cb906c33c771b78a,0x1e329622eab00ec3fe01,0x8791706996d30442f2cc,0x19207833a5502b51ad91,0x6a527b706ff3a800009c,0x3680196a6a640a4262f4,0xa7649131db22f5641828,0xf6000044ba1349f22aa2,0xce63960000351720bfe9,0xad222f91ecc5333c1f24,0xb051170000f27a000092],#[0x79000000000000ea6302,0x52706d2aa4824ec1b68b,0x7581de18d65a8f0515dc,0x8dd1d4d1220000a955e3,0x13fb320000330af31ef8,0x99f400dbd060c9d52423,0x75f2ec427ccc1a000084,0xab94e961e280c740f792,0x7493ab248f21c864bf52,0xc900009a3aa4d9e02d80,0xc28869a0e1633714df81,0xcdf0a99401a2865a84f2,0x2e317cb221523800001a,0x2b0000d3f8e4be60af62,0x78b495000000007248a5,0x800d2fc13032fa0000c4,0x2794e891b91509b15271,0x640000339bf430845213,0xbab429a86380ee9906c3,0x93e2f11bcd5b3c2412d3,0xa37231510b60c4615a79,0x3d0160033e163550740,0x2554c12458144b636e0c,0xdf516eb383248de8ae81,0xf4f4a3db58632234922c,0x96e1a5c00c53df102103,0xda45a1bbca4ef530ab,0x788e0177bc93000000,0xa2f1f2941f41e6f47e75,0xf9b40e0000027e00efb4,0xba712c0000d4d763af53,0x5292efa249408ae389d2],#[0x86e3124bb2a0b0b006c0,0x3140896bf38144a404e4,0x4b535f22ae14351057f3,0x9c0f642aa0f591514c,0x2ac19ed210e457306200,0x85b4fb291da10af4ff20,0x290271daf3ca31c6c3,0x73c9ef638692d1949e00,0x720000f07bc505415869,0xd4e197e467b462643c52,0x1db24f000010c00000d3,0xa70b8b43340000ab0ac5,0xa8634c327961d6094700,0x8b0000000043075c2d50,0x669368b9d022a8d37aa8,0x250000309ad94ce34138,0x97417460cb50d3e0f31b,0x6b541330ba21900bdba0,0x8c08b71ad993f1b137c0,0xc0b4a892d630e46365db,0x34af71d0082e645e32,0xf38b827f7026000000,0xf511250cec0fd10e0ab,0x220000a3a3c3c4d13851,0xb13c0000f88a511aec,0x18010eba7431a9410900,0x46bb99f3dbda88a23d5c,0x68c1c13445c2d3740ce8,0x9fd166590e4106000062,0x32aa81953852eda336a4,0xe59cc1ec17308d14d070,0xbb12606b66c1ae353733],#[0x5634fc3250000e32133,0x4de0bb0000a055401af0,0x94853958d9d1c4592f3b,0xeb000081c0348ab03bf3,0x1663e0644fc08f74d3d0,0xa5132a511c4d5a236d2,0x939393b448723f31d1a5,0x2220e9f0ccd3824a64,0x5852010000f0b1f0da00,0x6c3997bc4f93de322872,0x36cb47b4e6f33e385d51,0xffc2b328b618691f045,0x26a17fd04800e6009f40,0xf8a459f33201a6693e61,0xe102089417c0bcc07a7a,0x5ff3cd83c8f3662845fb,0xf3634372e6f16858347b,0xb6ea5fdabeb2bb601434,0x275a4d11b154ecdc0860,0x1b06390ac2b0b2ac178,0xd21a9aeb3161c5f2bf20,0xcec282c01e1512912862,0xed0532aa65e1f7a35313,0xe5511d11313c5ad2c8c0,0x65a01731924240f46ddc,0x3ca447b51ab1d29287a1,0xfb717b894e8b2834ef3a,0x1053cc5bb000e2316d3c,0xfba14861a7c0abe1a45a,0x17815f4252c4c7a0a470,0xd68023d1f4e14aaad412,0x349066e81af52f0c4983],#[0x903aff5000f1337c59e1,0xe682dac4e39119d37153,0xe1c0bd01d33172eb8ad3,0xb98129cbafdb91f2a978,0x29722cc07231d9000094,0xe13362eb2da2dd519352,0x43f1ac7518c05e000031,0x1d11076226821a921501,0x2a12bf391b35a723712,0x6ad1f89891d07522065b,0xb6281de20c301872e130,0xa7c4f7d0028a5e439272,0x7fe43a2c7fdab301fc7a,0xdf000059b42284415eb0,0xcccccb326943ddc23e82,0x4b22d08b402890,0x980d396c205c1c897d00,0x9c61ffb20bc535d12d52,0xa340ad9374a3addadb70,0x7d93d33c7d735ba31882,0x660a0e2f90044616283,0x92407203df096f13e54,0x9bdd2283032840e4f650,0x92914955265326322b62,0x731c29548cc41aebd29b,0x4293d1e81890688b6cda,0xb2c3bc90946b5338ed60,0xc7426d73b800b331dfc0,0x7bf433e8e76ae003a221,0xe7f198046f852361b269,0xf4bd1e189d0de61a290,0x81f20492f79ab4b23464],#[0x69e11e8036836f150df3,0x4c4b7422cff3f3012fc0,0xa24101e3b69bdd50c261,0x711ba0eb77d4282299c0,0x67b283119558e0cb0650,0xe3d23992cc12e7b2ee88,0xb7f94951409330fc1b41,0x35f2cdec5e3306f3a7bb,0xcb58d513f04c9d648eb8,0xef6979c18250ae88ca74,0x42a3d000092c730f8b3,0xeacbc609a523288b3975,0x4ef1a8cbb83b55a4b7c0,0x9644906300b1bc094020,0xac22e3ab5af3eac0f271,0xd277203993a031eaf4,0xd9632329a4743624c500,0x4dac9583b3c0207a47c0,0xf0ca57386ac10ca294a3,0x352a2278a9bfa2,0xc2649c3a2034d02900,0xc3906032a63c5c247d00,0xf47488c8689a5a5113,0x9a83c00b3b0000b32400,0xa5d1cbbd0e73ae4cb022,0x80ac04139118e41edfa,0xa66a110000a11ff3aae3,0x23a19f12c5821e101b93,0x9cd0b9832a1995607c0b,0x9d7a05322d4d02e26e1c,0x46248533450000a9d8c1,0xf0a5f4b6d3776d17a4],#[0xc19421842513134800,0xda51cf426f0000211b00,0x1b852081b08173e0fcb3,0xdc72700b3508b5f04a54,0x530000f3a421aff3c53b,0xd1808ee380000068e459,0x9d00000000f3bd003154,0xbd3d26a72b3fdbb2430,0x1b57c0fe026a64734c,0x81bb781c7863fb416400,0xbe9adf78970000000094,0xb7b9ffe4f100008333c1,0xe4826323b9d0a6fa43b0,0x5a328f1c2ae4ca0000bb,0x9989815b46c120c39d0a,0x11aa5c2c24b4042b0a,0xdd24fcc136c42d337800,0x54c124199d000032d46c,0xdc0000000031e4fcb233,0x28504c932dd4f084d670,0xb2187c47c363b5,0xd1d531e8e2fbd38c00,0x937601b8c49cbbfb00,0xeaa8de889e2e289e300,0x658cc2e521084ce33d62,0xe77a5b79c284758103c4,0x56537071812992e2c1f3,0x300000697c81f5000080,0x8e64e122ebea90a3ed70,0x1cb3550000c4b3a0dd72,0x82cf0e841d1f610d7d5,0xbe7a595202a47b51bf95],#[0x9e6a1644f9e154d873e2,0xcf84ee44eabb3ac51912,0x24159b37334f4b28133,0x87518f000084d2841434,0x8a797a3319023534a5c0,0x150000b93a2bceb45db3,0x5a701322f8b4e4227379,0x962d5a94df035846384,0x386994d451a0e91c0552,0x80d4ae0000644304ebc3,0xbc3527acfa54ddb48b64,0xc29015325e02a0933fd2,0xb119a7b1c3b049824b81,0x2200008116852561884c,0xb854bc550b0000ec0e70,0x6041fa647250c6a3b5b2,0xde52d3b67742cd30b91,0xd8d351450c84da342211,0x97f409e86532aae24351,0x42835e1c9a7b2f6a870a,0xb22356ca0fb0f4922521,0x3dc4b8a4c630cd527464,0x863888e25063ecc959b1,0x9e7246c3294244e37ee0,0x2f5ad3341930c5528da3,0x116212b4560000a12a10,0x1ba492bda352804650,0xe367e157345c23c600,0x1a89edec23f81ec0d501,0x24810410107213241c83,0x55f53443156476805194,0xda1b2ee28a245b000061],#[0x270123001f60e5b0d1bb,0x42a0f6438d2359c3d7ec,0x4400004003617ed487bc,0xbaa37f0000ab3394aaca,0x150000d3e2530f000011,0x49679257814734,0x2a2519690000728900,0x34a75522000000,0x53c31f22b700004c3900,0xa300007008d2b40000a4,0x2477a438c19af9,0x6077e2f60000c48400,0xd0e1e070e82211000000,0xf954f36d107d0000f2,0x846ec04554cd611500,0x68ab868cfff114b1e900,0x982b4b825d53e348d824,0x5c01691027b0dfba86d0,0x5c0000a2938b76f09122,0x88105bf3d8da8aa16b80,0x9794a994664c2e22ce54,0x4b6bada16f551421cc63,0x3fb35cd2fef8d41ab120,0x148494d503d346b261d4,0x199a93bf41eea24df2,0x1b925a8966708ccc4300,0x6bf93050ca9c46923b85,0x520640000b81704edf4,0x9acbaefc5dd357000004,0xfd321cf416000024f2c4,0x3bc3449479715c232ef1,0x2ee37b1b05127d546c14],#[0xa3331bf33568cb420071,0x2cb4e2ba53dbb949fd61,0x21d44d5bb503842838cb,0xd524c0000a18d341ddc,0x80e3d5c079418cb4b5c9,0x9b43d082543ad80000fa,0x8454000020809516ea,0x50306739f7a00b90f900,0x945b891ce384e76b2a40,0x653b5420a1000000003a,0x20231cfb88f382730242,0x727afd7266743e0000f3,0x8353fa00000000781bd3,0x6588620000c442609240,0xec0000f1530000f8cd10,0xa270820000b4d8b50ff0,0x8c052eb53123ee10c139,0x25f4311d342410562,0xd9000074c90000021b00,0xc1d76245fb,0xe4546184970000a08400,0xe40d03acdb9a0000a2,0xc90000f0072978c03c00,0x9bfc1d82a203e100008c,0x20486cf36bcbebe07eb1,0xdcb0b5f0d0e102b48374,0xdb0000e0855482309e0c,0x831dd1423713b04bb32,0x870000fb4a53980b50b1,0x544de02b1117a000073,0x99e819b411999bd31d33,0xce033b7395b410014110],#[0xc272b3f02c7227cb2661,0x951203083f7501a0612a,0x7742d91c4d6c130b0950,0x1f832ca09b11769093c8,0x67421f4f5000084fea9,0x1774e564346178b2ff15,0x75f1bd8444fc7ed2d7c3,0x4dd23062b2f271f18b4b,0x292c4155107c4ad14f31,0xbcf4dbf291a2412bd579,0xc21a19a96eab211f9ba,0x4d83dcb42e9073325583,0x2f000049413a953b1630,0x27000050d60bd802acf3,0xdef111028830b844dce1,0x90000e39f938f01eb5c,0x7b7d30f45f52af8971c3,0x21801d633cc256ba822b,0x5063b231183053e92801,0xd2b9fed009441e224a4,0x3a1037a88c420fe31010,0x2491851167c35d205d62,0xc21bcf521931efc0432c,0x6788e204703135814b94,0xc300fa44a013ffd00a52,0x3dd290a9cf28750c9bd0,0x3e920df93dab5edb7ad8,0x50ca52d0d2820a7455b0,0x6474f87156ac5513c231,0x9d42fc8c120000c179e4,0xf7929c747f401cd24232,0xf378c70000347c633a6b],#[0xc1413a234edbd413c9b2,0x3c1c45e3f2e004b297d3,0x87c8e3d439e1dcc44ca2,0xc0d11052c4183ab2f468,0x83a49d934b4339c1f3d4,0x6b58cca4e0918a5285ba,0x3d5047a37c5295b0d402,0x5f01e7917d2c484a46b4,0x2b102572070a8b3314b0,0x5b6358048913f602d8e3,0xfe32ca0000039950cf01,0xa13972250e2081b0d821,0x917b98847a0040123204,0x9800000000f30d847181,0xca501224fa9afcf1b3bc,0x705408834779fe203ae1,0xc6944e00006199a05a90,0x1d49ce3292a259f40342,0x9ffb97b3f5a3b403691b,0x374161644ab529b19c92,0xb4742f44cf53b7000044,0x6af3fcb03fb842d4c450,0xab22e0851ee31610db11,0xb092a5615d0ad6f4cc01,0x45717121cd1c4c014e43,0x33e841e5125b81]]
def g127D10 := limbs80 #[#[0x60ff583fd30ff4437d65,0xfd61ff507fd31ff487ff,0x3ff63ff58ffd43ffd87,0x359d599213a8b31d4370,0x624385047aa6728ee047,0x1c2438a080c0384000f1,0x238705161840300e10,0x4384060071c3c5890e14,0x78789062830501593162,0x30058c1c14587060091d,0xf16243820a00e1e2438,0x284803c5890e082801c7,0xe2c385060041c3c18708,0x8b0e141090038e1]]
def g127H10 := limbs80 #[#[0x600160525000b13100c,0x15420107140d00080100,0x1117f08010e190a0500,0x20a0c60000d000707,0x10004913011ea3011602,0x80f5d03440511090406,0xe680004180958b133f01,0x784408e38be3d8003833,0xf3093058646e6e835000,0x29266550f5c0002a21c3,0x70423e1d09ea6efe69b0,0x2c5083881916a0d0001a,0xe7e2a98c801994b017b,0x728a09f47c1b2a039,0x2b021c00001684e221d,0xf3c368b08d4329d0a614,0x11830c10c8a6ce6f47f7,0x8f3af28e086c922316e8,0xab65280551571674741c,0x581b9190f68e80157ccd,0xf566cb9d8d5b894e96a2,0xec39b0385e8001b3353e,0x1f83156364b0006a6a53,0x1a00044ba2a8cc8000d0,0x88eaac000000a1080030,0x91808a78420b80000007,0x7b6800346200095371af,0x86b4000000222cc26028,0x7c3359376f3d2cac8715,0x3067a42040f21c526aa,0x340001058000e7700000,0xd8400102f313711b8242],#[0x27e318590d0692724ea,0xd28ccdca726c611062dc,0xc00000000020ec37edb7,0x6c7aafaa48000000191,0x1a6f000090fcdbc3f00,0x3e1c001678f07dca80,0x492a3b2aed1140018300,0x52711606a4e053a83,0x9e8316999280004a4749,0x1404215e43628024299f,0xdc000e02bc1380612049,0x5b04c1cd2a3aa5e13820,0x97cbf148f90b994cb3e,0x432750c57d095a869005,0x7abc00000053a897452b,0x617bf4d8000af1084722,0x490a48c342444178786b,0xf243e0497945a0726785,0xb9763b20524ed315951c,0x112a7ff04e48253c28d5,0x495a0f3c5742244b4499,0x66ca26114db48000]]
def g127D11 (j : Nat) := if j=0 then 0x28818408037f else 0
def g127H11 := limbs80 #[#[0xd538793e46e00b62346,0x8018da71400149450000,0x4180000ab003c68400d4,0xce2597601]]
def g127L : Nat → Packing
  | 5 => (8,6,6,0,0,7,0,g127D5)
  | 6 => (409,5,6,0,0,12,0,g127D6)
  | 7 => (2173,4,6,0,0,16,0,g127D7)
  | 8 => (1338,3,6,0,0,16,0,g127D8)
  | 9 => (178,2,6,0,0,14,0,g127D9)
  | 10 => (13,1,6,0,0,10,0,g127D10)
  | 11 => (1,0,6,0,0,0,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 3 37 2 8 3 1 g127H6
  | 7 => lookupWord 137 1381 4 14 9 1 g127H7
  | 8 => lookupWord 703 4177 7 17 12 1 g127H8
  | 9 => lookupWord 444 1931 10 16 11 1 g127H9
  | 10 => lookupWord 62 293 8 13 8 1 g127H10
  | 11 => lookupWord 5 29 3 9 4 1 g127H11
  | _ => fun _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P5_0 : block g127 5 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B5 : block g127 5 0 8=true := g127P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_2 : block g127 6 2 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_98 : block g127 6 98 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_194 : block g127 6 194 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_290 : block g127 6 290 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_386 : block g127 6 386 23=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 409=true := (@block_merge g127 6 0 194 215 (@block_merge g127 6 0 2 192 g127P6_0 (@block_merge g127 6 2 96 96 g127P6_2 g127P6_98)) (@block_merge g127 6 194 96 119 g127P6_194 (@block_merge g127 6 290 96 23 g127P6_290 g127P6_386)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_96 : block g127 7 96 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_99 : block g127 7 99 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_195 : block g127 7 195 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_291 : block g127 7 291 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_387 : block g127 7 387 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_483 : block g127 7 483 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_579 : block g127 7 579 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_675 : block g127 7 675 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_771 : block g127 7 771 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_867 : block g127 7 867 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_963 : block g127 7 963 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1059 : block g127 7 1059 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1155 : block g127 7 1155 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1251 : block g127 7 1251 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1347 : block g127 7 1347 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1443 : block g127 7 1443 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1539 : block g127 7 1539 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1635 : block g127 7 1635 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1731 : block g127 7 1731 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1827 : block g127 7 1827 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1923 : block g127 7 1923 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_2019 : block g127 7 2019 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_2115 : block g127 7 2115 58=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 2173=true := (@block_merge g127 7 0 1059 1114 (@block_merge g127 7 0 483 576 (@block_merge g127 7 0 195 288 (@block_merge g127 7 0 96 99 g127P7_0 (@block_merge g127 7 96 3 96 g127P7_96 g127P7_99)) (@block_merge g127 7 195 96 192 g127P7_195 (@block_merge g127 7 291 96 96 g127P7_291 g127P7_387))) (@block_merge g127 7 483 288 288 (@block_merge g127 7 483 96 192 g127P7_483 (@block_merge g127 7 579 96 96 g127P7_579 g127P7_675)) (@block_merge g127 7 771 96 192 g127P7_771 (@block_merge g127 7 867 96 96 g127P7_867 g127P7_963)))) (@block_merge g127 7 1059 576 538 (@block_merge g127 7 1059 288 288 (@block_merge g127 7 1059 96 192 g127P7_1059 (@block_merge g127 7 1155 96 96 g127P7_1155 g127P7_1251)) (@block_merge g127 7 1347 96 192 g127P7_1347 (@block_merge g127 7 1443 96 96 g127P7_1443 g127P7_1539))) (@block_merge g127 7 1635 288 250 (@block_merge g127 7 1635 96 192 g127P7_1635 (@block_merge g127 7 1731 96 96 g127P7_1731 g127P7_1827)) (@block_merge g127 7 1923 96 154 g127P7_1923 (@block_merge g127 7 2019 96 58 g127P7_2019 g127P7_2115)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 23=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_23 : block g127 8 23 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_119 : block g127 8 119 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_215 : block g127 8 215 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_311 : block g127 8 311 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_407 : block g127 8 407 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_503 : block g127 8 503 75=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_578 : block g127 8 578 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_674 : block g127 8 674 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_770 : block g127 8 770 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_866 : block g127 8 866 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_962 : block g127 8 962 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_1058 : block g127 8 1058 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_1154 : block g127 8 1154 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_1250 : block g127 8 1250 88=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 1338=true := (@block_merge g127 8 0 578 760 (@block_merge g127 8 0 215 363 (@block_merge g127 8 0 23 192 g127P8_0 (@block_merge g127 8 23 96 96 g127P8_23 g127P8_119)) (@block_merge g127 8 215 192 171 (@block_merge g127 8 215 96 96 g127P8_215 g127P8_311) (@block_merge g127 8 407 96 75 g127P8_407 g127P8_503))) (@block_merge g127 8 578 384 376 (@block_merge g127 8 578 192 192 (@block_merge g127 8 578 96 96 g127P8_578 g127P8_674) (@block_merge g127 8 770 96 96 g127P8_770 g127P8_866)) (@block_merge g127 8 962 192 184 (@block_merge g127 8 962 96 96 g127P8_962 g127P8_1058) (@block_merge g127 8 1154 96 88 g127P8_1154 g127P8_1250))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 6=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_6 : block g127 9 6 86=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_92 : block g127 9 92 86=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 178=true := (@block_merge g127 9 0 6 172 g127P9_0 (@block_merge g127 9 6 86 86 g127P9_6 g127P9_92))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_1 : block g127 10 1 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 13=true := (@block_merge g127 10 0 1 12 g127P10_0 g127P10_1)
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
  · exact g127B5
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K246) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=1049651) (before_sound K246 V246) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K246 12 [(127,[]),(191,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V246 low127 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fc173192150b20f50,0xfc000003f03f03f])),(BitVec.ofNat 152 (word80 [0x850172112040120e50,0x41041041041041041041]))),((BitVec.ofNat 152 (word80 [0xc0065d6176a84a1610,0x3f000000fc0000fc0])),(BitVec.ofNat 152 (word80 [0x986592174a00a1611,0x45145145145145145145]))),((BitVec.ofNat 152 (word80 [0x315879048f057d60,0x3f000fc0000])),(BitVec.ofNat 152 (word80 [0xe215859048d057d68,0xe38e38e38e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xffda8449ba143138a0,0xfc0000fc0000000fff])),(BitVec.ofNat 152 (word80 [0x1084488a102120a2,0x8a28a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x3115a69573090090,0x3f00003f000000fff000])),(BitVec.ofNat 152 (word80 [0x101005a29132080083,0xc30c30c30c30c30c30c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e802002006c0ef,0xc000003fffffff000000])),(BitVec.ofNat 152 (word80 [4,0x10410410410410410410]))),((BitVec.ofNat 152 (word80 [0x280294c88cc8e70f,0xffffffc0000000000000])),(BitVec.ofNat 152 (word80 [0x20280004000cc0c108,0x20820820820820820820]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(1,0,222,0,10),(2,0,221,0,10),(4,0,219,0,10),(128,0,95,0,10),(8,0,215,0,9),(16,0,207,0,9),(64,0,159,0,9),(12,0,211,0,8),(0,4,139,80,7),(24,0,199,0,6),(72,0,151,0,6),(80,0,139,0,5),(80,4,139,0,5)]
def g223A : List (List Nat) := [[]]
def g223D8 := limbs80 #[#[0xfaf82551439ef825d543,0xdef825d543bef825d543,0xded73dc954bef825d153,0xfef825d543ded83dc954,0x54f1806000fef825d153,0x2e4e3cf80daac452a26d,0x7938104a4f1e7c058d5b,0x65c4673e0398cacb8d6e,0x730cb355e3939f022549,0xe9701042a525f88be7c0,0x1824a92486099b2b4e3c,0x12a492]]
def g223D9 := limbs80 #[#[0xd5450feea9a877bdc954,0xa2a77fdd543bfaeaa1fb,0x43bfee6aa7ef72552ffb,0x7fd73553feba2a7ff5d5,0xba5424cfc69288d83000,0x25248d26c65cf01fc1aa,0x4c73c0c20a2445b2c73c,0x24624acb1cf0307589ca,0xc6571cb3c0a196cb1cf0,0x9214c73c0c1740b1cf02,0xcb1cf028830a5b1cb3c0,0x50ac89c73c0c215309]]
def g223H9 := limbs80 #[#[0x610038000007000000,0x9200006300f50000,0xf000000000000000c4,0xf6]]
def g223D10 := limbs80 #[#[0x45c5c03fd54ff54ffd43,0xd524a338109b14928ce0,0x6a16519c18428]]
def g223H10 := limbs80 #[#[0xd6004974000057b2,0x9351,0x4a450000581000]]
def g223D11 (j : Nat) := if j=0 then 0xca842603ff else 0
def g223H11 (j : Nat) := if j=0 then 0x2d70 else 0
def g223L : Nat → Packing
  | 8 => (9,3,4,0,0,9,0,g223D8)
  | 9 => (11,2,4,0,0,9,0,g223D9)
  | 10 => (3,1,4,0,0,7,0,g223D10)
  | 11 => (1,0,4,0,0,0,0,g223D11)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 2 37 0 8 4 0 g223H9
  | 10 => lookupWord 2 29 0 8 4 0 g223H10
  | 11 => lookupWord 1 3 0 6 2 0 g223H11
  | _ => fun _ => none
def g223 : Forest := ⟨223,11,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_1 : block g223 8 1 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_7 : block g223 8 7 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 9=true := (@block_merge g223 8 0 1 8 g223P8_0 (@block_merge g223 8 1 6 2 g223P8_1 g223P8_7))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : block g223 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_1 : block g223 9 1 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_8 : block g223 9 8 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : block g223 9 0 11=true := (@block_merge g223 9 0 1 10 g223P9_0 (@block_merge g223 9 1 7 3 g223P9_1 g223P9_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P10_0 : block g223 10 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B10 : block g223 10 0 3=true := g223P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P11_0 : block g223 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B11 : block g223 11 0 1=true := g223P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0 = true)
  · exact (rfl : block g223 1 0 0 = true)
  · exact (rfl : block g223 2 0 0 = true)
  · exact (rfl : block g223 3 0 0 = true)
  · exact (rfl : block g223 4 0 0 = true)
  · exact (rfl : block g223 5 0 0 = true)
  · exact (rfl : block g223 6 0 0 = true)
  · exact (rfl : block g223 7 0 0 = true)
  · exact g223B8
  · exact g223B9
  · exact g223B10
  · exact g223B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 12 := lower_forest (g:=g223) (i:=0) (hints:=1075) (before_sound K127 V127) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K127 12 [(223,[]),(251,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V127 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffcaa21f992a55c000,0x4000003f00003f00003f])),(BitVec.ofNat 152 (word80 [0x29ca2207902a458000,0x45145145145145145145]))),((BitVec.ofNat 152 (word80 [0xa02ac2b05023ba13,0x40000fc0000fc003ffc0])),(BitVec.ofNat 152 (word80 [0x4ca02042b04003a202,0x41041041041041041041]))),((BitVec.ofNat 152 (word80 [0x1fcf4d6808388026b,0x3f000fc0000])),(BitVec.ofNat 152 (word80 [0x71f8f4d68080880223,0x238e38e38e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xfe400d90dea41e102e,0x8003f000fc0000000fff])),(BitVec.ofNat 152 (word80 [0xd900e8010102c,0xa28a28a28a28a28a28a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x112b6d083f8128ec,0xfc0000000000fff000])),(BitVec.ofNat 152 (word80 [0x80010b29083f00084c,0x1c71c71c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x2e542b025400c554,0xbf000000ffffff000000])),(BitVec.ofNat 152 (word80 [0x400280014004150,0x90410410410410410410]))),((BitVec.ofNat 152 (word80 [0x191c1206588680781,0x7fffffff000000000000])),(BitVec.ofNat 152 (word80 [0x10c0004100280481,0x20820820820820820820]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(4,0,235,0,10)]
def g239A : List (List Nat) := [[]]
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
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := lower_forest (g:=g239) (i:=0) (hints:=1049907) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 11 [(239,[]),(253,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff8aa21f892a57d000,0x4000003f00003f00003f])),(BitVec.ofNat 152 (word80 [0x298a2217802a478000,0x45145145145145145145]))),((BitVec.ofNat 152 (word80 [0xa02ec2a0d023ba33,0x40000fc0000fc003f000])),(BitVec.ofNat 152 (word80 [0x4ca02cc2a0c003b202,0x430c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x1fcf0d6900388024b,0x3f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x71b8f0569000880203,0x21861861861861861861]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe400d90dea41e102e,0x8003f000fc0000000fff])),(BitVec.ofNat 152 (word80 [0x400d800e8010102c,0xa28a28a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x112b6d083f8128ec,0xfc0000000000fff000])),(BitVec.ofNat 152 (word80 [0x80010329083f00086c,0x1c71c71c71c71c71c71c]))),((BitVec.ofNat 152 (word80 [0x2e542b025400c554,0xbf000000ffffff000000])),(BitVec.ofNat 152 (word80 [0x400280014004150,0x90410410410410410410]))),((BitVec.ofNat 152 (word80 [0x191c1206588680781,0x7fffffff000000000000])),(BitVec.ofNat 152 (word80 [0x10c0004100280481,0x20820820820820820820]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(4,0,243,0,10)]
def g247A : List (List Nat) := [[]]
def g247D10 (j : Nat) := if j=0 then 0xff else 0
def g247L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g247D10)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,10,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 1=true := g247P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 10 := by
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
  · exact g247B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 11 := lower_forest (g:=g247) (i:=0) (hints:=1049684) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 11 [(247,[]),(254,[48,65,82,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fc00001fc07,0xf21260612331974c84de])),(BitVec.ofNat 152 (word80 [0x244891224489122448,0x9210202023309208808e]))),((BitVec.ofNat 152 (word80 [0xfe0007f0003f8,0x438882c43a66b189c6])),(BitVec.ofNat 152 (word80 [0x142850a142850a1428,0x50408802401264208086]))),((BitVec.ofNat 152 (word80 [0x7f0003f80fe0000,0x10419c478c29217])),(BitVec.ofNat 152 (word80 [0xe1c3870e1c3870e1c,0x3000a104104438c28017]))),((BitVec.ofNat 152 (word80 [0x3f8000000000003ff,0xf01c11f81e0780fd4373])),(BitVec.ofNat 152 (word80 [0x489122448912244891,0x200001081c0500c14371]))),((BitVec.ofNat 152 (word80 [0xfc0000000000fffc00,0x601e00e007ff0267a0])),(BitVec.ofNat 152 (word80 [0x50a142850a142850a1,0x40600800c00344006720]))),((BitVec.ofNat 152 (word80 [0x3fff000000,0x3800000fff800007c28])),(BitVec.ofNat 152 (word80 [0xe1c3870e1c3870e1c3,0x82800008a7a800007c28]))),((BitVec.ofNat 152 (word80 [0xffffffffc000000000,0xc001fff00000000780c])),(BitVec.ofNat 152 (word80 [0x810204081020408102,0x40014d1000000001800]))),(0xfffe000000000038031,(BitVec.ofNat 152 (word80 [0x20408102040810204,0x9094000000000020000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(4,0,251,0,12),(32,0,223,0,12),(64,0,191,0,12),(128,0,127,0,12),(1,0,254,0,11),(2,0,253,0,11),(8,0,247,0,11),(16,0,239,0,11),(9,0,246,0,9),(10,0,245,0,9),(17,0,238,0,9),(18,0,237,0,9),(3,0,252,0,8),(24,0,231,0,8),(11,0,244,0,6),(19,0,236,0,6),(25,0,230,0,6),(26,0,229,0,6)]
def g255A : List (List Nat) := [[],[48,65,82,118]]
def g255D9 := limbs80 #[#[0x434c110fe450d414c110,0xaf768e9850d10ff4685,0x69850d10aef6929850d1,0x44135382adcae008ff6a,0xa0602c5b0cf0f83c7e2,0xa32ce0d04f87c1e3f142,0xdc5e2787c1e3f10b4805,0x3f1789e1f078fc42d214,0x23a7d3787c010f1f8885]]
def g255D10 := limbs80 #[#[0xfb28698221ff1414c110,0xdaa1a82885fd65131443,0xfb30a1a217fb9050d10f,0xeca706884ffe51834427,0xb27c22213ff93611109f,0xc2262887fe611304427f,0x22a1a21ff58350510ffa,0xc286886ff66143443feb,0x8c1a21bfd8460d10dff4,0x286886ff64d844437fb2,0xb1301c425023000ffecc,0x584a11272203d46f0b,0x9a52121f4087a4e319f3,0xb242c319f83878f8a208,0x4492d0d8c08e0e1e3e24,0x4826302c278313878f88,0x8b480c2d8c0be1e0e3e2,0xee3e22131131787838f8,0x878f8838511100fe1e00,0x83c5a6e1e0e3e20c1b83,0x7e0e1e3e20c1b87838f8,0xf1c2b87838f8a203c7a,0xf8a2c3870be0e1e3e289,0x1e0e3e28811242783878,0x3b87838f884480b094ce,0x86e1e0e3e24c2d183c40,0x1e3e20e2387838f883c3,0x87838f883c911100fe0e,0xe8b88110f199844403b,0x10]]
def g255H10 := limbs80 #[#[0x41000000,0xf40000003329000000,0x40000000020000000000]]
def g255D11 := limbs80 #[#[0x50510ff531443fe4c110,0x442ffe0d10bfd83443fd,0xffd43442ffe1110bfd84,0x50530ffd84443ff60d10,0x2e87c0f800ffd31503ff,0xb52969460c6c97b4d8ff,0x109206678b830e3c4208,0x7063c42c8199e260c38f,0x273e0c38f1082730c898,0xa243a6c18b1e11838e18,0xe21838f182f361c18f10,0xe0c7893cc30327c3831,0x7063c438918b46c54d13,0x2b0e0c78879230488cf8,0xb13061c78a42b2060bcc,0x12c4c3831e294a484]]
def g255H11 := limbs80 #[#[0x63bc0c4a48688a20600e,0x1300073c00345eea4ead,0x28a52c00e0e5000000,0x3140000289003c7d0400,0xa132f736e46800040986]]
def g255D12 := limbs80 #[#[0xffa83ff503fe987fd10,0x69c5121823889a8723c0,0x88a2049e58218e220832,0xa48608e22c8126961823,0x59]]
def g255H12 := limbs80 #[#[0x0,0x0,0x1e400000000000000,0x0,0x30000000000000000000,0x24a0000000001,0x0,0x0,0x12a0000,0x3a400000000000,0x0,0x16200000a00000000,0x0,0x0,0x0,0x126000000000000000,0x28400000000000000000,0x0,0x240000000,0x0,0x0,0x69c0000000,0x0,0x0,0x3ac0000000000,0xb880001090000,0x0,0x4a,0x4000000,0x860000000000000000]]
def g255D13 (j : Nat) := if j=0 then 0xe6290201888ff else 0
def g255H13 := limbs80 #[#[0x0,0x0,0x0,0x3c000000000004000,0xc1a80000000,0xb000000000000,0x0,0x79]]
def g255L : Nat → Packing
  | 9 => (5,4,5,0,0,9,0,g255D9)
  | 10 => (20,3,5,0,0,11,0,g255D10)
  | 11 => (12,2,5,0,0,10,0,g255D11)
  | 12 => (4,1,5,0,0,8,0,g255D12)
  | 13 => (1,0,5,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1 31 0 8 3 1 g255H10
  | 11 => lookupWord 6 37 5 10 5 1 g255H11
  | 12 => lookupWord 4 277 0 9 4 1 g255H12
  | 13 => lookupWord 1 97 0 7 2 1 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_1 : block g255 9 1 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 5=true := (@block_merge g255 9 0 1 4 g255P9_0 g255P9_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_10 : block g255 10 10 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_19 : block g255 10 19 1=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 20=true := (@block_merge g255 10 0 10 10 g255P10_0 (@block_merge g255 10 10 9 1 g255P10_10 g255P10_19))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_7 : block g255 11 7 5=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 12=true := (@block_merge g255 11 0 7 5 g255P11_0 g255P11_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 4=true := g255P12_0
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
  · exact (rfl : block g255 7 0 0 = true)
  · exact (rfl : block g255 8 0 0 = true)
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
  · exact g255B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=13) (i:=0) (before_sound K247 V247) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_52586

open PEqualNP.Outside.L_meta_52586 in
theorem PEqualNP.Outside.L_meta_52586 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
