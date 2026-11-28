import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49841_aux.Certificate10782_aux

def replayWords (xs : List Nat) := xs.foldl (fun a w => a * 2^60 + w) 0

namespace Core
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def zero : Sig := 0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def one : Sig := BitVec.allOnes 512
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def neg (a : Sig) : Sig := ~~~a
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem nrm_false (a : Sig) : nrm false a = a := rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma extract {u target} (gs : List Gate) (w : List Sig)
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma execute_bits (gs : List Gate) (i) (w : List Sig)
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 512
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def observe (a : Sig) : Wire Row := fun r => bit r a
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def plainWord (a : Sig) : Bool := !(bit 0 a)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def inputs : List Sig := [(BitVec.ofNat 512 (replayWords [0xaaaaaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa])),(BitVec.ofNat 512 (replayWords [0xcccccccc,0xccccccccccccccc,0xccccccccccccccc,0xccccccccccccccc,0xccccccccccccccc,0xccccccccccccccc,0xccccccccccccccc,0xccccccccccccccc,0xccccccccccccccc])),(BitVec.ofNat 512 (replayWords [0xf0f0f0f0,0xf0f0f0f0f0f0f0f,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f,0xf0f0f0f0f0f0f0])),(BitVec.ofNat 512 (replayWords [0xff00ff00,0xff00ff00ff00ff0,0xff00ff00ff00ff,0xff00ff00ff00f,0xf00ff00ff00ff00,0xff00ff00ff00ff0,0xff00ff00ff00ff,0xff00ff00ff00f,0xf00ff00ff00ff00])),(BitVec.ofNat 512 (replayWords [0xffff0000,0xffff0000ffff000,0xffff0000ffff00,0xffff0000ffff0,0xffff0000ffff,0xffff0000fff,0xf0000ffff0000ff,0xff0000ffff0000f,0xfff0000ffff0000])),(BitVec.ofNat 512 (replayWords [0xffffffff,0xfffffff,0xf00000000ffffff,0xff00000000fffff,0xfff00000000ffff,0xffff00000000fff,0xfffff00000000ff,0xffffff00000000f,0xfffffff00000000])),(BitVec.ofNat 512 (replayWords [0xffffffff,0xffffffff0000000,0xffffff,0xffffffffff00000,0xffff,0xffffffffffff000,0xff,0xffffffffffffff0,0x0])),(BitVec.ofNat 512 (replayWords [0xffffffff,0xfffffffffffffff,0xfffffffff000000,0x0,0xffff,0xfffffffffffffff,0xfffffffffffff00,0x0,0x0])),(BitVec.ofNat 512 (replayWords [0xffffffff,0xfffffffffffffff,0xfffffffffffffff,0xfffffffffffffff,0xfffffffffff0000,0x0,0x0,0x0,0x0]))]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def masked (d a : Sig) := a &&& d
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
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

end Core

namespace FirstGate12127
open Core

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def lost (T : Sig) (ws : List Sig) (rs : Row × Row) : Bool :=
  (bit rs.1 T != bit rs.2 T) && ws.all (fun a => bit rs.1 a == bit rs.2 a)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lost_sound {T ws rs u cap} (h : lost T ws rs = true) :
    Impossible u T cap ws.toFinset := by
  simp only [lost,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,beq_iff_eq] at h
  intro _ _ live
  obtain ⟨a,ha,hd⟩ := live_row_difference live h.1
  exact hd (h.2 a (List.mem_toFinset.mp ha))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def cuts (u : Bool) (T : Sig) (raw ws : List Sig) (cap : Nat)
    (slices : List (Sig × Nat)) (pairs : List (Row × Row)) :=
  pairs.any (lost T ws) || slices.any (fun p => poolCut u p.1 p.2 cap 0 raw ws)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cuts_sound {u T raw ws cap slices pairs} (nd : ws.Nodup)
    (prior : ∀ p ∈ slices, Slice u raw T p.1 p.2)
    (h : cuts u T raw ws cap slices pairs = true) : Impossible u T cap ws.toFinset := by
  simp only [cuts,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨rs,_,hh⟩ | ⟨p,hp,hh⟩
  · exact lost_sound hh
  · exact poolCut_sound (prior _ hp) [] rfl nd hh

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def firstCheck (u : Bool) (T : Sig) (raw : List Sig) (cap : Nat)
    (mins : List (Sig × Nat)) (pairs : List (Row × Row)) :=
  raw.all fun a => raw.all fun b => [0,1,2,3].all fun d =>
    [false,true].all fun ka => [false,true].all fun kb =>
      let z := bin d a b
      let child := childTwo raw a b d ka kb
      a == b || !allowedB u d || raw.contains z || decide (child.length > cap) ||
      cuts u T raw child (cap-1) mins pairs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem first_sound {u T raw cap mins pairs} (hd : raw.Nodup) (out : T ∉ raw)
    (prior : ∀ p ∈ mins, Slice u raw T p.1 p.2)
    (ok : firstCheck u T raw cap mins pairs = true) : Impossible u T cap raw.toFinset := by
  apply enum_step hd out
  intro a ha b hb d hOp ka kb hab fresh _ len
  have opmem : d ∈ [0,1,2,3] := by
    rcases allowed_four hOp with h | h | ⟨_,h⟩ | ⟨_,h⟩ <;> simp [h]
  have ab : allowedB u d = true := by
    obtain h | ⟨hu,h⟩ := hOp
    · simp [allowedB,h]
    · simp [allowedB,hu,h]
  have ok' := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp (List.all_eq_true.mp ok _ ha) _ hb) _ opmem) ka (by cases ka <;> simp)) kb (by cases kb <;> simp)
  simp only [beq_eq_false_iff_ne.mpr hab,ab,Bool.not_true, Bool.false_or,
    List.contains_eq_mem, decide_eq_false fresh, decide_eq_false (Nat.not_lt.mpr len)] at ok'
  apply cuts_sound _ prior ok'
  have er : ((raw.erase a).erase b).Nodup := (hd.erase _).erase _
  have ar : a ∉ (raw.erase a).erase b := fun hm => hd.not_mem_erase (List.mem_of_mem_erase hm)
  have br : b ∉ (raw.erase a).erase b := (hd.erase a).not_mem_erase
  have knd := kept_nd kb b _ er br
  have ax : a ∉ kept kb b ((raw.erase a).erase b) := by cases kb <;> simp [kept,ar,hab]
  refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ knd ax⟩
  intro hz
  rcases mem_kept hz with he | hz
  · exact fresh (he.symm ▸ ha)
  rcases mem_kept hz with he | hz
  · exact fresh (he.symm ▸ hb)
  · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hz))
end FirstGate12127

namespace Bound12127
open Core FirstGate12127
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def raw (i : Nat) := inputs.getD i zero
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def in6 := inputs.take 6
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def in5 := inputs.take 5
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def forceHigh (i : Nat) : Move := (~~~raw i,zero,Fin.ofNat 512 (2^i))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def forceLow (i : Nat) : Move := (zero,raw i,Fin.ofNat 512 (2^i))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def swapNext (i : Nat) : Move := (raw i &&& ~~~raw (i+1),raw (i+1) &&& ~~~raw i,Fin.ofNat 512 (2^i))
end Bound12127

namespace Small12127
open Core FirstGate12127
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child_nd {ws : List Sig} (hd : ws.Nodup) (a b : Sig) (d : Nat) (ka kb : Bool)
    (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b) (fresh : bin d a b ∉ ws) :
    (childTwo ws a b d ka kb).Nodup := by
  have er : ((ws.erase a).erase b).Nodup := (hd.erase _).erase _
  have ar : a ∉ (ws.erase a).erase b := fun hm => hd.not_mem_erase (List.mem_of_mem_erase hm)
  have br : b ∉ (ws.erase a).erase b := (hd.erase a).not_mem_erase
  have knd := kept_nd kb b _ er br
  have ax : a ∉ kept kb b ((ws.erase a).erase b) := by cases kb <;> simp [kept,ar,hab]
  refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ knd ax⟩
  intro hz
  rcases mem_kept hz with he | hz
  · exact fresh (he.symm ▸ ha)
  rcases mem_kept hz with he | hz
  · exact fresh (he.symm ▸ hb)
  · exact fresh (List.mem_of_mem_erase (List.mem_of_mem_erase hz))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem child_flip {ws : List Sig} (nd : ws.Nodup) (a b : Sig) {u d} (hd : allowed u d) (ka kb : Bool) :
    (childTwo ws a b d ka kb).toFinset = (childTwo ws b a (flipOp d) kb ka).toFinset := by
  simp only [childTwo,List.toFinset_cons,kept_fin,erase_fin (nd.erase _),erase_fin nd]
  rw [bin_flip hd]
  cases ka <;> cases kb <;> simp [Finset.erase_right_comm,Finset.insert_comm]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def delta (h : Row) (a : Sig) := a ^^^ a.rotateRight h.val
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def reachDiff (h : Row) : List Sig → Sig
  | [] => zero
  | a :: as => delta h a ||| reachDiff h as
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def broken (T : Sig) (h : Row) (ws : List Sig) := delta h T &&& ~~~reachDiff h ws != zero

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem diff_bit (h r : Row) (v : Sig) :
    bit r (delta h v) = (bit r v != bit (shifted h r) v) := by
  simp only [delta,bit,BitVec.getLsbD_xor]
  have hr := bit_shift h r v
  change _ = _ at hr
  simpa [bit] using congrArg (fun b => (v.getLsbD r.val ^^ b)) hr

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem reaches {h r : Row} {ws : List Sig} {a : Sig} (ha : a ∈ ws)
    (d : bit r a ≠ bit (shifted h r) a) : bit r (reachDiff h ws) = true := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | hm
    · change (delta h a ||| reachDiff h xs).getLsbD _ = true
      rw [BitVec.getLsbD_or]
      have hh : bit r (delta h a) = true := by simpa [diff_bit] using d
      change (_ || _) = _
      rw [show (delta h a).getLsbD r.val = true from hh]
      rfl
    · have hh := ih hm
      simpa [bit,reachDiff,hh,show (reachDiff h xs).getLsbD r.val=true from hh]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem broken_sound {T h ws u cap} (bad : broken T h ws=true) : Impossible u T cap ws.toFinset := by
  intro _ _ hh
  suffices z : delta h T &&& ~~~reachDiff h ws = zero by simpa [broken,z] using bad
  apply bit_ext
  intro r
  change (delta h T &&& ~~~reachDiff h ws).getLsbD r.val = (0 : Sig).getLsbD r.val
  rw [BitVec.getLsbD_and,BitVec.getLsbD_not]
  by_cases e : bit r T = bit (shifted h r) T
  · have q : bit r (delta h T)=false := by simp [diff_bit,e]
    rw [show (delta h T).getLsbD r.val=false from q]; simp
  · obtain ⟨a,ha,d⟩ := live_row_difference hh e
    have q := reaches (List.mem_toFinset.mp ha) d
    simp [show (reachDiff h ws).getLsbD r.val=true from q]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def layer (go : List Sig → Bool) (ws : List Sig) :=
  ws.all fun a => ws.all fun b => if a.toNat < b.toNat then
    [0,1,2,3].all fun d => let z := bin d a b
      z == zero || z == one || ws.contains z ||
      ([false,true].all fun ka => [false,true].all fun kb => go (childTwo ws a b d ka kb))
    else true

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem layer_sound {T ws cap} (nd : ws.Nodup) (out : T ∉ ws) {go : List Sig → Bool}
    (valid : ∀ child, child.Nodup → go child=true → Impossible true T (cap-1) child.toFinset)
    (ok : layer go ws=true) : Impossible true T cap ws.toFinset := by
  have oneSide (a b : Sig) (ha : a ∈ ws) (hb : b ∈ ws) (lt : a.toNat < b.toNat) (d : Nat)
      (hd : allowed true d) (ka kb : Bool) (fresh : bin d a b ∉ ws) (pp : proper (bin d a b)) :
      Impossible true T (cap-1) (childTwo ws a b d ka kb).toFinset := by
    have opmem : d ∈ [0,1,2,3] := by
      rcases allowed_four hd with h | h | ⟨_,h⟩ | ⟨_,h⟩ <;> simp [h]
    have ab := List.all_eq_true.mp (List.all_eq_true.mp ok _ ha) _ hb
    simp only [if_pos lt] at ab
    have op := List.all_eq_true.mp ab _ opmem
    simp only [beq_eq_false_iff_ne.mpr pp.1,beq_eq_false_iff_ne.mpr pp.2,
      List.contains_eq_mem,decide_eq_false fresh,Bool.false_or] at op
    exact valid _ (child_nd nd _ _ _ _ _ ha hb (fun e => (Nat.ne_of_lt lt) (congrArg BitVec.toNat e)) fresh)
      (List.all_eq_true.mp (List.all_eq_true.mp op ka (by cases ka <;> simp)) kb (by cases kb <;> simp))
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pp _
  have neN : a.toNat ≠ b.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
  rcases lt_or_gt_of_ne neN with hl | hl
  · exact oneSide _ _ ha hb hl _ hd _ _ fresh pp
  · rw [child_flip nd a b hd ka kb]
    rw [bin_flip hd] at fresh pp
    exact oneSide _ _ hb ha hl _ (flip_flip hd).1 _ _ fresh pp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def scan (T : Sig) (shifts : List Row) : Nat → List Sig → Bool
  | 0, ws => !ws.contains T
  | k+1, ws => decide (ws.length > k+2) || shifts.any (fun h => broken T h ws) ||
    (!ws.contains T && layer (scan T shifts k) ws)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem scan_sound {T shifts cap ws} (nd : ws.Nodup) (ok : scan T shifts cap ws=true) :
    Impossible true T cap ws.toFinset := by
  induction cap generalizing ws with
  | zero =>
    intro k hk hh
    have ke : k=0 := by omega
    subst k
    have mem : T ∈ ws.toFinset := hh.1.symm ▸ Finset.mem_singleton_self _
    simpa [scan,List.mem_toFinset.mp mem] using ok
  | succ k ih =>
    simp only [scan,Bool.or_eq_true,decide_eq_true_eq,List.any_eq_true,Bool.and_eq_true,
      Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at ok
    rcases ok with (big | ⟨h,_,hh⟩) | ⟨out,nxt⟩
    · intro n hn r
      have bound := live_size r
      rw [List.toFinset_card_of_nodup nd] at bound
      omega
    · exact broken_sound hh
    · exact layer_sound nd out (fun c eq r => ih eq r) nxt
end Small12127

namespace GateForest12127
open Core FirstGate12127 Small12127 Bound12127

abbrev Spec := Nat × List (Nat × Nat × Nat)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def rawChoices : List Sig → List (Nat × Nat × Nat) → List Choice
  | _, [] => []
  | ws, (d,i,j)::cs =>
    let q : Choice := (d,ws.getD i zero,ws.getD j zero)
    q :: rawChoices (ws++[choiceVal q]) cs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def pcheck (T : Sig) (raw : List Sig) (mins : List (Sig × Nat)) (s : Spec) (ws : List Sig) (k : Nat) :=
  match mins[s.1]? with
  | none => false
  | some m =>
    let cs := rawChoices (raw.eraseIdx (s.1/2)) s.2
    match makePool true m.1 raw cs with
    | none => false
    | some pool => poolCut true m.1 m.2 k cs.length pool ws

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem pcheck_sound {T raw mins s ws cap} (nd : ws.Nodup)
    (lo : ∀ p ∈ mins, Slice true raw T p.1 p.2)
    (ok : pcheck T raw mins s ws cap=true) : Impossible true T cap ws.toFinset := by
  unfold pcheck at ok
  split at ok
  · contradiction
  rename_i p get
  dsimp only at ok
  split at ok
  · contradiction
  rename_i pool eq
  exact poolCut_sound (lo _ (List.mem_of_getElem? get)) _ eq nd ok

abbrev Entry := List Sig × Nat × Nat × List (Nat × Nat)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Entry.ws (e : Entry) := e.1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Entry.cap (e : Entry) := e.2.1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Entry.bits (e : Entry) := e.2.2.1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Entry.links (e : Entry) := e.2.2.2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def linked (T : Sig) (states : Nat → Entry) (perm : Nat → List Move)
    (prior : Nat) (link : Nat × Nat) (k : Nat) (xs : List Sig) :=
  let moves := perm link.2
  let next := states link.1
  decide (link.1 < prior) && decide (next.cap=k) && (movedWord moves T == T) &&
    decide ((xs.map (movedWord moves)).toFinset = next.ws.toFinset)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem link_sound {T states perm prior link k xs}
    (onto : ∀ i, Function.Surjective (movedRow (perm i)))
    (low : ∀ i < prior, Impossible true T (states i).cap (states i).ws.toFinset)
    (ok : linked T states perm prior link k xs = true) : Impossible true T k xs.toFinset := by
  simp only [linked,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨small,ck⟩,goal⟩,wires⟩ := ok
  intro n hn h
  have run := live_rename h _ (onto link.2)
  simp only [← moved_eq_rename] at run
  rw [goal] at run
  have se : (xs.toFinset.image (movedWord (perm link.2))) = (states link.1).ws.toFinset := by
    rw [←wires]
    ext v
    simp [Finset.mem_image,List.mem_map]
  have fn : rename (movedRow (perm link.2)) = movedWord (perm link.2) := funext fun a => (moved_eq_rename _ a).symm
  rw [fn,se] at run
  exact low _ small _ (by omega) run

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def ticket (e : Entry) (a b : Sig) (op : Nat) (ka kb : Bool) :=
  let n := e.ws.length
  let span := if e.cap+1≤n then 1 else if e.cap≤n then 3 else 4
  let ai := e.ws.idxOf a
  let bi := e.ws.idxOf b
  let pos := ((bi*(bi-1)/2+ai)*4+op)*span+2*ka.toNat+kb.toNat
  (e.bits >>> (12*pos)) &&& 4095

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def cell (T : Sig) (raw : List Sig) (mins : List (Sig × Nat)) (specs : Nat → Spec)
    (states : Nat → Entry) (perm : Nat → List Move) (i : Nat)
    (a b : Sig) (op : Nat) (ka kb : Bool) (child : List Sig) :=
  let e := states i
  let k := e.cap-1
  if child.length > k+1 then true else
  let tag := ticket e a b op ka kb
  if tag < 1024 then lost T child (Fin.ofNat 512 (tag/32), Fin.ofNat 512 (tag % 32)) else
  if tag < 2048 then pcheck T raw mins (specs (tag-1024)) child k else
  match e.links[tag-2048]? with
  | some ptr => linked T states perm i ptr k child
  | none => false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem card_bound {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hz : bin d a b ∉ U := fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem hz] at ih
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem size_sound {T cap} {ws : List Sig} (nd : ws.Nodup) (h : ws.length > cap+1) :
    Impossible true T cap ws.toFinset := by
  intro n hn run
  have b := card_bound run
  rw [List.toFinset_card_of_nodup nd] at b
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cell_sound {T raw mins specs states perm i a b op ka kb child}
    (nd : child.Nodup) (onto : ∀ j, Function.Surjective (movedRow (perm j)))
    (lo : ∀ p ∈ mins, Slice true raw T p.1 p.2)
    (low : ∀ j < i, Impossible true T (states j).cap (states j).ws.toFinset)
    (ok : cell T raw mins specs states perm i a b op ka kb child=true) :
    Impossible true T ((states i).cap-1) child.toFinset := by
  unfold cell at ok
  dsimp only at ok
  split at ok
  · rename_i h; exact size_sound nd h
  split at ok
  · exact lost_sound ok
  split at ok
  · exact pcheck_sound nd lo ok
  split at ok
  · exact link_sound onto low ok
  · contradiction

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def taggedLayer (go : Sig → Sig → Nat → Bool → Bool → List Sig → Bool) (ws : List Sig) :=
  ws.all fun a => ws.all fun b => if a.toNat < b.toNat then
    [0,1,2,3].all fun d => let z := bin d a b
      z == zero || z == one || ws.contains z ||
      ([false,true].all fun ka => [false,true].all fun kb => go a b d ka kb (childTwo ws a b d ka kb))
    else true

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem tagged_sound {T ws cap} (nd : ws.Nodup) (out : T ∉ ws) {go : Sig → Sig → Nat → Bool → Bool → List Sig → Bool}
    (valid : ∀ a b d ka kb child, child.Nodup → go a b d ka kb child=true → Impossible true T (cap-1) child.toFinset)
    (ok : taggedLayer go ws=true) : Impossible true T cap ws.toFinset := by
  have oneSide (a b : Sig) (ha : a ∈ ws) (hb : b ∈ ws) (lt : a.toNat < b.toNat) (d : Nat)
      (hd : allowed true d) (ka kb : Bool) (fresh : bin d a b ∉ ws) (pp : proper (bin d a b)) :
      Impossible true T (cap-1) (childTwo ws a b d ka kb).toFinset := by
    have opmem : d ∈ [0,1,2,3] := by
      rcases allowed_four hd with h | h | ⟨_,h⟩ | ⟨_,h⟩ <;> simp [h]
    have ab := List.all_eq_true.mp (List.all_eq_true.mp ok _ ha) _ hb
    simp only [if_pos lt] at ab
    have op := List.all_eq_true.mp ab _ opmem
    simp only [beq_eq_false_iff_ne.mpr pp.1,beq_eq_false_iff_ne.mpr pp.2,
      List.contains_eq_mem,decide_eq_false fresh,Bool.false_or] at op
    exact valid a b d ka kb _ (child_nd nd _ _ _ _ _ ha hb (fun e => (Nat.ne_of_lt lt) (congrArg BitVec.toNat e)) fresh)
      (List.all_eq_true.mp (List.all_eq_true.mp op ka (by cases ka <;> simp)) kb (by cases kb <;> simp))
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pp _
  have neN : a.toNat ≠ b.toNat := fun e => ne (BitVec.eq_of_toNat_eq e)
  rcases lt_or_gt_of_ne neN with hl | hl
  · exact oneSide _ _ ha hb hl _ hd _ _ fresh pp
  · rw [child_flip nd a b hd ka kb]
    rw [bin_flip hd] at fresh pp
    exact oneSide _ _ hb ha hl _ (flip_flip hd).1 _ _ fresh pp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def nodeOK (T : Sig) (raw : List Sig) (mins : List (Sig × Nat)) (specs : Nat → Spec)
    (states : Nat → Entry) (perm : Nat → List Move) (i : Nat) :=
  let e := states i
  decide e.ws.Nodup && !e.ws.contains T &&
    taggedLayer (cell T raw mins specs states perm i) e.ws

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem certified {T raw mins specs states perm N} (onto : ∀ j, Function.Surjective (movedRow (perm j)))
    (lo : ∀ p ∈ mins, Slice true raw T p.1 p.2)
    (ok : ∀ i < N, nodeOK T raw mins specs states perm i = true) :
    ∀ i < N, Impossible true T (states i).cap (states i).ws.toFinset := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    have good := ok _ hi
    simp only [nodeOK,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at good
    exact tagged_sound good.1.1 good.1.2
      (fun _ _ _ _ _ _ nd v => cell_sound nd onto lo (fun j hj => ih j hj (by omega)) v) good.2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem move_swap : ∀ i : Fin 4, ∀ r : Row, rowMove (swapNext i.val) (rowMove (swapNext i.val) r) = r := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def permitted (xs : List (Fin 4)) := xs.map fun i => swapNext i.val
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem perm_onto (xs : List (Fin 4)) : Function.Surjective (movedRow (permitted xs)) := by
  induction xs with
  | nil => exact fun y => ⟨y,rfl⟩
  | cons j js ih =>
    intro y
    obtain ⟨v,hv⟩ := ih y
    refine ⟨rowMove (swapNext j.val) v,?_⟩
    change movedRow (permitted js) (rowMove (swapNext j.val) (rowMove (swapNext j.val) v)) = y
    rw [move_swap]
    exact hv
end GateForest12127

namespace CertBlocks12127
open Core GateForest12127
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def stamp (n a : Nat) : Sig := BitVec.ofNat 512 (a * ((2^512-1)/(2^(2^n)-1)))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def row (n : Nat) (ws : List Nat) (cap bits : Nat) (links : List (Nat×Nat)) : Entry :=
  ⟨ws.map (stamp n),cap,bits,links⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def Good (f : Nat → Bool) (start num : Nat) := ∀ i, start ≤ i → i < start+num → f i = true
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem checkGood {f : Nat → Bool} {start num : Nat}
    (cert : (List.range num).all (fun j => f (start+j)) = true) : Good f start num := by
  intro i lo hi
  have chk := List.all_eq_true.mp cert (i-start) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le lo] using chk
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem concatGood {f : Nat → Bool} {start n m : Nat}
    (a : Good f start n) (b : Good f (start+n) m) : Good f start (n+m) := by
  intro i l h
  by_cases c : i<start+n
  · exact a _ l c
  · exact b _ (by omega) (by omega)
end CertBlocks12127

namespace Tabfee8
open Core GateForest12127 CertBlocks12127 Bound12127
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def root := inputs.take 4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def target := stamp 4 0xfee8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def mins : List (Sig × Nat) := []
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem pri : ∀ m ∈ mins, Slice true root target m.1 m.2 := by simp [mins]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def ds : Array Entry := #[
  row 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (replayWords [0xa11421840a1061,0x140142061120000,0x128142000000121,0x610a10c2061,0xa10c20a10c20a1,0xc20a10c20610c4,0x610c40610c4061,0xc4062000000000]) [],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xff00] 3 (replayWords [0xa11211840a1,0x61121142061062,0x1201210620610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 4 [0xaaaa,0xfccc,0xfff0] 2 (replayWords [0x610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 4 [0xaa,0xcccc,0xfaf0,0xff00] 3 (replayWords [0xa11201240a1,0x61124142061000,0x8000000610a1,0xc20610620a00a1,0x620600600610a4]) [(2,0)],
  row 4 [0x8888,0xeeee,0xf0f0,0xff00] 3 (replayWords [0xa11211840a1,0xa41201210a4061,0x1218010610a00a0,0xa11280610a1800,0x61060000000000]) [(2,1),(2,2)],
  row 4 [0xaa,0xaa00,0xcccc,0xf0f0,0xff00] 4 (replayWords [0xa11421840a1061,0x140142061120000,0x803,0x610a10c2061,0x1280a18020a1062,0xa00a1062128061,0x801061060060061,0xa4000000800000]) [(1,3),(3,4),(3,3),(4,5)],
  row 4 [0xff0,0xaaaa,0xcccc,0xfff0] 3 (replayWords [0x610c40c4061,0x620a40a40620a1,0x60060,0x610a40c40610c4,0x610a40620a4062]) [],
  row 4 [0xff0,0xaaaa,0xcccc,0xf000] 3 (replayWords [0x61180182061,0x62180181062000,0x184000060060,0x610a40a10610c2,0x610a00620a1062]) [],
  row 4 [0xaaaa,0xfccc,0xfff0] 3 (replayWords [0xc2,0x610610a10c40a1,0xc20c40c20a1061,0x610a10620620c2,0xa40a00a10a40a1,0xc20620620610a4,0x600c4062060061,0x620610c40a40a4]) [],
  row 4 [0xaaaa,0xcccc,0xfaaa,0xfff0] 3 (replayWords [0xa10c20a10c2,0x610a10c20610a1,0xc20a10c20c4061,0x610c4062000000,0x610c40610c4]) [],
  row 4 [0xeaea,0xfcfc,0xffc0] 2 (replayWords [0x610c1,0x1420610620c2121,0x62060060061128]) [],
  row 4 [0xaaa,0xfccc,0xfff0] 2 (replayWords [0x610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 4 [0x8888,0xeeee,0xf0f0,0xff88] 3 (replayWords [0xa11211840a1,0xa41201210a4061,0xa00a0,0xa11288010a1800,0xa1068000000000]) [(10,6),(11,2)],
  row 4 [0xaaaa,0xdccc,0xfff0] 2 (replayWords [0x610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 4 [0x88,0xeeee,0xf0f0,0xff00] 3 (replayWords [0xa11211840a1,0xa41201210a4000,0x8010000a00a0,0xa11280610a1800,0x61060000000000]) [(13,1),(2,2)],
  row 4 [0xaaa,0xcccc,0xf000,0xfff0] 3 (replayWords [0x180000000000,0x610a10c2061062,0xa00a1062061184,0x801061000000800,0x600600610a4]) [(2,7),(11,3)],
  row 4 [0x8888,0xeeee,0xf0f0,0xff00] 4 (replayWords [0x1840a1,0xa1121188121184,0x1881841210a10a1,0x1210a40a4184128,0x120121128121184,0xa40a480b061061,0x12180a121809808,0x8071210610610a1,0x1280a01880a40a0,0xa10a40a1188128,0x1288060610610a1,0x8050a1804803802,0xa1061061801800,0x60000000000000,0x0]) [(6,1),(7,1),(8,1),(9,2),(12,8),(14,8),(15,2),(8,2),(9,1),(12,3),(14,3),(15,1)],
  row 4 [0xff0,0xaaaa,0xcccc,0xf0f0] 3 (replayWords [0x610c40c4061,0x620a40a40620a1,0xa1184121060060,0x610a40c40610c4,0x610a40620a4062]) [],
  row 4 [0xaaaa,0xcccc,0xfaf0,0xffaa] 3 (replayWords [0xc20a10a10c2,0xc40610610c4062,0x610a1,0xc20610a10a80a1,0xc20610680610c4]) [],
  row 4 [0x8888,0xaaaa,0xeeee,0xf0f0,0xff00] 4 (replayWords [0xa11211840a10c4,0x1401210c4121122,0x121141061121802,0x610a10c00a1148,0xa10a20a10c1061,0xa18010610a4000,0x800000000,0x62000000000]) [(17,1),(18,9),(18,10)],
  row 4 [0xaaa,0xcccc,0xf0f0,0xff00] 3 (replayWords [0xa11211840a1,0x61121142061062,0x1201210620610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xff80] 3 (replayWords [0xa11211840a1,0x61121142061062,0x1201210620610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 4 [0x2aaa,0xcccc,0xf0f0,0xff00] 3 (replayWords [0xa11211840a1,0x61121142061062,0x1201210620610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 4 [0x8080,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (replayWords [0xa11211840a1061,0x121142061062120,0x121062804121803,0x1210610a10c2061,0x620a00a1062802,0x60060,0x610a4801000000,0x800000000000]) [(20,11),(20,12),(20,2),(21,3),(22,5)],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xff88] 4 (replayWords [0x1840a1,0xa1121188121184,0x1881841210a10a1,0x1420c4061121148,0x61142148142121,0xc40c41210a4062,0x142128062121128,0x1211420a40a40c2,0x1480c00a10c40a1,0xc20c40c20a1148,0xa10a11280a00c2,0xa40a00a10a40a1,0xc21280c28040a4,0x680c4803068802,0x8018000c40a40a4]) [(8,2),(18,13),(18,10),(3,10),(3,13)],
  row 4 [0xaaaa,0xcccc,0xeaea,0xf0f0,0xff00] 4 (replayWords [0xa11211840a1121,0x142121142061121,0x142061121142121,0x1420a10c20a1188,0x610a18000610a1,0x1880a11880c4061,0x61148062000000,0x61148061148]) [(9,11)],
  row 4 [0xaaaa,0xcccc,0xf8f8,0xff88] 3 (replayWords [0xa11211840a1,0xc41211420c40a4,0x1201210a40c00a1,0xc20a10a00a00a1,0xc20a40c48000a4]) [(10,6)],
  row 4 [0xaaa,0xf0f0,0xfccc,0xff00] 3 (replayWords [0x61121142061,0xa11218000a1062,0x1201210620a1061,0xc2061060060061,0xa40620a00a1062]) [(11,3)],
  row 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff88] 4 (replayWords [0xa11211840a10c4,0x1211420c40a4120,0x1210a4805000000,0xc00a10c20a1,0xa00a00a10c2804,0xa18030a10a40c4,0x802000801000000,0x800000000000]) [(3,10),(3,13),(12,3),(26,3),(27,2),(20,1)],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xff08] 3 (replayWords [0xa11211840a1,0x610611420c4062,0x621210a40c00a1,0xc20a10a00a00a1,0xc20680688000a4]) [(13,2)],
  row 4 [0x8aaa,0xcccc,0xf0f0,0xff00] 3 (replayWords [0xa11211840a1,0x61121142061062,0x1201210620610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xff88] 3 (replayWords [0xa11211840a1,0x610611420c4062,0x621210a40c00a1,0xc20a10a00a00a1,0xc20680688000a4]) [(2,2)],
  row 4 [0x88,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (replayWords [0xa11211840a10c4,0x1211420c40a4120,0x1210a4000000803,0xc00a10c20a1,0xa00a00a10c2802,0xa18010a10a40c4,0x8000a4061000000,0x62000000000]) [(14,3),(29,8),(30,2),(31,3)],
  row 4 [0xaaa,0xcccc,0xf0f0,0xff00] 4 (replayWords [0x1840a1,0xa1121188121184,0x1881841210a10a1,0x142061061121148,0x121142148142121,0x61061121062062,0x142128120121128,0x1211420620620c2,0x610610a10c40a1,0xc20c40c20a1061,0x610a10620620c2,0xa40a00a10a40a1,0xc20620620610a4,0x600c4062060061,0x620610c40a40a4]) [],
  row 4 [0xaaa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (replayWords [0xa11211840a1061,0x121142061121142,0x121142121142121,0x1420610a10c2061,0xa10c20a10c20a1,0xc20a10c20610c4,0x610c40610c4061,0xc4062000000000]) [],
  row 4 [0xaaa,0xccc,0xf0f0,0xff00] 3 (replayWords [0xa11211840a1,0x61121142061062,0x1201210620610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 4 [0xaaa,0xcccc,0xf000,0xf0f0,0xff00] 4 (replayWords [0xa1121803000184,0x61121,0x142061062120121,0x62188000000000,0x610a10c2061062,0xa00a1062061802,0x801061000000800,0x600600610a4]) [(31,14),(27,3),(35,3),(15,3)],
  row 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff00] 5 (replayWords [0x1840a10a1121188,0x121184188184121,0xa10a11420c40c4,0x121148121142148,0x1421210c40c4121,0xa40a4142128120,0x1211281211420a4,0xa4816815814121,0x813121812811810,0x12180f1210c2148,0xc00a10c40a10c2,0xc40c20a11480a1,0xa11280a00c20a4,0xa00a10a40a10c2,0x1280c280e80d80c,0xa180b0a180a809,0x8080a18070a1803,0xa40a40c48010c4,0x806805804000000,0x803802061000,0x0,0x801800,0x62000000000000,0x0]) [(0,9),(5,9),(0,15),(5,15),(16,3),(19,7),(19,3),(23,3),(24,8),(25,6),(28,8),(32,8),(33,2),(34,2),(36,2),(23,5),(24,3),(25,5),(28,3),(32,3),(33,1),(34,1),(36,1)],
  row 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xffaa] 4 (replayWords [0xc20a10a10c20c4,0x610610c4120000,0x801000000,0x610a10c2061,0xa10c20a10c20a1,0xc20a10c20610c4,0x610c40610c4061,0xc4800000000000]) [(4,5),(1,3)],
  row 4 [0xaaaa,0xfcfc,0xffcc,0xfff0] 3 (replayWords [0xc20c40c2802,0xa10a10c2801062,0xa40a4062061061,0xc48000a4062062,0xa40e80620620c8]) [(2,3),(2,4),(2,11)],
  row 4 [0xaaaa,0xfcec,0xfff0] 2 (replayWords [0x610a1,0xc20610620a2121,0x620600600610c4]) [],
  row 4 [0xa8a8,0xcccc,0xfafa,0xff00] 3 (replayWords [0xc21201210c2,0xc11211420c10a1,0x1218010a10c00c0,0xc1128062000000,0x610618000a1]) [(2,16),(40,12)],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xffaa,0xffcc] 4 (replayWords [0x1211421218030a1,0xc20c20a1061000,0x121128121,0x8020c20a10a10c2,0x142148142801062,0xc20a1,0xc20a10a10c20a1,0xc2068068800128]) [(39,6),(41,17),(41,8),(31,3)],
  row 4 [0xaa,0xcccc,0xeeee,0xf0f0,0xff00] 4 (replayWords [0xa11421840a1120,0x120128184061184,0x122061000000121,0xa11880a1128,0x610a10c2061062,0xc20a10620c4000,0xa4000000,0x61062061800]) [(14,3)],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xffa8] 3 (replayWords [0xa10a11840c2,0x610611420c4062,0x621211420c00c0,0xc21480a80a8801,0xc20680688000c4]) [(40,2),(40,12)],
  row 4 [0x2aa,0xcccc,0xf0f0,0xff00] 3 (replayWords [0xa11211840a1,0x61121142061062,0x1201210620610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 4 [0xa8a8,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (replayWords [0xc21211840c20c4,0x1211420c4120120,0x121142805121804,0x1210c00c00c2148,0x1280c28030c20a1,0xa18020c21280c4,0x8010c4061061800,0xc4062000000000]) [(31,18),(41,4),(31,8),(41,3),(44,3),(45,14)],
  row 4 [0xaaa8,0xcccc,0xf0f0,0xff00] 3 (replayWords [0xc21421840c2,0xc41401420c4062,0x1201280620c00c0,0xc21480620a00a4,0x620600600620a4]) [],
  row 4 [0xfe,0xaaaa,0xcccc,0xf0f0] 3 (replayWords [0x610a10c2061,0x620a40a10620a1,0x1800a1121061062,0x610a4061140061,0x121062120062120]) [],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xfefe,0xff00] 4 (replayWords [0x1218011218000a1,0x1211840a1061121,0x142061062142121,0x62188000000000,0x148000000000128,0x610a1,0xc20610620a40a1,0x620610620610a4]) [(47,5),(48,3)],
  row 4 [0xee,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (replayWords [0xa11801840a1061,0x140148061062120,0x128062000000121,0x610a10c2061,0x620c20a10620a1,0x1880a1188061062,0x611280610c4061,0x1480620a4062128]) [],
  row 4 [0xa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (replayWords [0xc21421840c2061,0x1401420610a4120,0x1280a4000000121,0x610c00c2061,0xa00a00a40c2000,0xa10000610c4,0x610a40610c4061,0xc4062000000000]) [],
  row 4 [0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00] 5 (replayWords [0x1840a10a1121188,0x121184188184121,0xa10a1121816121,0x184815184121814,0x121184813184142,0x61061121812121,0x142811142121061,0x61121062062142,0x81014212180f121,0x1420620620a180e,0xa118880d1880a1,0x80c0a118880b188,0xc20610610a180a,0xa10c28090c20a1,0x610610a1062062,0xc28080c20a1807,0xa10c2062062806,0x8030c4000000000,0x0,0x8058040a4000,0x0,0x61804,0x61803062062000,0x802801800]) [(16,3),(19,7),(19,3),(38,9),(38,15),(0,15),(0,9),(42,19),(43,8),(42,18),(43,17),(46,6),(49,3),(50,8),(51,2),(42,20),(43,3),(42,21),(43,7),(46,5),(49,5),(50,3),(51,1)],
  row 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (replayWords [0xa11211840a10c4,0x1211420c40a4120,0x1210a4804121803,0x1210c00a10c20a1,0xa00a00a10c2802,0xa18010a10a40c4,0x800000061000000,0x62000000000]) [(4,3),(31,8),(20,2),(31,3),(20,1)],
  row 4 [0xaaaa,0xaaee,0xcccc,0xf0f0,0xff00] 4 (replayWords [0xa11211840a1061,0x121148061121184,0x121142062162121,0x620610a10c2061,0xa11880a1188062,0xc20a10620610c4,0x61148061062061,0x1480a4000000000]) [],
  row 4 [0x88aa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (replayWords [0xa11421840a1061,0x140142061120120,0x128142800142121,0x1210610a10c2061,0xa10c20a10c20a1,0xc20a10c20610c4,0x610c40610c4061,0xc4062000000000]) [(20,1)],
  row 4 [0xaa,0xa0a,0xcccc,0xf0f0,0xff00] 4 (replayWords [0xc21421840c2061,0x140142061120120,0x128142000000121,0x610c00c2061,0xa10000a0,0xa00a40c20610c4,0x610c40610c4061,0xa40620628000a4]) [(20,3)],
  row 4 [0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00] 4 (replayWords [0xa11211840a1121,0x184121184061121,0x142061062142121,0x620a11880a1188,0x610a10c2061062,0xc20a10620c4000,0xa4000000,0x61062000800]) [(4,3)],
  row 4 [0xaa,0x5500,0xaaaa,0xcccc,0xf0f0] 4 (replayWords [0x610a10c20610a1,0xc20a10c21420a1,0x1840a10a10c20a1,0xc20610c40610c4,0x140061142061061,0xc40610c4000000,0x128000062000000,0x800000]) [(17,22)],
  row 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xff00] 5 (replayWords [0x1840a10a1142188,0x142184188184142,0xa10a1142061061,0x184148140142148,0x142184061061811,0x810120000000000,0x80f128128142801,0x142000000000000,0x80f80e121,0xc2061,0x610a10c40a10c2,0xc40c20a1061061,0xa11280a10c280d,0xc20a180c0a10c2,0x1280c20a180b0a1,0xc280a0c20a1809,0xa10c28080c2061,0x1280610c48070c4,0x618060610c4128,0xc40618050610c4,0x8040c4061803061,0xc48020c4801800,0x62000000000000,0x0]) [(53,5),(5,3),(32,3),(54,7),(51,4),(55,15),(43,3),(56,4),(32,6),(54,6),(51,3),(55,23),(43,4),(56,3),(57,5),(38,3),(58,14),(58,3)],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xff00] 6 (replayWords [0x817,0x1840a10a1816121,0x188121815184188,0x1848141210a10a1,0x813142061061812,0x121148121811142,0x148142810121061,0x6180f121062062,0x80e14212812080d,0x12112812180c142,0x6206280b0c2061,0x6180a0a10c40a1,0x8090c20c40c2808,0xa10610618070a1,0x620628060c20a4,0xa08050a10a40a1,0x8040c2062062803,0x610a40608020c4,0x62060801061062,0x618000c40a40a4]) [(37,3),(52,3),(59,9),(59,15),(37,6),(52,6),(59,11),(59,23),(37,22),(52,22),(59,12),(59,2),(37,5),(52,5),(59,3),(59,14),(37,16),(52,16),(59,7),(59,1),(37,1),(52,1),(59,6),(59,5)]
]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def states (i : Nat) := ds[i]?.getD default
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def ms : Array (List (Fin 4)) := #[[1,0],[0,1,2,0,1],[1,2,0,1],[],[1],[0,1,2],[0,1],[0],[2],[1,2,1],[2,1],[1,2],[1,2,0],[2,1,0],[0,1,2,0,1,0],[1,2,1,0],[0,1,2,0],[2,0],[2,0,1],[2,0,1,0],[0,1,2,1,0],[0,1,2,1],[0,1,0],[1,2,0,1,0]]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def perm (i : Nat) := permitted (ms[i]?.getD [])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def specTab : Array Spec := #[]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def spec (i : Nat) := specTab[i]?.getD (0,[])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def checked (i : Nat) := nodeOK target root mins spec states perm i
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block0 : Good checked 0 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block1 : Good checked 4 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block2 : Good checked 8 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block3 : Good checked 12 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block4 : Good checked 16 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block5 : Good checked 20 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block6 : Good checked 24 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block7 : Good checked 28 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block8 : Good checked 32 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block9 : Good checked 36 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block10 : Good checked 40 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block11 : Good checked 44 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block12 : Good checked 48 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block13 : Good checked 52 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block14 : Good checked 56 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block15 : Good checked 60 1 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem total : Good checked 0 61 := (concatGood (concatGood (concatGood (concatGood block0 block1) (concatGood block2 block3)) (concatGood (concatGood block4 block5) (concatGood block6 block7))) (concatGood (concatGood (concatGood block8 block9) (concatGood block10 block11)) (concatGood (concatGood block12 block13) (concatGood block14 block15))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem impossible : Impossible true target 6 root.toFinset := by
  have h := certified (states:=states) (perm:=perm) (specs:=spec) (N:=61) (fun j => perm_onto _) pri (fun i hi => total i (by omega) hi) 60 (by decide)
  exact h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def essentials : List (Sig × Row × Row) := [(root.getD 0 zero,2,3),(root.getD 1 zero,1,3),(root.getD 2 zero,1,5),(root.getD 3 zero,1,9)]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower : Lower true root target 7 := by
  apply lower_impossible (L:=6) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=essentials) (by decide +kernel) a
    exact (show (essentials.map Prod.fst).toFinset = root.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact impossible

end Tabfee8

namespace Bound10782
open Core FirstGate12127
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def raw (i : Nat) := inputs.getD i zero
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def in7 := inputs.take 7
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def in6 := inputs.take 6
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def seven : Sig := (BitVec.ofNat 512 (replayWords [0xffffffff,0xfffffffefffffee,0x8fee8fee8ffffff,0xfffffffffefffff,0xee8fee8fee8ffff,0xfffffffffffefff,0xffee8fee8fee8ff,0xfffffffffffffef,0xffffee8fee8fee8]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def branchA : Sig := (BitVec.ofNat 512 (replayWords [0xfffffffe,0xffe8e8e8fffffff,0xeffe8e8e8ffffff,0xfeffe8e8e8fffff,0xffeffe8e8e8ffff,0xfffeffe8e8e8fff,0xffffeffe8e8e8ff,0xfffffeffe8e8e8f,0xffffffeffe8e8e8]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def branchB : Sig := (BitVec.ofNat 512 (replayWords [0xfffffffe,0xfee8fee8fffffff,0xefee8fee8ffffff,0xfefee8fee8fffff,0xffefee8fee8ffff,0xfffefee8fee8fff,0xffffefee8fee8ff,0xfffffefee8fee8f,0xffffffefee8fee8]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def forceLow (i : Nat) : Move := (zero,raw i,Fin.ofNat 512 (2^i))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def swapNext (i : Nat) : Move := (raw i &&& ~~~raw (i+1),raw (i+1) &&& ~~~raw i,Fin.ofNat 512 (2^i))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def m0 : List Move := [forceLow 6, swapNext 5, swapNext 4, swapNext 3, swapNext 2, swapNext 1, swapNext 0]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def d0 : Sig := ~~~raw 0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem s0 (h : Lower true in6 branchA 11) : Slice true in7 seven d0 11 :=
  slice_correct (ms := m0) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def m1 : List Move := [forceLow 6, swapNext 5, swapNext 4, swapNext 3, swapNext 2, swapNext 1]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def d1 : Sig := ~~~raw 1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem s1 (h : Lower true in6 branchA 11) : Slice true in7 seven d1 11 :=
  slice_correct (ms := m1) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def m2 : List Move := [forceLow 6, swapNext 5, swapNext 4, swapNext 3, swapNext 2]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def d2 : Sig := ~~~raw 2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem s2 (h : Lower true in6 branchA 11) : Slice true in7 seven d2 11 :=
  slice_correct (ms := m2) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def m3 : List Move := [forceLow 6, swapNext 5, swapNext 4, swapNext 3]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def d3 : Sig := ~~~raw 3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem s3 (h : Lower true in6 branchA 11) : Slice true in7 seven d3 11 :=
  slice_correct (ms := m3) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def m4 : List Move := [forceLow 6, swapNext 5, swapNext 4]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def d4 : Sig := ~~~raw 4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem s4 (h : Lower true in6 branchB 11) : Slice true in7 seven d4 11 :=
  slice_correct (ms := m4) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def m5 : List Move := [forceLow 6, swapNext 5]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def d5 : Sig := ~~~raw 5
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem s5 (h : Lower true in6 branchB 11) : Slice true in7 seven d5 11 :=
  slice_correct (ms := m5) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def minors : List (Sig × Nat) := [(d0,11), (d1,11), (d2,11), (d3,11), (d4,11), (d5,11)]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def lostRows : List (Row × Row) := [(41, 40), (35, 33), (5, 1), (12, 4), (49, 33), (52, 20), (26, 24), (21, 20), (96, 64), (72, 64), (65, 64), (22, 18), (66, 64), (68, 64), (80, 64), (48, 40), (10, 34)]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem seven_lower (a : Lower true in6 branchA 11) (b : Lower true in6 branchB 11) : Impossible true seven 12 in7.toFinset := by
  apply first_sound (mins := minors) (pairs := lostRows) (by decide +kernel) (by decide +kernel)
  · intro p hp
    simp only [minors,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact s0 a
    · exact s1 a
    · exact s2 a
    · exact s3 a
    · exact s4 b
    · exact s5 b
  · decide +kernel

end Bound10782

namespace ASub10782
open Core Bound10782
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def forceHigh (i : Nat) : Move := (~~~raw i,zero,Fin.ofNat 512 (2^i))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def base3Goal : Sig := (BitVec.ofNat 512 (replayWords [0xe8e8e8e8,0xe8e8e8e8e8e8e8e,0x8e8e8e8e8e8e8e8,0xe8e8e8e8e8e8e8e,0x8e8e8e8e8e8e8e8,0xe8e8e8e8e8e8e8e,0x8e8e8e8e8e8e8e8,0xe8e8e8e8e8e8e8e,0x8e8e8e8e8e8e8e8]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def base4Goal : Sig := (BitVec.ofNat 512 (replayWords [0xfee8fee8,0xfee8fee8fee8fee,0x8fee8fee8fee8fe,0xe8fee8fee8fee8f,0xee8fee8fee8fee8,0xfee8fee8fee8fee,0x8fee8fee8fee8fe,0xe8fee8fee8fee8f,0xee8fee8fee8fee8]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def bowGoal : Sig := (BitVec.ofNat 512 (replayWords [0xffeaeae8,0xffeaeae8ffeaeae,0x8ffeaeae8ffeaea,0xe8ffeaeae8ffeae,0xae8ffeaeae8ffea,0xeae8ffeaeae8ffe,0xaeae8ffeaeae8ff,0xeaeae8ffeaeae8f,0xfeaeae8ffeaeae8]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem base3 : Lower true (inputs.take 3) base3Goal 4 := by
  apply lower_impossible (L:=3) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro w hw
    let xs : List (Sig × Row × Row) := [(raw 0,2,3),(raw 1,1,3),(raw 2,1,5)]
    apply essential_ok (xs:=xs) (by decide +kernel) w
    exact (show (xs.map Prod.fst).toFinset = (inputs.take 3).toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr hw
  · exact Small12127.scan_sound (shifts:=[1,2,4]) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vf8a2 : Sig := (BitVec.ofNat 512 (replayWords [0x88888888,0x888888888888888,0x888888888888888,0x888888888888888,0x888888888888888,0x888888888888888,0x888888888888888,0x888888888888888,0x888888888888888]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f8a2 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 2) vf8a2 1 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,2,3), (raw 1,1,3)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vfea2 : Sig := (BitVec.ofNat 512 (replayWords [0xeeeeeeee,0xeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeee]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem fea2 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 2) vfea2 1 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,0,2)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vfa8a3 : Sig := (BitVec.ofNat 512 (replayWords [0xa8a8a8a8,0xa8a8a8a8a8a8a8a,0x8a8a8a8a8a8a8a8,0xa8a8a8a8a8a8a8a,0x8a8a8a8a8a8a8a8,0xa8a8a8a8a8a8a8a,0x8a8a8a8a8a8a8a8,0xa8a8a8a8a8a8a8a,0x8a8a8a8a8a8a8a8]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem fa8a3 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 3) vfa8a3 2 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,2,3), (raw 1,1,3), (raw 2,1,5)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vfe8a3 : Sig := (BitVec.ofNat 512 (replayWords [0xe8e8e8e8,0xe8e8e8e8e8e8e8e,0x8e8e8e8e8e8e8e8,0xe8e8e8e8e8e8e8e,0x8e8e8e8e8e8e8e8,0xe8e8e8e8e8e8e8e,0x8e8e8e8e8e8e8e8,0xe8e8e8e8e8e8e8e,0x8e8e8e8e8e8e8e8]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem fe8a3 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 3) vfe8a3 4 := by
  exact lift_ok (ms:=[]) (xs:=[]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vfeaa3 : Sig := (BitVec.ofNat 512 (replayWords [0xeaeaeaea,0xeaeaeaeaeaeaeae,0xaeaeaeaeaeaeaea,0xeaeaeaeaeaeaeae,0xaeaeaeaeaeaeaea,0xeaeaeaeaeaeaeae,0xaeaeaeaeaeaeaea,0xeaeaeaeaeaeaeae,0xaeaeaeaeaeaeaea]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem feaa3 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 3) vfeaa3 2 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,4,6), (raw 2,2,6)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffea3 : Sig := (BitVec.ofNat 512 (replayWords [0xfefefefe,0xfefefefefefefef,0xefefefefefefefe,0xfefefefefefefef,0xefefefefefefefe,0xfefefefefefefef,0xefefefefefefefe,0xfefefefefefefef,0xefefefefefefefe]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffea3 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 3) vffea3 2 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,0,2), (raw 2,0,4)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vfeac0a4 : Sig := (BitVec.ofNat 512 (replayWords [0xeac0eac0,0xeac0eac0eac0eac,0xeac0eac0eac0ea,0xc0eac0eac0eac0e,0xac0eac0eac0eac0,0xeac0eac0eac0eac,0xeac0eac0eac0ea,0xc0eac0eac0eac0e,0xac0eac0eac0eac0]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem feac0a4 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 4) vfeac0a4 3 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,8,9), (raw 1,4,6), (raw 2,2,6), (raw 3,1,9)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vfeae8a4 : Sig := (BitVec.ofNat 512 (replayWords [0xeae8eae8,0xeae8eae8eae8eae,0x8eae8eae8eae8ea,0xe8eae8eae8eae8e,0xae8eae8eae8eae8,0xeae8eae8eae8eae,0x8eae8eae8eae8ea,0xe8eae8eae8eae8e,0xae8eae8eae8eae8]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem feae8a4 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 4) vfeae8a4 5 := by
  exact lift_ok (ms:=[forceLow 3]) (xs:=[(raw 3,1,9)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffee8a4 : Sig := (BitVec.ofNat 512 (replayWords [0xfee8fee8,0xfee8fee8fee8fee,0x8fee8fee8fee8fe,0xe8fee8fee8fee8f,0xee8fee8fee8fee8,0xfee8fee8fee8fee,0x8fee8fee8fee8fe,0xe8fee8fee8fee8f,0xee8fee8fee8fee8]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffee8a4 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 4) vffee8a4 7 := by
  exact lift_ok (ms:=[]) (xs:=[]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffeeaa4 : Sig := (BitVec.ofNat 512 (replayWords [0xfeeafeea,0xfeeafeeafeeafee,0xafeeafeeafeeafe,0xeafeeafeeafeeaf,0xeeafeeafeeafeea,0xfeeafeeafeeafee,0xafeeafeeafeeafe,0xeafeeafeeafeeaf,0xeeafeeafeeafeea]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffeeaa4 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 4) vffeeaa4 5 := by
  exact lift_ok (ms:=[forceLow 3, swapNext 2, swapNext 1, swapNext 0]) (xs:=[(raw 0,0,1)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffeeea4 : Sig := (BitVec.ofNat 512 (replayWords [0xfeeefeee,0xfeeefeeefeeefee,0xefeeefeeefeeefe,0xeefeeefeeefeeef,0xeeefeeefeeefeee,0xfeeefeeefeeefee,0xefeeefeeefeeefe,0xeefeeefeeefeeef,0xeeefeeefeeefeee]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffeeea4 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 4) vffeeea4 3 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,0,2), (raw 2,8,12), (raw 3,4,12)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffffea4 : Sig := (BitVec.ofNat 512 (replayWords [0xfffefffe,0xfffefffefffefff,0xefffefffefffeff,0xfefffefffefffef,0xffefffefffefffe,0xfffefffefffefff,0xefffefffefffeff,0xfefffefffefffef,0xffefffefffefffe]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffffea4 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 4) vffffea4 3 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,0,2), (raw 2,0,4), (raw 3,0,8)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffeeafcc0a5 : Sig := (BitVec.ofNat 512 (replayWords [0xfeeafcc0,0xfeeafcc0feeafcc,0xfeeafcc0feeafc,0xc0feeafcc0feeaf,0xcc0feeafcc0feea,0xfcc0feeafcc0fee,0xafcc0feeafcc0fe,0xeafcc0feeafcc0f,0xeeafcc0feeafcc0]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffeeafcc0a5 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 5) vffeeafcc0a5 6 := by
  exact lift_ok (ms:=[forceLow 3, forceLow 4, swapNext 2, swapNext 1, swapNext 0]) (xs:=[(raw 0,16,17), (raw 4,1,17)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffeeafee8a5 : Sig := (BitVec.ofNat 512 (replayWords [0xfeeafee8,0xfeeafee8feeafee,0x8feeafee8feeafe,0xe8feeafee8feeaf,0xee8feeafee8feea,0xfee8feeafee8fee,0xafee8feeafee8fe,0xeafee8feeafee8f,0xeeafee8feeafee8]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffeeafee8a5 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 5) vffeeafee8a5 8 := by
  exact lift_ok (ms:=[forceLow 4]) (xs:=[(raw 4,1,17)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffeeefaa8a5 : Sig := (BitVec.ofNat 512 (replayWords [0xfeeefaa8,0xfeeefaa8feeefaa,0x8feeefaa8feeefa,0xa8feeefaa8feeef,0xaa8feeefaa8feee,0xfaa8feeefaa8fee,0xefaa8feeefaa8fe,0xeefaa8feeefaa8f,0xeeefaa8feeefaa8]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffffefeeea5 : Sig := (BitVec.ofNat 512 (replayWords [0xfffefeee,0xfffefeeefffefee,0xefffefeeefffefe,0xeefffefeeefffef,0xeeefffefeeefffe,0xfeeefffefeeefff,0xefeeefffefeeeff,0xfefeeefffefeeef,0xffefeeefffefeee]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffffefeeea5 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 5) vffffefeeea5 6 := by
  exact lift_ok (ms:=[forceLow 3, forceLow 4, swapNext 2, swapNext 1, swapNext 0, swapNext 3, swapNext 2, swapNext 1]) (xs:=[(raw 0,0,1), (raw 1,0,2)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffffefefea5 : Sig := (BitVec.ofNat 512 (replayWords [0xfffefefe,0xfffefefefffefef,0xefffefefefffefe,0xfefffefefefffef,0xefefffefefefffe,0xfefefffefefefff,0xefefefffefefeff,0xfefefefffefefef,0xffefefefffefefe]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffffefefea5 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 5) vffffefefea5 4 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,0,2), (raw 2,0,4), (raw 3,16,24), (raw 4,8,24)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffffffffea5 : Sig := (BitVec.ofNat 512 (replayWords [0xfffffffe,0xfffffffefffffff,0xefffffffeffffff,0xfefffffffefffff,0xffefffffffeffff,0xfffefffffffefff,0xffffefffffffeff,0xfffffefffffffef,0xffffffefffffffe]))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffffffffea5 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 5) vffffffffea5 4 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,0,2), (raw 2,0,4), (raw 3,0,8), (raw 4,0,16)] (by decide +kernel)
end ASub10782

namespace Tabfffe
open Core CertBlocks12127 Bound12127
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def root := inputs.take 4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def target := stamp 4 0xfffe
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower : Lower true root target 3 :=
  lower_count (by unfold proper; decide +kernel) [(raw 0,0,1),(raw 1,0,2),(raw 2,0,4),(raw 3,0,8)] (by decide +kernel)
end Tabfffe
namespace ASub10782
open Core
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem verified4 : Lower true (inputs.take 4) base4Goal 7 := Tabfee8.lower

end ASub10782

namespace BowCofs
open Core Bound10782 ASub10782 CertBlocks12127
namespace Tabeae8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def target := stamp 4 0xeae8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower : Lower true (inputs.take 4) target 5 :=
  lower_map (ms:=[]) (by decide +kernel) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (feae8a4 verified4)
end Tabeae8
namespace Tabf888
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def target := stamp 4 0xf888
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower : Lower true (inputs.take 4) target 3 :=
  lower_map (ms:=[swapNext 2, swapNext 1]) (by decide +kernel) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (feac0a4 verified4)
end Tabf888
namespace Tabfaa8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def target := stamp 4 0xfaa8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower : Lower true (inputs.take 4) target 5 :=
  lower_map (ms:=[swapNext 2, swapNext 1]) (by decide +kernel) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (feae8a4 verified4)
end Tabfaa8
namespace Tabfeee
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def target := stamp 4 0xfeee
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower : Lower true (inputs.take 4) target 3 :=
  lower_map (ms:=[]) (by decide +kernel) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffeeea4 verified4)
end Tabfeee
namespace Tabffea
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def target := stamp 4 0xffea
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower : Lower true (inputs.take 4) target 3 :=
  lower_map (ms:=[swapNext 1, swapNext 2]) (by decide +kernel) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffeeea4 verified4)
end Tabffea
namespace Tabfffe
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def target := stamp 4 0xfffe
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower : Lower true (inputs.take 4) target 3 :=
  lower_map (ms:=[]) (by decide +kernel) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffffea4 verified4)
end Tabfffe
end BowCofs

namespace TabBowtie
open Core GateForest12127 CertBlocks12127 Bound12127
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def root := inputs.take 5
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def target := stamp 5 0xffeaeae8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd0 : Sig := ~~~raw 0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl0 : Slice true root target sd0 3 :=
  slice_correct (ms:=[forceLow 4,swapNext 3,swapNext 2,swapNext 1,swapNext 0]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) BowCofs.Tabf888.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd1 : Sig := raw 0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl1 : Slice true root target sd1 3 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3,swapNext 2,swapNext 1,swapNext 0]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) BowCofs.Tabfffe.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd2 : Sig := ~~~raw 1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl2 : Slice true root target sd2 5 :=
  slice_correct (ms:=[forceLow 4,swapNext 3,swapNext 2,swapNext 1]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) BowCofs.Tabfaa8.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd3 : Sig := raw 1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl3 : Slice true root target sd3 3 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3,swapNext 2,swapNext 1]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) BowCofs.Tabfeee.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd4 : Sig := ~~~raw 2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl4 : Slice true root target sd4 5 :=
  slice_correct (ms:=[forceLow 4,swapNext 3,swapNext 2]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) BowCofs.Tabfaa8.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd5 : Sig := raw 2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl5 : Slice true root target sd5 3 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3,swapNext 2]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) BowCofs.Tabfeee.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd6 : Sig := ~~~raw 3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl6 : Slice true root target sd6 5 :=
  slice_correct (ms:=[forceLow 4,swapNext 3]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) BowCofs.Tabeae8.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd7 : Sig := raw 3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl7 : Slice true root target sd7 3 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) BowCofs.Tabffea.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd8 : Sig := ~~~raw 4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl8 : Slice true root target sd8 5 :=
  slice_correct (ms:=[forceLow 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) BowCofs.Tabeae8.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd9 : Sig := raw 4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl9 : Slice true root target sd9 3 :=
  slice_correct (ms:=[forceHigh 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) BowCofs.Tabffea.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def mins : List (Sig × Nat) := [(sd0,3),(sd1,3),(sd2,5),(sd3,3),(sd4,5),(sd5,3),(sd6,5),(sd7,3),(sd8,5),(sd9,3)]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem pri : ∀ m ∈ mins, Slice true root target m.1 m.2 := by
  intro m hm
  simp only [mins,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sl0
  · exact sl1
  · exact sl2
  · exact sl3
  · exact sl4
  · exact sl5
  · exact sl6
  · exact sl7
  · exact sl8
  · exact sl9
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def ds : Array Entry := #[
  row 5 [0xa0a0a0a,0xaaaaaaaa,0xcccccccc,0xfafafafa,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210c2,0x2c20d20c2061221,0xd40610a42a40b4,0xa40a13082210a1,0xc21c20ca0c2061,0x1210cc0610a41a4,0xac0a40a1310121,0xa10c0061061401,0xa0000000000400,0x610c4,0x610a40610c4061,0xa112c000000000]) [],
  row 5 [0xeeeeeeee,0xfafafafa,0xfcfcfcfc,0xff00ff00,0xffff0000] 4 (replayWords [0x121221308121061,0x22134a061062262,0x72062064264074,0x64061121352061,0x6216206a062064,0x16406c064061062,0x6112a061064061,0x12c062064062400]) [],
  row 5 [0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xfafafafa,0xff00ff00,0xffff0000] 5 (replayWords [0x121221308121062,0x2620720620a1221,0x38c0a10a42a40b4,0xa406122134a061,0x6216206a0620a1,0x1213940a10a41a4,0xac0a4061121352,0x610c2000000000,0x620a4062400062,0x6106112a0a10a4,0xa112c0610a1800,0x610c4000000000]) [(1,0)],
  row 5 [0xa0a0a0a,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210c2,0x2210d20c20a42a4,0xb40a406122134a,0x61062262072062,0xc21210ca0c20a4,0x1a40ac0a4061121,0x35206106216206a,0x620a00a00a4402,0x614010a2061000,0xa10000c4000,0x128000000,0x6106206112a]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfafafafa,0xfcfcfcfc,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210a1,0x22134a0a10c22c2,0xd20c20c42210d4,0xc40a42a40b40a4,0xa11213520a10c2,0x1c20ca0c20c4121,0xcc0c40a41a40ac,0xa40a10c20a1400,0x610000000000a1,0xa40a112c0c20c4,0xc2400062000000,0x640648000a4]) [(1,0)],
  row 5 [0xaaaaaaaa,0xc8c8c8c8,0xf0f0f0f0,0xfafafafa,0xff00ff00,0xffff0000] 5 (replayWords [0x121221308121221,0x3082213080a1221,0x38c0a10612210d4,0x610a42a40b40a4,0x1213101213100a1,0x1213940a1061121,0xcc0610a41a40ac,0xa4401000000000,0x403000000000128,0x610a1,0xc40610a10a4000,0x12c0610c40610a4]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfefefefe,0xff00ff00,0xffff0000] 5 (replayWords [0x121221308121221,0x3082213080a1221,0xd20a10612210d4,0x61062262072062,0x1213101213100a1,0x1210ca0a1061121,0xcc06106216206a,0x62401000000000,0x403000000000128,0x610a1,0xc20610620a40a1,0x620610620610a4]) [],
  row 5 [0xe0e0e0e,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] 5 (replayWords [0x308121121221310,0x221308310308221,0x12112134a061061,0x2212d022134a2d0,0xd0221061061221,0x62062308272262,0x221272072308062,0x622210a10a1308,0x2d20d22212d2221,0x3080a10a1352061,0x611211c8121352,0x1c80c8121061061,0x12106206231016a,0x16212116a06a310,0x620621210a10a1,0x3101ca0ca1211ca,0x1213100a10a1061,0xa00610c0062062,0x610620610c00a0,0xa00610a10610c0,0xc20c00610c2061,0xc00a10a10620c2,0x620a00a10a0062,0xa10620a00c20a0]) [],
  row 5 [0xe0e0e0e,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x121221308121388,0x22130c221061221,0xd4061062262072,0x62221308221308,0x390121314121061,0x1210cc061062162,0x6a062121310121,0x3100610c00c4061,0x620a00a4062000,0xa1000061062,0x610a40610c4061,0xc40620a40620a4]) [],
  row 5 [0xe0e0e0e,0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xff00ff00,0xffff0000] 5 (replayWords [0x121221308121221,0x308221308061221,0x34a061062262072,0x620a10d22210a1,0x121310121310061,0x121352061062162,0x6a0620a10ca121,0xa10c0000000000,0xa0000000000404,0x61062,0x12a0610c2061,0xa10620a10620c2]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfafafafa,0xff00ff00,0xfff0fff0,0xffff0000] 5 (replayWords [0xa12213080a1308,0x2213082211ca308,0x2211ca0612210d4,0x610a42a40b40a4,0x1210000000000a1,0xc20a14060610a1,0xc40610a10a40a1,0x2343941ca0ca0ca,0x611c40cc0610a4,0x1240ac0a41c8061,0x61405062000000,0x610c40610a4]) [],
  row 5 [0xf0e0f0e,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] 4 (replayWords [0x121221308121061,0x2210d0061062262,0x720620a10d2221,0xa10611210cc061,0x6212806a0620a1,0xca1210a1061062,0x610a00610c0061,0xa10620a00620a0]) [],
  row 5 [0xffee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 4 (replayWords [0xa11210ca0a1061,0x1210cc061062128,0x6a062121300121,0x2210610a10c2061,0x620c20a10620a1,0xd20a1221061062,0x611280610c4061,0x221062072062220]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffeeffee,0xffff0000] 5 (replayWords [0x221801221407121,0x2213081210a1221,0xd20a106122130a,0x61062262072062,0x310000000000800,0xa10a14020c4000,0xa4000000,0xa11210ca0a1,0x611210cc061062,0x12806a0620610a1,0xc20610620c20a1,0x62061062061128]) [(11,0),(12,0)],
  row 5 [0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1213003081210a1,0x2d22d20a10612c4,0x2d4061062220230,0x62000000221000,0xa11210ca0a1061,0x121312061062162,0x6a062121310121,0x3100610a10c2061,0x620c20a10620a1,0x2d20a12d2061062,0x6112a0610c4061,0x2d40620a4062230]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (replayWords [0x308121121221310,0x221308310308221,0x12112138c0a10a1,0x2212d222138c2d2,0xd22210a10a1221,0x40722130880e308,0x22180d221308407,0x30834a061061221,0x40022134a80c34a,0x221061061221062,0x62308272262221,0x272072308062062,0x3940a10a11211ca,0x1213941ca0ca121,0xa10a1121406121,0x31080b31012180a,0x121310406310352,0x61061121400121,0x352809352121061,0x61121062062310,0x16a16212116a06a,0x3100620620a1402,0xa18088078060a1,0x8050a1804402402,0xc20610610a1400,0xa10c28030c20a1,0x610610a1062062,0xc28020c20a1801,0xa10c2062062400,0x8000c4000000000,0x0,0x4004000a4000,0x0,0x61400,0x61800062062000,0x40040012a]) [(0,1),(2,0),(3,0),(4,1),(5,1),(6,0),(7,0),(8,0),(9,0),(10,1),(13,0),(14,2),(10,3),(13,2),(14,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xcececece,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210c2,0x2210d20c2221308,0x22130806122134a,0x61062262072062,0xc21210ca0c2121,0x310121310061121,0x35206106216206a,0x620c24010a10a1,0x610e10c2061062,0xa00a40620c4000,0xa4062062,0xa40610620610a4]) [],
  row 5 [0x2020202,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210c2,0x2210d20c20c4221,0xd40c4062262072,0x62221308221308,0xc21210ca0c20c4,0x1210cc0c4062162,0x6a062121310121,0x3100c00c00c2401,0x620a00a4062000,0xa1000060060,0x620a4000000061,0x128000000000]) [],
  row 5 [0xa0a0a0a,0x22222222,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210c2,0x2210d20c20c4221,0xd40c40a42a40b4,0xa4062262072062,0xc21210ca0c20c4,0x1210cc0c40a41a4,0xac0a406216206a,0x620c00c00c2401,0xa00a00a40c2000,0xa1000000000,0x61000060060062,0xc40620a4400062]) [],
  row 5 [0xff0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 4 (replayWords [0xc21211ca0c2061,0x1211cc0610a4128,0x6a06a121300121,0x2210610c00c2061,0xa00a00a40c21ca,0xc20a10a10610c4,0x610a40610c4061,0xc40620621280a4]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xff0aff0a,0xffff0000] 5 (replayWords [0x221800221407121,0x2213081210c2221,0xd20c20612210d4,0x610a42a40b40a4,0x3100000000000c2,0x1ca0a10a10c4061,0x610c4062062128,0xa40c21211ca0c2,0x611211cc0610a4,0x12806a06a0610c0,0xc20610a00a00a4,0xc20610c40610a4]) [(19,0)],
  row 5 [0xa0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1213003081210c2,0x2c20d20c20612c4,0xd40610a42200b4,0xa4000000221000,0xc21210ca0c2061,0x1210cc0610a41a4,0xac0a4121310121,0x3100610c00c2061,0xa00a00a40c2000,0xa10000610c4,0x610a40610c4061,0xc4062000000000]) [],
  row 5 [0xa0a0a0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (replayWords [0x308121121221310,0x221308310308221,0x12112138c0c20c2,0x2212d222138c2d2,0xd22210c20c234a,0x610612212d4221,0x34a2d40d4221061,0x612210a40a4308,0x2b42a42212b40b4,0x3080a40a4221407,0x221308808308221,0x807221308407308,0x3940c20c21211ca,0x1213941ca0ca121,0xc20c2352061061,0x1211cc1213521cc,0xcc121061061121,0xa40a43101ac1a4,0x1211ac0ac3100a4,0xa4121406121310,0x806310121805121,0x3104063100c2061,0x614010c40c00c2,0xc40c2401061061,0x4024020a0000000,0x8040a40a40c2,0x4020c2000000000,0x804402,0xa1000000000061,0xa40610c48030c4,0x618020610c40a4,0xa40614000610c4,0x8010c4061800061,0xc44000c4402402,0x62000000000000,0x0]) [(16,0),(17,0),(3,0),(18,0),(0,0),(20,0),(21,2),(20,2),(21,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffa8a8] 4 (replayWords [0x1212213081210a1,0xa10d20c2061061,0xd40c4062062072,0x1280c21210ca0c2,0xc41210cc0c4072,0x1201210720c00c0,0xc24080720b00b4,0x720700700720b4]) [],
  row 5 [0xa8a8a8a8,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210c2,0x2210d20c20c4221,0xd40c4128220221,0x128407221801221,0xc21210ca0c20c4,0x1210cc0c4120120,0x121230406121800,0x1210c00c00c2404,0x1280c212c0c20a1,0xa14000c21280c4,0x12a0c4061061402,0xc4062000000000]) [(23,2),(23,0)],
  row 5 [0x54545454,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210a1,0x2210d20a1061221,0xd4061128220221,0x12834a22134a221,0xa11210ca0a1061,0x1210cc061120120,0x121230352121352,0x1210610a10c2061,0xa00a00a10c20c2,0xa10c20a1060060,0x610c40c40610c4,0x61000000062000]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfffcfffc,0xffff0000] 5 (replayWords [0x308221308221308,0x2213082210c2221,0xd20c20c42210d4,0xc4062220072062,0x1210000000000a1,0x61000,0x230062062,0x2300c21c20ca0c2,0xc41c40cc0c4062,0x12806a0620c20c4,0xc24050620a40a4,0x620a40620620a4]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff00fc] 4 (replayWords [0x1212213081210a1,0xa10c21ca061061,0xc41cc128062062,0x1280c21211ca0c2,0xc41211cc0c4062,0x1201210620c20c4,0xc24090620a40a4,0x620700620620a4]) [],
  row 5 [0xfcfc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210c2,0x2212d20c20c4221,0x2d40c4062220221,0x6200000034a000,0xc21210ca0c20c4,0x1210cc0c4062120,0x6a062406121800,0x1210c20c40c240a,0x620a40a40620a1,0xa10c22d20a4062,0x620a40610610c4,0x2d4062128062128]) [(27,2)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfcfcfcfc,0xff00ff00,0xffff0000] 6 (replayWords [0x308121121221310,0x221308310308221,0x12112134a40734a,0x22180922134a808,0x34a22140722138c,0xc20c22212d2221,0x38c2d20d22210c2,0xc234a0c40c4221,0x2d422134a2d40d4,0x2210c40c4221062,0x62308230220221,0x230072308062062,0x352406352121807,0x121352806352121,0x4061213940c20c2,0x1211ca1213941ca,0xca1210c20c2352,0xc40c41211cc121,0x3521cc0cc1210c4,0xc4121062062310,0x12812012112806a,0x310062062400400,0xa1000000000000,0x0,0x400402061000000,0x0,0x805128128,0x804062062803062,0x628021281280c2,0x4020c24000c40c4,0x400400,0x4004020620620c2,0xa40a48010a40a4,0xc20620624000a4,0xa40c4062062800,0x620620c40a40a4]) [(4,1),(4,0),(24,0),(6,0),(17,0),(25,0),(26,0),(28,2),(26,2),(28,0)],
  row 5 [0xaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa] 5 (replayWords [0x30012112140b0c2,0xa10a10c20c4061,0x610c4220000000,0x400000000000,0xa11210ca0a1061,0x1210cc061121310,0x121230121310121,0x2210610a10c2061,0xa10c20a10c20a1,0xc20a10c20610c4,0x610c40610c4061,0xc4072000000000]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa,0xffffcccc] 5 (replayWords [0x221308221400121,0x2213101210a10c2,0xc20a1061000000,0x2210720720b4,0x34212112140c0c2,0xa10a10c234a2d4,0xd40d4062000000,0xa11210ca0a1,0x2d4121312121072,0x1721210720c20a1,0xc20a10720c20a1,0x72070070072230]) [],
  row 5 [0xf0a0f0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210c2,0x2210d20c2061221,0xd40610a42a40b4,0xa422138c22138c,0xc21213940c2061,0x1210cc0610a4128,0x6a06a121310121,0x3940610c00c2061,0xa00a00a40c2000,0xa10000610c4,0x610a40610c4061,0xc40620621280a4]) [],
  row 5 [0xcccccccc,0xf0f0f0f0,0xffaaffaa,0xffffaaaa,0xffffff00] 4 (replayWords [0x12112806a06a121,0x1300720720a1121,0x1ca0a10611211cc,0x61062062128406,0xc20a10a10c20c4,0x610610c40c20a1,0xa10c20c4061061,0xc40610a10c2061]) [],
  row 5 [0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffaaffaa,0xffff0000,0xffffaaaa] 5 (replayWords [0x308000000000062,0x62128406128121,0x6a06a0c20a10a1,0xc20c40610610c4,0x221230072072121,0x2218001210a1221,0x2d20a10612212d4,0x61310000000000,0xc20a10a10c20c4,0x610610c40a1121,0x1ca0a10611211cc,0x610610a10c2061]) [(33,0)],
  row 5 [0xaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffaaffaa,0xffff0000] 5 (replayWords [0x220220230407121,0x40b2281210a12c2,0xd20a10612c40d4,0x61000000221000,0x3100000000000c2,0xa10a10c20c4061,0x610c4062000000,0xa11211ca0a1,0x611211cc061121,0x12806a06a0610a1,0xc20610a10c20a1,0xc20610c40610c4]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa,0xffffff00] 5 (replayWords [0x221308221406121,0xa11ca,0x1ca0a10611cc1cc,0x61221230072072,0x3083103084060c2,0xa10a10c20c4061,0x610c4062000000,0xa11ca1ca0a1,0x611cc1cc061130,0x1308002300610a1,0xc20610a10c20a1,0xc20610c40610c4]) [(33,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00aa00,0xffff0000,0xffffaaaa] 5 (replayWords [0x40b00000000040d,0xc20a1,0xa10c20c4061061,0xc4062000000000,0x1212213101210a1,0x2212d20a1061221,0x2d4061221230000,0x720a11213140a1,0x61121312061121,0x3101212300610a1,0xc20610a10c20a1,0xc20610c40610c4]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xffffffaa] 5 (replayWords [0x40b00000000040d,0xc20a1,0xa10c20c4061061,0xc4062000000000,0x1212213081210a1,0x2212d20a1061221,0x2d4061128230072,0x720a11211ca0a1,0x611211cc061121,0x12806a06a0610a1,0xc20610a10c20a1,0xc20610c40610c4]) [],
  row 5 [0xffaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 5 (replayWords [0x3840a10a11211ca,0x1213841ca1ca121,0xa10a1342061061,0x1211cc1213421cc,0x1cc121061061121,0x220121300128128,0x12112806a300220,0x6a121221121300,0x308300121308121,0x3002212210c2061,0x610a10c40a10c2,0xc40c20a1061061,0xa11280a10c21ac,0xc20a11ac0a10c2,0x1280c20a12210a1,0xc238c0c20a138c,0xa10c22210c2061,0x1280610c416a0c4,0x6116a0610c4128,0xc40612210610c4,0x34a0c406134a061,0xc42210c4128308,0x62220221062128,0x221128220308220]) [],
  row 5 [0xffaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1213003101210a1,0x2c20d20a10612c4,0xd4061128220230,0x128000000221000,0xa11211ca0a1061,0x1211cc061121128,0x6a06a121310121,0x3100610a10c2061,0xa10c20a10c20a1,0xc20a10c20610c4,0x610c40610c4061,0xc4062062128230]) [],
  row 5 [0xffaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffaaffaa] 5 (replayWords [0x3000000000000c2,0xa10a10c20c4061,0x610c4220000000,0x40e000000000,0xa11211ca0a1061,0x1211cc061121128,0x6a121308121,0x2210610a10c2061,0xa10c20a10c20a1,0xc20a10c20610c4,0x610c40610c4061,0xc4128221128308]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffaaffaa,0xffff0000] 6 (replayWords [0x22140722180e80d,0x80c22180b22180a,0x407407308121121,0x221406221308809,0x30822112112138c,0xa10a12212d2221,0x38c2d20d22210a1,0xa134a061061221,0x2d422134a2d40d4,0x221061061221128,0x128308808308221,0x807221308128128,0x406800310000000,0x0,0x8060c20c2,0x4020a10a18050a1,0xa14020c20c2804,0xc40c4400061061,0x8030610614000c4,0xc4406406062000,0x0,0x4060a1,0xa11211ca121802,0x1ca1ca1210a10a1,0x4060610611211cc,0x1218011cc1cc121,0x61061121406121,0x800128128000000,0x40640606a0c2,0x610610a10c40a1,0xc20c40c20a1061,0x610a11280a10c2,0x1ac0c20a11ac0a1,0xc21280c2061128,0x610c416a0c4061,0x16a0610c41280c4]) [(30,2),(31,2),(31,3),(13,0),(32,1),(13,1),(32,0),(34,0),(35,0),(36,2),(37,2),(38,0),(39,0),(40,0),(41,0)],
  row 5 [0xc0c0e0e,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] 4 (replayWords [0x121300308121061,0x2610d0061062220,0x720620a10d2221,0xa10611210c8061,0x6216206a0620a1,0xca1210a1061062,0x610a00610c0061,0xa10620a00620a0]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xcccceeee,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1213003081210a1,0x2c20d20a134a308,0x22122106126134a,0x61062220072062,0xa11210ca0a1121,0x310121310061121,0x35206106216206a,0x620a18000a1402,0x610a10c2061062,0xc20a10620c4000,0xa4062062,0x23006106206112a]) [(43,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xff00ffaa,0xffff0000] 5 (replayWords [0x30840b221221121,0x3213081210a12c2,0xd20a10612c40d4,0x61128220230128,0x3100000000000c2,0xa10a10c20c4061,0x610c4062062128,0x2300a11211ca0a1,0x611211cc061121,0x12806a06a0610a1,0xc20610a10c20a1,0xc20610c40610c4]) [],
  row 5 [0xaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x30030030840b0a1,0x2c20d20a10612c4,0xd4061128220230,0x128000000221000,0xa11c20ca0a1061,0x1c40cc061120120,0x128230000000121,0x610a10c2061,0xa10c20a10c20a1,0xc20a10c20610c4,0x610c40610c4061,0xc4062000000000]) [],
  row 5 [0xaaaa,0xaa00aa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x30030030840b0a1,0x2c20d20a10612c4,0xd4061220220230,0x308000000221000,0xa11c20ca0a1061,0x1c40cc061000000,0x121000120120128,0x3100610a10c2061,0xa10c20a10c20a1,0xc20a10c20610c4,0x610c40610c4061,0xc4062062406128]) [],
  row 5 [0xaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (replayWords [0x30812112140b310,0x30030831030840b,0x12112138c0a10a1,0x3082d22c238c2d2,0xd23080a10a134a,0x610613082d42c4,0x34a2d40d4308061,0x61407407220000,0x808230230,0x308407308000000,0x808,0x407221000000000,0x3940a10a11211ca,0x1213941ca0ca121,0xa10a1352061061,0x1211cc1213521cc,0xcc121061061121,0x230121310807310,0x121806121310230,0x230121406121310,0x805310121804121,0x3104063100c2061,0x610a10c40a10c2,0xc40c20a1061061,0xa12300a10c22b4,0xc20a12b40a10c2,0x2300c20a14020a1,0xc28030c20a1802,0xa10c24020c2061,0x2300610c42720c4,0x612720610c4230,0xc40614000610c4,0x8010c4061800061,0xc44000c4407407,0x62000000000000,0x0]) [(44,0),(21,1),(44,1),(21,0),(45,0),(46,0),(35,0),(47,0),(30,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffcccc,0xfffff0f0] 5 (replayWords [0x22122134a400121,0x3103101210a1000,0x34a0d40d4,0x30a0620a4072062,0x12131031012138c,0xd20d230c061000,0xa4062062,0xa40d21213140d2,0xd41213120d4062,0x12006a0620d00d0,0xd240f0620a40a4,0x620a40620620a4]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfaf8faf8,0xff00ff00,0xffff0000] 4 (replayWords [0x3002213082210a1,0x2210d20a10c4221,0xd40c40a42200b4,0xa40a11210ca0a1,0xc41c40cc0c40a4,0x1240ac0a4061061,0xc20a10620620a1,0xc20640642320a4]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaa88] 4 (replayWords [0x1211213082210a1,0x2210d20a1061061,0xd40c4062062072,0xa40a11c20ca0a1,0xc41c40cc0c4072,0x1300ac0720c00a1,0xc20a10720a00a1,0x720700700720a4]) [],
  row 5 [0xaa88aa88,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x3002213082210a1,0x2210d20a10c4221,0xd40c40a42200b4,0xa4407221801221,0xa11c20ca0a10c4,0x1c40cc0c40a4310,0xac0a4121121400,0x3100c00a10c20a1,0xa00a00a10c2402,0xa18000a10a40c4,0x2320a4061061406,0xc4062000000000]) [(50,0),(51,0)],
  row 5 [0x55445544,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210a1,0x2210d20a1061221,0x30a0610a42200b4,0xa4308221308221,0xa11210ca0a1061,0x1210cc0610a4120,0x1210a4310121352,0x1210610a10c2061,0xa00a00a10c20c2,0xa10c20a1060060,0x610a40c40611cc,0x61000000062000]) [],
  row 5 [0xf0c0f0c,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x3082213082210a1,0x22138c0a10c4221,0xd40c4062220072,0x62308221308221,0xa11a13940a10c4,0x1c40cc0c4062128,0x6a062121121352,0x3940c00a10c40a1,0x620a00a1062000,0xc20000a4062,0x620a4061061410,0xc40620a40620a4]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xff00ff00,0xfff0fff0,0xffff0000,0xfffff0f0] 5 (replayWords [0x2210000000000a1,0xa11ca4061ca314,0xca0ca0610c40c4,0x610620a40a4062,0x30c2d20d20d2304,0x30430c4110612c4,0xd40610622300b4,0x62121000000000,0x610c40c4061062,0xa40a40620611c4,0xcc0610621280ac,0x620600600610a4]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xffffffcc] 5 (replayWords [0x221000000000121,0xa10c2,0xc20a1061000000,0xa40620620a4,0x30831030840c0a1,0x2c20d20a11cc2d4,0xd40d4062230072,0x620a11c20ca0a1,0x2d41cc0cc0cc062,0x12806a0620c20a1,0xc20a10620a00a1,0x620a40620620a4]) [],
  row 5 [0xffcc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x3002213102210a1,0x2212d20a11cc221,0x2d41cc0622200b4,0x62000000308000,0xa11c20ca0a12d4,0x1cc0cc0cc062128,0x6a062121121400,0x3100c20a10c20a1,0x620a00a10620c2,0xa10c20a10a4062,0x620a40610611cc,0x2d40620a40620a4]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffccffcc,0xffff0000] 6 (replayWords [0x30840730822180b,0x22130880a308221,0x407221308412308,0x221352221308352,0x30822140622138c,0xa10a12212d2221,0x38c2d20d22210a1,0xa134a1cc1cc221,0x40022134a80930a,0x2211cc1cc221062,0x62308230220221,0x230072308062062,0x400400121000000,0x0,0x8080a10a1,0x4020c20c28070c2,0xc24020a10a1400,0x406061000000000,0x0,0x8060a40a4805,0x62062804062062,0x8030a40a44060a1,0xa13521ca1c2802,0x1ca0ca3520a10a1,0x3524063524001cc,0x1cc000000000400,0x4000cc406062062,0x352128128801128,0x6a3520620620c2,0x4100c20a11cc0a1,0xc21cc0c20a1400,0xa10a10620620c2,0xa40a00a10a40a1,0xc20620624000a4,0xa41cc062062800,0x620621cc0a40a4]) [(10,1),(31,2),(49,2),(52,0),(13,0),(21,3),(53,0),(26,0),(54,0),(55,1),(56,0),(57,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfafafaf0,0xff00ff00,0xffff0000] 4 (replayWords [0x3003003084130a1,0x2210d20a10612c4,0xd4061062224072,0x620a11210ca0a1,0x611c40cc061062,0x12406a0620610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 5 [0xaaaaaa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x30030030840e0a1,0x2c20d20a10612c4,0xd4061062308072,0x62221221406308,0xa11c20ca0a1061,0x1c40cc061062310,0x6a062121121407,0x3100610a10c2061,0x620a00a1062402,0xa18010a1060060,0x610a4400061800,0x61128000000000]) [(59,1),(59,0)],
  row 5 [0x55555500,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210a1,0x2212d20a1061221,0x2d4061062220221,0x62308221308221,0xa11211ca0a1061,0x1211cc061062120,0x121062310121310,0x1210610a10c2061,0x620a00a10621ca,0xa11ca0a1060060,0x610a41cc0611cc,0x61000000128000]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf3f3f3f0,0xff00ff00,0xffff0000] 4 (replayWords [0x3043043084140a1,0x2210d20a1061261,0xd0061062224072,0x620a11210ca0a1,0x611610c8061062,0x12406a0620610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 5 [0xf0f0f00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x3083103084150a1,0x2a138c0a10612c4,0xd40610622300b4,0x6222122130838c,0xa11a13940a1061,0x1c40cc061062128,0xac062121121310,0x3940610a10c2061,0x620a00a1062000,0x1ca000060060,0x610a4400061800,0x61128062128062]) [(62,1)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xffffff00] 6 (replayWords [0x406406221000000,0x0,0x406407121,0x0,0x809,0xa10a14021ca1ca,0x8081ca1ca4020a1,0xa1807061061400,0x1cc1cc8061cc1cc,0x400061061805062,0x62804128128803,0x128128802062062,0x308407308406310,0x310000000000406,0x40640638c0a10a1,0x3082d22d238c2d2,0x2d23080a10a134a,0x610613082d42d4,0x34a2d42d4308061,0x61407062062308,0x230230801230230,0x3080620623940a1,0xa13101ca1ca394,0x1ca1ca3100a10a1,0x3520610613101cc,0x1cc3521cc1cc310,0x61061406062062,0x310128128800128,0x1283100620620c2,0x610610a10c40a1,0xc20c40c20a1061,0x610a10620620c2,0xa40a00a10a40a1,0xc20620620610a4,0x600c4062060061,0x620610c40a40a4]) [(36,2),(36,0),(60,0),(38,0),(46,0),(61,0),(56,0),(63,1),(56,1),(63,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (replayWords [0x407308121121406,0x22131022180d308,0x310308406221121,0x12140738c0a10a1,0x4022212d222180c,0x38c2d20d2402221,0xa10a140734a061,0x614002212d4221,0x80b34a2d40d4400,0x221061061407221,0x6206280a308230,0x220809221230072,0x407308062062406,0x3940a10a1402121,0x1ca1218083941ca,0xca4021210a10a1,0x406352061061400,0x1211cc121807352,0x1cc0cc400121061,0x61406121062062,0x806310128120805,0x12112806a406310,0x620624020c2061,0x614000a10c40a1,0x8040c20c40c2400,0xa10610614020a1,0x620628030c20a4,0xa08020a10a40a1,0x4020c2062062400,0x610a40608010c4,0x62060800061062,0x614000c40a40a4]) [(15,0),(22,1),(15,1),(22,0),(29,0),(42,0),(48,2),(58,0),(58,1),(42,2),(48,0),(58,2),(58,3),(64,0)]
]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def states (i : Nat) := ds[i]?.getD default
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def ms : Array (List (Fin 4)) := #[[],[1],[3],[3,1]]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def perm (i : Nat) := permitted (ms[i]?.getD [])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def specTab : Array Spec := #[(2,[]),(2,[(2,0,1)]),(4,[]),(4,[(2,0,1)]),(2,[(0,0,1)]),(2,[(1,1,2)]),(6,[]),(8,[]),(2,[(0,0,1),(1,3,4)]),(2,[(2,1,2),(1,3,4)]),(2,[(2,1,3)]),(6,[(2,0,3)]),(6,[(1,1,3)]),(8,[(2,0,3)]),(6,[(0,0,3)]),(2,[(1,1,3)]),(4,[(1,1,2)]),(6,[(1,2,3)]),(8,[(1,1,3)]),(6,[(0,0,3),(1,2,4)]),(6,[(3,1,3),(1,2,4)]),(6,[(3,2,3)])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def spec (i : Nat) := specTab[i]?.getD (0,[])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def checked (i : Nat) := nodeOK target root mins spec states perm i
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block0 : Good checked 0 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block1 : Good checked 4 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block2 : Good checked 8 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block3 : Good checked 12 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block4 : Good checked 16 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block5 : Good checked 20 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block6 : Good checked 24 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block7 : Good checked 28 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block8 : Good checked 32 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block9 : Good checked 36 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block10 : Good checked 40 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block11 : Good checked 44 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block12 : Good checked 48 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block13 : Good checked 52 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block14 : Good checked 56 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block15 : Good checked 60 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block16 : Good checked 64 2 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem total : Good checked 0 66 := (concatGood (concatGood (concatGood (concatGood block0 block1) (concatGood block2 block3)) (concatGood (concatGood block4 block5) (concatGood block6 block7))) (concatGood (concatGood (concatGood block8 block9) (concatGood block10 block11)) (concatGood (concatGood block12 block13) (concatGood block14 (concatGood block15 block16)))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem impossible : Impossible true target 7 root.toFinset := by
  have h := certified (states:=states) (perm:=perm) (specs:=spec) (N:=66) (fun j => perm_onto _) pri (fun i hi => total i (by omega) hi) 65 (by decide)
  exact h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def essentials : List (Sig × Row × Row) := [(root.getD 0 zero,2,3),(root.getD 1 zero,1,3),(root.getD 2 zero,1,5),(root.getD 3 zero,1,9),(root.getD 4 zero,1,17)]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower : Lower true root target 8 := by
  apply lower_impossible (L:=7) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=essentials) (by decide +kernel) a
    exact (show (essentials.map Prod.fst).toFinset = root.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact impossible

end TabBowtie

namespace ASub10782
open Core Bound10782
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem baseBow : Lower true (inputs.take 5) bowGoal 8 := TabBowtie.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffeeefaa8a5 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 5) vffeeefaa8a5 8 := by
  exact lift_ok (ms:=[swapNext 2, swapNext 3]) (xs:=[]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) baseBow
end ASub10782

namespace Compact10782
open Core GateForest12127 FirstGate12127
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def matching (r : Row) : List Sig → Sig
  | [] => one
  | v :: ws => (if bit r v then v else ~~~v) &&& matching r ws

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem separated {r s : Row} {a : Sig} {ws : List Sig} (mem : a ∈ ws)
    (diff : bit s a ≠ bit r a) : bit s (matching r ws) = false := by
  induction ws with
  | nil => simp at mem
  | cons v vs ih =>
    rcases List.mem_cons.mp mem with rfl | hm
    · cases h : bit r a <;> cases hs : bit s a <;> simp_all [matching,bit,s.isLt]
    · have tail := ih hm
      change ((if bit r v then v else ~~~v) &&& matching r vs).getLsbD s.val = false
      rw [BitVec.getLsbD_and,show (matching r vs).getLsbD s.val = false from tail]
      simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def collision (T : Sig) (rs : List Row) (ws : List Sig) :=
  rs.any fun r => !bit r T && (T &&& matching r ws != zero)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem collision_sound {T rs ws cap} (bad : collision T rs ws = true) :
    Impossible true T cap ws.toFinset := by
  obtain ⟨r,_,test⟩ := List.any_eq_true.mp bad
  simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne] at test
  intro k hk live
  apply test.2
  apply bit_ext
  intro s
  change (T &&& matching r ws).getLsbD s.val = zero.getLsbD s.val
  rw [BitVec.getLsbD_and]
  cases hs : bit s T with
  | false =>
    rw [show T.getLsbD s.val = false from hs, Bool.false_and]
    simp [zero]
  | true =>
    have ds : bit s T ≠ bit r T := by simp [hs,test.1]
    obtain ⟨a,ha,hd⟩ := live_row_difference live ds
    have tail := separated (List.mem_toFinset.mp ha) hd
    rw [show (matching r ws).getLsbD s.val = false from tail, Bool.and_false]
    simp [zero]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def fullPool (raw : List Sig) (mins : List (Sig × Nat)) (s : Spec) (ws : List Sig) (k : Nat) :=
  match mins[s.1]? with
  | none => false
  | some m =>
    let cs := rawChoices raw s.2
    match makePool true m.1 raw cs with
    | none => false
    | some pool => poolCut true m.1 m.2 k cs.length pool ws

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem fullPool_sound {T raw mins s ws cap} (nd : ws.Nodup)
    (lo : ∀ p ∈ mins, Slice true raw T p.1 p.2)
    (ok : fullPool raw mins s ws cap=true) : Impossible true T cap ws.toFinset := by
  unfold fullPool at ok
  split at ok
  · contradiction
  rename_i m h
  dsimp only at ok
  split at ok
  · contradiction
  rename_i pool eq
  exact poolCut_sound (lo _ (List.mem_of_getElem? h)) _ eq nd ok

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def label (e : Entry) (a b : Sig) (op : Nat) (ka kb : Bool) :=
  let n := e.ws.length
  let span := if e.cap+1≤n then 1 else if e.cap≤n then 3 else 4
  let ai := e.ws.idxOf a
  let bi := e.ws.idxOf b
  let pos := ((bi*(bi-1)/2+ai)*4+op)*span+2*ka.toNat+kb.toNat
  let width := e.bits &&& 15
  (e.bits >>> (4+width*pos)) &&& ((1<<<width)-1)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def step (T : Sig) (negRows : List Row) (raw : List Sig) (mins : List (Sig × Nat)) (spec : Nat → Spec)
    (entries : Nat → Entry) (book : Nat → List Nat) (perm : Nat → List Move) (i : Nat)
    (a b : Sig) (op : Nat) (ka kb : Bool) (ws : List Sig) :=
  let e := entries i
  let k := e.cap-1
  if ws.length>k+1 then true else
  match label e a b op ka kb with
  | 0 => collision T negRows ws
  | w+1 =>
    let key := (book i).getD w 0
    if key % 2=0 then fullPool raw mins (spec (key/2)) ws k else
    match e.links[key/2]? with
    | some ptr => linked T entries perm i ptr k ws
    | none => false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem step_sound {T negRows raw mins spec entries book perm i a b op ka kb ws}
    (nd : ws.Nodup) (onto : ∀ j, Function.Surjective (movedRow (perm j)))
    (minOk : ∀ p ∈ mins, Slice true raw T p.1 p.2)
    (prev : ∀ j < i, Impossible true T (entries j).cap (entries j).ws.toFinset)
    (ok : step T negRows raw mins spec entries book perm i a b op ka kb ws=true) :
    Impossible true T ((entries i).cap-1) ws.toFinset := by
  unfold step at ok
  dsimp only at ok
  split at ok
  · exact size_sound nd (by assumption)
  split at ok
  · exact collision_sound ok
  · split at ok
    · exact fullPool_sound nd minOk ok
    · split at ok
      · exact link_sound onto prev ok
      · contradiction

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def good (T : Sig) (negRows : List Row) (raw : List Sig) (mins : List (Sig × Nat))
    (spec : Nat → Spec) (entries : Nat → Entry) (book : Nat → List Nat) (perm : Nat → List Move) (i : Nat) :=
  let e := entries i
  decide e.ws.Nodup && !e.ws.contains T &&
    taggedLayer (step T negRows raw mins spec entries book perm i) e.ws

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem certifiedA {T negRows raw mins spec entries book perm N}
    (onto : ∀ j, Function.Surjective (movedRow (perm j)))
    (minOk : ∀ p ∈ mins, Slice true raw T p.1 p.2)
    (ok : ∀ i < N, good T negRows raw mins spec entries book perm i = true) :
    ∀ i < N, Impossible true T (entries i).cap (entries i).ws.toFinset := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    have g := ok _ hi
    simp only [good,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at g
    exact tagged_sound g.1.1 g.1.2
      (fun _ _ _ _ _ _ nd v => step_sound nd onto minOk (fun j hj => ih j hj (by omega)) v) g.2

end Compact10782

namespace AMin10782
open Core Bound10782 ASub10782 CertBlocks12127
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom0 := stamp 6 0xffff0000ffff
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut0 : Slice true in6 branchA dom0 8 :=
  slice_correct (ms:=[forceLow 5, swapNext 0, swapNext 1, swapNext 2, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffeeafee8a5 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom1 := stamp 6 0xff00ff00ff00ff
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut1 : Slice true in6 branchA dom1 8 :=
  slice_correct (ms:=[forceLow 5, swapNext 0, swapNext 1, swapNext 2, swapNext 4, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffeeafee8a5 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom2 := stamp 6 0xf0f0f0f0f0f0f0f
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut2 : Slice true in6 branchA dom2 8 :=
  slice_correct (ms:=[forceLow 5, swapNext 0, swapNext 3, swapNext 2, swapNext 1, swapNext 4, swapNext 3, swapNext 2, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffeeefaa8a5 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom3 := stamp 6 0x3333333333333333
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut3 : Slice true in6 branchA dom3 8 :=
  slice_correct (ms:=[forceLow 5, swapNext 0, swapNext 4, swapNext 3, swapNext 2, swapNext 1, swapNext 4, swapNext 3, swapNext 2, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffeeefaa8a5 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom4 := stamp 6 0x5555555555555555
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut4 : Slice true in6 branchA dom4 8 :=
  slice_correct (ms:=[forceLow 5, swapNext 4, swapNext 3, swapNext 2, swapNext 1, swapNext 0, swapNext 1, swapNext 4, swapNext 3, swapNext 2, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffeeefaa8a5 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom5 := stamp 6 0xff000000ff
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut5 : Slice true in6 branchA dom5 7 :=
  slice_correct (ms:=[forceLow 4, forceLow 5, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffee8a4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom6 := stamp 6 0xffffffff
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut6 : Slice true in6 branchA dom6 6 :=
  slice_correct (ms:=[forceLow 5, swapNext 0, swapNext 1, swapNext 2]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffeeafcc0a5 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom7 := stamp 6 0xffff0000ffff0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut7 : Slice true in6 branchA dom7 6 :=
  slice_correct (ms:=[forceHigh 5, swapNext 1, swapNext 0, swapNext 2, swapNext 1, swapNext 3, swapNext 2, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffffefeeea5 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom8 := stamp 6 0xff00ff00ff00ff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut8 : Slice true in6 branchA dom8 6 :=
  slice_correct (ms:=[forceHigh 5, swapNext 1, swapNext 0, swapNext 2, swapNext 1, swapNext 3, swapNext 2, swapNext 4, swapNext 3]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffffefeeea5 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom9 := stamp 6 0xffff0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut9 : Slice true in6 branchA dom9 5 :=
  slice_correct (ms:=[forceHigh 4, forceLow 5, swapNext 0, swapNext 1, swapNext 2]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffeeaa4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom10 := stamp 6 0xff000000ff0000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut10 : Slice true in6 branchA dom10 5 :=
  slice_correct (ms:=[forceLow 4, forceHigh 5, swapNext 0, swapNext 1, swapNext 2, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffeeaa4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom11 := stamp 6 0xff00ff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut11 : Slice true in6 branchA dom11 5 :=
  slice_correct (ms:=[forceHigh 4, forceLow 5, swapNext 0, swapNext 1, swapNext 2, swapNext 3]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffeeaa4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom12 := stamp 6 0xff000000ff00
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut12 : Slice true in6 branchA dom12 5 :=
  slice_correct (ms:=[forceHigh 4, forceLow 5, swapNext 0, swapNext 1, swapNext 2, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (ffeeaa4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom13 := stamp 6 0xf0f00000f0f
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut13 : Slice true in6 branchA dom13 5 :=
  slice_correct (ms:=[forceLow 4, forceLow 5, swapNext 0, swapNext 1, swapNext 3, swapNext 2, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (feae8a4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom14 := stamp 6 0xf000f000f000f
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut14 : Slice true in6 branchA dom14 5 :=
  slice_correct (ms:=[forceLow 4, forceLow 5, swapNext 0, swapNext 1, swapNext 3, swapNext 2, swapNext 4, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (feae8a4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom15 := stamp 6 0x333300003333
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut15 : Slice true in6 branchA dom15 5 :=
  slice_correct (ms:=[forceLow 4, forceLow 5, swapNext 0, swapNext 3, swapNext 2, swapNext 1, swapNext 2, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (feae8a4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom16 := stamp 6 0x33003300330033
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut16 : Slice true in6 branchA dom16 5 :=
  slice_correct (ms:=[forceLow 4, forceLow 5, swapNext 0, swapNext 3, swapNext 2, swapNext 1, swapNext 2, swapNext 4, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (feae8a4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom17 := stamp 6 0x303030303030303
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut17 : Slice true in6 branchA dom17 5 :=
  slice_correct (ms:=[forceLow 4, forceLow 5, swapNext 2, swapNext 1, swapNext 0, swapNext 3, swapNext 2, swapNext 1, swapNext 4, swapNext 3, swapNext 2, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (feae8a4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom18 := stamp 6 0x555500005555
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut18 : Slice true in6 branchA dom18 5 :=
  slice_correct (ms:=[forceLow 4, forceLow 5, swapNext 3, swapNext 2, swapNext 1, swapNext 0, swapNext 1, swapNext 2, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (feae8a4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom19 := stamp 6 0x55005500550055
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut19 : Slice true in6 branchA dom19 5 :=
  slice_correct (ms:=[forceLow 4, forceLow 5, swapNext 3, swapNext 2, swapNext 1, swapNext 0, swapNext 1, swapNext 2, swapNext 4, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (feae8a4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom20 := stamp 6 0x505050505050505
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut20 : Slice true in6 branchA dom20 5 :=
  slice_correct (ms:=[forceLow 4, forceLow 5, swapNext 3, swapNext 2, swapNext 1, swapNext 0, swapNext 3, swapNext 2, swapNext 1, swapNext 4, swapNext 3, swapNext 2, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (feae8a4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom21 := stamp 6 0x1111111111111111
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut21 : Slice true in6 branchA dom21 5 :=
  slice_correct (ms:=[forceLow 4, forceLow 5, swapNext 3, swapNext 2, swapNext 1, swapNext 0, swapNext 4, swapNext 3, swapNext 2, swapNext 1, swapNext 4, swapNext 3, swapNext 2, swapNext 3, swapNext 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (feae8a4 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom22 := stamp 6 0xffff
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut22 : Slice true in6 branchA dom22 4 :=
  slice_correct (ms:=[forceLow 3, forceLow 4, forceLow 5]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (fe8a3 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom23 := stamp 6 0xff00ff
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut23 : Slice true in6 branchA dom23 4 :=
  slice_correct (ms:=[forceLow 3, forceLow 4, forceLow 5]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (fe8a3 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom24 := stamp 6 0xff
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut24 : Slice true in6 branchA dom24 4 :=
  slice_correct (ms:=[forceLow 3, forceLow 4, forceLow 5]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (fe8a3 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def dom25 := stamp 6 0x101010101010101
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem cut25 : Slice true in6 branchA dom25 4 :=
  slice_correct (ms:=[forceLow 3, forceLow 4, forceLow 5, swapNext 2, swapNext 1, swapNext 0, swapNext 3, swapNext 2, swapNext 1, swapNext 4, swapNext 3, swapNext 2]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) (fe8a3 verified4)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def mins : List (Sig × Nat) := [(dom0,8),(dom1,8),(dom2,8),(dom3,8),(dom4,8),(dom5,7),(dom6,6),(dom7,6),(dom8,6),(dom9,5),(dom10,5),(dom11,5),(dom12,5),(dom13,5),(dom14,5),(dom15,5),(dom16,5),(dom17,5),(dom18,5),(dom19,5),(dom20,5),(dom21,5),(dom22,4),(dom23,4),(dom24,4),(dom25,4)]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem prior : ∀ m ∈ mins, Slice true in6 branchA m.1 m.2 := by
  intro m hm
  simp only [mins,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cut0
  · exact cut1
  · exact cut2
  · exact cut3
  · exact cut4
  · exact cut5
  · exact cut6
  · exact cut7
  · exact cut8
  · exact cut9
  · exact cut10
  · exact cut11
  · exact cut12
  · exact cut13
  · exact cut14
  · exact cut15
  · exact cut16
  · exact cut17
  · exact cut18
  · exact cut19
  · exact cut20
  · exact cut21
  · exact cut22
  · exact cut23
  · exact cut24
  · exact cut25

end AMin10782

namespace ATable10782
open Core Bound10782 GateForest12127 CertBlocks12127 Compact10782 AMin10782
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def wireBank : Array Nat := #[0xeeeeeeeeeeeeeeee,0xfafafafafafafafa,0xff00ff00ff00ff00,0xfffcfcfcfffcfcfc,0xffff0000ffff0000,0xffffffff00000000,0xfcfcfcfcfcfcfcfc,0xffffff00ffffff00,0xffffffffff000000,0xff000000ff000000,0xffffff00000000,0xff000000ff00,0x303030302020202,0xfffffffffafafafa,0xfffffffffcfcfcfc,0xfffcfffcfcfcfcfc,0xffffff00ffff0000,0xff00ff00ff00,0xff00ff0000000000,0xff00ff00ff000000,0xffff0000ff00,0xffffffffff00ff00,0xff00ff00,0xfcfcfffffcfcfcfc,0xffff00000000,0xffffffffaaaaaaaa,0xfffffffff0f0f0f0,0xffffffffcccccccc,0xf0f0f0f0a0a0a0a,0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0e0e0e0e,0xffffffffeeeeeeee,0xccccffffcccccccc,0xfefefefefefefefe,0xfffffffffefefefe,0xf0f0f0f0f0f0f0f0,0xf0f0fffff0f0f0f0,0xe0e0f0f0e0e0e0e,0xfefefffffefefefe,0xfff0fff0fff0fff0,0xffffffff0e0e0e0e,0xe0e0e0e0e0e0e0e,0xfffff0f0fffff0f0,0xffffffffffff0000,0xfffefffe0e0e0e0e,0xfffcfffccccccccc,0xfffffff0ffff0000,0xfff0fff000000000,0xf0f00000000,0xf0f0f0f00000000,0xabababab88888888,0xafafafafaaaaaaaa,0xcfcfcfcfcccccccc,0xff0f0000ff00,0xff0fff0fff00ff00,0xf0f0f0f0f000f00,0xe0effff0e0e0e0e,0xf0e0f0e0f0e0f0e,0xffeeffeeffeeffee,0xfffcfffcfffcfffc,0xfffefffef0f0f0f0,0xfffafffa00000000,0xffeeffee,0xfffafffafffafffa,0xffeeffee00000000,0xffffeeeeffffeeee,0xfffefffef8f8f8f8,0xffffffff88888888,0x8888888888888888,0xeaeaeaeaeaeaeaea,0xfffffffcffff0000,0xffffffffc0c0c0c0,0xffffffeeffff0000,0x707070707060706,0xf0f0f0f0f0e0f0e,0xffff0000ffee,0xf8f8f8f8f8f8f8f8,0xffffffffffeeffee,0x30300000000,0xffff00eeffff00ee,0xeeee0000eeee,0xffaaffaaffaaffaa,0xffccffccffccffcc,0xfffcfffcf0f0f0f0,0xfffefffefcfcfcfc,0xfffefffeeeeeeeee,0xffffffaaffff0000,0x303030303020302,0xc0c0c0c0c0c0c0c0,0xffff0000ffaa,0xfffffffffff0fff0,0xffaaffaa,0xf0f0f3f3f0f0f0f0,0xeeeeefefeeeeeeee,0xfdfcfdfcfdfcfdfc,0xf000f000f000f00,0xabaaabaaabaaabaa,0x300030003000300,0xfff0f0f0fff0f0f0,0xfffffffffff0f0f0,0xffffff00aaaaaa,0xf0f0f0f0c0c0c0c,0x303030300000000,0xff00ff00cc00cc00,0xff00ff00ff00cc00,0xffffffffffccffcc,0xf000f00,0xffff0000aaaa,0xfff0fff0f0f0f0f0,0x3333333322222222,0xddddddddcccccccc,0xf3f3f3f3f2f2f2f2,0xafafafafaeaeaeae,0xf0f0f0f0f0a0f0a,0xfcfcfcfcf8f8f8f8,0xcccccccc88888888,0xfefefefef0f0f0f0,0xffffeeeeffff0000,0xeeeeeeee00000000,0x5555555550505050,0xccccccccc8c8c8c8,0x3333333332323232,0xf0f0f0f1f0e1f0e,0xf0f0f0f0e0e0e0e0,0xaaaaaaaaa8a8a8a8,0xfffffffffffcfffc,0xffff0000eeee,0xf000f000e000e00,0xff000f00ff000e00,0xff0f0000ff0e,0xff0fff0fff0eff0e,0xf0f00000e0e,0xf000f000f100f100,0xff0f0f0fff0e0e0e,0xf0f0f000e0e0e,0xffccccccffcccccc,0xf0f0e0e0e0e,0xffccffcccccccccc,0x505050504040404,0xff00ff00ee00ee00,0xff00ff00ff00ee00,0x3000300,0x5555555554545454,0xefefefefeeeeeeee,0x101010100000000,0x1f0f1f0f1f0e1f0e,0xeeeeeeee,0xababababaaaaaaaa,0xf3f3f3f3f0f0f0f0,0xff030000ff00,0xff11ff11ff00ff00,0xf0f0fffff0f0fafa,0xeeeeffffeeeefefe,0xb0b0b0b0a0a0a0a,0xbbbbbbbbaaaaaaaa,0xf5f5f5f5f0f0f0f0,0xfbfbfbfbfafafafa,0xeeeeffffeeeeeeee,0x303030303000300,0xefefefefefeeefee,0xa0a0f0f0a0a0a0a,0xaaaaffffaaaaaaaa,0xa0a0a0a0a0a0a0a,0xc0c0f0f0c0c0c0c,0xc8c8ccccc8c8c8c8,0xfafafffffafafafa,0xa8a8aaaaa8a8a8a8,0xe0f0e0f0e0e0e0e,0x606070706060606,0xeeee0000eeeeeeee,0x202030302020202,0xf0a0f0a0f0a0f0a,0xffffaaaaffffaaaa,0xffffccccffffcccc,0xdddcdddcdddcdddc,0xf3f2f3f2f3f2f3f2,0xffffffffafaeafae,0xafaeafae,0xafaeafaeafaeafae,0xf0f0f0f03020302,0xffffffff0f0a0f0a,0xaaaaafafa0a0a0a0,0xaaaaafaf88888c8c,0x3333333333003300,0xfff0fff0aaa0aaa0,0xffaaffaacc88cc88,0xf0a0f0a,0xafafafafafaaafaa,0xeeeaeeeaeaeaeaea,0xeeeceeececececec,0xaaa8aaa888888888,0xf0e0f0e0e0e0e0e,0xfffafffaf0f0f0f0,0x2020a0a0a0a,0xfffffcfcf0f0f0f0,0xf0e0f0e0a0a0a0a,0xffeeffeeaaaaaaaa,0xffffffccffff0000,0xffaaffaa00000000,0xafafafafafaeafae,0xf0f0f0f0f0c0f0c,0xc0c0c0c0c0c0c0c,0xffffffffffaaffaa,0xa0a0b0b0a0a0a0a,0xaaaaafafaaaaaaaa,0x3333333330303030,0x3333333300000000,0xff00ff00ff00aa00,0xff00ff00aa00aa00,0xcfcfcfcfcececece,0xff0f0000ff0a,0xff0fff0fff0aff0a,0xf0f00000a0a,0xc0c0c0c4c4c4c4c,0xa0a0a0a,0xffff0000fff0,0xa0a0f0f0a0a0e0e,0xaaaaffffaaaaeeee,0x2222222222222222,0xb0b0b0b0b0a0b0a,0xaeaeafafaeaeaeae]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def mk (ids : List Nat) (k bits : Nat) (links : List (Nat × Nat)) : Entry := ⟨ids.map (fun i => stamp 6 (wireBank[i]?.getD 0)),k,bits,links⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def data : Array Entry := #[
  mk [0,1,2,3,4,5] 5 0x2020000012 [],
  mk [0,1,6,7,8] 4 0x201012 [],
  mk [0,1,6,9,7,5] 5 (replayWords [0xc000000000000,0x201012]) [(1,0)],
  mk [0,1,6,2,4,8] 5 (replayWords [0xc0000,0x201012]) [(1,0)],
  mk [10,0,1,6,2,4] 5 0x201000100002 [],
  mk [0,1,6,9,2,4,5] 6 (replayWords [0xb0,0xa00000000000000,0x90000000000000,0x0,0x870065004,0x300002000100014]) [(0,1),(0,2),(0,0),(2,0),(3,0),(4,0)],
  mk [0,1,6,2,4,7,5] 6 (replayWords [0x30000,0x201012]) [(2,0)],
  mk [11,0,1,6,2,4,5] 6 0x201000100002 [],
  mk [12,0,2,4,5,13] 5 (replayWords [0x240000000,0x2]) [],
  mk [0,1,2,4,5,14] 6 (replayWords [0x8,0x700000000000000,0x0,0x603000003,0x250403000003210,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4]) [(8,1),(8,2)],
  mk [0,1,2,15,4,5] 5 0x2020000012 [],
  mk [0,1,6,2,16,5] 5 0x201012 [],
  mk [17,0,1,6,4,5] 5 0x201000100002 [],
  mk [0,1,6,18,2,4,5] 6 (replayWords [0xa09000000000,0x0,0x870065004,0x300002000100014]) [(10,1),(10,2),(10,0),(11,0),(12,3)],
  mk [0,1,6,19,4,5] 5 0x201012 [],
  mk [20,0,1,6,2,5] 5 0x201000100002 [],
  mk [0,1,6,2,4,5,21] 6 (replayWords [0x8,0x30000000000000,0x0,0x0,0x20010013]) [(14,3),(15,0)],
  mk [22,0,1,6,2,4,5] 6 0x201000100002 [],
  mk [0,1,23,2,4,5] 5 0x1101 [],
  mk [24,0,1,6,2,4,5] 6 (replayWords [0x8000570,0x600005403020104]) [(18,1),(18,2),(18,0)],
  mk [0,1,6,2,4,5] 7 (replayWords [0xc,0x8000c0000b8000b,0xa8000a00009,0x800090000400005,0x10040220500004,0x48100402004,0x800040000381004,0x1e038000700006,0x800060000580004,0x50000400005,0x40000480004,0x48000400003,0x800040000380004,0x50000400005,0x40000480004,0x48000400003,0x800040000380002,0x6031400100002,0x106310020314001,0x10821100202,0xc0010000108215]) [(5,0),(6,0),(7,0),(7,3),(9,1),(9,2),(9,0),(13,0),(16,0),(17,0),(19,3),(13,3),(16,3),(17,3),(19,0)],
  mk [12,0,2,4,25,26] 5 0x0 [],
  mk [0,1,2,4,27,26] 6 (replayWords [0x1440001080,0x0,0xc20000880000,0x0,0x0,0x0,0x3]) [(21,2),(21,1)],
  mk [0,1,2,4,5,27,26] 6 (replayWords [0xc00000000020,0x100000000,0x2]) [],
  mk [28,0,2,4,27,13] 5 0x0 [],
  mk [12,29,2,4,27,13] 5 0x1000000000000001 [],
  mk [29,6,2,4,27,13] 6 (replayWords [0x1,0xc400011e0000000,0x1440,0x1184400000000,0x0,0x0,0x0,0x0,0x0,0x3]) [(24,4),(25,0)],
  mk [29,6,2,4,5,27,13] 6 (replayWords [0x200000001000,0x0,0x2]) [],
  mk [0,1,2,4,5,27,14] 6 (replayWords [0x8,0x30020,0x2000000,0x0,0x3]) [(8,2)],
  mk [12,30,1,2,4,5,25] 6 (replayWords [0x206000,0x100400,0x0,0x3]) [(21,5),(8,5)],
  mk [29,0,6,2,4,5,26] 7 (replayWords [0x8,0x400000000000000,0x0,0x0,0xf0000003c000,0x380d000000354d1,0x80001806c580000,0x0,0x0,0x400000010005,0x50149400001,0x800018067300000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x140000000000a00,0x100000000000601,0x40000000000005]) [(22,2),(23,2),(26,5),(27,5),(9,2),(28,6),(29,1)],
  mk [31,29,6,2,4,5,32] 6 (replayWords [0x40006000,0x800,0x0,0x403]) [(8,6)],
  mk [28,30,0,2,4,5,13] 6 (replayWords [0x300000,0x800000000,0x102]) [(8,0),(24,0)],
  mk [12,29,30,2,4,5,13] 6 (replayWords [0x40006000,0x100000000,0x0,0x80000003]) [(8,0),(25,0)],
  mk [29,30,1,2,4,5,14] 7 (replayWords [0xed00000000000,0x0,0xc07000,0x73ba900000000,0x807000007370,0x0,0x0,0x0,0x3000303650000,0x0,0x0,0x0,0x0,0x0,0x0,0x4400000000,0x2000203210004]) [(9,0),(26,2),(27,2),(31,6),(32,1),(33,2)],
  mk [20,29,30,1,6,2,5] 6 (replayWords [0x20003,0x200000400002]) [(15,0)],
  mk [29,30,1,6,2,4,5,21] 7 (replayWords [0xc050000,0x0,0x0,0x0,0x40,0x30020000083]) [(16,0),(35,0)],
  mk [29,33,1,6,2,4,5] 6 0x200042 [(18,1)],
  mk [29,30,1,23,2,4,5] 6 0x200020000042 [(18,0)],
  mk [24,29,30,1,6,2,4,5] 7 (replayWords [0xc0000000,0xba0900008000070,0x600050403020104]) [(37,2),(37,0),(19,0),(38,2),(38,0)],
  mk [29,30,1,6,2,4,5] 8 (replayWords [0xa,0x58000980005,0x800090000480008,0x800048000500004,0x14050200400005,0x30140501e03,0x8000080200,0x81c008000180001,0x8060181a0180005,0x800048000600005,0x800058000400005,0x58000580003,0x50000580005,0x800008000080005,0x800058000180001,0x800058000480004,0x50000480004,0x800030000500004,0x800048000080000,0x800048000480001,0x800018000480000,0x80a019c00080000,0x84a521080000000,0x181001,0x9c000800019c670,0x80c009400080000,0x942521080000000,0x84000,0x802008c22080005]) [(20,0),(30,6),(30,5),(34,2),(34,0),(36,0),(39,3),(36,3),(39,0)],
  mk [29,34,2,4,27,26] 6 (replayWords [0x1470,0x1e80000000000,0x0,0x1460001a80000,0x0,0x8040000000000,0x6030000000,0x4400000003]) [],
  mk [34,2,4,25,27,26] 5 0x0 [],
  mk [29,34,2,4,5,27,26] 6 (replayWords [0x50000,0x40000,0x6000880000,0x3]) [(42,0)],
  mk [29,30,34,2,4,5,26] 7 (replayWords [0x8,0xc40000000000000,0x0,0x0,0x341000000041af0,0x0,0x0,0x0,0x0,0x340e00000039a06,0x6018b500004,0x800048128380000,0x0,0x30006000000,0x0,0x0,0x28005000000,0x0,0x2,0xc0000000000001,0x40000000000000,0x5]) [(41,2),(43,2),(41,0),(43,0)],
  mk [31,29,30,2,4,5,35] 6 0x80000000000000001 [],
  mk [29,30,36,2,4,5,35] 7 (replayWords [0xdc0000000000b,0xa00b00a009008,0x9008007650000,0x3430000000,0x1210000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4]) [(45,4),(45,1),(45,0)],
  mk [20,29,30,36,34,2,5] 6 0x0 [],
  mk [29,30,36,34,2,4,5,21] 7 (replayWords [0xa040006,0x4b0000000000000,0x0,0x4,0x80000000000000,0x3]) [(47,0)],
  mk [29,30,37,34,2,4,5] 6 0x1000001 [],
  mk [38,29,30,2,4,5] 5 0x0 [],
  mk [29,30,36,39,2,4,5] 6 0xc080400000002 [(50,4),(50,1),(50,0)],
  mk [24,29,30,36,34,2,4,5] 7 (replayWords [0x97870000000060,0x500000403020104]) [(49,4),(49,1),(49,0),(51,0)],
  mk [29,30,36,34,2,4,5] 8 (replayWords [0xc,0x800068000c00006,0x8000b800048000b,0x48000602806,0x180602a0602801,0x10040102601,0x8000080200,0x824008000280002,0x80a028220280006,0x800048000800006,0x8000681c0601e06,0x1e0681c0680001,0x10000680006,0x800008000080006,0x800068000280002,0x800068000481406,0x16060160481404,0x800010000100004,0x800048000080000,0x800048000480002,0x800028000480001,0x90000000000000,0x9cc0000000,0x290600,0x1,0x10000100001,0x10000100001,0x10000080000,0x800010000080005]) [(44,4),(44,1),(44,0),(46,0),(48,0),(52,3),(48,3),(52,0)],
  mk [29,30,2,40,4,5,41] 6 0x0 [],
  mk [42,2,40,4,25,27] 5 0x0 [],
  mk [42,29,2,40,4,5,27] 6 0x2000000000001 [(55,0)],
  mk [42,29,30,2,43,5,44] 6 (replayWords [0x3020000000,0x0,0x400000000000002]) [],
  mk [29,30,2,45,4,5] 5 0x0 [],
  mk [42,29,2,46,4,5] 5 0x0 [],
  mk [42,29,30,2,47,5] 5 0x0 [],
  mk [42,29,30,2,48,4,5] 6 (replayWords [0x280000000000000,0x200180100080000,0x3]) [(58,0),(59,2),(59,0),(60,0)],
  mk [49,42,29,30,2,4,5] 6 0x21 [(50,0)],
  mk [42,29,30,2,40,4,5] 7 (replayWords [0xd00000000c00000,0x300b00000000500,0xa00000000400900,0x200800000,0x700700000700,0x300000000,0x0,0x700700003,0x600000000005000,0x5000004000004,0x3110002000,0x103000005000003,0x4000003100,0x2000100000000,0x0,0x4]) [(54,0),(56,2),(56,0),(57,3),(61,0),(62,3)],
  mk [50,29,30,2,4,5,41] 6 0x80000000000000001 [],
  mk [31,29,30,2,4,5,41] 6 0x0 [],
  mk [29,30,36,2,4,5,41] 7 (replayWords [0xb,0x54000000000000a,0x130028004c009,0x1100240044001,0x41ee00040034406,0xb00040028004,0x80080004001c000,0x0,0x1,0x180000040000400,0x0,0x0,0x0,0x10005000000,0x0,0x0,0x10004000000,0x0,0x1,0x60000001,0x20000000,0x5]) [(54,0),(54,3),(64,0),(65,0)],
  mk [29,51,2,4,27,26] 5 0x0 [],
  mk [42,28,2,4,25,27] 5 0x0 [],
  mk [42,36,2,4,25,27] 6 (replayWords [0xd00000000,0x500c00000000b00,0x0,0xa00000,0x500900000000,0x800000000000000,0x500700000000,0x600600000000500,0x400000000300300,0x2100004]) [(55,0),(55,3),(67,1),(68,0),(67,4),(68,2)],
  mk [42,50,2,4,25,27] 5 0x0 [],
  mk [42,36,2,4,5,25,27] 6 0x80400000000000002 [(70,0)],
  mk [42,50,52,2,4,27] 5 0x0 [],
  mk [42,50,29,2,4,27] 6 (replayWords [0x8c00,0x0,0x0,0x0,0x0,0x0,0x2002110000000,0x3]) [(72,0)],
  mk [42,50,29,2,4,5,27] 6 (replayWords [0xc0000,0x240000000000,0x2]) [(70,0)],
  mk [29,51,36,2,4,5,27] 6 0x20000000000001 [(67,0)],
  mk [42,28,30,2,4,5,25] 6 (replayWords [0x80100000000,0x2]) [(68,0)],
  mk [42,29,36,2,4,5,27] 7 (replayWords [0x8,0xc00000000000000,0x0,0x0,0x3c0000000000200,0x0,0x380000000000800,0x0,0x0,0xb58000020000202,0x2008b500000,0x24030000000d200,0x0,0x8008000000,0x0,0x38007000000,0x8006000000,0x0,0x28005000000,0x800000080000000,0x61000000,0x10001000005]) [(56,0),(56,3),(69,0),(71,0),(73,0),(74,0),(75,4),(76,2)],
  mk [50,31,29,30,2,4,5] 6 0x0 [],
  mk [42,50,29,53,2,4,5] 6 (replayWords [0x80400000,0x0,0x2]) [(72,2)],
  mk [54,42,29,30,2,5] 5 0x0 [],
  mk [42,29,30,2,55,4,5] 6 0x4000000000000001 [(80,0)],
  mk [42,50,29,30,2,4,5] 7 (replayWords [0x3,0x300d1800002,0x2008f700006,0xb40000000000001,0x80001806c000000,0x0,0x0,0x0,0x5800a000000,0x0,0x0,0x0,0x48008000000,0x0,0x3,0x300e6000000,0x2,0x200a4000000,0x1,0x800018062080005]) [(78,0),(79,2),(79,0),(81,0),(62,3),(81,3),(62,0),(64,0),(73,2),(74,2),(73,0),(74,0)],
  mk [42,56,29,30,2,4,5] 6 0x21 [],
  mk [20,42,29,30,36,2,5] 6 0x0 [],
  mk [42,29,30,36,2,4,5,21] 7 (replayWords [0x9008,0x70060000000,0x51140000000000,0x0,0x0,0x300000000,0x20100000000000,0x4]) [(57,3),(83,0),(84,0)],
  mk [57,29,30,36,2,4,5] 6 0x40001 [(50,0)],
  mk [42,29,33,36,2,4,5] 6 0x0 [],
  mk [24,42,29,30,36,2,4,5] 7 (replayWords [0x9080000000070,0x600000504031214]) [(86,0),(87,2),(87,0),(62,0)],
  mk [42,29,30,36,2,4,5] 8 (replayWords [0xe,0x80000d80008,0xd000060000c,0x800060000103001,0x10000100402,0x20080202e02,0x50000501405,0x2c050000482804,0x8120482a0482808,0x60000980008,0x80000100401,0x24080000800002,0x20000800008,0x50000500008,0x801e0482204,0x8220801e0600001,0x40101c0600006,0x20000200006,0x60000500005,0x60000601604,0x81a0481a0601601,0x80010000110001,0x10800100001,0x280010000000000,0x12440000002,0x20000100002,0x10100200e01,0x40100c0100a02,0x6010040100205]) [(63,0),(63,3),(66,0),(77,2),(77,0),(82,0),(85,0),(88,3),(85,3),(88,0)],
  mk [58,29,30,36,2,4,5] 7 (replayWords [0x7800a000000,0x500000000001800,0x68014000000,0x58014000000,0x4c00a0014002600,0x480000000001e00,0x60012000000,0x0,0x0,0x440090012002200,0x7800f000000,0x0,0x0,0x40007800f001c06,0x1a0000006,0x160000000,0x149000000,0x0,0x200038006000a00,0x100018002000205]) [],
  mk [29,30,36,2,59,4,5] 8 (replayWords [0xb000a00,0xb000a00050e050,0xd0505050e020002,0x2020502000d000,0x3000d0003000100,0x101010d0100040,0x404040d04000a,0xc0b0b0b0b0a0c0,0xa0a020002000a0a,0xa0003000b000a0,0xa00010001000a,0xa00040004000,0xa00022500000000,0x5900380055,0x3800175000000,0x46500000,0x2200200,0x25002000200020,0x2000200020002,0x200020003000,0x100010003000300,0x40004000300010,0x1000200010004]) [(90,0)],
  mk [29,6,2,60,4,27,26] 6 (replayWords [0x70,0x1850000000000,0x1030000000000,0x0,0x810000003]) [],
  mk [29,0,2,61,4,27] 5 0x0 [],
  mk [29,30,1,2,62,4,26] 6 0x8040000000000002 [(93,5)],
  mk [63,29,0,36,2,4,27] 6 0x41 [],
  mk [29,30,1,2,64,4,5,26] 7 (replayWords [0xa0900000008000,0x80000070600,0x500000000400,0x0,0x0,0x30000201000000,0x4]) [(92,2),(94,0),(95,5)],
  mk [29,30,2,61,4,32] 5 0x0 [],
  mk [29,30,36,2,65,4,32] 6 0x2000000001 [(97,0)],
  mk [63,29,30,36,2,4,32] 6 0x80000000000000001 [],
  mk [31,29,30,2,59,4,5] 6 0x0 [],
  mk [29,30,36,2,59,4,5,32] 7 (replayWords [0xa98670065004000,0x30200,0x0,0x0,0x0,0x0,0x14]) [(98,0),(99,0),(100,0)],
  mk [29,30,0,36,2,66,5,44] 7 (replayWords [0x8,0x700000605000,0x0,0x0,0x40003000,0x200000000000000,0x0,0x14]) [],
  mk [0,2,67,4,5] 4 0x0 [],
  mk [0,2,61,4,68] 4 0x0 [],
  mk [69,0,2,61,4,5] 5 (replayWords [0x8000000,0x40000002]) [(103,0),(104,0)],
  mk [29,30,0,2,61,4,5] 6 (replayWords [0xa200180100,0x0,0x0,0x13]) [(105,0),(93,2),(93,0),(97,0)],
  mk [70,6,2,71,5] 4 0x0 [],
  mk [29,6,2,71,72] 4 0x0 [],
  mk [69,0,36,2,73,5] 5 (replayWords [0x8000000,0x4002]) [(107,1),(108,1)],
  mk [29,30,0,36,2,73,5] 6 0x11 [(109,0)],
  mk [29,30,0,36,2,65,4,5] 7 (replayWords [0x9,0x22000200001e07,0x1a000000000000,0x0,0x18002d404a0e60,0x148000c40000000,0x0,0x0,0x15]) [(106,0),(110,0),(94,6),(94,5),(98,0)],
  mk [74,0,2,4,5] 4 0x0 [],
  mk [75,0,2,4,68] 4 0x0 [],
  mk [75,69,0,2,4,5] 5 (replayWords [0x800000000,0x102]) [(112,0),(113,0)],
  mk [75,29,30,0,2,4,5] 6 0x1001 [(114,0)],
  mk [76,0,77,2,5] 4 0x0 [],
  mk [76,0,36,2,68] 4 0x0 [],
  mk [76,69,0,36,2,5] 5 (replayWords [0x800000000,0x4000000002]) [(116,0),(117,0)],
  mk [76,29,30,0,36,2,5] 6 0x1001 [(118,0)],
  mk [29,30,0,36,2,4,5,78] 7 (replayWords [0x8007,0x60054000300,0x20000000000000,0x0,0x0,0x0,0x0,0x14]) [(115,0),(119,0)],
  mk [63,29,30,0,36,2,4,5] 7 (replayWords [0xd0c000b000a,0x0,0x0,0x0,0x0,0x98,0x760005040302014]) [(95,2),(95,0),(99,0)],
  mk [79,29,30,36,6,2,4,5] 7 (replayWords [0x200030,0x100000080003]) [],
  mk [29,30,0,36,2,59,4,5] 8 (replayWords [0x6400c0017002c00,0x30015000000,0x0,0x4c0028014002600,0x8012000000,0x10011000000,0x40007800f002000,0x380000000001c00,0x0,0x38007800f001c00,0x0,0x3,0x140000000000001,0x800d00060034003,0x198000000000000,0xad4000000000004,0x250000000000003,0x60000000,0x180531c00018c60,0x0,0x0,0x100028003000800,0x8003000000,0x10003000000,0x880000000000000,0x840000000000000,0x40200000004215]) [(96,6),(96,5),(101,0),(102,3),(111,0),(120,0),(121,0),(122,7)],
  mk [29,30,36,2,80,5] 7 (replayWords [0x8,0x8008008004004,0x400400c00c00c,0xc002002082302,0x6006186306004,0x400400a008008,0x8008002004004,0x4006004004004,0x4004004004004,0x4004004004004,0x4004002002002,0x2006006006006,0x2002004002003]) [],
  mk [81,29,30,36,2,4,5] 8 (replayWords [0x1,0x10000100001,0x70000600007,0x60000800003,0x800080000380002,0x20080202002,0x50000501405,0x20050000481e04,0x812048200481e01,0x10000100001,0x10000100001,0x10000108001,0x11000100001,0x80010000128001,0x1,0x244000000600003,0x800070000600006,0x20000200006,0x60000500005,0x600006396b7,0x1c0725cd601603,0x800020000200003,0x800038000500005,0x38000380c04,0x812048100380c02,0x20000100002,0x10020200a01,0x4010020100202,0x6010040100205]) [(124,3)],
  mk [29,6,2,82,4,27,26] 6 (replayWords [0x300000000000,0x0,0x28000800402]) [(55,4)],
  mk [29,0,2,40,4,27,26] 6 0x202001 [],
  mk [29,30,1,2,83,4,5,26] 7 (replayWords [0x60000050000,0x200180,0x0,0x900000000100,0x2000000003]) [(56,5),(126,2),(127,5)],
  mk [29,30,2,40,4,32,26] 6 (replayWords [0x1000000,0x1]) [],
  mk [31,29,30,2,40,4,5] 6 0x80000001 [],
  mk [29,30,36,2,82,4,5,14] 7 (replayWords [0x9a61,0x600000006020000,0x80,0x0,0x0,0x3]) [(129,4),(130,4)],
  mk [29,30,0,2,40,4,5,26] 7 (replayWords [0xa00000909000,0x0,0x8070006000500,0x0,0x4020000,0x3020000000,0x14]) [(127,2),(127,0),(129,0)],
  mk [29,30,0,36,2,43,5,44] 7 (replayWords [0x8,0x700006040000,0x0,0x0,0x50400000,0x0,0x302000000,0x14]) [(57,0)],
  mk [29,30,1,2,84,4,5] 6 0x300030000008100002 [(59,5)],
  mk [70,2,85,4,5] 4 0x0 [],
  mk [29,2,85,4,72] 4 0x0 [],
  mk [69,36,2,86,4,5] 5 (replayWords [0x8000000,0x42]) [(135,1),(136,1)],
  mk [29,30,36,2,86,4,5] 6 0x200000000000000012 [(137,0)],
  mk [70,6,2,87,5] 4 0x0 [],
  mk [29,6,2,87,72] 4 0x0 [],
  mk [69,0,36,2,47,5] 5 (replayWords [0x8000000,0x4002]) [(139,1),(140,1)],
  mk [29,30,0,36,2,47,5] 6 0x3200000000012 [(141,0),(60,0)],
  mk [29,30,0,36,2,48,4,5] 7 (replayWords [0xe0d0000000,0x0,0xc000b08a980760,0x54000000000000,0x302000000,0x14]) [(61,0),(134,6),(134,5),(138,0),(142,0)],
  mk [88,70,2,4,5] 4 0x0 [],
  mk [88,29,2,4,72] 4 0x0 [],
  mk [88,29,89,2,4,5] 5 (replayWords [0x80000000000,0x400002]) [(144,0),(145,0)],
  mk [88,29,30,36,2,4,5] 6 0x1000001 [(146,0)],
  mk [90,70,6,2,5] 4 0x0 [],
  mk [90,29,6,2,72] 4 0x0 [],
  mk [90,29,89,6,2,5] 5 (replayWords [0x80000000000,0x400002]) [(148,0),(149,0)],
  mk [90,29,30,36,6,2,5] 6 0x1000001 [(150,0)],
  mk [29,30,0,36,2,4,5,91] 7 (replayWords [0xe060000,0xa940000000000,0x0,0x0,0x6100000000000,0x13]) [(147,1),(151,1)],
  mk [92,29,30,36,6,2,4,5] 7 (replayWords [0xc,0x280000000000000,0x71a0010,0x3]) [],
  mk [29,30,93,1,2,4,5] 6 0x1000101 [],
  mk [29,30,94,36,2,4,5] 6 0x4000001 [(50,0)],
  mk [49,29,30,0,36,2,4,5] 7 (replayWords [0xa090000000,0x86,0x760005403020104]) [(154,6),(154,5),(155,0),(62,0)],
  mk [29,30,0,36,2,40,4,5] 8 (replayWords [0x7800e801c003600,0x4801a000000,0x28019000000,0x5c0060018002e00,0x8016000000,0x10015000000,0x500090012002800,0x4c0000000002600,0x28012000000,0x440090012002200,0x0,0x4,0x940000000000004,0xa40000000000006,0x3df05ad8b5c1ef0,0x800e00020038001,0xd00040034000,0x240500000025204,0xa94048189581404,0x800000020000004,0x800000040000000,0x180829c05014c60,0x28005000000,0x28005000002,0x80000000000001,0x840000000000000,0x40200000004215]) [(63,0),(128,6),(128,5),(131,1),(132,0),(133,3),(143,0),(152,0),(153,1),(156,3)],
  mk [29,95,2,4,27,26] 5 0x1000000000000001 [],
  mk [96,0,36,2,4,25,27] 6 (replayWords [0x40,0x0,0x0,0x0,0x180000000004083]) [(158,1)],
  mk [97,6,2,4,27,26] 5 0x1000000000000001 [],
  mk [98,29,6,2,4,27,26] 6 (replayWords [0x8000000,0x70600,0x0,0x504000000000000,0x0,0x3020104]) [(160,0)],
  mk [0,2,99,4,25,27] 5 (replayWords [0x300000000000000,0x80000042]) [],
  mk [29,2,3,4,27,26] 5 0x1000000000000001 [],
  mk [29,6,9,7,27,26] 5 (replayWords [0x200000000000000,0x4000000002]) [],
  mk [29,6,2,4,27,100] 5 0x1000000000000001 [],
  mk [101,30,1,2,4,26] 5 0x100000000001 [],
  mk [29,6,9,2,4,27,26] 6 (replayWords [0xc000000,0xb0a0000000000,0x90800000,0x700000006,0x5000,0x430021000004]) [(162,4),(163,0),(164,0),(165,5),(166,2),(165,0),(166,1)],
  mk [29,6,2,4,7,27,26] 6 (replayWords [0x300000000000,0x28,0x100000000002]) [(164,0)],
  mk [11,29,6,2,4,27,26] 6 (replayWords [0x300000000000,0x800,0x44002]) [],
  mk [12,29,2,4,27,26] 5 0x1000000000000001 [],
  mk [29,6,2,4,27,32,26] 6 (replayWords [0x1840,0x30000000000000,0xa040000,0x34010000,0x3]) [(24,6),(170,0)],
  mk [28,102,0,2,4,25] 5 0x0 [],
  mk [28,0,36,2,4,27] 6 (replayWords [0x900000,0x800000000000,0x700000000600,0x0,0x0,0x0,0x0,0x0,0x5000,0x5000000004300,0x200000000104]) [(24,0),(172,2)],
  mk [28,0,36,2,4,25,27] 6 (replayWords [0x4000000,0x8000000007060,0x500004,0x0,0x0,0x300000002014]) [(68,0),(24,0),(172,0)],
  mk [103,29,6,2,4,27,26] 6 (replayWords [0x20,0x40006000,0x20002000,0x0,0x3]) [],
  mk [29,2,15,4,27,26] 5 0x1000000000000001 [],
  mk [29,6,104,2,4,27,26] 6 (replayWords [0x300000000000,0x0,0x2400002]) [(176,0)],
  mk [29,6,105,4,27,26] 5 0x1000000000000001 [],
  mk [90,30,1,2,25,26] 5 0x1000000000000001 [],
  mk [29,6,2,4,27,26,106] 6 (replayWords [0xc020,0xa040006020000,0x10000000000000,0x0,0x3]) [(178,3),(179,2)],
  mk [107,29,6,2,4,27,26] 6 (replayWords [0x50,0x0,0x8180,0x0,0x4080003]) [],
  mk [108,30,1,2,4,25,26] 6 (replayWords [0x300000000000,0x0,0x21002]) [],
  mk [29,6,2,4,27,26] 7 (replayWords [0x5,0xc06009e80005c00,0x5d7618c00000b,0xc0000b80000b400,0xb00000ac0000a,0x80000a400006806,0x409e80005c00009,0xe89c09a50000c00,0x9230000c00008,0x800008400008000,0x7c00007800007,0x400007000006c00,0x6806405d80005,0xc00005d85c05950,0xc00005130000,0xc00004800004400,0x4000003c00003,0x800000403003403,0x400002c00000,0xc00002800000c00,0x2400000401c02,0x1c00400001800,0xc00001400000,0xc00000440000c00,0xc20000400006]) [(41,0),(69,4),(126,0),(159,4),(92,0),(161,0),(126,3),(159,8),(92,3),(161,3),(167,0),(168,0),(169,0),(169,3),(26,5),(171,0),(173,6),(174,6),(175,0),(177,0),(180,0),(181,5),(182,9),(177,3),(180,3),(181,10),(182,2),(26,0),(171,5),(173,4),(174,4),(177,5),(180,5),(181,0),(182,7),(177,10),(180,10),(181,3),(182,1)],
  mk [28,0,2,4,27,26] 5 0x0 [],
  mk [29,6,2,4,25,27,26] 6 (replayWords [0x4008000,0x760000,0x50000000000004,0x300000000000200,0x0,0x104]) [(42,0),(170,0),(184,6),(184,4)],
  mk [50,0,36,2,4,25,27] 6 (replayWords [0x30,0x40000,0x30000,0x0,0x800000403]) [(70,0)],
  mk [0,2,109,4,25,27] 5 0x1000000000000001 [],
  mk [29,6,2,16,27,26] 5 0x1000000000000001 [],
  mk [17,29,6,4,27,26] 5 0x1000000000000001 [],
  mk [29,6,18,2,4,27,26] 6 (replayWords [0x70,0x0,0x0,0xc280000000000,0x1180880003]) [(187,4),(176,0),(188,0),(189,3)],
  mk [29,6,19,4,27,26] 5 (replayWords [0x200000000000000,0x4000000002]) [],
  mk [20,29,6,2,27,26] 5 0x1000000000000001 [],
  mk [29,6,2,4,27,26,21] 6 (replayWords [0xa040006000000,0x20000000000000,0x0,0x80000003]) [(191,3),(192,0)],
  mk [22,29,6,2,4,27,26] 6 (replayWords [0x200000000000,0x0,0x400000044002]) [],
  mk [24,29,6,2,4,27,26] 6 (replayWords [0x200000000000,0x0,0x10002]) [],
  mk [28,102,0,2,4,5] 5 0x0 [],
  mk [28,0,36,2,4,5,27] 6 (replayWords [0x8000000030,0x100000080,0x0,0x3]) [(184,0),(196,0)],
  mk [29,6,2,4,5,27,26] 7 (replayWords [0x581b0000002ad65,0x280000000000000,0x0,0x0,0x201b0000006efbd,0x32000000c,0x5c0000000000000,0x0,0x0,0x20160000005956a,0x800000280000009,0x801200220040007,0x800e001a0030005,0xa10900140025003,0x8005000c0014000,0x0,0x20004000000,0x0,0x18003000000,0x1,0x20000005]) [(43,0),(71,4),(185,0),(186,4),(175,0),(190,0),(193,0),(194,0),(195,3),(190,3),(193,3),(194,3),(195,0),(27,5),(197,6),(27,0),(197,4)],
  mk [29,6,2,4,25,27,13] 6 (replayWords [0x300000003800,0x40,0x2]) [(25,0),(184,4)],
  mk [52,0,2,4,27,26] 5 0x0 [],
  mk [50,29,0,2,4,27,26] 6 0x20042 [(200,0)],
  mk [12,29,30,2,4,25,26] 6 (replayWords [0xc0000000000,0x800102]) [(21,0),(25,5)],
  mk [28,110,0,2,4,26] 5 0x0 [],
  mk [28,30,1,2,4,25,27] 6 (replayWords [0x300,0x8000000000,0x102]) [(21,5),(203,5)],
  mk [28,30,0,2,4,25,26] 6 (replayWords [0xc000000000,0x20102]) [(21,0),(203,0)],
  mk [29,30,1,2,4,27,26] 7 (replayWords [0x500000000002800,0x0,0x0,0x4c0000000000600,0x480000000000400,0x440000000000600,0x0,0x0,0x400f0000003cc07,0x340000000000001,0x80001806c580000,0x0,0x5000a000000,0x10009000000,0x0,0x40008000000,0x10007000000,0x1,0x10046280002,0x100000000000001,0x10062080005]) [(22,0),(41,0),(127,5),(127,10),(26,6),(199,6),(201,5),(202,2),(204,4),(205,1)],
  mk [12,29,30,2,4,5,26] 6 (replayWords [0x300800,0x40000000000,0x2]) [(170,0)],
  mk [28,30,0,2,4,5,26] 6 (replayWords [0x320000,0x400000000,0x2]) [(184,0)],
  mk [29,30,1,2,4,5,27,26] 7 (replayWords [0x801e00,0x0,0xe680000000c0,0x5,0x800a00000025000,0x380073,0x501060000000,0x0,0x0,0x4000000000205]) [(23,0),(43,0),(185,2),(201,5),(27,6),(207,2),(208,1)],
  mk [29,111,6,2,4,26] 6 (replayWords [0x700000,0xc00b00000000,0xa00000000000000,0x0,0x900900000000000,0x0,0x800800000,0x0,0x507000,0x6504300004000,0x302000001000004]) [],
  mk [50,52,0,36,2,4,27] 6 (replayWords [0x1000,0x180020400003]) [(200,0),(72,0)],
  mk [50,110,0,36,2,4,25] 6 0x81 [],
  mk [50,29,0,36,2,4,27] 7 (replayWords [0x140000000000400,0x400000000000407,0xb80000000000000,0x0,0x0,0x6800d000000,0x0,0x0,0x0,0x6000c000000,0x0,0x0,0xb42808020000,0x40008000000,0x128000003,0x980000000000000,0x100500000014801,0x10062080005]) [(210,1),(211,0),(201,0),(73,0),(212,2)],
  mk [29,111,6,2,4,5,26] 6 (replayWords [0x60050000,0x8000180100,0x0,0x10000003]) [(200,6)],
  mk [50,29,0,36,2,4,5,27] 7 (replayWords [0xa000,0x980000000000000,0x703003065000000,0x0,0x0,0x400000000,0x30320104]) [(214,1),(74,0),(186,0),(201,0)],
  mk [103,29,30,6,2,4,5,26] 7 (replayWords [0x60060004000000,0x1440180004000,0x0,0x0,0x80003]) [(175,0)],
  mk [20,29,30,1,2,5,26] 6 (replayWords [0x20002000,0x400000000,0x2]) [(192,2)],
  mk [29,30,1,2,4,5,26,21] 7 (replayWords [0x800700006005000,0x0,0x4000000030,0x0,0x2000000000000,0x10000000,0x4]) [(193,2),(217,0)],
  mk [29,33,6,2,4,5,26] 6 (replayWords [0x40030000,0x100000,0x0,0x10000003]) [],
  mk [24,29,30,1,2,4,5,26] 7 (replayWords [0x7000006a000000,0x200000,0x0,0x0,0xc30000004083]) [(219,2),(195,2)],
  mk [28,0,112,2,4,5] 5 0x0 [],
  mk [29,113,6,2,4,5,27] 6 (replayWords [0xc0800,0x1000000000,0x2]) [(221,6)],
  mk [28,30,1,2,4,5,32] 6 (replayWords [0x300800,0x0,0x102]) [(8,5)],
  mk [28,110,30,1,2,4,5] 6 (replayWords [0xc00000,0x0,0x8402]) [(221,5),(203,5)],
  mk [28,30,1,2,4,5,25] 7 (replayWords [0x6600000000000,0x0,0x3000,0x300c00000b000,0x33a0000000000,0x0,0x9000,0x9008000007000,0x6550303000,0x0,0x0,0x0,0x0,0x0,0x0,0x400000000,0x300000200100004]) [(222,2),(29,0),(204,0),(212,5),(223,0),(224,0)],
  mk [31,29,6,2,4,5,27] 6 (replayWords [0x300800,0x10000000,0x2]) [],
  mk [29,30,1,2,4,5,26,14] 7 (replayWords [0xa000,0x9007000,0x80070000000000,0x3600540030,0x0,0x2000000000000,0x0,0x104]) [(28,5),(171,6),(223,4),(32,1),(226,6),(207,2)],
  mk [12,28,0,36,2,4,5] 6 0xc080000402 [(221,0),(8,0)],
  mk [28,30,0,36,2,4,5] 7 (replayWords [0x800e00000000000,0x2000202dc0,0xb00800000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa000008000,0x2820808000000,0x9800007600000,0x500000000,0x400103000002114]) [(228,0),(32,0),(173,0),(197,0),(208,0)],
  mk [28,30,0,36,2,4,5,25] 7 (replayWords [0xc00005b00,0x500000000000000,0xa00000009008070,0x0,0x0,0x600050000,0x40302014]) [(29,5),(76,0),(174,0),(205,0),(224,5),(32,0)],
  mk [114,30,1,2,4,5,25] 6 (replayWords [0x800,0x10000000,0x2]) [],
  mk [90,0,115,2,5] 4 0x0 [],
  mk [90,116,0,36,2,5] 5 (replayWords [0x800000000,0x4000000002]) [(232,0)],
  mk [90,30,0,36,2,5,25] 6 (replayWords [0x302000,0x400000000,0x2]) [(179,5),(233,0)],
  mk [29,30,1,2,4,5,26,91] 7 (replayWords [0x8000,0x700600005003000,0x40030000000000,0x2000000020,0x0,0x1000000000000,0x0,0x4]) [(180,6),(231,4),(234,1)],
  mk [108,30,0,36,2,4,5,25] 7 (replayWords [0x40040000000,0x180000,0x0,0x0,0x810003]) [(182,5)],
  mk [29,30,1,2,4,5,26] 8 (replayWords [0x1041000000,0x9,0xc00003400009800,0x3400009400002,0x400009000002400,0x6406000de0000,0xc00000de0de8e20,0x400008600000,0x400000c07c00de0,0xc00000de0de7,0x400003400007000,0x3400006c00002,0x400006800002400,0x6406002080000,0xc00002086005d60,0x400005540000,0x400000c30000c00,0xc00c34d20c00003,0x400002400004400,0x3400003400002,0x3c04003c03400,0x3400000400003,0x800003400003400,0xc00000c00003,0x400002400002002,0xc03002c02400002,0x400000400002800,0x2400002400000,0xc00000c00002400,0x2070000400001,0x850000400001041,0x0,0x400000c00,0xc00c00800400006]) [(30,2),(44,0),(77,5),(128,0),(96,0),(128,3),(96,3),(183,2),(198,2),(206,0),(209,0),(213,5),(215,5),(216,2),(218,0),(220,3),(218,3),(220,0),(225,4),(34,0),(227,0),(229,1),(230,1),(235,0),(236,7),(235,3),(236,1)],
  mk [29,30,117,2,4,5] 7 (replayWords [0xa,0xa00a00a00a00a,0xa00a00a00c00a,0xa002402082682,0x4804104a82008,0x8008008008008,0x8008002002002,0x2004004004004,0x6006006006002,0x2002002004004,0x4004002002002,0x2004004004004,0x2002002002003]) [],
  mk [29,30,36,2,118,5] 7 (replayWords [0xc,0xe00c00c00c006,0xc00600c00c00c,0xc002002082302,0x400410430200a,0x600a00600a00a,0xa00a002002002,0x2004004004004,0x6008008006002,0x2002002004004,0x4004002002002,0x2004004004004,0x2002002002003]) [],
  mk [29,30,119,36,2,4,5] 8 (replayWords [0x6,0x800098000680009,0x800068000700006,0x800070000680004,0x800068000480006,0xb72000000000000,0x8400080200,0x85a008000210002,0x80211a0080009,0x800070000c00009,0x80009800048000b,0x8000980009b6946,0x81a06b6d5982809,0x800008000080009,0x800098000200002,0x98000700004,0x800090000700007,0x35ef681a06b6307,0x1e070000080000,0x800070000700002,0x20000700004,0xb54a681a06b58b4,0x814048000080000,0x800048000480002,0x20000480000,0x84000a020084870,0x980008c00214800,0x8c2308800080000,0x800008000080005]) [(238,0),(239,3),(239,0)],
  mk [50,29,30,2,4,32,26] 6 (replayWords [0x1000000,0x1]) [],
  mk [31,29,30,2,4,32,26] 6 (replayWords [0x300000000000,0x0,0x20102]) [(25,6),(25,5)],
  mk [28,29,30,2,4,27,13] 6 (replayWords [0x300000000000,0x0,0x810002]) [(25,0),(24,0)],
  mk [29,30,36,2,4,25,14] 7 (replayWords [0x400a000000286f0,0x0,0x2,0xb80000000000006,0xb00000000000000,0x2c0a00000028600,0x0,0x0,0x0,0x4,0xa00000000000000,0x0,0x0,0x0,0x18007000000,0x0,0x0,0x18006000000,0x2,0x800028065200001,0x10062080005]) [(26,1),(26,2),(129,4),(129,8),(241,4),(242,4),(243,1),(243,2)],
  mk [31,29,30,2,4,5,26] 6 0x80000000000000001 [],
  mk [29,30,36,2,4,5,25,14] 7 (replayWords [0xa9870000,0x0,0x60050000000000,0x0,0x0,0x400300000000000,0x0,0x2000104]) [(27,1),(27,2),(241,4),(245,4)],
  mk [50,110,29,36,2,4,32] 6 (replayWords [0x10000,0x1]) [],
  mk [50,31,29,30,2,4,32] 6 (replayWords [0x80400,0x0,0x2]) [],
  mk [50,29,30,36,2,4,32] 7 (replayWords [0xa09,0x9198700000,0x6500000000,0x4300000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100100000,0x100100000000,0x2100000000000,0x0,0x4]) [(241,0),(247,2),(247,0),(248,0)],
  mk [50,29,30,36,2,4,5,32] 7 (replayWords [0x8,0x30000004000000,0x80000000000,0x0,0x0,0x3]) [(241,0),(78,0)],
  mk [31,29,30,19,4,5] 5 0x0 [],
  mk [20,31,29,30,2,5] 5 0x0 [],
  mk [31,29,30,2,4,5,21] 6 (replayWords [0x81000000000,0x0,0x2]) [(251,3),(252,0)],
  mk [20,29,30,36,2,5,32] 6 (replayWords [0x810000000,0x0,0x2]) [(252,0)],
  mk [29,30,36,2,4,5,32,21] 7 (replayWords [0x38730000,0x600500000000000,0x40,0x32001000000000,0x0,0x0,0x0,0x4]) [(253,0),(254,0)],
  mk [24,31,29,30,2,4,5] 6 0x0 [],
  mk [24,29,30,36,2,4,5,32] 7 (replayWords [0xc20000,0x400000000000000,0x0,0x2]) [(256,0)],
  mk [29,113,30,2,4,5,14] 6 (replayWords [0x2010,0x0,0x2]) [],
  mk [28,120,30,2,4,5,13] 6 0x0 [],
  mk [28,29,121,2,4,5,13] 6 0x80000000000000001 [],
  mk [28,122,29,2,4,5,13] 6 (replayWords [0x80400,0x0,0x2]) [],
  mk [28,29,30,2,4,5,13] 7 (replayWords [0xfe00000000000,0x0,0xd0b000,0xbcb4a00000000,0x9870000000000,0x0,0x6000005,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400,0x300000000200100,0x4]) [(258,2),(33,0),(32,0),(243,0),(247,5),(259,0),(260,0),(261,0)],
  mk [123,29,30,2,4,5] 5 0x0 [],
  mk [114,29,121,2,4,5] 5 0x0 [],
  mk [76,29,30,124,2,5] 5 0x0 [],
  mk [125,30,36,2,4,5,126] 6 (replayWords [0xa,0x40006004002000,0x0,0x0,0x3]) [(263,4),(264,1),(264,2),(265,4)],
  mk [127,29,30,124,2,4,5] 6 0x0 [],
  mk [125,30,36,2,4,5,14] 7 (replayWords [0x8,0x3c0000000000007,0xc001a0030005,0x800900140024001,0xa0e000000000001,0x18a000000000000,0x908000000000000,0x0,0x0,0x0,0x0,0x800000020000000,0x0,0x0,0x0,0x800000020000000,0x0,0x0,0x800000020000000,0x1,0x800000020000001,0x20000005]) [(260,1),(260,2),(266,0),(267,8),(266,3),(267,4)],
  mk [31,29,30,2,4,5,13] 6 (replayWords [0x200400,0x0,0x2]) [],
  mk [29,30,36,2,4,5,32,35] 7 (replayWords [0xe00c000000,0xa008006000000,0x4010000000,0x0,0x0,0x3]) [(45,0),(269,6),(269,5)],
  mk [128,31,29,30,2,4,5] 6 0x0 [],
  mk [31,29,30,129,4,5] 5 0x0 [],
  mk [130,31,29,30,2,5] 5 0x0 [],
  mk [31,29,30,2,131,4,5] 6 (replayWords [0x2,0x100000000000000,0x2]) [(272,3),(273,0)],
  mk [132,31,29,30,2,4,5] 6 0x0 [],
  mk [31,29,30,133,2,4,5] 6 0x0 [],
  mk [29,30,2,134,4,5] 5 0x0 [],
  mk [135,29,30,2,4,5] 5 0x0 [],
  mk [31,29,2,136,4,5] 5 0x0 [],
  mk [31,29,30,7,8] 4 0x0 [],
  mk [31,29,30,9,7,5] 5 0x200000000000001 [(280,0)],
  mk [31,29,30,2,4,8] 5 0x20000000001 [(280,0)],
  mk [10,31,29,30,2,4] 5 0x0 [],
  mk [31,29,30,9,2,4,5] 6 (replayWords [0x90,0x800000000000000,0x70000000000000,0x0,0x650043002,0x100000000000004]) [(277,0),(278,0),(279,2),(279,0),(281,0),(282,0),(283,0)],
  mk [31,29,30,2,4,7,5] 6 0x10000000001 [(281,0)],
  mk [11,31,29,30,2,4,5] 6 0x0 [],
  mk [137,29,30,2,4,5] 5 0x0 [],
  mk [31,29,2,138,4,5] 5 0x0 [],
  mk [31,29,30,2,16,5] 5 0x0 [],
  mk [17,31,29,30,4,5] 5 0x0 [],
  mk [31,29,30,18,2,4,5] 6 (replayWords [0x807000000000,0x0,0x650043002,0x100000000000004]) [(287,3),(288,2),(288,0),(289,0),(290,3)],
  mk [22,31,29,30,2,4,5] 6 0x0 [],
  mk [31,29,30,2,4,5] 7 (replayWords [0xd,0xc8000c0000b,0x8000b0000a8000a,0x98000180001,0x800018000180000,0x800008000180000,0x800010000900008,0x800080000780007,0x68000600001,0x800018000180001,0x800008000080000,0x800008000580005,0x48000400001,0x800018000180001,0x800008000080000,0x800008000380003,0x28000200001,0x800018000180001,0x800010000180001,0x800018000100000,0x800008000080005]) [(271,0),(274,0),(275,3),(276,0),(271,3),(274,3),(275,0),(276,3),(284,0),(285,0),(286,0),(286,3),(78,0),(65,0),(291,0),(253,0),(292,0),(256,3),(291,3),(253,3),(292,3),(256,0)],
  mk [12,139,2,4,5,32] 5 (replayWords [0x8040000000,0x2]) [],
  mk [12,31,29,2,4,5,32] 6 (replayWords [0x8006000,0x800000,0x0,0x400000003]) [(294,0)],
  mk [31,29,30,140,2,4,5] 6 0x0 [],
  mk [31,29,30,141,4,5] 5 0x0 [],
  mk [76,31,29,30,2,5] 5 0x0 [],
  mk [31,29,30,2,4,5,78] 6 (replayWords [0xc2000000400,0x0,0x2]) [(297,3),(298,0)],
  mk [142,143,30,36,2,4,5] 6 0x21 [(263,4)],
  mk [127,31,29,30,2,4,5] 6 0x0 [],
  mk [31,29,30,2,4,5,32] 7 (replayWords [0x3,0x180000000000009,0x110020003c007,0xd0018002c001,0xa80000000000000,0xa40000000000004,0x20e000000000000,0x0,0x0,0x0,0x0,0x600000014000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40000000c000,0x200000004005]) [(295,2),(295,0),(248,0),(261,6),(261,5),(296,0),(299,0),(300,1),(301,3),(296,3),(299,3),(300,7),(301,0)],
  mk [96,31,29,30,2,4,5] 6 0x21 [],
  mk [31,29,30,36,2,4,5] 7 (replayWords [0x5c0010016000400,0x0,0x0,0x5400a0002002600,0x0,0x480010011000400,0x0,0x0,0x3c0080010001e00,0x38001000d000400,0x0,0x0,0x2c006000c001601,0xa00140008001,0x900120008000,0x102000000,0x0,0x1c0030002000a00,0x100018002000205]) [(45,0),(130,0),(303,0),(130,3),(303,3),(245,0),(78,0)],
  mk [31,29,30,36,2,4,5,32] 7 (replayWords [0x1c10000000,0xb00000000000a0,0x900000000008010,0x0,0x0,0x760054000,0x30102014]) [(33,6),(33,5),(31,2),(31,0),(242,0),(248,0),(45,0)],
  mk [114,29,30,2,4,5,13] 6 (replayWords [0x200400,0x0,0x2]) [(264,0)],
  mk [75,29,30,2,4,5,32] 6 (replayWords [0x810,0x0,0x2]) [],
  mk [76,29,30,36,2,5,32] 6 (replayWords [0x810000000,0x0,0x2]) [(265,0),(298,0)],
  mk [29,30,36,2,4,5,32,78] 7 (replayWords [0xc000b000,0xa00900008007600,0x50000000000040,0x32001000000000,0x0,0x0,0x0,0x4]) [(266,1),(299,0),(306,6),(306,5),(307,0),(308,0),(99,0)],
  mk [127,29,30,36,2,4,5,32] 7 (replayWords [0x1600006,0x20000002000000,0x0,0x0,0x0,0x3]) [(267,0),(301,0)],
  mk [29,30,36,2,4,5,32] 8 (replayWords [0x9a79800000,0x9,0x630002220009230,0x22200085f0001,0x9e00081f00019e0,0x75c6da0960006,0x580000965d60415,0x400000000000000,0x1144c00000,0x4,0x800002000004400,0x2000004000001,0x800003c00001800,0x38d0000800003,0xb0000800000400,0x400000400000,0x400001000001000,0x400001000002,0x1800002800,0x2000002000000,0x800002400002000,0x2000000400000,0x400002000002000,0x1000001000002,0x1800000800,0x1c00001800001,0x800000400000400,0x1800001800001,0x1000001800,0x800000400400,0x401400800000800,0x1001001000c00,0x800000400000400,0x400000400006]) [(34,4),(34,1),(131,1),(131,7),(244,1),(246,1),(249,0),(250,0),(255,0),(257,3),(255,3),(257,0),(262,6),(262,5),(268,1),(46,0),(270,0),(293,0),(302,0),(304,0),(305,0),(309,0),(310,3),(309,3),(310,0)],
  mk [103,143,30,36,2,4,5] 6 0x0 [],
  mk [103,29,30,36,2,4,5,14] 7 (replayWords [0xc000000000,0xa046000000,0x4000,0x0,0x10,0x3]) [(312,0)],
  mk [28,120,30,1,2,4,5] 6 0x21 [],
  mk [28,122,29,1,2,4,5] 6 0x80801 [],
  mk [28,29,30,1,2,4,5,13] 7 (replayWords [0x80000000,0x7006500,0x40000000000003,0x30000000000000,0x0,0x0,0x20,0x10004]) [(314,0),(315,0)],
  mk [12,139,0,2,4,5] 5 0xc080042 [],
  mk [12,31,29,0,2,4,5] 6 0x8006000802000003 [(317,0)],
  mk [31,29,30,144,2,4,5] 6 0x0 [],
  mk [145,31,29,30,2,4,5] 6 0x80000000000000001 [],
  mk [146,29,30,2,4,5] 5 0x0 [],
  mk [98,143,30,36,2,4,5] 6 0x842 [(321,4),(50,8)],
  mk [31,29,30,0,2,4,5] 7 (replayWords [0xd00,0x500300500000300,0x100000000100300,0x0,0xc00,0x500b00500000000,0x0,0x0,0xa00500900500000,0x0,0x0,0x3100000000003,0x300000000008007,0x6005000301000,0x3330004000003,0x2000001004]) [(318,2),(318,0),(319,0),(320,0),(100,0),(322,1),(100,3),(322,7),(312,1)],
  mk [31,29,30,0,2,4,5,32] 7 (replayWords [0xc,0xa008006000000,0x820000000000,0x0,0x0,0x10000003]) [(315,6),(315,5),(312,1)],
  mk [127,29,30,0,36,2,4,5] 7 (replayWords [0x6300000000000,0x0,0x0,0xb1a0010000003]) [],
  mk [29,30,0,36,2,4,5,32] 8 (replayWords [0xc,0x14000000000000b,0x8015002c005400a,0x1200260048001,0xc60f0006003c6f5,0xa96000000000000,0xb9a000000000005,0xb16000000000000,0x0,0x1,0x800000060000000,0x280529400014a50,0x8002000000,0x10001000000,0x0,0x0,0x200028009001000,0x0,0x0,0x0,0x180028007000c00,0x0,0x0,0x100028003000800,0x8003000000,0x10003000000,0x880000000000000,0x840000000000000,0x40200000004215]) [(101,0),(101,3),(313,1),(316,6),(316,5),(323,0),(324,0),(120,0),(325,3),(120,3),(325,0)],
  mk [147,20,29,30,36,2,5] 6 0x0 [],
  mk [147,29,30,36,2,4,5,21] 7 (replayWords [0xc050000,0x51a0000,0x0,0x0,0x4080000,0x3]) [(327,0)],
  mk [147,24,29,30,36,2,4,5] 7 0x21 [],
  mk [147,29,30,36,2,4,5] 8 (replayWords [0xb,0x800080000b00008,0xa800068000a,0x68000500004,0x800050000480001,0x80010000108001,0x29400100002,0x940028000000000,0x5ae60000008,0x68000900008,0x80000480005,0x80000800001,0x10000800008,0x28000280008,0x801e0582205,0x8220801e0680004,0x800050000680006,0x800010000100006,0x800068000280002,0x800068000681805,0x81c0581c0681804,0x800010040101404,0x800048000280a02,0x814048000481005,0x816058140481001,0x10000100001,0x100e0100401,0x40100c0280801,0x6010060100205]) [(328,0),(329,3),(328,3),(329,0)],
  mk [29,148,30,36,2,4,5] 7 (replayWords [0x40001000000,0x18001000000,0x5400a0013002400,0x40000000001800,0x0,0x0,0x0,0x400088011002000,0x6000f000000,0x0,0x0,0x34007000e001a00,0x6000b000000,0x0,0x280040008001200,0x40008000000,0x1c0030005000800,0x18003000001,0x40000000000005]) [],
  mk [103,29,30,36,2,4,25] 7 (replayWords [0xa300000000,0x3900000000000,0x0,0x0,0x200800,0x0,0x0,0x200,0x700000000000000,0x0,0x600600000000,0x3600000000500,0x500000000003400,0x103000002104]) [],
  mk [103,29,30,36,2,4,5] 8 (replayWords [0x2,0x68000200006,0x800020000480002,0x48000380003,0x80e038080380003,0x8000300c0300803,0x21000100002,0x480010000212200,0x6,0x800048000800006,0x800068000380003,0x800068000680003,0x30000680006,0x800010000780006,0x800068180200802,0x1c068180480003,0x800038000480004,0x800030000300004,0x800048000100005,0x800048000481002,0x8020140481003,0x800038000380003,0x800038000380003,0x800038000000000,0x390e0000003,0x30000300003,0x3,0x10a000000100202,0x8020060100205]) [(331,0),(332,0)],
  mk [29,53,149,6,2,4,5] 6 0x1001 [],
  mk [103,29,30,149,6,2,4,5] 7 (replayWords [0x1c60,0xa000000,0x0,0x0,0x40000000000030,0x4000000080003]) [(334,0)],
  mk [150,70,6,2,5] 4 0x0 [],
  mk [150,29,6,2,72] 4 0x0 [],
  mk [150,29,89,6,2,5] 5 (replayWords [0x80000000000,0x400002]) [(336,0),(337,0)],
  mk [150,29,30,36,6,2,5] 6 0x1000001 [(338,0)],
  mk [29,30,0,36,2,151,4,5] 7 (replayWords [0x807000000,0x0,0x36540000,0x3020000,0x0,0x14]) [(339,1)],
  mk [103,29,30,36,6,2,4,5] 8 (replayWords [0xb5ac0902f390,0x38018000000,0x28017000001,0x40000005,0xd80000000000000,0x0,0x5000a8015002800,0x0,0x0,0x0,0x440098012002200,0x3c0080010001e00,0x0,0x0,0x0,0x30007000d001803,0x940000000000003,0x9c0000000000005,0x800a00040028000,0x123180000,0x1c050000001ce73,0x800000040000000,0x107300002,0x800000040000000,0x83180000,0x40010002000205]) [(335,5),(335,0),(313,0),(340,4),(122,3),(340,8),(122,0),(216,5),(216,0)],
  mk [29,53,0,2,4,5,26] 6 (replayWords [0x300000,0x800004000000,0x2]) [(200,2)],
  mk [29,30,144,2,4,5,26] 6 (replayWords [0x1000,0x1]) [],
  mk [50,29,30,0,2,4,5,26] 7 (replayWords [0xa0a0000000,0x90000000000050,0x800070006000000,0x0,0x0,0x5,0x400003002000104]) [(342,2),(342,0),(343,0),(201,2),(201,0),(241,0)],
  mk [29,6,2,4,5,32,13] 6 (replayWords [0x100000002000,0x100000000,0x2]) [],
  mk [29,30,1,2,4,5,27,14] 7 (replayWords [0xb000a000,0x9800,0x70000000000,0x6005000004300,0x0,0x2000000000000,0x0,0x104]) [(28,0),(199,2),(345,2),(33,2),(208,1)],
  mk [29,30,36,2,4,5,25,35] 7 (replayWords [0xa008000000,0x6004002000000,0x0,0x0,0x0,0x3]) [(245,4)],
  mk [12,29,30,112,2,4,5] 6 0x200400000002 [],
  mk [12,29,30,36,2,4,5] 7 (replayWords [0x48014000000,0x40013000000,0x0,0x480088010001e00,0x0,0x0,0x0,0x0,0x34007000e001a00,0x0,0x0,0x0,0x2c006000c001600,0x240800000025294,0x8000000e0000000,0x149000004,0xe0000000,0xc5000000,0x100018002000205]) [(348,5),(348,0),(207,5),(207,0)],
  mk [12,29,30,36,2,4,5,25] 7 (replayWords [0x5d00cb0000,0xa0000000000000,0x900080000007060,0x0,0x0,0x5004000,0x30000002014]) [(29,5),(29,0),(202,5),(202,0),(33,5),(33,0)],
  mk [29,30,152,6,2,4,5] 6 0x1001001 [],
  mk [29,30,153,36,2,4,5] 6 0x2100000000002 [(50,0)],
  mk [108,29,30,36,6,2,4,5] 7 (replayWords [0x86760005000040,0x300000201000004]) [(351,5),(351,0),(352,4)],
  mk [29,30,0,36,2,4,5,26] 8 (replayWords [0x1860000000,0xa800280,0xa400280009c00,0x250009800250001,0x990000000000000,0x2a48e02a02a28,0x602a004001d05d0,0x5f79d00008001a0,0x9a09c6da0000000,0x0,0x0,0x190060000000,0x61802956002802,0x975805400400000,0x400544c00000800,0x800924400000,0x0,0x1800100,0xe0003c00,0xf0003800000000,0x0,0x0,0x18000d0000,0xb00030000c0,0x2c00000000000,0x0,0x1882,0x1802862402001,0x800001800461c00,0x1800001800861,0x400001020000000,0xc10000,0x10,0x20000000010416]) [(30,2),(30,0),(44,0),(132,0),(132,3),(206,6),(209,6),(206,5),(209,5),(244,1),(246,1),(332,1),(344,0),(34,6),(346,6),(34,5),(346,5),(46,0),(347,1),(349,1),(350,1),(152,0),(353,7),(152,3),(353,1)],
  mk [154,155,30,1,2,4,5] 6 0x81 [],
  mk [29,30,149,1,2,4,5] 7 (replayWords [0x240000000001200,0x8000f000000,0x800e000001,0x80001806d600000,0x0,0x5800b000000,0x0,0x0,0x0,0x5000a000000,0x0,0x0,0x0,0x8090000000c480,0x9c0000020000203,0x180000000000003,0xa0000000,0x100200000008620,0x8001000005]) [(355,4),(210,6),(214,6),(342,5)],
  mk [29,111,156,6,2,4,5] 6 (replayWords [0xa000200180000,0x0,0x20,0x10000010000003]) [],
  mk [50,29,53,0,36,2,4,5] 7 (replayWords [0x500000a0009,0x0,0x0,0x0,0x8000000000,0x700006000005,0x50004300020104]) [(357,1),(342,0),(79,0),(211,2)],
  mk [154,29,30,157,2,4,5] 6 0x200400000002 [],
  mk [29,30,144,36,2,4,5] 7 (replayWords [0x28011000000,0x38008000f001c00,0x0,0x0,0x0,0x0,0x30006800d001800,0x0,0x0,0x0,0x28005800b001400,0x0,0x0,0x240829c05014c00,0x28005000000,0x28005000002,0xc0000000000001,0x40000000000000,0x5]) [(359,6),(359,5),(319,0),(343,0)],
  mk [50,29,30,144,36,2,4,5] 7 (replayWords [0x6,0x280000000000000,0x0,0x1,0x30000000100000,0x2000000000003]) [(343,0),(78,0)],
  mk [54,0,77,2,5] 4 0x0 [],
  mk [54,0,36,2,68] 4 0x0 [],
  mk [54,69,0,36,2,5] 5 (replayWords [0x800000000,0x4000000002]) [(362,0),(363,0)],
  mk [54,29,30,0,36,2,5] 6 (replayWords [0x320000,0x100002]) [(364,0),(80,0)],
  mk [29,30,0,36,2,55,4,5] 7 (replayWords [0x908000000,0x0,0x74460000,0x5040000,0x302000000,0x14]) [(81,0),(365,0)],
  mk [50,29,30,0,36,2,4,5] 8 (replayWords [0x104000110100003,0x92403003248c02,0x401c00001c01e28,0x400000c00000c00,0xe07c00004100000,0x0,0x0,0x0,0x1d00078001e0,0x7400000000000,0x0,0x1a0,0x70001b0006800,0x0,0x180006400190,0x6000000000000,0x0,0x150,0x5c00160005400,0x120144130100104,0x920000004000100,0x4000,0x100000000000000,0x4500000003c30,0x3,0x870000000000000,0x30a28930934c2,0xc92890070030000,0x71c71c51401,0xc02071801400c10,0x400c01030800406]) [(356,6),(358,2),(356,5),(358,0),(360,0),(361,0),(344,0),(82,0),(366,0),(156,3),(366,3),(156,0),(213,2),(215,2),(213,0),(215,0),(249,0),(250,0)],
  mk [29,30,37,1,2,5,44] 6 (replayWords [0x100000,0x1]) [],
  mk [38,29,30,19,5] 4 0x0 [],
  mk [38,29,30,2,5,44] 5 0x100000000000001 [(369,0)],
  mk [29,30,158,36,2,5,44] 6 (replayWords [0x2000000000,0x0,0x1000000000002]) [(370,0)],
  mk [24,29,30,0,36,2,5,44] 7 (replayWords [0x70000,0xc000000,0x0,0x0,0x0,0x1600030100083]) [(368,6),(368,5),(371,0)],
  mk [159,29,30,36,6,2,4,5] 7 (replayWords [0x200030,0x100000080003]) [],
  mk [29,30,160,36,2,4,5] 6 0x4000001 [],
  mk [56,29,30,0,36,2,4,5] 7 (replayWords [0x807000000000,0x6050000000,0x24,0x320001000000004]) [(374,0),(83,0)],
  mk [20,29,30,0,36,2,5] 7 (replayWords [0x400090011002000,0x800f000000,0x1000e000000,0x0,0x0,0x30006800d001800,0x0,0x0,0x0,0x24005800a001200,0x8008000000,0x10007000000,0x3,0x80000000000002,0x840000000000002,0x30008000c000,0x40200000004210,0x0,0x5]) [(35,4),(35,1),(47,0),(84,0),(217,6),(217,5),(254,0),(327,0)],
  mk [20,29,30,0,36,2,5,21] 7 (replayWords [0xa,0x950000008000000,0x0,0x6100000000000,0x0,0x10000003]) [],
  mk [29,30,0,36,2,4,5,21] 8 (replayWords [0x28a0000000,0x4238a10,0x4000214212960,0x8,0x1e0007c001e0,0x75a71930c6cc3,0x196990400180000,0x400180000800170,0x800170004000,0x4000000000,0x1600a00000000a2,0x800000000000000,0x130005400,0x140004c00000000,0x400120000000000,0x800110000000,0x2800100000,0x0,0xf0004000,0x100003c00000000,0x0,0x2,0x800000003800000,0x28b2c028034a3,0x2c02800000000,0x400000002800000,0x800000000070,0x2400080001c00,0x400060000,0x800050,0x1020000000,0xc10000,0x10,0x20000000010416]) [(36,4),(36,1),(48,0),(85,0),(102,3),(133,3),(218,6),(218,5),(255,0),(328,0),(372,3),(120,0),(373,1),(152,0),(375,0),(376,0),(377,0)],
  mk [161,162,30,1,2,4,5] 6 0x81 [],
  mk [163,164,0,2,4,5] 5 0x0 [],
  mk [161,30,0,36,2,4,5] 6 0x20000000012 [(380,2)],
  mk [29,30,37,1,2,4,5] 7 (replayWords [0x70011000000,0x0,0x300000000001800,0x8000e000000,0x0,0x1000f000000,0xd00000038000,0x7000e000000,0x0,0x0,0x0,0x6800d000000,0x0,0x0,0x0,0xc0c000000086b5,0x120000004,0x1c0000000000003,0xa0000000,0x10030000000c430,0x10001000005]) [(37,6),(379,4),(38,0),(381,1),(49,0),(87,5),(219,6),(368,0)],
  mk [29,33,37,6,2,4,5] 6 0x201000100002 [],
  mk [24,29,30,37,1,2,4,5] 7 (replayWords [0x380,0x0,0x60000001450000,0x46000000004083]) [(383,2),(368,0)],
  mk [161,29,165,2,4,5] 5 0x0 [],
  mk [161,29,30,166,2,4,5] 6 0x200400000002 [(385,0)],
  mk [167,30,36,23,2,4,5] 6 0xc080400000002 [(50,4),(385,1),(385,2)],
  mk [38,29,30,2,8] 4 0x0 [],
  mk [38,29,30,9,2,5] 5 0x200000000000001 [(388,0)],
  mk [11,38,29,30,2,5] 5 0x0 [],
  mk [22,168,29,30,4,5] 5 0x0 [],
  mk [38,29,30,2,4,5] 6 (replayWords [0x8030000000000,0x0,0x0,0x20000400000000,0x0,0x0,0x0,0x0,0x3]) [(389,0),(390,0),(370,0),(391,3)],
  mk [38,29,30,36,2,4,5] 6 0x0 [],
  mk [38,29,30,158,2,4,5] 6 0x80001 [],
  mk [29,30,158,36,2,4,5] 7 (replayWords [0x90014000000,0x0,0x0,0x440098012002200,0x0,0x0,0x1000000048000,0x0,0x440090012002200,0x0,0x0,0x0,0x3c0080010001e00,0x0,0x0,0x240e6b00b029290,0x40007000000,0x30005000002,0xc0000000000001,0x40000000000000,0x5]) [(386,6),(386,5),(38,4),(38,1),(387,1),(51,0),(392,0),(393,0),(394,0),(371,0)],
  mk [169,0,2,4,5] 4 0x0 [],
  mk [38,0,2,4,68] 4 0x0 [],
  mk [38,69,0,2,4,5] 5 (replayWords [0x800000000,0x102]) [(396,0),(397,0)],
  mk [38,29,30,0,2,4,5] 6 0x1001 [(398,0)],
  mk [29,30,0,158,36,2,4,5] 7 (replayWords [0x1,0x850000000008006,0x4000000000013]) [(399,0)],
  mk [24,38,29,30,2,4,5] 6 0x200000000001 [(370,0)],
  mk [24,29,30,158,36,2,4,5] 7 (replayWords [0x200,0x0,0xc20000000000000,0x2000000000003]) [(401,0),(371,0)],
  mk [24,29,30,170,36,2,4,5] 7 0x20001 [],
  mk [171,70,2,4,5] 4 0x0 [],
  mk [171,29,2,4,72] 4 0x0 [],
  mk [171,29,89,2,4,5] 5 (replayWords [0x80000000000,0x400002]) [(404,0),(405,0)],
  mk [171,29,30,36,2,4,5] 6 0x1000001 [(406,0)],
  mk [29,162,30,36,6,2,4,5] 7 (replayWords [0xacb,0xa09800007605000,0x403020001000004]) [(37,1),(38,1),(37,2),(38,2),(49,4),(51,0),(407,0)],
  mk [24,29,30,0,36,2,4,5] 8 (replayWords [0x1d7400,0x1e01d0006c00000,0x6c00000000000,0x0,0x90009000230002,0x400000001c00220,0xc00,0x2100000075d0000,0x0,0x2000000001d0000,0x0,0x1f00074001d0,0x7c00000000000,0x0,0x0,0x79d0000000,0x0,0x1c0006c001b0,0x7000000000000,0x0,0x1a0,0x6c001b0006800,0x170006400180005,0xc00000001c00160,0xc00,0x150000000120005,0x130004804430,0x4,0x70000000000000,0x3ca28938934c2,0xc92890070030000,0x71c71c51401,0xc02071801400c10,0x400c01030800406]) [(382,6),(384,6),(382,5),(384,5),(395,0),(400,0),(402,0),(122,1),(403,0),(408,1),(156,0),(39,4),(39,1),(52,0),(88,0),(372,0),(220,6),(220,5),(257,0),(329,0)],
  mk [29,30,0,36,2,4,5] 9 (replayWords [0x9400004400,0x9000004400008,0xc00002c00008800,0x2c00008400000,0xc00008000000c00,0x7c07802807407,0x6c02806800400,0x400400406400,0x400000800000800,0x800806000800004,0x400002c00005c00,0x4400004400000,0xc00005800004400,0x4404802805405,0x4c04404804400,0x400000400004,0x400004400000800,0x800004400002,0xc00000c00004000,0x2c00002c03002,0x803c03803402c03,0x2c00000400000,0x400002c00002c00,0x800000800002,0xc00000c01802802,0x402001c00c01800,0xc00000400400401,0x400c00000c00000,0x800800801000c00,0x410800000000,0x410,0x400000000000000,0x400400420,0x410416]) [(40,4),(40,1),(53,0),(89,0),(91,0),(123,0),(125,3),(157,0),(91,3),(123,3),(125,0),(157,3),(237,6),(237,5),(240,0),(311,0),(326,0),(330,0),(333,1),(341,1),(354,0),(367,0),(378,0),(409,3),(378,3),(409,0)],
  mk [172,29,30,36,83,4,5] 7 (replayWords [0xe00400000000,0xc00,0xe00000000500e00,0xe00e00000,0xd00000000d00000,0xc00,0xb00000000000000,0xa00000000a00,0x9900,0x0,0x800000000,0x700000000000006,0x5000000000,0x4300000000000,0x200000000,0x200000100100004]) [],
  mk [29,30,36,2,173,174,5] 8 (replayWords [0x800080e,0x80808000800080,0xe08080800050004,0x50004000e000,0x2000e0002000100,0x101010e0100030,0x303030e030001,0x703b0010001177,0x50004d0050004d0,0x8c002000880020,0x6660000000000,0x30803b001000,0x3b3050004a00500,0x4a008900200088,0x2000108017001,0x171066600000,0x4000200,0x50004000400010,0x101050400040003,0x30305040002000,0x100010002000200,0x30003000200010,0x1000100010004]) [(411,3),(411,9)],
  mk [29,175,2,4,27,26] 5 0x0 [],
  mk [29,30,176,2,4,5,26] 6 (replayWords [0x200000,0x4000000,0x2]) [(413,6)],
  mk [29,30,36,2,4,5,177] 6 (replayWords [0x8000,0x1]) [],
  mk [178,29,30,36,2,4,5] 6 0x0 [],
  mk [29,179,36,2,4,5,27] 6 0x200000000001 [(413,1)],
  mk [29,179,30,36,4,5,21] 6 (replayWords [0x100000,0x1]) [],
  mk [29,179,30,36,2,4,5] 7 (replayWords [0x70018000000,0x0,0x18017000000,0x5000b0015002800,0x98012000000,0x440000000001c00,0x0,0x0,0x400088011002000,0x0,0x0,0x0,0x3c007000e001a00,0x4,0x60000000,0x30005800a001200,0x40008000000,0x1c0030005000800,0xc0000000000601,0x40000000000005]) [(414,6),(415,0),(416,0),(417,0),(418,0)],
  mk [180,29,30,36,2,4,5] 6 0x0 [],
  mk [29,30,36,2,4,5,181] 7 (replayWords [0xa,0xd00000000000009,0x801200260048002,0x1100080040007,0x800e001a0030005,0x800900140024004,0x7000c0014000,0x0,0x1,0x40000000,0x0,0x0,0x0,0x0,0x0,0x0,0x20004000002,0x60000000,0x0,0x1,0x20000000,0x5]) [(415,2),(420,5)],
  mk [172,102,30,2,4,25] 5 0x0 [],
  mk [172,30,36,2,4,25,27] 6 (replayWords [0xc000000,0x0,0x8000000042]) [(413,4),(422,0)],
  mk [29,182,30,2,4,5,26] 6 0x0 [],
  mk [172,30,36,2,4,5,25] 7 (replayWords [0xdc00000000000,0x0,0x0,0x0,0xb00000000500,0x0,0x50060000a00000a,0x6000009000,0x802000006800,0x700000000500000,0x0,0x700700,0x500500005,0x6000000000,0x500500000000000,0x4300,0x200100004]) [(417,2),(423,0),(424,8)],
  mk [29,183,30,36,2,4,5] 6 (replayWords [0x8000000000,0x40000000002]) [],
  mk [172,102,29,30,2,4,5] 6 (replayWords [0x800000,0x0,0x42]) [(422,0)],
  mk [172,29,30,36,2,4,5,27] 7 (replayWords [0xba090080000000,0x75650000000000,0x4000000,0x0,0x30000,0x0,0x201000004]) [(414,5),(423,0),(415,2),(426,8),(427,0)],
  mk [172,184,29,30,36,4,5] 6 0x0 [],
  mk [172,29,30,36,4,5,21] 7 (replayWords [0xdd00000000000,0x50c00000c8c0000,0xb000005,0x0,0x500000000608,0x8000000000,0x0,0x600a00,0x900000000900,0x0,0x0,0x800800,0x7,0x6000000000,0x5400000000000,0x300200,0x100100004]) [(418,2),(429,0)],
  mk [172,29,30,36,2,4,5] 8 (replayWords [0x9,0x88000900008,0x800010000100401,0x30010000280002,0x80002800028000a,0x38000b80003,0x800050000501405,0x2c050000a02604,0x8120482a0a02608,0x822010000100008,0x822088000280002,0x800088000880003,0x800090000880008,0x800050000500008,0x800088200902409,0x24088200100001,0x4010040100001,0x8001000013c001,0x10000100001,0x10000101c01,0x4010040101a02,0x800028000280002,0x800029400100002,0xa80028000000000,0x2b160000003,0x800050000500003,0x8000380c0481204,0x8100380c0280801,0x6010060100205]) [(419,2),(411,0),(421,0),(425,0),(428,0),(430,0)],
  mk [28,29,36,2,83,4,27] 6 0x8000000001 [(422,2)],
  mk [29,30,2,185,4,25,26] 6 (replayWords [0x40000000000,0xc00080004002]) [],
  mk [28,30,2,82,4,25,26] 6 0x200010002 [],
  mk [29,30,2,40,4,25,26] 7 (replayWords [0xf00000000f00,0xe00,0x400300000,0x400000000000,0xd00000000200,0x303,0x3c00000400,0x30000b00000a000,0x9300000000000,0x800800000800,0x400000000,0x200800,0x4700000000006,0x3000002000,0x202530004000003,0x4000402430,0x200100004]) [(127,2),(423,1),(129,0),(432,5),(433,0),(434,4)],
  mk [31,29,2,83,4,5,27] 6 (replayWords [0x10000,0x1]) [(288,0)],
  mk [29,30,2,40,4,5,26,13] 7 (replayWords [0xe00000c,0x5c058030000000,0x20000000010,0x0,0x0,0x3]) [(436,5)],
  mk [28,30,36,2,82,4,5,25] 7 (replayWords [0x800000000000,0x0,0x70000006050,0x0,0x0,0x4030000000002,0x10000000000004]) [(434,0)],
  mk [29,30,2,40,4,5,26] 8 (replayWords [0x4,0xd12000000000000,0x5ac00500005,0xac0050000301c02,0x4c002000024c932,0xa024c00200002,0x4c8090000080008,0x800008000800001,0x800078000180005,0x800050000580005,0x301c0294002,0x295c0200002,0x80200a0200002,0x9400080002b4000,0x800029400180002,0xb00018000500005,0x816058160500005,0x14020000200005,0x14050000080005,0x800050000500001,0x800058000500002,0x112000000000000,0x2a000080003,0x14000800029c001,0x800031400180002,0x100020000214002,0x21000200002,0x140020000080001,0x800010000080005]) [(132,0),(425,4),(425,1),(435,0),(435,2),(437,0),(438,4),(437,2),(438,1)],
  mk [29,30,36,2,82,4,27,26] 7 (replayWords [0x50000000,0x0,0x0,0x0,0x1100d00000100,0x100000080000003]) [(126,0)],
  mk [28,29,30,36,2,83,4,5] 7 (replayWords [0x300000000000,0x0,0xa0400000064b0,0x4080000,0x3]) [(427,2),(432,0)],
  mk [29,30,36,2,186,4,5,27] 7 (replayWords [0xe001,0x880000000000000,0x280,0x0,0x200000d00000000,0x80000000000003]) [(433,6)],
  mk [187,29,30,36,2,4,5,26] 7 (replayWords [0xc0000000000080,0x0,0x40000002]) [],
  mk [29,30,36,2,82,4,5,27] 8 (replayWords [0xd,0x880000000000005,0x1a0014006800b,0x16c5cdec5b17172,0x1525485b5400a,0x1200260048008,0x940000000000000,0x801000020040000,0x0,0x3c0028005001e00,0x20005000002,0x8000001c0000000,0x140200000008400,0x800008025680000,0x30005000a001800,0x2c0000000001600,0x0,0x1000a000000,0x800a000002,0x40000000000004,0x8008000a0020001,0x611847298002,0x100000000000002,0xa0000002,0x20044280000,0x100100000010800,0x10003000000,0x1,0x20000005]) [(128,1),(428,0),(435,6),(440,0),(131,0),(441,2),(442,0),(443,5)],
  mk [29,188,30,36,83,4,5] 6 0x0 [],
  mk [56,29,30,36,82,4,5] 7 (replayWords [0xf00e00000000000,0xc00e00,0xd00d00000,0x0,0x0,0xc00b00,0xa00000000a00,0x9000,0x5000008800000,0x700000000,0x600000000000000,0x0,0x5400000000000,0x300200,0x100000000104]) [(445,2),(429,5)],
  mk [29,30,36,2,173,5,44] 8 (replayWords [0x3,0x9ce000000000000,0x40180134001,0x1344d301002,0xc000300002c0d04,0x3c0018000420001,0x800043800080004,0x200008000101001,0x340010000134404,0x18042000100004,0x218031800280003,0x180028000580001,0x800058000180005,0x800008000580000,0x800010000100401,0x16010000318002,0x800031800280004,0x280018000420001,0x800042400080004,0x20000800039ce00,0x2,0x800018000300002,0x800028000080003,0x28000280001,0x40100c0280001,0x800008000200001,0x800018000100001,0x18000080001,0x10000080005]) [(133,4),(430,10),(430,3),(446,10),(446,3)],
  mk [189,2,85,4,5] 4 0x0 [],
  mk [29,190,2,84,4,5] 5 0x20001 [(448,2)],
  mk [191,36,2,86,4,5] 5 (replayWords [0x8000000,0x42]) [(448,1),(136,1)],
  mk [191,29,36,2,46,4,5] 6 (replayWords [0x90800,0x0,0x706000000000005,0x40,0x300000201000004]) [(449,5),(450,0)],
  mk [192,29,2,46,4,5] 5 0x0 [],
  mk [29,30,2,193,85,4,5] 6 0xc20001000000002 [(450,6),(452,6)],
  mk [194,29,30,2,4,195,5] 6 0x0 [],
  mk [196,30,36,2,197,4,5] 6 0x0 [],
  mk [29,30,2,193,4,5] 7 (replayWords [0x7,0x700070007000,0x800090008000800,0x20002020208020,0x8000800080008,0x110010101180,0x200070007000700,0x70002070200020,0x2020700070007,0x700010001000,0x100010002000200,0x20002000600050,0x4000300010001,0x100010002000,0x200020002000200,0x20002000200010,0x1000100010004]) [(451,6),(453,0),(454,9),(455,1)],
  mk [163,29,30,2,84,4,5] 6 0x80000001 [],
  mk [196,29,30,36,2,4,5] 6 0x21 [],
  mk [29,30,36,2,197,4,5] 7 (replayWords [0x5800a8014002600,0x28006000000,0x0,0x800008026000000,0x180010006000400,0x480088011002400,0x440000000000a00,0x0,0x0,0x440010011000402,0x8010000a003c007,0xc001a0030005,0x800a00120020003,0x980000000000000,0x0,0x0,0x140028005000a00,0x0,0x100010003000400,0x40008001000205]) [(134,4),(457,4),(138,1),(458,0)],
  mk [29,30,77,2,47,5] 5 0x21 [(139,1)],
  mk [29,30,36,2,87,72] 5 0x2001 [(140,0)],
  mk [69,29,30,36,2,47,5] 6 (replayWords [0x90800,0x0,0x706000000000000,0x50400000000030,0x200010000000004]) [(141,0),(460,0),(461,1)],
  mk [163,29,30,36,2,198,5] 6 0x0 [],
  mk [29,30,36,2,87,5] 7 (replayWords [0x8,0xa00090009000,0x660060606680600,0x80008000800080,0x8000800080008,0x100010101080,0x600060706000600,0x60607000700070,0x7000700070007,0x700010001000,0x100010006000600,0x60006000600060,0x6000600060006,0x600060005000,0x400030002000100,0x10001000100010,0x1000100010004]) [(462,4),(142,4),(463,2),(463,1)],
  mk [29,30,36,2,199,4,5] 8 (replayWords [0xa,0x98000a00009,0x80005aee0000000,0x294002,0x80a029560280005,0x800018000580001,0x800058000080005,0x800008000108001,0x4010960280009,0xd2b5a0280a2e969,0x82a098260280002,0x800098260980001,0x8000a0000980009,0x800008000a00009,0x800098000100001,0x98000294002,0xc8a0294512c0005,0xac001b56d5bd6e1,0xb4005ac000a5695,0xb16a0a40029c001,0x204029ca7298002,0x800028000280002,0x800028000280002,0x800028000280002,0x800028000280001,0x800008000200001,0x800018000100001,0x18000080001,0x10000080005]) [(143,4),(456,5),(459,2),(456,0),(459,1),(464,0)],
  mk [29,200,30,36,2,4,5] 6 0x400001 [],
  mk [163,201,29,30,2,4,5] 6 0x21 [],
  mk [114,29,30,36,2,4,5] 7 (replayWords [0x58016000000,0x0,0x0,0x5400a0013002400,0x0,0x0,0x0,0x0,0x400088011002000,0x7000e000007,0x120000000,0x0,0x3c007000e001a00,0xc0000002c005,0x800000140000000,0x128000000,0x0,0x140038006000a00,0x100018002000205]) [(466,2),(147,0),(467,2)],
  mk [90,30,70,36,2,5] 5 0x200001 [(148,0)],
  mk [90,29,30,36,2,72] 5 0x2000001 [(149,0)],
  mk [90,29,89,30,36,2,5] 6 (replayWords [0x9080000000000,0x70600000,0x500000000,0x0,0x430021000004]) [(469,0),(150,0),(470,0)],
  mk [90,202,29,30,36,2,5] 6 0x0 [],
  mk [90,29,30,36,2,5] 7 (replayWords [0x8,0x800080008000,0xa000a000a000a00,0xa000a000a000a0,0x1000100080001,0x200030009000,0x900080008000800,0x80008000800080,0x8000800080008,0x800020008000,0x800080007000600,0x50004000100010,0x1000100030003,0x300030001000,0x100010001000300,0x30003000300020,0x1000100010004]) [(471,0),(151,0),(472,0),(472,5)],
  mk [29,30,36,2,4,5,203] 8 (replayWords [0x3,0x44c000000000000,0x420d03bc004,0x20003bd0f294c00,0x3,0x38001b400318001,0xb400330000ac003,0x18000ac00128c00,0x4,0x38000400003,0x800028000280002,0x800028000480001,0x800048000180004,0x800008000480000,0x800010000100002,0x800010000380002,0x800028000380003,0x800018000400003,0x800038000080004,0x38000380001,0x4010100380002,0x940028000298002,0x800029400280002,0x980028000280002,0x800028000280001,0x800008000200001,0x800018000100001,0x18000080001,0x10000080005]) [(152,4),(468,5),(468,0),(473,0)],
  mk [92,29,30,36,2,4,5] 8 (replayWords [0x8,0x800080000880008,0x10800100001,0x80010000400005,0x800040000580004,0x38000400003,0x800029400100002,0x940028000000000,0x9ce40000008,0x10000100008,0x80000580008,0x800080000800003,0x800088000800008,0x280a0282208,0x801e0882208,0x8220801e0108001,0x12000100001,0x80010000120001,0x10000100001,0x10000101c01,0x4010040101a05,0x800038000600005,0x800058000280002,0x800058000581404,0x12040100581403,0x800028000280003,0x8000380c0401204,0x100380c0280801,0x6010060100205]) [(153,0)],
  mk [204,29,30,36,2,4,5] 6 0x0 [],
  mk [29,205,30,36,2,4,5] 7 (replayWords [0x78001000000,0x0,0x40001000000,0x0,0x500098012002200,0x40000000000800,0xd0000003c000,0x0,0x0,0x40007800f002000,0x7800f000000,0x0,0x0,0x38006800d001c00,0x2000d000000,0x0,0x30005800a001200,0x40008000000,0x140038006000a00,0x20003000001,0x40000000000005]) [(154,6),(155,0),(476,5)],
  mk [49,29,30,36,2,4,5] 8 (replayWords [0xe000e0e,0xe040e000d000c0,0xd000c000e000a,0xa0a040a0004000,0x600040006000400,0x20004000200044,0xf0000000000000e,0xec00e000ee00,0xe000e000e000e00,0xe000e000e000e0,0xe000e000e000e,0xe4e0,0xc000a000a00,0xc000c0006000d0,0xc000c0002000d,0xc000c0b0d0d0,0xd0d0c0b0a000a00,0xa000a000a000a0,0xa000a00000000,0xa49000006000,0x200080006000605,0x40404070605020,0x104040403020104]) [(477,0),(477,2),(156,0)],
  mk [29,30,36,2,82,4,5] 9 (replayWords [0x8,0x800080000880008,0x50360a83405,0x320a8300280002,0x80a0282e028000a,0x800018000b00001,0x8000a800008000a,0x8000100001,0x4010260100008,0x24088220882208,0x24080200280002,0x800080200800001,0x800088000800008,0x8000880008,0x80000100401,0x22080000294400,0x6,0x3c001b400538001,0xb40062c000a0005,0x24000a000294a00,0x2,0x94002800029c002,0x800029400280002,0x980028000280a02,0x880000000294a01,0x800008000200001,0x800018000100001,0x18000080001,0x10000080005]) [(157,4),(412,3),(412,7),(91,0),(431,5),(91,1),(431,0),(439,4),(444,0),(444,5),(447,3),(465,0),(474,0),(475,0),(478,8)],
  mk [154,29,2,4,27,26] 5 0x0 [],
  mk [154,29,36,2,4,5,27] 6 0x20000000000001 [(480,0)],
  mk [28,29,149,2,4,27] 5 0x0 [],
  mk [29,52,30,2,4,27,26] 6 (replayWords [0xc0000000,0x2004002]) [(200,0),(480,5),(482,6)],
  mk [28,30,156,2,4,5,25] 6 0x100000000001 [],
  mk [29,52,30,2,4,5,26] 7 (replayWords [0xbb00000000000,0x0,0x0,0xf00000000,0xc00e00000000400,0x0,0x100000d,0xbc0000b000,0xc0411000b000400,0x0,0xa00,0xa00000000400900,0x0,0x800800000000,0x400700000000600,0x500000000400300,0x2100000000004]) [(342,2),(343,0),(481,5),(483,0),(484,4)],
  mk [50,110,29,30,2,4,26] 6 0x20001 [(482,5)],
  mk [50,206,29,2,4,27,26] 6 0x11 [],
  mk [50,29,30,2,4,25,26] 7 (replayWords [0x400000000002000,0x0,0x0,0x0,0x3c0000000000207,0x340000000000000,0x0,0x6,0x160000005,0xc0000000000004,0xa00000000000000,0x0,0x0,0x8007000000,0x18007000000,0x0,0x8006000000,0x18006000000,0x8005000000,0x18004000000,0x308c02004005]) [(483,2),(201,2),(241,0),(486,0),(487,2)],
  mk [50,122,29,2,4,5,26] 6 0x80000000000000001 [],
  mk [50,29,30,2,4,5,26,13] 7 (replayWords [0x6000000,0xa040006000000,0x22000,0x0,0x0,0x3]) [(489,0)],
  mk [50,206,29,30,2,4,5,26] 7 (replayWords [0xc000000,0x280001010000,0x0,0x0,0x180000004013]) [(484,1),(487,0)],
  mk [50,29,30,2,4,5,26] 8 (replayWords [0x6,0x318000000000000,0x50000480005,0x48000400003,0x80004000038000a,0x800020000a00002,0x98000080009,0x80006460f0,0x1,0x800048000180004,0x800018000380001,0x80003800018c002,0x1b800200001,0x8c00080001b4000,0x800063180000000,0x480003,0x800058000480004,0x800020000500004,0x800048000080005,0x48000480001,0x806018140480003,0x800020000400003,0x800038000080004,0x38000380001,0x806018100380002,0x8000300002,0x20000180601,0x80a020000080001,0x806018040080005]) [(485,0),(485,2),(344,0),(488,0),(488,2),(490,0),(491,2),(490,2),(491,0)],
  mk [103,102,29,2,4,27,26] 6 0x800000000001 [],
  mk [28,29,112,2,4,27] 5 0x0 [],
  mk [29,113,30,2,4,27,26] 6 (replayWords [0x80000000,0x1000002]) [(480,5),(494,6)],
  mk [28,29,30,2,4,32,26] 6 (replayWords [0x200000000000,0x0,0x10002]) [(25,5)],
  mk [28,110,29,30,2,4,26] 6 0x800040000002 [(494,5),(203,0)],
  mk [28,120,30,2,4,25,26] 6 (replayWords [0x1000000,0x11]) [],
  mk [28,29,30,2,4,25,26] 7 (replayWords [0x40000000000200,0x0,0x0,0x0,0x400000000000600,0x3c0000000000200,0x0,0x7,0x1a0000001,0xb00000000000000,0x840000000000000,0x0,0x0,0x1800b000000,0x5000a000000,0x0,0x18009000000,0x40008000000,0x18007000000,0x30005000000,0x418801004005]) [(493,2),(495,2),(202,0),(205,0),(434,0),(434,3),(487,6),(496,0),(497,0),(498,0)],
  mk [28,29,30,2,4,27,26] 6 (replayWords [0x300000000000,0x0,0x810002]) [(170,0),(184,0)],
  mk [31,29,30,2,4,25,26] 6 (replayWords [0x200000000000,0x0,0x102]) [(170,2)],
  mk [29,30,36,2,4,25,27,13] 7 (replayWords [0xa0080000,0x900,0x870000003000000,0x0,0x60054003,0x0,0x0,0x20000000104]) [(171,1),(199,0),(496,5),(243,0),(500,4),(501,5)],
  mk [12,28,29,36,2,4,27] 6 0x8040000002 [(494,0),(25,0)],
  mk [28,102,29,30,2,4,25] 6 0x800000001002 [(172,0)],
  mk [28,29,30,36,2,4,27] 7 (replayWords [0xf00,0x10ed00000,0x0,0xc00000000b00,0x0,0x400,0xa00000000000000,0x0,0x0,0x400900000000000,0x0,0x4140101001,0x7000000000,0x8100004000407,0x460000305000004,0x300000200100004]) [(503,0),(173,0),(243,0),(432,0),(432,3),(486,5),(504,2)],
  mk [28,29,30,36,2,4,25,27] 7 (replayWords [0x70000,0xc0000000000,0xb0a0000000000,0x908007000000000,0x0,0x0,0x700006000,0x50040302014]) [(202,5),(174,0),(204,0),(497,5),(243,0),(504,0)],
  mk [114,29,30,2,4,25,26] 6 0x41 [],
  mk [90,29,30,36,2,25,27] 6 (replayWords [0x200000000000,0x0,0x400002]) [(179,5)],
  mk [29,30,36,2,4,25,27,203] 7 (replayWords [0x90050000,0x800700000000600,0x540000003000000,0x0,0x0,0x0,0x2000,0x104]) [(180,1),(507,5),(508,0)],
  mk [108,29,30,36,2,4,25,27] 7 (replayWords [0x60000000,0x0,0x0,0x200000,0x0,0x281030813]) [(182,5)],
  mk [29,30,36,2,4,25,27] 8 (replayWords [0x404800dc0,0x400000414929,0x800002c00009400,0x2c00009000001,0xc00008c00001c00,0x8a10001000008,0x1f0001000000417,0x800000000000000,0xc07400dc0,0x400000dc0c06,0xc00002c00006800,0x2c00006400001,0xc00006000001c00,0x5d60001000005,0x540001000000404,0xc00520000400000,0x520400d14000000,0x2,0xc00001c00003c00,0x2c00002c00001,0x3800002c00,0x2c00000400400,0x403402c00002c00,0xc00c00c03002,0xc00001c00001000,0x2800001c00001,0xc00000400400402,0x401c00001c00000,0xc00c00c02001c00,0x1000000400400,0x401801000001000,0xc00c00c01401,0x410000400,0x400430420400006]) [(183,1),(206,4),(206,1),(435,6),(435,5),(440,1),(435,11),(435,10),(440,7),(488,6),(499,5),(244,2),(502,0),(505,0),(506,0),(509,0),(510,3),(509,3),(510,0),(499,6),(488,5),(244,0),(502,2),(505,2),(506,2),(509,2),(510,9),(509,9),(510,2)],
  mk [29,30,36,2,4,25,27,26] 7 (replayWords [0x24a0,0x24600000000000,0x880107800e0,0x1ac00000000005,0x800a00000480080,0x380062,0x800400000000000,0x0,0x0,0x6000040000205]) [(185,1),(185,2),(185,0),(500,5),(500,0),(500,6),(500,2),(500,4),(500,1)],
  mk [50,110,29,36,2,4,27] 6 0x0 [],
  mk [50,29,30,36,2,4,25,27] 7 (replayWords [0xa90000,0x800,0x700000000000000,0x6005000000000,0x0,0x0,0x0,0x40020302014]) [(186,0),(513,0),(513,2)],
  mk [20,29,30,36,2,25,27] 6 (replayWords [0x200000000000,0x0,0x400002]) [(192,1)],
  mk [29,30,36,2,4,25,27,21] 7 (replayWords [0xa0009,0x800700000000500,0x650040003000000,0x0,0x0,0x0,0x2000,0x200000000000104]) [(193,1),(515,0)],
  mk [24,29,30,36,2,4,25,27] 7 (replayWords [0x50000000,0x0,0x0,0x0,0x0,0x200830813]) [(195,1)],
  mk [29,113,30,2,4,5,26] 6 0x0 [],
  mk [28,120,30,2,4,5,25] 6 0x0 [],
  mk [28,29,30,2,4,5,26] 7 (replayWords [0x840000000000000,0x0,0x0,0x1100000044003,0x400000020000c07,0xb9a000020001200,0x0,0x6,0x160000003,0x20000000,0xa80000020001200,0x0,0x0,0x0,0x40008000000,0x0,0x0,0x38007000000,0x30005000000,0x20003000000,0x10001000005]) [(518,2),(207,0),(208,0),(500,0),(513,5),(519,4)],
  mk [28,29,30,2,4,5,25,26] 7 (replayWords [0x4100000000,0xe00c000000,0xa000,0x8034020,0x0,0x403]) [(487,6),(519,0)],
  mk [28,102,29,30,2,4,5] 6 0x800000000042 [(196,0)],
  mk [28,29,30,36,2,4,5,27] 7 (replayWords [0xe00d0000000,0xcba90000000000,0x807004000000650,0x0,0x0,0x400000000,0x30020100004]) [(207,5),(197,0),(486,5),(500,0),(522,0)],
  mk [29,30,36,2,4,5,25,27] 8 (replayWords [0x9555e75d0,0x820825550820000,0x1c00,0x250001c00250001,0x800240001800240,0x8c00210008800,0x210000890000000,0xe07de0,0x8001e0de7430,0x1,0xc001c0001c001c0,0x18001b0001800,0x1b0006800180006,0x400180000975950,0x800150955090,0x4,0xc00110004800110,0x40000e0003c00,0xe00034000b0003,0xb0000892820,0x20820c92,0x30000000030c30,0x0,0x0,0x800,0x70000000000000,0xc00070000000000,0x0,0x800060000,0xc00060,0x800,0x50000000000000,0xc00040000000800,0x800c20400006]) [(198,1),(209,4),(209,1),(488,6),(488,5),(512,0),(514,0),(516,0),(517,3),(516,3),(517,0),(520,5),(521,5),(246,2),(523,0),(520,6),(521,6),(246,0),(523,2)],
  mk [154,29,155,30,2,4,26] 6 0x41 [],
  mk [28,29,30,149,2,4,25] 6 0x41 [],
  mk [29,52,30,36,2,4,27] 7 (replayWords [0xe100000,0xd00000000,0xc00b00000000500,0x0,0x400,0xa00000000000000,0x500a00000,0x0,0x400900000000000,0x500900,0x800800000,0x800800000000,0x800800000607000,0x4604000405430,0x2100000000004]) [(210,1),(525,5),(526,6)],
  mk [154,207,29,30,2,4,26] 6 (replayWords [0x800,0x0,0x4000000002]) [(480,0)],
  mk [50,110,29,53,36,2,4] 6 0x20000001 [(482,5)],
  mk [50,29,52,30,36,2,4,27] 7 (replayWords [0xa090800,0x0,0x0,0x0,0x0,0x700605004002,0x30000000002014]) [(211,0),(528,5),(483,0),(529,2)],
  mk [50,31,29,30,2,4,25] 6 0x0 [],
  mk [50,29,30,36,2,4,25,32] 7 (replayWords [0xc,0x50008006000000,0x4010000000,0x0,0x0,0x3]) [(247,0),(513,2),(531,0)],
  mk [50,110,29,30,36,2,4] 7 (replayWords [0xa00000000a00000,0xa00a00000c00000,0xc0000000ba00,0x6000009000000,0x8700006000,0x5000000000400,0x300000000000000,0x2000001000004]) [(529,0),(247,0),(486,0)],
  mk [50,110,29,30,36,2,4,25] 7 (replayWords [0x380000000000000,0x0,0x0,0x300,0x281030004013]) [(526,5),(212,0),(247,0)],
  mk [50,29,30,36,2,4,25] 8 (replayWords [0x7,0x68000700006,0x800060000580006,0x58000180001,0xe000180001e000b,0xd80028000ad0002,0x800014c80000000,0x946000,0x6,0x800058000780006,0x800068000180001,0x800068000680002,0x800070000680006,0x800010040101c06,0x800068000200007,0x68000580001,0x800018000580005,0x800028000600005,0x800058000100401,0x18058000580002,0x60000580001,0x800018000180001,0x800018000180601,0x806018000000000,0x1a860000002,0x800010040101202,0x800028000201003,0x80c028000100201,0x100018000108205]) [(527,2),(530,2),(332,0),(213,2),(488,0),(249,0),(532,0),(533,0),(534,0)],
  mk [154,29,30,2,4,5,26] 6 (replayWords [0x800,0x40000000000,0x2]) [(480,0)],
  mk [28,29,30,149,2,4,5] 6 (replayWords [0x800000,0x0,0x400000002]) [(482,0)],
  mk [29,52,30,36,2,4,5,27] 7 (replayWords [0xfed,0xcb00a0000000000,0x905008007650040,0x0,0x0,0x0,0x302001000004]) [(214,1),(536,5),(483,0),(537,6)],
  mk [50,110,29,30,36,2,4,5] 7 (replayWords [0x9000800000002,0x700000000000000,0x0,0x0,0x0,0x60,0x500000000043214]) [(537,5),(513,0),(486,0)],
  mk [50,29,30,36,2,4,5,25] 8 (replayWords [0x8,0x880000000000005,0x801900160064004,0x801800120060001,0x80170006005c00b,0x14002a0050009,0x900000000000008,0xca2000000000002,0x1000160040002,0xf0012003c000,0x31806470c002,0xc001a0030001,0x108200000008421,0x8c0000000000000,0x0,0x0,0x0,0x1000b000000,0x28002000b001400,0x0,0x0,0x10009000000,0x200020009001000,0x0,0x18003000000,0x83000000,0x10007000000,0x140020006000a00,0x40411003008215]) [(538,2),(215,2),(514,0),(488,0),(250,0),(539,0)],
  mk [20,28,29,30,36,2,5] 6 0x0 [],
  mk [28,29,30,36,2,4,5,21] 7 (replayWords [0x8007,0x0,0x65430000000000,0x0,0x0,0x0,0x2010000000000,0x4]) [(541,0)],
  mk [20,29,30,36,2,5,25] 7 (replayWords [0x9,0x840000000000002,0x800a000a0028009,0x1000220040007,0x800d001c0034006,0x180000000000005,0x800a000a0028000,0x4,0x120000004,0xe0000000,0x180100000004200,0x0,0x0,0x0,0x28005000000,0x0,0x0,0x8004000000,0x0,0x8003000000,0x0,0x200000004005]) [(217,6),(217,4),(515,0),(515,1),(254,0),(541,5),(254,1),(541,0)],
  mk [29,30,36,2,4,5,25,21] 8 (replayWords [0x2,0xc635a50a5296312,0x940000000000003,0x1359000c0064d92,0x9c000000000000b,0x180008006000b,0x170008005c001,0x12d5000a005455a,0x80000000000003,0x13000c004c002,0x9251000a0044b18,0xe001e0038006,0x800b0018002c005,0x1c0000000000003,0xc0000000,0x1c0500000014a02,0x120000002,0x100000000,0x1c0200000008400,0x28006000000,0x0,0x0,0x10006000002,0x800000080000002,0x800000080000002,0x800028045200000,0x0,0x10003000000,0x10001000005]) [(218,6),(218,4),(516,0),(516,1),(255,0),(542,5),(255,1),(542,0),(543,0)],
  mk [161,29,30,2,4,5,26] 6 0x80000000000000001 [],
  mk [28,29,30,37,2,4,5] 6 0x80001 [],
  mk [29,162,30,36,2,4,5,27] 7 (replayWords [0xba9,0x870060000000000,0x5040000,0x0,0x0,0x0,0x302001000004]) [(219,1),(545,5),(546,6)],
  mk [24,28,29,30,36,2,4,5] 7 (replayWords [0xc280000,0x8d13]) [(546,0)],
  mk [24,29,30,36,2,4,5,25] 8 (replayWords [0x8,0x80000000000001,0x801a00060068006,0x190018006400c,0x16002e005800a,0x80130028004c009,0x100000000000008,0x460000000000000,0x31800400c006,0x180000002,0x1e0000002,0x1c0000000,0x100200000008401,0x8c0000000000000,0xd0000000c000,0x0,0x0,0x18003000000,0x83000000,0x0,0x0,0x1000c000000,0x2c006000c001600,0x0,0x1000a000000,0x200020009001000,0x10007000000,0x140020006000a00,0x40411003008215]) [(547,2),(220,6),(547,1),(220,4),(517,0),(517,1),(257,0),(548,5),(257,1),(548,0)],
  mk [28,29,30,2,4,5,25,13] 7 (replayWords [0x200a000000,0x46004000000,0x2000,0x0,0x0,0x3]) [(519,0)],
  mk [29,30,36,2,4,5,32,13] 7 (replayWords [0x87620000,0x500,0x400000000000000,0x3002000000000,0x0,0x0,0x0,0x10000000004]) [(345,0),(269,0),(269,5)],
  mk [28,29,30,36,2,4,5,32] 7 (replayWords [0x50080000000,0x70000000000000,0x600000000000010,0x0,0x0,0x500004000,0x30200014]) [(33,5),(223,0),(496,0)],
  mk [31,29,30,208,4,5] 5 0x0 [],
  mk [90,31,29,30,2,5] 5 0x0 [],
  mk [31,29,30,2,4,5,203] 6 (replayWords [0x81000000000,0x0,0x2]) [(553,3),(554,0)],
  mk [90,29,121,36,2,5] 5 0x0 [],
  mk [90,29,30,36,2,5,32] 6 (replayWords [0x810000000,0x0,0x2]) [(556,5),(554,0)],
  mk [29,30,36,2,4,5,32,203] 7 (replayWords [0xba930000,0x800700000000600,0x500000000000040,0x32001000000000,0x0,0x0,0x0,0x4]) [(555,0),(306,5),(557,0)],
  mk [108,31,29,30,2,4,5] 6 0x0 [],
  mk [108,29,30,36,2,4,5,32] 7 (replayWords [0xc20000,0x400000000000000,0x0,0x2]) [(559,0)],
  mk [28,29,121,2,4,5,26] 6 (replayWords [0x2400,0x0,0x2]) [],
  mk [28,122,29,2,4,5,26] 6 0x80000000000000001 [],
  mk [28,29,30,2,4,5,26,13] 7 (replayWords [0x8000,0x7006500,0x40000000000000,0x300210000,0x0,0x0,0x0,0x4]) [(259,0),(519,4),(561,0),(562,0)],
  mk [125,30,36,2,4,5,27,14] 7 (replayWords [0x200c000000,0xa008006000000,0x4010000000,0x0,0x0,0x3]) [(260,2),(561,1)],
  mk [12,31,29,2,4,5,27] 6 (replayWords [0xc0800,0x1000000000,0x2]) [],
  mk [31,29,30,209,2,4,5] 6 0x200001 [(288,2)],
  mk [107,122,29,36,2,4,5] 6 0x0 [],
  mk [31,29,30,2,4,5,25] 7 (replayWords [0x840000000000008,0x8010001e0038006,0x800c00160028001,0x80030006000c000,0xa00000000000004,0x80030006000c000,0x0,0x1,0x800000060000000,0x200100000004200,0x700000018000,0x0,0x0,0x8005000000,0x0,0x0,0x8004000000,0x0,0x18003000000,0x0,0x200000004005]) [(565,2),(436,2),(436,9),(531,0),(489,6),(566,0),(555,0),(567,6),(559,3),(566,3),(555,3),(567,11),(559,0)],
  mk [31,29,30,2,4,5,25,32] 7 (replayWords [0x200a000000,0x8006000000,0x4010000000,0x0,0x0,0x3]) [(261,5),(562,6)],
  mk [31,29,30,36,2,4,5,25] 7 (replayWords [0xeada0000000,0xcba90000000080,0x700000000006050,0x0,0x0,0x43000,0x2014]) [(207,6),(226,2),(501,0),(531,0),(269,0)],
  mk [29,30,36,2,4,5,25,32] 8 (replayWords [0x418c00000,0x8628400,0x8000,0x1f00080001f0007,0x8001d00078001d0,0x71b6970006400,0x1761704b0000000,0xd65400,0xc30,0x5,0x120004c00120,0x44000f0004000,0xf00038000c0003,0x4000c00004b2810,0x10410c70,0x0,0x0,0x0,0x2400000002,0x400000,0x400000000070,0x30000000030c00,0x0,0x0,0x0,0x0,0xc00060000000000,0x0,0x0,0xc00050,0x400,0x40000000000000,0xc00020000000000,0x400010000006]) [(227,4),(346,1),(437,6),(437,11),(490,6),(502,5),(532,0),(262,5),(550,5),(551,0),(552,0),(558,0),(560,3),(558,3),(560,0),(520,6),(563,6),(564,1),(347,0),(568,0),(569,0),(570,0)],
  mk [29,113,30,36,2,4,5] 7 (replayWords [0x20013000000,0x0,0x480088004002000,0x0,0x0,0x0,0x0,0x38007800f001c00,0x0,0x0,0x0,0x30006800d001800,0x2,0x160000000,0x280722404011000,0x720004010000,0x180028004000600,0x1,0x40000000000005]) [(348,6),(518,0)],
  mk [28,29,30,210,36,2,4,5] 7 (replayWords [0x450400000200000,0x6000000810003]) [(348,5),(258,2)],
  mk [28,29,30,112,2,4,5] 6 (replayWords [0xc00000,0x0,0x800400002]) [(221,0),(494,0)],
  mk [12,28,29,30,36,2,4,5] 7 (replayWords [0x800000000,0x0,0x0,0x0,0x70000006,0x500040302000,0x10004]) [(348,5),(228,0),(574,0),(33,0),(503,0)],
  mk [211,28,29,30,36,2,5] 6 0x0 [],
  mk [28,29,30,36,2,212,4,5] 7 (replayWords [0x1440,0x0,0x6000,0x810000,0x3]) [(576,0)],
  mk [28,29,30,152,2,4,5] 6 0x80001 [],
  mk [213,28,29,30,36,2,4,5] 7 (replayWords [0x8180000,0x0,0x100000,0x2003]) [(578,0)],
  mk [28,29,30,36,2,4,5] 8 (replayWords [0x9800005400,0x9400005400009,0x3c00008c00,0x3c00000800000,0x800800808800800,0x8600001c00007,0xde0001c00001000,0x1000000800001,0x807401007,0x800800806c05,0x400003c00006800,0x5400005400000,0x800000800005400,0x5400001c00006,0x400005400005400,0x1000001000005,0x400005405006005,0x805c05805405003,0xc00000800000800,0x3c00003c00001,0xc00004c00003c00,0x3c00001000001,0x3c00003c03,0x804804004404003,0xc03800800000870,0x800000820000,0x820000800000840,0x800000000000,0x8d0800000,0x1c00001001001,0x3001c00001c01,0x802c02802402001,0xc01800801401000,0xc00800800800406]) [(572,2),(573,0),(349,0),(575,0),(229,0),(262,0),(577,0),(579,3),(441,0),(577,3),(579,0),(441,3),(505,0),(523,0),(533,5),(539,5),(520,0),(542,0),(548,3),(542,3),(548,0)],
  mk [103,102,29,36,2,4,5,27] 7 (replayWords [0xc000000,0x280001030000,0x0,0x0,0x100000002003]) [(484,2),(493,0)],
  mk [29,113,30,36,2,4,5,27] 7 (replayWords [0xdc00000ba9,0x180070000000000,0x600000050100000,0x0,0x0,0x40030000,0x201000000004]) [(536,5),(222,0),(495,0),(574,6),(258,0)],
  mk [28,110,29,30,36,2,4,5] 7 (replayWords [0xd000c00000000,0xb00010000000000,0x0,0x0,0x100a0209,0x80000070,0x600005000143214]) [(574,5),(224,5),(574,0),(224,0),(497,5),(497,0)],
  mk [90,28,29,30,36,2,5] 6 0x0 [],
  mk [28,29,30,36,2,4,5,203] 7 (replayWords [0xa040000,0x6000000,0x0,0x0,0x810000,0x3]) [(584,0)],
  mk [108,28,29,30,36,2,4,5] 7 (replayWords [0x4380000,0x0,0xc280000,0x8d13]) [(578,0)],
  mk [28,29,30,36,2,4,5,25] 8 (replayWords [0xc30000000,0x84001f0,0x80001f0007800,0x1c00074001c0000,0x10410496c10,0x68000b0006400,0xb0000d30000000,0x416000,0x0,0x0,0x0,0x400000400575,0x800005400000005,0x130030,0x30c00010,0x34920010010410,0x0,0x0,0x0,0x0,0xc001100000000f0,0x4000100003c00,0x0,0x0,0xc00,0xe00000000c0003,0x4000d0003000000,0xb0000000010000,0x400000400c12800,0x2410,0xc00,0x80000000050001,0xc00060001400010,0x40c20010010416]) [(581,2),(582,2),(350,0),(230,0),(550,0),(225,0),(438,0),(438,3),(491,6),(506,0),(534,5),(499,0),(521,0),(552,0),(583,0),(262,0),(585,0),(586,3),(585,3),(586,0)],
  mk [114,29,30,36,2,4,5,25] 7 (replayWords [0xcb00000000,0xa9870000000000,0x600000000005040,0x0,0x0,0x3000,0x2014]) [(231,0),(507,0),(306,0)],
  mk [90,29,30,115,2,5] 5 0x2001 [(232,0)],
  mk [90,214,29,36,2,5] 5 0x0 [],
  mk [90,29,116,30,36,2,5] 6 (replayWords [0x90000000000,0x80700000,0x6050000,0x4000,0x30021000004]) [(233,0),(589,0),(590,5)],
  mk [215,216,29,30,36,2,5] 6 0x0 [],
  mk [90,29,30,36,2,5,25] 7 (replayWords [0x840000000000002,0x8005000a0014008,0x8010001e0038006,0x800c00160028000,0x980000000000004,0x8005000a0014000,0x3,0x100000003,0xe0000000,0x180100000004200,0x0,0x0,0x0,0x28005000000,0x0,0x0,0x8004000000,0x0,0x8003000000,0x0,0x200000004005]) [(234,0),(234,5),(508,0),(508,5),(591,0),(557,0),(592,6),(584,5),(591,5),(557,5),(592,4),(584,0)],
  mk [29,30,36,2,4,5,25,203] 8 (replayWords [0x2,0x13200000000000c,0x170000000000003,0x16f6000c0058d62,0x14000000000000a,0x8014000a0050009,0x8012000a0048001,0x162000000000001,0x80000000000003,0x10000c0040002,0x15e400000010847,0xc001a0030005,0x800900140024001,0x140000000000000,0x0,0x2,0x800000100000002,0x8000000e0000000,0x140200000008400,0x0,0x0,0x0,0x10006000002,0xa0000002,0xa0000000,0x20004000000,0x0,0x10003000000,0x10001000005]) [(235,6),(235,4),(509,0),(509,5),(558,0),(585,5),(558,5),(585,0),(588,5),(588,0),(593,0)],
  mk [217,29,30,36,2,4,5] 6 0x0 [],
  mk [29,218,30,36,2,4,5] 7 (replayWords [0x400100000,0x0,0x0,0x300e00400,0x300000000000000,0xc000004000000,0x400000d,0x300400400,0x300000400400000,0x0,0xb00c00,0xc00b00000000000,0x0,0x800a00900800000,0x700600000300500,0x400300000000000,0x2100000000004]) [(351,6),(352,1),(595,0)],
  mk [108,29,30,36,2,4,5] 8 (replayWords [0x1,0x10040101001,0x78000700007,0x800070000880005,0x88000500008,0x800030000880003,0x20000200001,0x20000100202,0x20010040100201,0x13800100001,0x80010000100001,0x10000100001,0x10000100001,0x80010000110001,0x1,0x204000000700005,0x78000700007,0x30000780007,0x70000200802,0x1e070000701a07,0x81e0781e0701a05,0x30000600005,0x50000200002,0x50000501204,0x10040160501203,0x20000200003,0x300a0401004,0xe0300a0100202,0x6010040100205]) [(596,2),(596,1),(353,0)],
  mk [29,218,30,36,2,4,5,27] 7 (replayWords [0x690,0x876,0x150040000000000,0x0,0x300000,0x0,0x0,0x201000000004]) [(545,5),(578,6)],
  mk [108,29,30,36,2,4,5,25] 8 (replayWords [0x1,0x8c0000000000000,0x108427c84006,0x800e001a003800c,0x16002e005800a,0x80130028004c001,0x9c0000000000000,0x864000000000000,0x8007000000,0x3,0x800000220000003,0x800000200000000,0x1c030000000c600,0x40078001000200,0xe00000004000,0x0,0x0,0x800008061380000,0xe1000000,0x0,0x0,0x1800d000000,0x30006800d001800,0x0,0x1800b000000,0x24003800a001200,0x18008000000,0x140038006000a00,0x40418801004215]) [(598,2),(236,0),(598,1),(236,5),(510,0),(510,5),(560,0),(586,5),(560,5),(586,0)],
  mk [29,30,36,2,4,5,25] 9 (replayWords [0xc30c00000,0xc,0x2f0002ec000bad0,0x2ec000aea0001,0xe7000a680001e70,0x9a50001220009,0x230001220008600,0x5d0007de0000,0x5d0000c34000000,0x7,0x2c00006c00,0x2c00006800001,0xc00006400001c00,0x6170001000005,0x950001000005130,0x400004910000,0x400000c04000c30,0xc30c02,0xc00001c00003c00,0x2c00002c00001,0x3800002c00,0x2c00000400003,0x400002c00002c00,0xc00c00c03002,0xc00001c00001000,0x2800001c00001,0xc00000400002400,0x1c00001c00000,0xc00c00c02001c00,0x1000000400001,0x800001000001000,0xc00c00c01401,0x400000c00,0xc00c00800400006]) [(237,6),(237,4),(354,4),(439,4),(444,2),(444,1),(439,8),(444,9),(444,7),(492,4),(511,0),(524,0),(535,5),(540,5),(511,1),(524,1),(535,0),(540,0),(544,0),(549,3),(544,3),(549,0),(311,0),(571,0),(580,5),(587,5),(311,1),(571,5),(580,0),(587,0),(474,0),(594,0),(597,3),(599,3),(474,3),(594,3),(597,0),(599,0)],
  mk [154,29,30,149,2,4,5] 6 0x80001 [],
  mk [31,29,52,30,2,4,5] 6 0x0 [],
  mk [29,52,30,144,36,2,4,5] 7 (replayWords [0x1,0x850000000000008,0x6000810000003]) [(359,5),(601,6),(602,0)],
  mk [154,29,30,36,2,4,5] 7 (replayWords [0x10015000000,0x48014000000,0x0,0x4c0090011002000,0x0,0x0,0x0,0x0,0x38007800f001c00,0x0,0x0,0x0,0x30006800d001800,0x900000008001,0x160000000,0x142000000,0x48009000000,0x200038006000a00,0x100018002000205]) [(359,0),(481,0),(536,0)],
  mk [154,29,155,30,36,2,4,5] 7 (replayWords [0x300,0x0,0x0,0x0,0x2280200000000,0x6000813]) [(355,0),(359,0),(525,0)],
  mk [50,29,155,30,36,2,4] 7 (replayWords [0x100c00,0x0,0x0,0x0,0x100b00,0x0,0xa00,0xa00000900,0x900000000002900,0x800700000,0x600600006000,0x2000005200000,0x4000003000,0x2000001004]) [],
  mk [29,52,30,36,2,4,5] 8 (replayWords [0x800090000980009,0x8000700007,0x800070000580005,0x8160583a0580000,0xf00020000de8002,0x582e0183205,0x8300582e0180201,0x800058000180609,0x70000b00009,0x90000580005,0x800090000900002,0x98000900009,0x280982a0982a09,0x28090000180601,0x826090000700005,0x800058000700007,0x20000780007,0x70200782207,0x822070200700001,0x8060181e0700005,0x800058000580005,0x8000581a0581605,0x816058180580005,0x816058160580002,0xc050120400e02,0xc020000180601,0x80a020000188200,0x5]) [(356,6),(360,0),(603,0),(604,5),(605,5),(527,0),(538,0),(606,5),(485,0)],
  mk [29,52,30,53,36,2,4,5] 7 (replayWords [0xb0a00000b,0xa0000000000000,0x0,0x0,0x0,0x987650,0x40302001000004]) [(357,1),(601,5),(601,6)],
  mk [154,207,29,30,36,2,4,5] 7 (replayWords [0x9000000000000,0x80700000000000,0x0,0x0,0x206,0x5000,0x43214]) [(481,0),(601,0),(528,0)],
  mk [50,29,52,30,36,2,4,5] 8 (replayWords [0xc60002030001,0x280000006,0x35a01818c601a00,0x884000180000206,0x300000000000000,0x0,0x0,0x0,0x4c0090012002600,0x8012000000,0x440010012002200,0x0,0x0,0x40007800f002000,0x800f000000,0x38001000f001c00,0x0,0x34006000c001a00,0x6000c000000,0x4c580000,0x200050009001000,0x8007000000,0x140010006000a02,0x80000000000001,0x846000000000000,0x40208800004215]) [(608,0),(358,2),(361,0),(609,5),(485,0),(530,0)],
  mk [54,29,30,77,2,5] 5 0x2001 [(362,0)],
  mk [54,29,30,36,2,68] 5 0x2001 [(363,0)],
  mk [54,69,29,30,36,2,5] 6 (replayWords [0x908000000,0x7060,0x504,0x30000000,0x2104]) [(364,0),(611,0),(612,0)],
  mk [54,219,29,30,36,2,5] 6 0x0 [],
  mk [54,29,30,36,2,5] 7 (replayWords [0x6,0x600060006000,0xb000707070a0700,0x9000a000a00090,0x9000a000a0009,0x900060006000,0x600060006000600,0x60006000600060,0x6000600060006,0x600080006000,0x600060007000700,0x70007000700070,0x7000700060006,0x700060005000,0x400030002000100,0x10001000100010,0x1000100010004]) [(613,0),(365,0),(614,0),(614,2)],
  mk [29,30,36,2,55,4,5] 8 (replayWords [0x7,0x800070000780007,0x202a0282802,0x8260280a0281a02,0x800028000280a02,0x800020080202402,0x68000080009,0x8000680001,0x800090000180007,0x200799f1781e07,0x3e1070000280a02,0x81e070000700002,0x20000700007,0x8000780007,0x70000180007,0x800070000295a00,0x2,0x94002b00022c002,0xa800320000a4003,0x18000a400320001,0x9c003180019c002,0x940028000290002,0x800029400280002,0x980028000294002,0x800029800280002,0x20000200002,0x20000200002,0x20000080001,0x800010000080005]) [(366,0),(615,0)],
  mk [50,207,29,30,36,2,4] 8 (replayWords [0xc000a00,0xe000c000c00010,0x1000c000c0004,0x4000c000c000,0x5000d000c000c00,0x70007000c000c0,0x70007000c000a,0x10001000a000,0xa00040004000a00,0xa0005000b000a0,0xa00070007000a,0xa00070007000,0xa00010001000100,0x10001000100010,0x1000112010001,0x700102000000000,0x171000004000400,0x40004000000000,0x4790000044301,0x470040305000,0x707070805000500,0x70707060500012,0x4030121210004]) [(606,5),(606,0)],
  mk [50,29,30,36,2,4,5] 9 (replayWords [0x3,0xa8000b8000a,0x800030000800009,0x80000000006,0xb5a0681c06b4003,0x7c0040000f74004,0x3700010000d,0xe800100006b5a00,0xa,0x800080000c8000a,0x8000a8000680006,0x8000a8000a80004,0xb8000a8000a,0x800010000b8000a,0x8000a828030300b,0x82c0a8280800006,0x800068000800008,0x40000900008,0x80000100009,0x80000801e03,0x26090220801e06,0x800068000680006,0x800068000680006,0x800068000000000,0x6b9a0000004,0x10000600004,0x400e0301605,0x120400e0100203,0xa020060100205]) [(607,0),(610,0),(333,2),(607,2),(610,2),(333,0),(367,0),(492,0),(616,0),(478,3),(616,3),(478,0),(535,0),(540,0),(617,2),(535,2),(540,2),(617,0)],
  mk [161,29,30,36,2,5,44] 6 (replayWords [0x100000,0x1]) [],
  mk [29,162,30,36,2,5,44] 7 (replayWords [0xee00000000000,0xc0d00000dad0000,0x0,0xb00000000,0xb00c0000000040a,0xa000000000,0x0,0xb00000000,0xb00100000000400,0x0,0xa00,0xa00000000400a00,0x0,0x900800000000,0x400700000000600,0x500000000400300,0x2100000000004]) [(368,6),(371,0),(619,5),(368,4),(371,1),(619,0)],
  mk [24,29,30,36,2,5,44] 8 (replayWords [0xddd0000,0xc0e0bf,0xc000bfcfe0007,0xe0007000e000,0x4000e0004000e00,0x1000e0001000dd,0xdd000000000000c,0xc00b000cc00b000,0x300070003000700,0x30004000300040,0x3000100030001,0xddd000000000,0xb0007000c00,0xb000b0004000c0,0xb000b0001000c,0xb000b000c0c0,0xc0c0b0007000400,0xa0007000700010,0x9000700070003,0x30308070004000,0x100060004000400,0x30303050400010,0x3030302010004]) [(620,0),(620,2),(372,0),(620,1),(372,1),(372,4)],
  mk [220,29,30,36,2,4,5] 6 0x0 [],
  mk [29,188,30,36,2,4,5] 7 (replayWords [0x30016000000,0x0,0x5400a0013002400,0x0,0x0,0x0,0x0,0x44007800f002200,0x8000f000000,0x6,0x1c0000000,0x34006000c001600,0x0,0x0,0x280048008000e00,0x30006000000,0xc0028004000600,0x1,0x40000000000005]) [(374,0),(622,5),(445,0)],
  mk [56,29,30,36,2,4,5] 8 (replayWords [0xa,0x98000a00009,0x800070000700007,0x70000700006,0x1806008060000c,0x38000200003,0x8000c0000100002,0x10000602e07,0x2c0702c0702a09,0x800070000700009,0x800098000600006,0x98000980003,0x8000a0000980009,0x800010000a00009,0x800098240a0280a,0x28098240700007,0x1c0701c0700007,0x380070000744007,0x73800700007,0x400070000701e07,0x1c0701c0701a06,0x60000600006,0x60000600006,0x60000000000,0x62d40000003,0x800010000480003,0x8000380c0280802,0x100380c0100202,0x808020060100205]) [(623,0),(623,2),(375,0),(446,0),(446,2)],
  mk [20,29,30,36,2,5] 8 (replayWords [0x9,0x900090009000,0xc0006000e000600,0xc0004000d00040,0xc0001000b0001,0xa00090009000,0x900090009000900,0x90009000900090,0x9000900090009,0x9000a0009000,0x900090006000400,0x80006000600010,0x7000600060003,0x200060004000,0x100050004000400,0x30002000400010,0x3000200010004]) [(376,0),(376,1),(376,4),(543,0),(543,2),(543,1)],
  mk [20,29,30,36,2,5,21] 8 (replayWords [0x9990000,0x99a000,0xae006,0x600aa006600ae00,0x4400aa004400ae0,0x1100aa001100bb,0xbd0000000000009,0xa0990000009990,0x30006000c000600,0x30004000c00040,0x30001000c0001,0xb00099009000,0x9900990090009a0,0x9000990090009a,0x9000990090009,0xa009000b0009a00,0x900099006000400,0x80006000600010,0x7000600060003,0x200060004000,0x100050004000400,0x30002000400010,0x3000200010004]) [(377,0),(377,1),(377,4)],
  mk [29,30,36,2,4,5,21] 9 (replayWords [0x3,0x9ce000000000000,0x633fe5f4006,0x30005f59d39e200,0xb,0x700026800a6c002,0x6800b64000dc00a,0x60000dc00b54001,0xc800a4c001c8006,0x300058000630005,0x80003822039c000,0x39ce0700002,0x80000200007,0x8000780000,0x800070000180006,0x800018000580003,0x80e038180580005,0x800020000600005,0x800058000080006,0x58000580001,0x800060000580003,0x9c00380003a8003,0x800039c00380003,0xa4003800039c003,0x80003a000380002,0x8000300002,0x20000180002,0x800020000080001,0x800010000080005]) [(378,0),(378,1),(378,4),(447,3),(447,9),(447,7),(544,0),(544,2),(544,1),(621,3),(474,0),(624,4),(474,2),(624,1),(474,1),(624,0),(625,0),(626,0)],
  mk [161,29,30,37,2,4,5] 6 0x80001 [],
  mk [38,29,162,30,2,4,5] 6 0x0 [],
  mk [29,162,30,158,36,2,4,5] 7 (replayWords [0x1,0x850000000000008,0x6000810000003]) [(386,5),(628,6),(629,0)],
  mk [29,221,30,36,2,4,5] 6 0x400001 [(50,0)],
  mk [163,164,29,30,2,4,5] 6 0x800000000042 [(50,0),(380,0)],
  mk [161,29,30,36,2,4,5] 7 (replayWords [0x88017000000,0x0,0x60016000000,0x0,0x0,0x5400a0013002400,0xf00000044000,0x0,0x0,0x0,0x400088011002000,0x0,0x0,0x0,0x38007800f001c00,0xd00000030006,0x120000000,0x16a000000,0x48008000000,0x140038006000a00,0x100018002000205]) [(631,2),(407,0),(381,0),(386,0),(632,2),(545,0),(619,0)],
  mk [161,29,162,30,36,2,4,5] 7 (replayWords [0xc280200000000,0x6000813]) [(379,0),(386,0)],
  mk [29,162,30,36,2,4,5] 8 (replayWords [0xb,0xb02c0b0360b,0xa000098000a,0x98000080005,0x8000d0000580000,0x800020000c80002,0xb02e018300b,0x2c0b02e0180201,0x8000b000018060b,0xb4c00b0000b,0x5800b0000b0000b,0xb0000b0000b,0xb0000b0000b,0x2e0b02c0b02c0b,0x2e0b0000b02c0b,0x2c0b0000980005,0x8000a0000980009,0x800020000a00009,0x8000982a0a0280a,0x280982a0980001,0x806018280980005,0x800020000900005,0x8000581a0882007,0x81c0581a0580001,0x806018180580002,0xc050120400e02,0xc020000180601,0x80a020000188200,0x5]) [(382,6),(395,0),(630,0),(633,5),(634,5),(382,4),(395,1),(630,5),(633,0),(634,0),(408,0),(547,0),(547,5),(620,0)],
  mk [29,162,30,33,36,2,4,5] 7 (replayWords [0x987650,0x40302001000004]) [(383,1),(628,5),(628,6)],
  mk [24,161,29,30,36,2,4,5] 7 (replayWords [0x380,0x0,0xc280000,0x8d13]) [(628,0),(619,0)],
  mk [24,29,162,30,36,2,4,5] 8 (replayWords [0x15a8002054009,0x240000000,0x0,0x0,0x580018015002c00,0x8000000000020a,0xd40000000000000,0x1100000054000,0x0,0x0,0x5800a8015002c00,0xa8015000000,0x55a00000,0x0,0x0,0x4c0090012002600,0x8012000000,0x440090012002200,0x0,0x38008000f001c00,0x800d000000,0x2c001000c001600,0x200050009001000,0x8007000000,0x140010006000a02,0x80000000000001,0x846000000000000,0x40208800004215]) [(636,0),(384,6),(402,0),(637,5),(636,1),(384,4),(402,1),(637,0),(620,0)],
  mk [24,29,30,36,2,4,5] 9 (replayWords [0xbdee0b8300b,0xdc00b5800a8000b,0x5800a8000300007,0xd8000700003,0x40000d00004,0x3000010000c,0x800010000bdee00,0xb,0x8000bd400b8000b,0xdc00b8000b8000b,0x8000b8000b8000b,0x8000b8000b8000b,0x8000b8000b8000b,0x80000000000000b,0xe2e000000a80007,0xb0000a8000a,0x800040000b0000a,0x8000a800010000b,0xa8000a8280b,0x2c0b02c0a82807,0x40000980007,0x70000100009,0x70000701a03,0x220801e0701a04,0x10000600004,0x400e0301605,0x120400e0100203,0xa020060100205]) [(635,0),(638,0),(478,4),(635,2),(638,2),(478,1),(409,0),(635,1),(638,1),(478,0),(409,1),(409,4),(621,0),(549,0),(549,2),(549,1)],
  mk [29,30,36,2,4,5] 10 (replayWords [0xc,0x800058000c00005,0x8000b800038000b,0x38000a80002,0xa0000200009,0x800008000900000,0x800088000180008,0x18000580003,0x800078000580005,0x800020000700005,0x800058000080006,0x800058000580001,0x800060000580003,0x800020000500003,0x800038000080004,0x800038000380001,0x800040000380002,0x8000300002,0x20000180002,0x800020000080001,0x800010000080005]) [(410,0),(410,1),(410,4),(479,0),(479,2),(479,1),(479,3),(479,9),(479,7),(600,0),(618,4),(600,2),(618,1),(600,1),(618,0),(627,0),(639,3),(627,3),(639,0)]
]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def entries (i : Nat) := data[i]?.getD default
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def books : Array (List Nat) := #[[0,2],[4,6],[8,10,1],[12,14,1],[16,18],[20,22,1,24,3,26,5,28,7,9,11],[30,32,1],[34,36],[38,40],[42,44,2,1,46,3,28,48],[50,2],[52,54],[56,58],[60,62,1,24,3,26,5,28,7,9],[64,66],[68,70],[72,74,1,3],[76,78],[2],[1,24,3,26,80,5,28,82],[84,86,38,88,2,90,24,92,26,28,1,3,5,7,9,11,13,15,17,19,21,23,25,27,29],[],[92,26,1,24,3],[26,24,94],[],[40],[1,96,98,38,3,100,26],[38,100],[1,102,46,104],[2,1,106,3],[108,110,112,28,84,1,3,5,7,92,9,11,24,13,38,86],[1,24,84,114],[1,3,40],[1,3,106,40],[1,116,44,118,3,5,2,7,9,120,46,11,28,122],[1,70,124],[1,74,126,128,130,3],[1,26],[1,2],[1,90,3,88,5,7,26,82,9,28,132,134],[88,1,90,84,38,26,2,28,136,92,130,138,3,5,7,9,11,13,15,17],[28,140,142,144,146,26,24],[],[1,92,146,42,46],[28,110,26,148,150,152,1,3,112,5,7,116,146,92,46,24,86],[154],[156,1,158,3,40,5,114,160,162,154,164,92,166],[],[162,160,168,170,1],[146],[],[1,3,5],[1,90,3,88,5,86,146,7,92],[88,86,28,110,90,26,148,24,172,160,162,92,170,154,164,174,1,3,5,146,7,9,11,13,15],[],[],[1],[154,176,86],[],[],[],[1,3,5,86,7],[1],[160,178,180,182,184,86,176,1,3,5,7,9,11],[166],[],[186,114,188,1,3,5,190,192,156,194,196,158,198,200,40,7,160,162,154,164,24,166],[],[],[202,24,204,1,92,206,3,208,5,7,210,9,11],[],[146,1],[],[212,1,214,48],[1,212,48],[1],[216,1],[94,140,24,210,218,1,220,3,146,5,7,9,11,13,15,222,48],[],[1,94],[],[1],[40,1,212,224,3,226,5,7,9,11,13,15,86,17,19,21,23],[162],[],[162,160,1,24,168,86,3,228,5],[1],[],[146,1,24,3,230,5,222,86,7],[232,86,110,222,234,236,148,238,24,230,160,180,162,1,154,228,164,3,176,146,5,7,9,11,13,15,17,19],[232,240,242,234,236,244,246,238,172,162,248,250,252,254,180,256,154,176,146,258],[260,262,250,264,162,266,268,84,1,270,272,154,258,146],[28,142,50,274,276,278,280],[],[282,1],[284],[286,150,288,1,26,3,5,290,292,294],[],[1],[154],[],[296,1,3,250,5,262,162,298,160,300],[302,304,306,154,24,164,308,310],[],[],[1,3],[1,3,5,7,146],[],[],[1,3],[1],[312,314,316,318,320,322,262,324,160,1,86,326,3,328,5,7,9,146],[],[],[1,3],[1],[],[],[1,3],[1],[330,332,334,300,86,1,328,3],[316,284,320,336,338,324,262,160,322,1,3,5,258],[340,342,344,346],[260,264,92,250,24,262,162,348,350,352,354,160,86,270,272,328,1,3,258,5,7,9,11,13,15],[356,308,358,164,360,362],[154,328,364,366,368,84,370,92,164,372,160,374,1,272,146,362],[1,142,376],[142],[1,150,3,5,264,378],[84],[160],[1,2,3,162,160,354],[380,150,382,384,1,3,5,258,178,262],[386,388,1,164,4,390,392,86],[276,1,2],[],[],[1,3],[1,84],[],[],[1,3],[1,52,3],[394,60,1,3,2,5,38,146,7,24,262,86,9,328],[],[],[1,3],[1],[],[],[1,3],[1],[396,162,382,24,1,328,3],[398,28,258,354,162,400],[2],[1],[1,2,3,38,402,146,5,24,80,7],[404,290,266,268,86,84,1,178,262,160,162,92,2,38,384,24,406,272,408,328,3,5,258,7,9,11,13,15,17,19],[410],[1,24,258,412],[414],[1,92,416,418,420,396,422,424],[426,428,430],[0],[144,8],[38],[16],[1,92,3,28,258,362,5,7,9,11,13,20],[1,144,30],[432,144,34],[158],[92,1,114,118,3,434],[],[222,436,98,1,212,438,440,92,3],[208,146,1,40,3,442,2,5],[84,120,444,438],[50],[1,446,448],[66],[124],[418,118,168,1,3,278],[258,108,418,450,76],[452,146,454],[28,1,92,3,5,7,258,9,11,13,15,362,17,19,21,23,25,27,29,31,33,35,118,84,146,37,39,41,43,45,47,49,51,53,55,57,59,61,108,38,63,65,67,69,71,73,75,77],[],[1,3,5,456,114,7,458,460],[146,1,438,462],[276],[52],[56],[1,92,3,28,5,7,60],[144,64],[68],[142,72,168,1,3],[258,76],[146,80],[],[188,1,438,3],[1,3,258,362,92,5,7,146,28,118,9,11,13,15,17,19,21,23,25,27,29,84,108,122,31,33,38],[1,3,458],[],[1,146],[146,1,3],[],[1,3,2],[1,146,3],[1,116,464,118,3,92,5,258,7,362,9,11,13,120,26,15,17,19,146,84],[1,466,40],[1,40,212],[1,3,5,464,116,7,146,9,468,26,11,102,13,46,118,84],[114,156,470,92,84,472,146,258,362,474,476,478],[146,438,1,3],[480],[1,482,3,24,146,438,140,94,5,7,212,258,362,440,48,9],[84,1,118,146,474,484],[1,102,146,3,5,482,7,48,462,42],[118,486,1,146,28,438],[1,124],[150,1,126,378,26,168,488,3],[84,118,490,82],[1,468,146,3,492,132,494],[],[496,1,84],[1,498,456],[84,1,3],[1,3,456,500,2,462,5,7,26,84,9,11],[434,84,114],[1,3,44,5,116,7,468,9,11,122],[38,1,3],[38,40,1,222,436,462,502,216,3,212,504,5,7,9],[458,1,208,146,40,3,216,2,5,7,9,11],[294,84],[],[1,124],[1,3,362],[1,506,468,3,168,488,5,76],[508,146,1,510],[116,1,468,84,3,92,5,26,286,7,258,9,488,11,362,13,512,15,17,19,21,23,25,146,27,29,31,33,35,2,37,39,41,43,45,47,49,51,53],[46,514,258,362,146,516],[310,518,520,522,164,146,322],[524,526,38,528,530,532,2,534,516,84,1,92,146,536,160,3,162,258,322,154,5,164,362,520,484],[84],[1,3,114],[1,3,40],[1,538,44,3,460,5,7,9,96,2,11,13,540,15,100,28],[154],[1,3,44,5,2,7,100,114,542,498],[158],[92,84],[114,1,92,166,3,156,5,158,84,7],[1,166,84,3],[],[],[1,3],[68,1],[72,1,160,162,544,3,298,546],[],[324,80,1],[548,118],[],[106],[158,106],[1,3,5,550,7,9,154,552,554,11,40,13,15,26,556],[],[],[],[1,3,5,558,7],[],[44,560,562,156,564,1,548,3,354,5,7,558,9,11,566,568],[154,40],[114,1,3,5,40,92,84],[],[],[],[1,3],[],[],[],[],[],[],[1],[1],[],[1,3,5,548,7,40,9,11,13],[1],[],[],[],[],[],[114,1,3,548,5,40,7,9],[],[548,114,40,1,3,5,7,9,11,13,15,17,19,21,23,25,27,212,29,31,33,35,37,39,41,43],[156,158],[1,212,114,158],[],[],[],[384,1,3],[1],[],[548,1,40,3,5,212,84,114,7,9,11,13,15,17,19,21,23,25],[162],[232,114,156,234,236,158,238,1,548,40,160,162,3,5,154,164,7,9,570,166,198,11,13],[114,1,3,5,548,7,40,24,9,11,84,13],[154,1],[114,84],[1,3],[1,3,298,162,5,7,114,9,544,11,13,160],[154,1,3,164,544],[458,114,1,102,3,298,5,544,7,572,9,11,13,15,17,19,21,23,25,484,27,84,29,31,33,35,37,39,41,160,162,43,45,154,164,47,49,24,496],[],[574,444,576,578,1,580],[456],[158],[456,552,26,582,1,92,3,556],[40,156,158],[548,1,114,158],[],[92],[],[1,3],[548,1,40,3,212,5,7,114,9,11,13,15,17],[40,212,86,1,3,5],[510,328,544,584,154,164],[458,102,92,114,24,298,1,544,3,5,484,7,586,9,86,11,13,262,15,17,328,19,21,496],[],[162,160,298,546,324,1],[544],[530,496,38,526,588,534,532,84,166,92,24,160,546,162,154,324,164,590,458,1,3,5,7],[146,592,594,596,114,158,364,598,234,600,258,578,160,162,362,154,164,602,604,530,606],[2,578,146,460,442,540,258,362,608,610],[2,578,1,146,118,438,120,160,612,162,258,154,614,164,362,616,486,3],[120],[1,576,120,614,618,146,28],[],[],[1,3],[1],[620,162,300,622,298,360,328,1],[90,92,118,1,438,108,120,3,5,578,28,624,7,9,612,258,576,11,13,614,362,486,15,17,146],[1,146,212],[84],[1,3,626,5,146,7,9,11,328,212],[456,458],[1,3,5,44,92,7,102,9,46,104,84],[1,158,40,568,498],[154,158],[628,598,592,630,114,1,578,40,158,3,160,162,154,164,614,632,542,634,5,7],[502,146,1,3,158,540,2,5,7,106,9,40,11],[38],[154,1],[1,38,3,84,454,164,5,28],[108,468,110,148,1,86,3,84,5,92,382,258,7,636,362,9,11,13,15,17,146,19,21,23,25,2,27,29,38,31,33,24,35,37,39,41,262,43,45,328,47,49],[84],[116,2,638,1,118,120,640,46,146,258,362,3,5,7,488,492],[642,484,96,472,146],[1,644,48,462,146,42,3,5,7,94],[154,40],[1,156,3,158,114,646,40,5,648,160,162,154,164,84,544,324,7],[166,1,84,3,114],[],[],[1,3],[1,68,3],[650,72,1,162,652,24,168,328,3],[2,1,462,3,38,5,438,7,146,24,9,92,11,110,148,86,13,84,15,212,262,17,19,652,258,328,21,23,570,362,25,27,29,31,33,35],[512],[],[1],[1,572],[1,3,654,5,146,328,656],[418,396,658,660],[162],[662,24,1,168,72,3,162,652],[70,124,164,664,666,668,1,3,68,5,7,670,656,9,11,672,13,15],[70,162,670,328,168],[74,126,266,268,1,3,72,5,7,262,160,162,9,11,674,272,13,15,146,17,19,21,2,38,24,168,23,390,25,86,27,29,328,31,33],[84],[],[38,1],[1,676,2,3,5,7,80,678,9,11,494,146,512,488,13,492,15],[80,82],[1,676,492,132,146,494,3],[],[154,1],[1,3,5],[],[1],[],[],[1,3,5,7],[],[84],[1,680,3,682,5,684,7,686,84,9,11,13,15,17,160,572,154,544,324,19],[],[],[1,3],[1],[686,688,690,584,86,1],[1],[324,80,1,3],[544],[],[],[1,3],[1],[1,3,38,5,7,84,692,9,132,28,11,13],[2,1,132,3,38,5,82,7,146,24,9,11,13,15,17,364,368,86,19,21,23,25,80,27,29,262,272,670,328,31,154,656,33,35,37,39],[38,2,86,1,3,84,5,92,7,24,262,160,9,11,13,15,328,154,17,19,21,23,272,25,27,29,31,33,35,37,39,41,43,45,47,49,51],[160,38,694,162,696,698,412,700,702,704,706,252,708,258],[710,712,714,716,718,154,38,164,1,720,2,3,722,362],[],[1,146],[162],[],[1],[724],[350,242,726,728,262,268,730,250,234,172,180,600,732,240,734,154,724,1,248,146,3,5,7,9],[],[736,738,258,740,190,742,192,744,38,1,3,198,746,200,748,750,752,154,754,354,756],[],[1,258,3],[],[1,354,758,760,762,258,764,146,3,766,5,768,770],[84,154],[162,1],[1,38,258,3,354,5,7,376,9,162,702],[],[160,1,354,694,162,772,774,706,146,258,3,708,702],[232,702,160,234,376,38,252,1,354,768,694,162,254,256,3,154,708,706,146,258,5,7,9,11],[1],[258,146,456],[776,146],[1,778,258,780,776,3,456,782,784,5,7,9,11,146,84],[1],[778,746,380,1,382,150,786],[742,760,762,146,788,2,1,748],[380,1,778,382,258,150,3,5,84,790,792,7,9,146,11,13,15,17,160,794],[1,258,108,118,796],[162,160,350,456,1,3],[258,146,798,326,1,800,802],[258,738,746],[102,260,1,804,258,38,218,118,3,806,808,810,5,7,146,2,812,376,9,11,160,162,354,13,15,814,816],[],[2,1,390,382,162,768,818,652,3,814,820,822,160,258,774],[302,824,826,1,828,718,154,164,3,5,362,146,2,7,9,722],[],[1],[1,3],[1,50,218,830,3,362,832,394,146],[],[1,292,3],[],[],[292,378,1,3,5,7,834,146,836],[146],[146],[314,838,1,3,840,146,842,844,262,846,268,84,5,7,848,850,852,154,536,604,530,300],[1],[1],[1,3,52,854,856,164,858,5,146],[],[860,1,3,5,7,862,164,146,864,866],[312,868,836,1,870,526,160,530,38,3,146,5,84,7,9,872,2,874,866,864,154,11,744],[162],[162],[232,876,878,234,38,1,3,746,162,822,738,5,254,748,256,154,880,570,740,756,198,258],[1],[1],[664,164,1,124,3,162,882,5,362],[],[124,884,164,1,3,5,7,882,886,362],[330,126,738,1,742,162,884,886,258,744,38,3,84,5,154,7,400],[530,400,160,526,888,38,338,258,354,84,398,1,874,872,154,890,892,742,162],[],[146,894,1,896,38,3,5,692,234,552,554,600,898,160,900,154,902,604,530,904],[2,896,1,146,38,402,3,5,636,80,160,906,820,570,198],[260,2,376,1,160,3,5,38,7,162,9,354,84,11,13,814,718,154,15,17,258,19,21,23,25,27,29],[],[1],[],[1,3,5],[908],[146,642,1,550,3,5,258,150,362,152,456,84,7,9,678],[1],[574],[550,456,146,1,3,258,362,910,786,642,5,7,912,914,9,84],[158],[552,550,786,626,1],[120,916,1,84,3,918],[550,1,146,626,3,5,920,258,922,362,924,84,7,9,154,636,570,11,13,15,17],[118],[],[1,3],[1,456],[1,3],[908],[456,146,550,1,3,5,7,258,9,362,11,13,15,17,912,19],[1,3,456],[1,114],[1,3,98,5,460,7,9,458,11,926],[1,3],[460,1],[460,96,38,40,1,3,482,5,7,9,438,440,11,540,13],[460,146,458,1,3,5,40,7,9,442,2,11],[168],[1,124],[1,258,330,390,458,3,928,5,336],[928,146,458,362,1,510],[458,1,102,460,3,5,930,7,9,11,928,13,15,17,932,19,484,38,21,23,25,27,29,31,33,35,37,2,39,41,43,45,47,49,51,53,55,57],[1,3,5,108,7,118,9,468,11,456,13,100,114,102,15,458,17,460],[],[102,146,458,1,438,3,462,5,100,114],[1,70],[1,258,934,102,390,458,928,3,804,742],[102,146,458,1,936],[],[],[456,642,1,3,5,550,150,152,922,938,7,9,154,636,554,11,40],[146,456,550,1,84,604,3],[114,1],[38,1,3,40,940,460,5,7,100,114,542,498,456,9],[1,458,102,3,5,258,362,7,146,9,460,11,13,930,15,17,928,19,21,484,38,23,25,118,27,29,804,810,496,2,31,33,456,35,37,742,604],[146],[146],[146,96,1,594,482,38,3,460,258,362,5,942,944,540],[1,38],[1],[482,146,594,1,438,3,5,7,114,498],[],[442,1,92,3,456,5],[632,542,598,592,1,442,114,3,946,158,5,84],[540,480,502,146,1,3,5],[2,462,456,146,442,1,3,5,7,9,788,258,914,362,948,950,786,26,642,11,13,15,17,84],[1,606],[154,1],[1,38,3,482,146,118,928,594,5,462,7,100,544,952,498],[614,632,954,542,1,458,956,3,5],[2,462,456,146,458,1,3,742,258,604,362,442,5,7,788,914,786,950,642,438,9,11,84,652,570],[],[160,162,652,740,756,958,554,1],[124,960,1,3,962,672,5,362,7,670,892,964,70,9,11,68,13,15,966],[1,126,3,258,742,886,146,5,7,744,74,9,11,72,13,15,160,162,674,400,2,390,458,456,604,17],[154],[154],[1,38,3,146,928,132,5,936,544,952,846],[570,968,198,970,1,456],[2,132,604,146,458,1,3,456,5,7,742,886,962,9,11,530,972,974,82,13,15,80,17,19,670,154],[456,604,1,40,556],[1,456,3,458,5,114,498,84],[114,458,1,3,40,5,498,456],[],[],[1,3],[],[1,3],[738,1,742,162,458,3,544,5,298,976,160],[],[846,454,1],[106,212],[158],[552,550,1,636,3,5,7,26],[562,1,156,3,548,566],[212,114,158],[1],[],[548,1,40,3,5,7,212,9,114,11,13,15,17,19,21,23,25],[40,1,456,3,212],[978,1,3,548,914,980,5,7,554,114,498,982,9,40],[458,1,102,3,5,7,9,11,13,15,17,114,19,21,298,23,25,544,27,29,31,33,456,35,37,39,41,43,742,258,604,362,588,24,38],[1,156,728,114,158,730,548,234,40,600,594,160,162,154,164,902,166,904,3],[40,1,498,3,456],[1,154,3],[106,1,40,3,5,7,158,9],[],[748,162,160,554,1],[154],[154,1,164,554],[232,456,642,462,234,38,40,1,3,5,7,9,11,160,748,162,13,15,17,154,554,164,19,21,23,880,570,786,198,25,27,29,31,33,35,37,39,41],[984,1,574,438,3,118],[118,1,40,3,496,5,548,7,544,952,84,9,114],[158,456,106,84,502,1,458,3,5,7,540,9,11],[],[742,162,986,554,1],[554,604,982,154,1,456,164],[456,146,462,1,458,3,5,7,9,11,40,742,258,13,604,362,15,2,17,19,21,23,25,84,27,29,31,748,33,35,554,37,39],[978,168,1,914,294,3,554,742,160,982,5,738],[1],[],[884,988,362,1,3,5,162,882,124],[],[124,960,1,3,882,362,5,7,884,9,11,13,15,17,19,21,23],[1,126,3,742,258,886,5,7,330,9,11,738,13,15,162,884,390,458,17,456,19,604,21,888,160],[],[164,680,154,544,682,1,990,84,3,5,160,572,686,324],[154,604,974,132,38,510,1,164,84,454,3,5,160,882,886,530,362],[810,1,362,990,3,544,952,154,164],[604,146,132,960,458,1,362,3,456,5,7,742,886,882,2,9,11,154,510,13,15,454,17,19,164],[458,1,2,456,3,5,742,7,9,11,604,13,15,17,886,19,21,23,25,27,29,31,33,35,37,39,41,43,38,45,47,49,51,84,53,55,57,59,160,61,63,65,67,154,69,71,73,75],[154],[],[594,1,3,498,456,5],[232,598,592,234,992,114,158,994,40,1,578,160,162,154,164,602,968,970,606,3,5],[598,146,84,1,3,5],[946,146,456,786,592,442,114,158,598,84,258,362],[146,642,462,594,1,38,3,5,7,9,456,234,600,876,258,160,162,900,362,154,164,898,84,604,530,11,13,15,17],[1,438,3,462,5,100,114,542,498,146,460],[614,598,996,998,1,3,540,440,5],[462,146,786,642,594,1,3,438,5,7,9,456,84,876,258,652,900,362,570,11],[1],[1],[664,164,1,3,68,162,906,5,672],[],[164,1,3,5,7,906,68,1000,672,362,1002],[650,1,1004,72,652,162,2,390,38,256,382,1006,146,1000,820,154,3,258,674,874,958],[120,84,38,438,946,1,146,3,118,1008,258,956,362,1010],[2,462,1,3,5,146,38,438,7,9,11,13,84,15,160,652,17,258,19,154,570,21,362,23,820,25,27,29,31,33,35],[880],[146,974,1,1012,3,5,7,9,11,886,154,164,1014,604],[1012,1,146,654,3,5,1016,7,9,11,1018,718,154,164,670],[],[168,878,38,1,3,738,234,746,748,600,732,876,734,5,898,822,154,902,742,400,904,390],[2,822,1,390,168,38,662,3,5,382,162,72,254,652,256,7,9,154,1020,820,570,160,198,258],[124,664,164,70,1,68,3,5,670,674,7,362,9,11],[124,664,362,70,1,68,3,5,670,162,674,258,154,168],[74,1,126,72,3,5,160,7,9,11,674,718,13,258,15,17,19,2,21,162,23,390,38,25,27,84,29,31,154,33,35],[154],[],[686,1,3,846,692,5],[1],[1,3],[232,900,894,234,38,1,3,5,896,552,7,692,9,160,880,154,554,570,968,970,198,11,13],[978,146,982,1,3,692],[146,974,132,686,1,38,3,5,7,9,692,11,84,13,15,17,19,21,1014,886,160,604,154,530,23,25,27],[1,82,3,132,5,936,544,952,846],[570,968,198,970,1,692,3],[132,146,530,974,686,1,3,82,5,7,692,9,11,80,13,15,1014,886,670,17,604,154],[2,132,1,3,5,146,38,82,7,9,11,13,84,80,15,17,19,21,23,160,670,718,154,25,27,29,31],[38,1,2,84,3,5,160,7,9,11,154,13,15,17,718,19,21,23,25,27,29,31,33,35,37]]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def book (i : Nat) := books[i]?.getD []
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def groups : Array (List (Fin 4)) := #[[],[0,1],[0],[3],[0,1,0],[1],[1,0],[3,0,1],[3,0,1,0],[3,0],[3,1],[3,1,0]]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def perm (i : Nat) := permitted (groups[i]?.getD [])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def specs : Array Spec := #[(2,[(0,3,4),(1,1,6)]),(4,[]),(13,[]),(15,[]),(2,[(0,3,4),(1,3,4)]),(3,[(0,3,4),(1,3,4)]),(2,[(0,3,4),(1,5,6)]),(3,[(0,3,4),(1,5,6)]),(2,[(0,3,4),(2,5,6)]),(3,[(0,3,4),(2,5,6)]),(2,[(0,3,4)]),(3,[(0,3,4)]),(21,[]),(20,[]),(17,[]),(2,[(1,3,4)]),(3,[(1,3,4)]),(2,[(2,3,4)]),(3,[(2,3,4)]),(3,[]),(3,[(1,0,5),(3,2,6)]),(2,[(0,0,5),(1,1,6)]),(4,[(1,1,2),(1,5,6)]),(3,[(0,0,5),(1,2,6)]),(2,[(1,0,1),(2,1,5)]),(2,[(0,3,5),(1,1,6)]),(2,[(0,3,5),(1,4,6)]),(3,[(0,3,5),(1,4,6)]),(2,[(0,4,5),(2,3,6)]),(3,[(0,4,5),(2,3,6)]),(2,[(0,3,5)]),(3,[(0,3,5)]),(2,[(1,4,5),(0,3,6)]),(3,[(1,4,5),(0,3,6)]),(2,[(1,3,5),(3,4,6)]),(3,[(1,3,5),(3,4,6)]),(2,[(1,3,5)]),(3,[(1,3,5)]),(2,[(2,3,5)]),(3,[(2,3,5)]),(2,[(3,4,5)]),(3,[(3,4,5)]),(2,[]),(2,[(1,0,1)]),(3,[(1,0,2)]),(4,[(1,1,2)]),(25,[]),(2,[(1,0,1),(1,1,5)]),(2,[(3,0,5),(1,1,5)]),(3,[(1,0,2),(1,5,6)]),(2,[(0,0,1),(1,5,6)]),(4,[(1,1,5)]),(3,[(1,0,2),(2,2,5)]),(2,[(1,0,5),(0,1,6)]),(3,[(1,2,5)]),(2,[(3,0,1)]),(4,[(1,1,2),(1,2,5)]),(2,[(1,0,1),(1,5,6)]),(3,[(1,0,2),(1,2,5)]),(2,[(1,1,5)]),(2,[(3,1,5)]),(2,[(2,1,5)]),(4,[(1,3,5),(3,4,6)]),(4,[(1,3,5)]),(1,[(0,0,1),(1,2,6)]),(0,[(1,0,2),(1,1,2)]),(4,[(3,4,5)]),(0,[(0,0,1),(1,2,6)]),(1,[(1,0,2),(1,1,2)]),(5,[(1,0,2),(1,1,2)]),(2,[(3,0,1),(1,1,5)]),(8,[(1,1,5),(1,2,5)]),(7,[(1,1,5),(1,2,5)]),(6,[]),(2,[(2,0,1)]),(8,[(1,2,5)]),(7,[(1,2,5)]),(0,[]),(2,[(1,1,5),(3,0,6)]),(2,[(1,0,5),(3,1,6)]),(1,[]),(8,[]),(7,[]),(2,[(1,0,1),(3,5,6)]),(23,[]),(0,[(1,0,1),(1,2,6)]),(1,[(1,0,1),(1,2,6)]),(5,[(1,0,1),(1,2,6)]),(5,[(1,0,1),(3,2,6)]),(21,[(1,2,3)]),(1,[(1,0,1),(3,2,6)]),(4,[(2,1,2),(1,2,3)]),(3,[(2,0,2),(1,2,3)]),(4,[(2,1,2),(1,5,6)]),(3,[(2,0,2),(1,5,6)]),(0,[(2,2,5),(2,0,6)]),(0,[(0,0,2),(3,5,6)]),(0,[(2,2,5),(2,1,6)]),(0,[(0,1,2),(3,5,6)]),(0,[(0,2,5)]),(0,[(2,2,5)]),(3,[(1,0,2),(1,0,5)]),(8,[(1,0,5),(1,1,5)]),(7,[(1,0,5),(1,1,5)]),(3,[(2,0,2),(1,0,5)]),(4,[(2,1,2),(1,1,5)]),(21,[(3,2,5)]),(3,[(2,0,2),(0,2,5)]),(2,[(1,0,1),(1,0,5)]),(8,[(1,1,5)]),(7,[(1,1,5)]),(3,[(2,0,2)]),(4,[(2,1,2),(3,2,5)]),(3,[(2,0,2),(3,2,5)]),(0,[(1,0,1),(3,2,6)]),(4,[(2,1,2)]),(0,[(2,0,2)]),(0,[(0,0,2)]),(0,[(2,1,2)]),(0,[(0,1,2)]),(1,[(2,1,2),(1,0,6)]),(1,[(3,0,1),(3,2,6)]),(1,[(2,0,2),(1,1,6)]),(1,[(2,0,1),(3,2,6)]),(4,[(1,1,3),(3,2,6)]),(2,[(1,0,1),(1,3,6)]),(3,[(1,0,3),(3,2,6)]),(0,[(3,2,3)]),(0,[(0,2,3)]),(11,[]),(3,[(1,0,3)]),(1,[(1,0,1)]),(4,[(1,1,3)]),(1,[(3,0,1)]),(1,[(2,0,1)]),(0,[(1,0,1),(1,3,6)]),(5,[(1,0,1)]),(2,[(3,1,3),(3,5,6)]),(3,[(0,3,5),(1,2,6)]),(3,[(3,2,3),(3,5,6)]),(2,[(1,1,3)]),(2,[(0,3,5),(1,0,6)]),(3,[(3,0,3),(3,5,6)]),(1,[(1,0,2),(1,2,5)]),(2,[(3,0,3)]),(4,[(1,2,3)]),(4,[(0,3,5),(1,2,6)]),(4,[(3,2,3),(3,5,6)]),(3,[(1,0,3),(1,0,5)]),(1,[(1,0,1),(1,5,6)]),(1,[(1,0,1),(2,5,6)]),(3,[(1,0,4),(1,4,5)]),(3,[(3,0,4),(1,4,5)]),(4,[(3,1,4),(1,4,5)]),(1,[(1,0,1),(1,4,6)]),(3,[(0,0,5),(1,4,6)]),(3,[(1,0,3),(0,5,6)]),(3,[(0,3,5),(1,0,6)]),(0,[(1,0,1),(2,0,5)]),(4,[(0,3,5),(1,1,6)]),(0,[(1,0,1),(2,1,5)]),(0,[(1,0,1),(0,5,6)]),(0,[(1,0,1),(3,5,6)]),(3,[(0,0,5),(1,3,6)]),(0,[(1,0,1)]),(3,[(1,0,3),(1,5,6)]),(3,[(1,3,5),(3,0,6)]),(4,[(1,3,5),(3,1,6)]),(4,[(3,1,3),(3,5,6)]),(3,[(1,0,3),(3,5,6)]),(2,[(3,4,5),(1,1,6)]),(3,[(3,4,5),(1,2,6)]),(2,[(1,1,4),(2,5,6)]),(0,[(1,1,2),(1,5,6)]),(3,[(3,0,3)]),(16,[]),(4,[(3,1,3)]),(19,[]),(3,[(2,0,3),(1,4,6)]),(4,[(2,1,3),(1,4,6)]),(0,[(1,0,1),(3,3,6)]),(9,[]),(0,[(3,0,1)]),(3,[(2,0,4)]),(0,[(2,0,1)]),(2,[(1,0,1),(3,4,6)]),(4,[(2,1,4)]),(1,[(1,0,1),(3,4,6)]),(2,[(1,0,3)]),(1,[(0,0,5),(1,2,6)]),(3,[(1,2,3),(1,2,5)]),(1,[(1,2,5)]),(14,[]),(3,[(1,2,4),(1,4,5)]),(2,[(1,4,5)]),(24,[]),(1,[(1,0,1),(1,2,4)]),(3,[(1,2,3),(0,5,6)]),(3,[(1,2,3),(1,5,6)]),(2,[(1,0,3),(3,5,6)]),(1,[(2,0,5)]),(3,[(1,2,4),(2,5,6)]),(3,[(1,2,3)]),(0,[(1,2,3)]),(0,[(1,0,1),(1,2,3)]),(2,[(3,0,3),(1,1,6)]),(3,[(3,2,3)]),(2,[(3,1,3),(1,0,6)]),(2,[(1,1,3),(1,1,5)]),(2,[(1,1,3),(1,5,6)]),(2,[(3,3,5),(1,1,6)]),(3,[(3,3,5),(1,2,6)]),(2,[(3,1,3)]),(11,[(1,2,4)]),(9,[(1,2,3)]),(3,[(0,3,4),(1,2,6)]),(12,[(1,1,5),(1,2,5)]),(3,[(2,0,2),(3,5,6)]),(3,[(0,0,2)]),(3,[(3,2,5)]),(3,[(0,2,5)]),(3,[(1,0,5),(3,2,5)]),(2,[(0,1,5),(1,1,5)]),(2,[(2,1,3),(1,1,5)]),(2,[(1,1,5),(0,3,6)]),(2,[(2,1,3),(1,5,6)]),(2,[(2,0,4),(1,0,5)]),(2,[(1,0,5),(3,4,6)]),(2,[(1,0,5)]),(3,[(1,0,5)]),(2,[(1,0,5),(1,1,5)]),(4,[(3,2,5)]),(4,[(1,1,5),(1,2,5)]),(0,[(0,1,5),(1,2,6)]),(4,[(1,2,5)]),(17,[(3,0,5)]),(2,[(3,0,5),(1,1,6)]),(2,[(2,0,1),(2,5,6)]),(2,[(2,0,1),(0,5,6)]),(3,[(3,0,5),(1,2,5)]),(4,[(3,1,2),(0,5,6)]),(4,[(1,1,5),(3,2,5)]),(3,[(3,0,5)]),(2,[(0,1,5)]),(0,[(1,0,2),(1,2,5)]),(2,[(3,1,4),(2,5,6)]),(0,[(1,0,2),(2,2,5)]),(0,[(0,0,5),(1,2,6)]),(3,[(2,0,5)]),(2,[(3,0,1),(3,5,6)]),(0,[(1,0,2),(1,0,5)]),(2,[(2,0,1),(1,0,5)]),(2,[(1,0,1),(2,0,5)]),(4,[(1,2,3),(1,5,6)]),(3,[(2,0,4),(1,0,5)]),(3,[(1,0,5),(3,4,6)]),(5,[(1,0,2),(1,2,5)]),(4,[(0,1,5),(1,2,6)]),(2,[(1,0,1),(0,5,6)]),(4,[(0,1,5),(1,4,6)]),(5,[(1,0,1),(0,5,6)]),(10,[]),(3,[(0,0,5)]),(0,[(0,0,5)]),(4,[(0,1,5)]),(0,[(2,0,5)]),(0,[(0,1,5)]),(0,[(2,1,5)]),(1,[(1,0,1),(0,5,6)]),(3,[(1,0,5),(1,2,5)]),(2,[(1,0,5),(3,1,5)]),(2,[(2,0,1),(3,5,6)]),(0,[(1,0,1),(1,5,6)]),(1,[(1,0,1),(3,5,6)]),(4,[(1,1,5),(3,2,6)]),(4,[(1,2,5),(3,2,5)]),(0,[(1,0,2),(1,5,6)]),(0,[(1,0,5),(3,2,6)]),(4,[(2,2,5),(3,2,5)]),(18,[]),(3,[(1,2,5),(0,0,6)]),(2,[(1,1,5),(0,0,6)]),(4,[(1,2,5),(3,1,6)]),(17,[(0,0,5)]),(4,[(1,1,2),(3,5,6)]),(0,[(3,2,5)]),(5,[(1,0,1),(1,5,6)]),(2,[(1,1,5),(3,1,5)]),(0,[(1,1,2)]),(4,[(1,1,2),(2,5,6)]),(2,[(2,1,5),(3,1,5)]),(0,[(1,0,2)]),(0,[(1,0,1),(2,5,6)]),(4,[(3,1,5)]),(4,[(2,1,5)]),(5,[(1,0,1),(3,5,6)]),(2,[(1,0,1),(2,5,6)]),(3,[(3,2,5),(1,0,6)]),(0,[(0,0,1)]),(2,[(3,1,5),(1,0,6)]),(0,[(3,0,2)]),(2,[(3,0,1),(2,5,6)]),(0,[(1,0,5)]),(2,[(3,0,1),(0,5,6)]),(4,[(1,1,2),(0,5,6)]),(2,[(3,0,5),(3,1,5)]),(1,[(1,1,2),(2,5,6)]),(0,[(1,1,2),(2,5,6)]),(5,[(1,1,2),(2,5,6)]),(3,[(0,2,5),(1,2,5)]),(3,[(3,0,5),(1,3,6)]),(0,[(1,0,1),(0,3,6)]),(1,[(1,1,2)]),(3,[(1,2,5),(3,2,5)]),(0,[(2,0,1),(3,2,6)]),(0,[(1,1,2),(0,0,6)]),(2,[(2,0,1),(1,5,6)]),(0,[(1,1,2),(0,5,6)]),(0,[(1,2,5)]),(4,[(3,1,5),(1,2,6)]),(20,[(3,1,5)]),(2,[(3,0,5)]),(4,[(3,2,5),(1,1,6)]),(0,[(1,0,1),(0,2,6)]),(0,[(1,0,1),(2,2,6)]),(3,[(3,2,5),(1,3,6)]),(1,[(3,2,5)]),(3,[(1,4,5),(3,4,5)]),(1,[(1,0,1),(3,4,5)]),(2,[(1,3,5),(3,1,6)]),(1,[(1,1,2),(1,5,6)]),(3,[(1,3,5),(3,2,6)]),(12,[]),(1,[(3,0,1),(3,4,5)]),(1,[(2,0,1),(3,4,5)]),(1,[(3,4,5)]),(6,[(2,3,4)]),(0,[(1,3,5)]),(4,[(3,4,5),(1,2,6)]),(0,[(3,0,2),(1,2,5)]),(0,[(1,1,5),(3,0,6)]),(0,[(1,0,5),(3,1,6)]),(4,[(3,4,5),(1,1,6)]),(3,[(3,4,5),(1,0,6)]),(3,[(1,0,4),(2,5,6)]),(4,[(1,1,4),(2,5,6)]),(2,[(3,4,5),(1,0,6)]),(1,[(1,0,2)]),(4,[(1,1,3),(3,2,3)]),(2,[(1,0,3),(1,1,3)]),(3,[(0,2,3)]),(1,[(2,0,2)]),(0,[(1,1,3)]),(5,[(2,0,2)]),(0,[(1,0,3),(3,2,6)]),(3,[(1,0,4)]),(2,[(1,0,4),(1,1,4)]),(4,[(1,1,4)]),(1,[(1,0,4),(1,1,4)]),(5,[]),(1,[(1,1,4)]),(1,[(1,0,4)]),(5,[(2,1,2),(1,0,6)]),(3,[(3,2,3),(1,0,6)]),(0,[(3,0,2),(2,1,6)]),(0,[(3,0,1),(0,2,6)]),(0,[(3,0,2),(2,3,6)]),(0,[(3,0,2),(0,3,6)]),(4,[(3,2,3),(1,5,6)]),(2,[(1,0,3),(1,5,6)]),(1,[(2,0,2),(1,5,6)]),(1,[(1,0,5)]),(1,[(3,0,5)]),(1,[(1,0,2),(1,5,6)]),(1,[(1,0,5),(3,2,6)]),(0,[(2,2,5),(2,3,6)]),(0,[(0,2,3),(3,5,6)]),(5,[(2,0,2),(1,5,6)]),(1,[(2,0,2),(3,5,6)]),(1,[(1,0,2),(1,0,5)]),(8,[(1,0,5)]),(1,[(2,0,2),(1,0,5)]),(5,[(2,0,2),(1,0,5)]),(2,[(1,0,3),(1,0,5)]),(4,[(3,2,3)]),(1,[(2,0,2),(2,0,5)]),(4,[(3,2,3),(1,3,5)]),(2,[(1,0,3),(1,3,5)]),(8,[(1,0,5),(1,2,5)]),(4,[(1,2,3),(1,2,5)]),(1,[(1,0,5),(1,2,5)]),(5,[(1,0,5),(1,2,5)]),(1,[(3,0,5),(1,2,5)]),(2,[(2,0,5)]),(1,[(1,0,5),(3,2,5)]),(0,[(1,2,3),(1,2,5)]),(5,[(1,2,5)]),(1,[(2,2,5)]),(1,[(0,1,2),(1,5,6)]),(1,[(3,0,1),(1,1,5)]),(1,[(1,1,5),(0,0,6)]),(1,[(1,1,5),(3,0,6)]),(1,[(1,1,5)]),(5,[(1,1,5)]),(0,[(1,0,3),(1,1,5)]),(0,[(1,1,5)]),(1,[(3,1,5)]),(0,[(1,0,3)]),(1,[(2,1,5)]),(4,[(0,2,3)]),(5,[(3,2,5)]),(4,[(1,3,5),(3,2,6)]),(4,[(1,4,5)]),(2,[(1,0,4),(1,4,5)]),(1,[(1,0,4),(1,4,5)]),(1,[(0,2,5),(1,1,6)]),(5,[(0,2,5),(1,1,6)]),(5,[(0,0,5),(1,2,6)]),(2,[(1,0,3),(0,5,6)]),(4,[(1,1,3),(0,5,6)]),(1,[(0,1,5),(1,0,6)]),(1,[(3,0,1),(0,5,6)]),(0,[(1,0,5),(0,1,6)]),(0,[(3,0,1),(3,5,6)]),(0,[(1,0,5),(0,3,6)]),(0,[(3,0,3),(3,5,6)]),(5,[(0,1,5),(1,0,6)]),(8,[(1,4,5)]),(1,[(0,2,5),(1,4,6)]),(22,[]),(4,[(0,3,5),(1,4,6)]),(1,[(0,0,5),(1,4,6)]),(5,[(0,0,5)]),(0,[(1,0,3),(0,5,6)]),(4,[(0,3,5)]),(1,[(0,0,5)]),(0,[(0,3,5)]),(0,[(2,3,5)]),(1,[(3,2,5),(1,0,6)]),(1,[(1,0,2),(2,5,6)]),(5,[(1,0,5),(3,2,6)]),(1,[(1,0,5),(3,4,6)]),(0,[(1,0,3),(1,5,6)]),(5,[(1,0,5)]),(4,[(2,3,5)]),(0,[(1,0,3),(3,5,6)]),(5,[(2,0,5)]),(0,[(1,0,2),(2,5,6)]),(4,[(1,2,4),(2,5,6)]),(5,[(3,2,5),(1,0,6)]),(0,[(3,2,5),(1,0,6)]),(0,[(3,0,2),(2,5,6)]),(0,[(3,0,2),(0,5,6)]),(1,[(1,2,4),(2,5,6)]),(2,[(1,0,5),(3,0,5)]),(4,[(0,2,5),(1,2,5)]),(0,[(1,0,5),(1,2,5)]),(0,[(1,0,5),(3,2,5)]),(0,[(3,1,2),(1,2,5)]),(0,[(1,2,5),(3,1,6)]),(1,[(1,2,5),(3,2,5)]),(0,[(1,2,5),(3,2,5)]),(5,[(1,2,5),(3,2,5)]),(4,[(3,1,2),(3,5,6)]),(0,[(1,0,5),(1,1,5)]),(1,[(1,0,5),(1,1,5)]),(5,[(1,0,5),(1,1,5)]),(1,[(0,0,1),(1,5,6)]),(0,[(0,0,1),(1,5,6)]),(0,[(0,2,5),(1,2,5)]),(0,[(1,1,5),(3,2,5)]),(3,[(3,0,2),(2,5,6)]),(3,[(3,0,2),(0,5,6)]),(4,[(3,1,5),(3,2,5)]),(5,[(1,0,5),(3,2,5)]),(4,[(0,2,5)]),(0,[(2,0,1),(3,5,6)]),(0,[(2,1,2),(0,5,6)]),(0,[(3,1,5),(3,2,5)]),(1,[(0,2,5)]),(7,[(1,0,5)]),(1,[(1,0,5),(3,4,5)]),(1,[(3,0,5),(3,4,5)]),(1,[(2,0,5),(3,4,5)]),(0,[(2,0,2),(1,5,6)]),(0,[(2,0,2),(3,5,6)]),(4,[(0,4,5)]),(0,[(3,0,5)]),(1,[(3,0,1),(3,5,6)]),(0,[(2,0,2),(1,0,5)]),(4,[(2,1,2),(3,5,6)]),(0,[(1,0,5),(0,2,6)]),(0,[(2,1,2),(1,1,5)]),(1,[(1,0,5),(0,2,6)]),(5,[(1,0,5),(3,1,6)]),(4,[(1,1,5),(3,4,6)]),(0,[(0,0,1),(3,2,6)]),(0,[(2,0,2),(2,1,6)]),(2,[(3,1,5),(2,0,6)]),(0,[(3,1,2),(0,5,6)]),(0,[(3,2,5),(1,3,6)]),(1,[(3,2,5),(3,4,6)]),(4,[(3,2,5),(1,3,6)]),(0,[(2,2,3)]),(1,[(3,1,5),(3,2,5)]),(5,[(3,1,5),(3,2,5)]),(4,[(1,4,5),(3,4,5)]),(1,[(3,4,5),(1,0,6)]),(2,[(1,4,5),(3,4,5)]),(1,[(1,4,5),(3,4,5)]),(0,[(1,3,5),(3,2,6)])]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def spec (i : Nat) := specs[i]?.getD (0,[])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def negatives : List Row := [0,1,2,4,8,9,10,12,16,17,18,20,32]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def check (i : Nat) := good branchA negatives in6 mins spec entries book perm i
end ATable10782

namespace ATable10782
open Core Bound10782 GateForest12127 CertBlocks12127 Compact10782 AMin10782
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk0 : Good check 0 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk4 : Good check 4 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk8 : Good check 8 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk12 : Good check 12 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk16 : Good check 16 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk20 : Good check 20 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk24 : Good check 24 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk28 : Good check 28 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk32 : Good check 32 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk36 : Good check 36 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk40 : Good check 40 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk44 : Good check 44 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk48 : Good check 48 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk52 : Good check 52 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk56 : Good check 56 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk60 : Good check 60 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk64 : Good check 64 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk68 : Good check 68 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk72 : Good check 72 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk76 : Good check 76 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk80 : Good check 80 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk84 : Good check 84 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk88 : Good check 88 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk92 : Good check 92 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk96 : Good check 96 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk100 : Good check 100 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk104 : Good check 104 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk108 : Good check 108 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk112 : Good check 112 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk116 : Good check 116 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk120 : Good check 120 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk124 : Good check 124 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk128 : Good check 128 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk132 : Good check 132 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk136 : Good check 136 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk140 : Good check 140 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk144 : Good check 144 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk148 : Good check 148 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk152 : Good check 152 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk156 : Good check 156 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk160 : Good check 160 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk164 : Good check 164 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk168 : Good check 168 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk172 : Good check 172 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk176 : Good check 176 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk180 : Good check 180 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk184 : Good check 184 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk188 : Good check 188 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk192 : Good check 192 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk196 : Good check 196 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk200 : Good check 200 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk204 : Good check 204 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk208 : Good check 208 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk212 : Good check 212 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk216 : Good check 216 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk220 : Good check 220 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk224 : Good check 224 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk228 : Good check 228 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk232 : Good check 232 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk236 : Good check 236 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk240 : Good check 240 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk244 : Good check 244 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk248 : Good check 248 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk252 : Good check 252 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk256 : Good check 256 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk260 : Good check 260 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk264 : Good check 264 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk268 : Good check 268 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk272 : Good check 272 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk276 : Good check 276 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk280 : Good check 280 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk284 : Good check 284 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk288 : Good check 288 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk292 : Good check 292 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk296 : Good check 296 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk300 : Good check 300 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk304 : Good check 304 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk308 : Good check 308 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk312 : Good check 312 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk316 : Good check 316 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk320 : Good check 320 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk324 : Good check 324 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk328 : Good check 328 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk332 : Good check 332 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk336 : Good check 336 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk340 : Good check 340 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk344 : Good check 344 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk348 : Good check 348 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk352 : Good check 352 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk356 : Good check 356 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk360 : Good check 360 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk364 : Good check 364 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk368 : Good check 368 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk372 : Good check 372 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk376 : Good check 376 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk380 : Good check 380 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk384 : Good check 384 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk388 : Good check 388 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk392 : Good check 392 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk396 : Good check 396 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk400 : Good check 400 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk404 : Good check 404 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk408 : Good check 408 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk412 : Good check 412 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk416 : Good check 416 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk420 : Good check 420 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk424 : Good check 424 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk428 : Good check 428 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk432 : Good check 432 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk436 : Good check 436 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk440 : Good check 440 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk444 : Good check 444 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk448 : Good check 448 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk452 : Good check 452 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk456 : Good check 456 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk460 : Good check 460 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk464 : Good check 464 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk468 : Good check 468 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk472 : Good check 472 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk476 : Good check 476 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk480 : Good check 480 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk484 : Good check 484 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk488 : Good check 488 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk492 : Good check 492 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk496 : Good check 496 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk500 : Good check 500 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk504 : Good check 504 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk508 : Good check 508 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk512 : Good check 512 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk516 : Good check 516 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk520 : Good check 520 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk524 : Good check 524 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk528 : Good check 528 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk532 : Good check 532 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk536 : Good check 536 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk540 : Good check 540 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk544 : Good check 544 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk548 : Good check 548 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk552 : Good check 552 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk556 : Good check 556 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk560 : Good check 560 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk564 : Good check 564 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk568 : Good check 568 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk572 : Good check 572 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk576 : Good check 576 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk580 : Good check 580 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk584 : Good check 584 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk588 : Good check 588 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk592 : Good check 592 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk596 : Good check 596 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk600 : Good check 600 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk604 : Good check 604 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk608 : Good check 608 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk612 : Good check 612 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk616 : Good check 616 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk620 : Good check 620 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk624 : Good check 624 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk628 : Good check 628 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk632 : Good check 632 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk636 : Good check 636 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem chunk640 : Good check 640 1 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem total : Good check 0 641 := (concatGood (concatGood (concatGood (concatGood (concatGood (concatGood (concatGood chunk0 chunk4) (concatGood chunk8 (concatGood chunk12 chunk16))) (concatGood (concatGood chunk20 chunk24) (concatGood chunk28 (concatGood chunk32 chunk36)))) (concatGood (concatGood (concatGood chunk40 chunk44) (concatGood chunk48 (concatGood chunk52 chunk56))) (concatGood (concatGood chunk60 chunk64) (concatGood chunk68 (concatGood chunk72 chunk76))))) (concatGood (concatGood (concatGood (concatGood chunk80 chunk84) (concatGood chunk88 (concatGood chunk92 chunk96))) (concatGood (concatGood chunk100 chunk104) (concatGood chunk108 (concatGood chunk112 chunk116)))) (concatGood (concatGood (concatGood chunk120 chunk124) (concatGood chunk128 (concatGood chunk132 chunk136))) (concatGood (concatGood chunk140 chunk144) (concatGood chunk148 (concatGood chunk152 chunk156)))))) (concatGood (concatGood (concatGood (concatGood (concatGood chunk160 chunk164) (concatGood chunk168 (concatGood chunk172 chunk176))) (concatGood (concatGood chunk180 chunk184) (concatGood chunk188 (concatGood chunk192 chunk196)))) (concatGood (concatGood (concatGood chunk200 chunk204) (concatGood chunk208 (concatGood chunk212 chunk216))) (concatGood (concatGood chunk220 chunk224) (concatGood chunk228 (concatGood chunk232 chunk236))))) (concatGood (concatGood (concatGood (concatGood chunk240 chunk244) (concatGood chunk248 (concatGood chunk252 chunk256))) (concatGood (concatGood chunk260 chunk264) (concatGood chunk268 (concatGood chunk272 chunk276)))) (concatGood (concatGood (concatGood chunk280 chunk284) (concatGood chunk288 (concatGood chunk292 chunk296))) (concatGood (concatGood chunk300 chunk304) (concatGood chunk308 (concatGood chunk312 chunk316))))))) (concatGood (concatGood (concatGood (concatGood (concatGood (concatGood chunk320 chunk324) (concatGood chunk328 (concatGood chunk332 chunk336))) (concatGood (concatGood chunk340 chunk344) (concatGood chunk348 (concatGood chunk352 chunk356)))) (concatGood (concatGood (concatGood chunk360 chunk364) (concatGood chunk368 (concatGood chunk372 chunk376))) (concatGood (concatGood chunk380 chunk384) (concatGood chunk388 (concatGood chunk392 chunk396))))) (concatGood (concatGood (concatGood (concatGood chunk400 chunk404) (concatGood chunk408 (concatGood chunk412 chunk416))) (concatGood (concatGood chunk420 chunk424) (concatGood chunk428 (concatGood chunk432 chunk436)))) (concatGood (concatGood (concatGood chunk440 chunk444) (concatGood chunk448 (concatGood chunk452 chunk456))) (concatGood (concatGood chunk460 chunk464) (concatGood chunk468 (concatGood chunk472 chunk476)))))) (concatGood (concatGood (concatGood (concatGood (concatGood chunk480 chunk484) (concatGood chunk488 (concatGood chunk492 chunk496))) (concatGood (concatGood chunk500 chunk504) (concatGood chunk508 (concatGood chunk512 chunk516)))) (concatGood (concatGood (concatGood chunk520 chunk524) (concatGood chunk528 (concatGood chunk532 chunk536))) (concatGood (concatGood chunk540 chunk544) (concatGood chunk548 (concatGood chunk552 chunk556))))) (concatGood (concatGood (concatGood (concatGood chunk560 chunk564) (concatGood chunk568 (concatGood chunk572 chunk576))) (concatGood (concatGood chunk580 chunk584) (concatGood chunk588 (concatGood chunk592 chunk596)))) (concatGood (concatGood (concatGood chunk600 chunk604) (concatGood chunk608 (concatGood chunk612 chunk616))) (concatGood (concatGood chunk620 (concatGood chunk624 chunk628)) (concatGood chunk632 (concatGood chunk636 chunk640))))))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem impossibleA : Impossible true branchA 10 in6.toFinset := by
  have h := certifiedA (entries:=entries) (perm:=perm) (spec:=spec) (book:=book) (negRows:=negatives) (N:=641) (fun j => perm_onto _) prior (fun i hi => total i (by omega) hi) 640 (by decide)
  exact h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def requirements : List (Sig × Row × Row) := [(raw 0,2,3),(raw 1,1,3),(raw 2,1,5),(raw 3,16,24),(raw 4,8,24),(raw 5,1,33)]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lowerA : Lower true in6 branchA 11 := by
  apply lower_impossible (L:=10) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=requirements) (by decide +kernel) a
    exact (show (requirements.map Prod.fst).toFinset = in6.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact impossibleA
end ATable10782
end PEqualNP.Outside.L_meta_49841_aux.Certificate10782_aux

namespace PEqualNP.Outside.L_meta_49841_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 8 → Bool
abbrev F := X → Bool

def Cst (f : F) : Prop := ∃ b, f = fun _ => b

def Av (s : Set F) (f : F) : Prop := Cst f ∨ ∃ u ∈ s, f = u ∨ f = fun x => !u x

def comb (t : Bool) (a b : F) : F := fun x => if t then a x && b x else a x || b x

def rs (i : Fin 8) (c : Bool) (f : F) : F := fun x => f (Function.update x i c)

def Ind (i : Fin 8) (f : F) : Prop := ∀ x b, f (Function.update x i b) = f x

def Smp (i : Fin 8) (c : Bool) (f : F) : Prop := Ind i f ∨ Cst (rs i c f)

def LI (i : Fin 8) (f : F) : Prop := Ind i f ∨ ∃ e, f = fun x => xor (x i) e

inductive Prog : Set F → F → ℕ → Prop where
  | done {s f} (h : Av s f) : Prog s f 0
  | gate {s f a b k} (t : Bool) (ha : Av s a) (hb : Av s b)
      (tail : Prog (insert (comb t a b) s) f k) : Prog s f (k + 1)

theorem av_mem {s : Set F} {f} (h : f ∈ s) : Av s f := Or.inr ⟨f, h, Or.inl rfl⟩

theorem av_ins {s : Set F} {f} (g) (h : Av s f) : Av (insert g s) f := by
  rcases h with h | ⟨u, hu, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, Set.mem_insert_of_mem _ hu, h⟩

theorem av_not {s : Set F} {f} (h : Av s f) : Av s (fun x => !f x) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨!b, rfl⟩
  · exact Or.inr ⟨_, hu, Or.inr rfl⟩
  · exact Or.inr ⟨u, hu, Or.inl (by funext x; simp)⟩

theorem av_rs {s t : Set F} {i c} (hs : ∀ u ∈ s, Av t (rs i c u)) {f} (h : Av s f) :
    Av t (rs i c f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl ⟨b, rfl⟩
  · exact hs _ hu
  · exact av_not (hs _ hu)

theorem av_cheap {s : Set F} (t) {a b : F} (ha : Av s a) (hb : Av s b) (h : Cst a ∨ Cst b) :
    Av s (comb t a b) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e (fun _ => e) b = b by funext x; cases e <;> simp [comb]]
      exact hb
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩
  · by_cases h : e = t
    · subst h
      rw [show comb e a (fun _ => e) = a by funext x; cases e <;> simp [comb]]
      exact ha
    · exact Or.inl ⟨e, by funext x; cases t <;> cases e <;> simp_all [comb]⟩

theorem smp_av {s : Set F} {i c} (hs : ∀ u ∈ s, Smp i c u) {f} (h : Av s f) : Smp i c f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨b, h⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!b, by funext x; exact congrArg not (congrFun h x)⟩

theorem li_av {s : Set F} {i} (hs : ∀ u ∈ s, LI i u) {f} (h : Av s f) : LI i f := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inl fun _ _ => rfl
  · exact hs _ hu
  · rcases hs _ hu with h | ⟨e, rfl⟩
    · exact Or.inl fun x b => congrArg not (h x b)
    · exact Or.inr ⟨!e, by funext x; cases e <;> simp⟩

theorem restrict {i : Fin 8} {c : Bool} {s : Set F} {f k} (p : Prog s f k) :
    ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) →
    ∃ j ≤ k, Prog t (rs i c f) j ∧ (j = k → (∀ u ∈ s, Smp i c u) → Smp i c f) := by
  induction p with
  | done h => exact fun t hs => ⟨0, le_rfl, .done (av_rs hs h), fun _ h' => smp_av h' h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro t hs
    have pa := av_rs hs ha
    have pb := av_rs hs hb
    by_cases hc : Cst (rs i c a) ∨ Cst (rs i c b)
    · obtain ⟨j, hj, q, _⟩ := ih t (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_cheap tag pa pb hc
        · exact hs _ hu)
      exact ⟨j, by omega, q, fun he => by omega⟩
    · obtain ⟨j, hj, q, act⟩ := ih (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (hs _ hu))
      refine ⟨j + 1, by omega, .gate tag pa pb q, fun he ss => act (by omega) ?_⟩
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · have sa := (smp_av ss ha).resolve_right (fun h => hc (.inl h))
        have sb := (smp_av ss hb).resolve_right (fun h => hc (.inr h))
        exact Or.inl fun x e => by simp only [comb, sa x e, sb x e]
      · exact ss _ hu

theorem strict {i : Fin 8} {c : Bool} {s : Set F} {f k} (p : Prog s f k) (t : Set F)
    (hs : ∀ u ∈ s, Av t (rs i c u)) (hi : ∀ u ∈ s, Smp i c u) (hf : ¬ Smp i c f) :
    ∃ j, j + 1 ≤ k ∧ Prog t (rs i c f) j := by
  obtain ⟨j, hj, q, h⟩ := restrict p t hs
  exact ⟨j, lt_of_le_of_ne hj (fun he => hf (h he hi)), q⟩

theorem li_smp {i c f} (h : LI i f) : Smp i c f := by
  rcases h with h | ⟨e, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨xor c e, by funext x; simp [rs]⟩

theorem kill {i : Fin 8} {t : Bool} {a b : F} (h : (∃ e, a = fun x => xor (x i) e) ∨
    ∃ e, b = fun x => xor (x i) e) : ∃ c, Cst (rs i c (comb t a b)) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]

theorem double {i : Fin 8} {s : Set F} {f k} (p : Prog s f k) (hs : ∀ u ∈ s, LI i u)
    (hf : ∀ c, ¬ Smp i c f) :
    ∃ c, ∀ t : Set F, (∀ u ∈ s, Av t (rs i c u)) → ∃ j, j + 2 ≤ k ∧ Prog t (rs i c f) j := by
  induction p with
  | done h => exact absurd (li_smp (li_av hs h)) (hf true)
  | @gate s f a b k tag ha hb tail ih =>
    by_cases hl : (∃ e, a = fun x => xor (x i) e) ∨ ∃ e, b = fun x => xor (x i) e
    · obtain ⟨c, hc⟩ := kill (t := tag) hl
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := strict tail t (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl hc
        · exact ht _ hu) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inr hc
        · exact li_smp (hs _ hu)) (hf c)
      exact ⟨j, by omega, q⟩
    · have ia := (li_av hs ha).resolve_right (fun h => hl (.inl h))
      have ib := (li_av hs hb).resolve_right (fun h => hl (.inr h))
      obtain ⟨c, hc⟩ := ih (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact Or.inl fun x e => by simp only [comb, ia x e, ib x e]
        · exact hs _ hu) hf
      refine ⟨c, fun t ht => ?_⟩
      obtain ⟨j, hj, q⟩ := hc (insert (comb tag (rs i c a) (rs i c b)) t) (by
        intro u hu
        rcases Set.mem_insert_iff.mp hu with rfl | hu
        · exact av_mem (Set.mem_insert _ _)
        · exact av_ins _ (ht _ hu))
      exact ⟨j + 1, by omega, .gate tag (av_rs ht ha) (av_rs ht hb) q⟩

def stock : Set F := Set.range fun (i : Fin 8) (x : X) => x i

theorem stock_li (i) : ∀ u ∈ stock, LI i u := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inr ⟨false, by simp⟩
  · exact Or.inl fun x b => by simp [Function.update_of_ne h]

theorem stock_rs (i c) : ∀ u ∈ stock, Av stock (rs i c u) := by
  rintro _ ⟨j, rfl⟩
  by_cases h : j = i
  · subst h
    exact Or.inl ⟨c, by funext x; simp [rs]⟩
  · exact Or.inr ⟨_, ⟨j, rfl⟩, Or.inl (by funext x; simp [rs, Function.update_of_ne h])⟩

def pt (n : ℕ) : X := fun i => n.testBit i

theorem good_at {i c f} (a b d : ℕ)
    (h : (f (Function.update (pt a) i true) != f (pt a)) &&
        (rs i c f (pt b) != rs i c f (pt d)) = true) : ¬ Smp i c f := by
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  obtain ⟨ha, hb⟩ := h
  rintro (hi | ⟨v, e⟩)
  · exact ha (hi _ _)
  · rw [e] at hb
    simp at hb

def Low (n : ℕ) (f : F) : Prop := ∀ k, Prog stock f k → n ≤ k

theorem zero (f : F) : Low 0 f := fun _ _ => Nat.zero_le _

theorem one {n f} (i c) (h : ¬ Smp i c f) (t : Low n (rs i c f)) : Low (n + 1) f := by
  intro k p
  obtain ⟨j, hj, q⟩ := strict p stock (stock_rs i c) (fun u hu => li_smp (stock_li i u hu))
    h
  have := t j q
  omega

theorem two {n f} (i) (h0 : ¬ Smp i false f) (h1 : ¬ Smp i true f)
    (t0 : Low n (rs i false f)) (t1 : Low n (rs i true f)) : Low (n + 2) f := by
  intro k p
  obtain ⟨c, hc⟩ := double p (stock_li i) (by
    intro c
    cases c
    · exact h0
    · exact h1)
  obtain ⟨j, hj, q⟩ := hc stock (stock_rs i c)
  cases c
  · have := t0 j q
    omega
  · have := t1 j q
    omega

def rd (w : List F) (i : ℕ) : F := fun x => (w.map fun f => f x).getD i false

def gv (w : List F) (g : Gate) : F := fun x => g.op.eval (g.inputs.map fun i => rd w i x)

theorem rd_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (i : ℕ) : Av s (rd w i) := by
  by_cases h : i < w.length
  · have e : rd w i = w[i] := by funext x; simp [rd, h]
    rw [e]
    exact hw _ (List.getElem_mem h)
  · exact Or.inl ⟨false, by funext x; simp [rd, Nat.le_of_not_lt h]⟩

theorem gv_av {s : Set F} {w : List F} (hw : ∀ u ∈ w, Av s u) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hl : g.inputs.length ≤ 2) :
    Av s (gv w g) ∨ (g.op ≠ .not ∧ ∃ t a b, Av s a ∧ Av s b ∧ gv w g = comb t a b) := by
  obtain ⟨op, args⟩ := g
  simp only at hop hl
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨k, r⟩⟩⟩
  · left
    exact Or.inl ⟨op.eval [], by funext x; simp [gv]⟩
  · left
    rcases hop with rfl | rfl | rfl
    · rw [show gv w ⟨.and, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.or, [i]⟩ = rd w i by funext x; simp [gv, GateOp.eval]]
      exact rd_av hw i
    · rw [show gv w ⟨.not, [i]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr ⟨by simp, true, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · exact Or.inr ⟨by simp, false, _, _, rd_av hw i, rd_av hw j,
        by funext x; simp [gv, GateOp.eval, comb]⟩
    · left
      rw [show gv w ⟨.not, [i, j]⟩ = fun x => !rd w i x by funext x; simp [gv, GateOp.eval]]
      exact av_not (rd_av hw i)
  · simp at hl

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem toProg (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (o : ℕ) :
    ∀ (w : List F) (s : Set F), (∀ u ∈ w, Av s u) →
    ∃ k ≤ (gs.filter fun g => !isNot g).length,
      Prog s (rd (gs.foldl (fun w g => w ++ [gv w g]) w) o) k := by
  induction gs with
  | nil => exact fun w s hw => ⟨0, le_rfl, .done (rd_av hw o)⟩
  | cons g gs ih =>
    intro w s hw
    have hg' := hg g (by simp)
    have ih := ih fun v hv => hg v (by simp [hv])
    have hlen : (gs.filter fun g => !isNot g).length ≤
        ((g :: gs).filter fun g => !isNot g).length := by
      rw [List.filter_cons]
      split <;> simp
    rcases gv_av hw g hg'.1 hg'.2 with h | ⟨hn, t, a, b, ha, hb, e⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) s (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact hw _ h'
        · rw [List.mem_singleton.mp h']
          exact h)
      exact ⟨k, hk.trans hlen, p⟩
    · obtain ⟨k, hk, p⟩ := ih (w ++ [gv w g]) (insert (comb t a b) s) (by
        intro u hu
        rcases List.mem_append.mp hu with h' | h'
        · exact av_ins _ (hw _ h')
        · rw [List.mem_singleton.mp h', e]
          exact av_mem (Set.mem_insert _ _))
      refine ⟨k + 1, ?_, .gate t ha hb p⟩
      have : isNot g = false := by
        rcases hg'.1 with h | h | h
        · simp [isNot, h]
        · simp [isNot, h]
        · exact absurd h hn
      simp [this]
      simpa using hk

theorem fold_eval (gs : List Gate) (x : X) : ∀ w : List F,
    (gs.foldl (fun w g => w ++ [gv w g]) w).map (fun f => f x) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map fun f => f x) := by
  induction gs with
  | nil => exact fun _ => rfl
  | cons g gs ih =>
    intro w
    simp only [List.foldl_cons, ih, List.map_append, List.map_cons, List.map_nil]
    rfl

theorem all_not_not_of_guillabert_pr42591 {n : ℕ} {f : F} (hl : Low n f) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : gs.length ≤ n)
    (he : ∀ x : X, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨k, hk, p⟩ := toProg gs hg o
    (List.ofFn fun (i : Fin 8) (x : X) => x i) stock (by
      intro u hu
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact av_mem ⟨i, rfl⟩)
  have e : rd (gs.foldl (fun w g => w ++ [gv w g])
      (List.ofFn fun (i : Fin 8) (x : X) => x i)) o = f := by
    funext x
    rw [← he x, rd, fold_eval, List.map_ofFn]
    rfl
  rw [e] at p
  have h := hl k p
  have hle := List.length_filter_le (fun g => !isNot g) gs
  have hall : ∀ g ∈ gs, (!isNot g) = true := by
    rw [← List.length_filter_eq_length_iff]
    omega
  intro g hm
  have h2 := hall g hm
  refine ⟨?_, (hg g hm).2⟩
  rcases (hg g hm).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp [isNot, h] at h2

private theorem signed_av {s : Set F} (point : Certificate10782_aux.Core.Row → X)
    {bank : List (Certificate10782_aux.Core.Wire Certificate10782_aux.Core.Row)}
    (hs : ∀ v ∈ s, Certificate10782_aux.Core.Available true bank (fun r => v (point r)))
    {f : F} (h : Av s f) :
    Certificate10782_aux.Core.Available true bank (fun r => f (point r)) := by
  rcases h with ⟨b,rfl⟩ | ⟨a,ha,rfl | rfl⟩
  · exact Or.inr (Or.inl ⟨b,rfl⟩)
  · exact hs _ ha
  · exact Certificate10782_aux.Core.avail_inv rfl (hs _ ha)

private theorem signed_prog {s : Set F} {f : F} {k : Nat} (p : Prog s f k)
    (point : Certificate10782_aux.Core.Row → X) (roots : List (Certificate10782_aux.Core.Wire Certificate10782_aux.Core.Row)) :
    ∀ m bank, Certificate10782_aux.Core.Reach true roots m bank →
      (∀ v ∈ s, Certificate10782_aux.Core.Available true bank (fun r => v (point r))) →
      ∃ pool, Certificate10782_aux.Core.Reach true roots (m+k) pool ∧
        Certificate10782_aux.Core.Available true pool (fun r => f (point r)) := by
  induction p with
  | done h => intro m bank hm hs; exact ⟨bank,hm,signed_av point hs h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro m bank hm hs
    let a' := fun r => a (point r)
    let b' := fun r => b (point r)
    let w := Certificate10782_aux.Core.combine (!tag) a' b'
    have hl : (fun r => comb tag a b (point r)) = w := by
      cases tag <;> rfl
    have hr : Certificate10782_aux.Core.Reach true roots (m+1) (w :: bank) :=
      Certificate10782_aux.Core.Reach.two (!tag) hm (signed_av point hs ha) (signed_av point hs hb)
    obtain ⟨pool,hp,hv⟩ := ih (m+1) (w :: bank) hr (by
      intro v h
      rcases Set.mem_insert_iff.mp h with rfl | h
      · rw [hl]
        exact Or.inl (List.mem_cons_self)
      · exact Certificate10782_aux.Core.available_cons w (hs _ h))
    exact ⟨pool,by simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hp,hv⟩

private theorem from_signed_L_meta_10782 {f : F} {L : Nat}
    {roots : List Certificate10782_aux.Core.Sig} {targetWord : Certificate10782_aux.Core.Sig}
    (cols : Fin 8 → Certificate10782_aux.Core.Sig)
    (hcols : ∀ i, cols i ∈ roots ∨ cols i = Certificate10782_aux.Core.zero)
    (he : ∀ r : Certificate10782_aux.Core.Row, Certificate10782_aux.Core.bit r targetWord =
      f (fun i => Certificate10782_aux.Core.bit r (cols i)))
    (h : Certificate10782_aux.Core.Lower true roots targetWord L) : Low L f := by
  intro k p
  let point := fun r i => Certificate10782_aux.Core.bit r (cols i)
  obtain ⟨pool,hp,hv⟩ := signed_prog p point (roots.map Certificate10782_aux.Core.observe) 0
    (roots.map Certificate10782_aux.Core.observe) Certificate10782_aux.Core.Reach.start (by
      rintro _ ⟨i,rfl⟩
      rcases hcols i with hmem | hz
      · exact Or.inl (List.mem_map.mpr ⟨cols i,hmem,rfl⟩)
      · apply Or.inr; apply Or.inl
        exact ⟨false,by funext r; change Certificate10782_aux.Core.bit r (cols i) = false
                        rw [hz]; simp [Certificate10782_aux.Core.bit,Certificate10782_aux.Core.zero]⟩)
  have eq : Certificate10782_aux.Core.observe targetWord = fun r => f (point r) := funext he
  rw [← eq] at hv
  exact h k pool (by simpa using hp) hv

def target : F := fun x => (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)

def chosen : F := fun x => (x 0 && x 3) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 4) || (x 1 && x 6) || (x 1 && x 7) || (x 2 && x 6) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem donorLeaf : Low 11 (rs 6 false (rs 2 false target)) := (from_signed_L_meta_10782 (f := (rs 6 false (rs 2 false target))) ![(Certificate10782_aux.Core.inputs.getD 0 Certificate10782_aux.Core.zero), (Certificate10782_aux.Core.inputs.getD 3 Certificate10782_aux.Core.zero), Certificate10782_aux.Core.zero, (Certificate10782_aux.Core.inputs.getD 1 Certificate10782_aux.Core.zero), (Certificate10782_aux.Core.inputs.getD 4 Certificate10782_aux.Core.zero), (Certificate10782_aux.Core.inputs.getD 2 Certificate10782_aux.Core.zero), Certificate10782_aux.Core.zero, (Certificate10782_aux.Core.inputs.getD 5 Certificate10782_aux.Core.zero)] (by decide +kernel) (by decide +kernel) Certificate10782_aux.ATable10782.lowerA)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem sameLeaf : ∀ (b : Bool) (x : X),
    rs 6 false (rs 2 b chosen) x = rs 6 false (rs 2 false target) x := by
  decide +kernel

theorem sharedLeaf (b : Bool) : Low 11 (rs 6 false (rs 2 b chosen)) :=
  (funext (sameLeaf b)).symm ▸ donorLeaf

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem lower : Low 14 chosen :=
  two 2 (good_at 64 9 0 (by decide +kernel)) (good_at 64 9 0 (by decide +kernel))
    (one 6 false (good_at 1 9 0 (by decide +kernel)) (sharedLeaf false)) (one 6 false (good_at 0 9 0 (by decide +kernel)) (sharedLeaf true))

def witness : List Gate := [⟨.or, [6, 7]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [10, 9]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [12, 8]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [20, 17]⟩, ⟨.or, [21, 18]⟩]

theorem witness_ok : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : X, Circuit.eval ⟨witness, 22⟩ (List.ofFn x) = chosen x := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem target_eq : ∀ x : X, chosen x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_49841_aux

open PEqualNP.Outside.L_meta_49841_aux in
theorem PEqualNP.Outside.L_meta_49841 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hg _ he
  by_cases hs : 15 ≤ gates.length
  · exact ⟨witness, 22, witness_ok, hs, fun x => (witness_eval x).trans (target_eq x)⟩
  · exact ⟨gates, o, all_not_not_of_guillabert_pr42591 lower gates o hg (by omega)
      (fun x => (he x).trans (target_eq x).symm), le_rfl, he⟩
