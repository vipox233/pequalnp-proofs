import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32097.Certificate10782_aux

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
def inputs : List Sig := [(BitVec.ofNat 512 (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)),(BitVec.ofNat 512 (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc)),(BitVec.ofNat 512 (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0)),(BitVec.ofNat 512 (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00)),(BitVec.ofNat 512 (0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000)),(BitVec.ofNat 512 (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000)),(BitVec.ofNat 512 (replayWords [0xffffffff,0xffffffff0000000,0xffffff,0xffffffffff00000,0xffff,0xffffffffffff000,0xff,0xffffffffffffff0,0x0])),(BitVec.ofNat 512 (replayWords [0xffffffff,0xfffffffffffffff,0xfffffffff000000,0x0,0xffff,0xfffffffffffffff,0xfffffffffffff00,0x0,0x0])),(BitVec.ofNat 512 (replayWords [0xffffffff,0xfffffffffffffff,0xfffffffffffffff,0xfffffffffffffff,0xfffffffffff0000,0x0,0x0,0x0,0x0]))]
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
  row 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (0xa11421840a10611401420611200001281420000001210000610a10c20610a10c20a10c20a10c20a10c20610c40610c40610c40610c4062000000000) [],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xff00] 3 (0xa11211840a10611211420610621201210620610a10c20610620a00a10620600600610a4) [],
  row 4 [0xaaaa,0xfccc,0xfff0] 2 (0x610a10c20610620a00a10620600600610a4) [],
  row 4 [0xaa,0xcccc,0xfaf0,0xff00] 3 (0xa11201240a10611241420610000008000000610a10c20610620a00a10620600600610a4) [(2,0)],
  row 4 [0x8888,0xeeee,0xf0f0,0xff00] 3 (0xa11211840a10a41201210a40611218010610a00a00a11280610a1800061060000000000) [(2,1),(2,2)],
  row 4 [0xaa,0xaa00,0xcccc,0xf0f0,0xff00] 4 (0xa11421840a10611401420611200000000000000008030000610a10c20611280a18020a10620a00a10621280618010610600600610a4000000800000) [(1,3),(3,4),(3,3),(4,5)],
  row 4 [0xff0,0xaaaa,0xcccc,0xfff0] 3 (0x610c40c40610620a40a40620a10000000000600600610a40c40610c40610a40620a4062) [],
  row 4 [0xff0,0xaaaa,0xcccc,0xf000] 3 (0x611801820610621801810620000001840000600600610a40a10610c20610a00620a1062) [],
  row 4 [0xaaaa,0xfccc,0xfff0] 3 (0xc20610610a10c40a10c20c40c20a10610610a10620620c20a40a00a10a40a10c20620620610a40600c40620600610620610c40a40a4) [],
  row 4 [0xaaaa,0xcccc,0xfaaa,0xfff0] 3 (0xa10c20a10c20610a10c20610a10c20a10c20c40610610c40620000000000610c40610c4) [],
  row 4 [0xeaea,0xfcfc,0xffc0] 2 (0x610c11420610620c2121062060060061128) [],
  row 4 [0xaaa,0xfccc,0xfff0] 2 (0x610a10c20610620a00a10620600600610a4) [],
  row 4 [0x8888,0xeeee,0xf0f0,0xff88] 3 (0xa11211840a10a41201210a40610000000000a00a00a11288010a18000a1068000000000) [(10,6),(11,2)],
  row 4 [0xaaaa,0xdccc,0xfff0] 2 (0x610a10c20610620a00a10620600600610a4) [],
  row 4 [0x88,0xeeee,0xf0f0,0xff00] 3 (0xa11211840a10a41201210a40000008010000a00a00a11280610a1800061060000000000) [(13,1),(2,2)],
  row 4 [0xaaa,0xcccc,0xf000,0xfff0] 3 (0x1800000000000610a10c20610620a00a10620611848010610000008000000600600610a4) [(2,7),(11,3)],
  row 4 [0x8888,0xeeee,0xf0f0,0xff00] 4 (0x1840a10a11211881211841881841210a10a11210a40a41841281201211281211840a40a480b06106112180a1218098088071210610610a11280a01880a40a00a10a40a11881281288060610610a18050a18048038020a1061061801800060000000000000000000000000000) [(6,1),(7,1),(8,1),(9,2),(12,8),(14,8),(15,2),(8,2),(9,1),(12,3),(14,3),(15,1)],
  row 4 [0xff0,0xaaaa,0xcccc,0xf0f0] 3 (0x610c40c40610620a40a40620a10a11841210600600610a40c40610c40610a40620a4062) [],
  row 4 [0xaaaa,0xcccc,0xfaf0,0xffaa] 3 (0xc20a10a10c20c40610610c40620000000000610a10c20610a10a80a10c20610680610c4) [],
  row 4 [0x8888,0xaaaa,0xeeee,0xf0f0,0xff00] 4 (0xa11211840a10c41401210c41211221211410611218020610a10c00a11480a10a20a10c10610a18010610a4000000000800000000000062000000000) [(17,1),(18,9),(18,10)],
  row 4 [0xaaa,0xcccc,0xf0f0,0xff00] 3 (0xa11211840a10611211420610621201210620610a10c20610620a00a10620600600610a4) [],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xff80] 3 (0xa11211840a10611211420610621201210620610a10c20610620a00a10620600600610a4) [],
  row 4 [0x2aaa,0xcccc,0xf0f0,0xff00] 3 (0xa11211840a10611211420610621201210620610a10c20610620a00a10620600600610a4) [],
  row 4 [0x8080,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (0xa11211840a10611211420610621201210628041218031210610a10c20610620a00a10628020000000000600600610a4801000000000800000000000) [(20,11),(20,12),(20,2),(21,3),(22,5)],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xff88] 4 (0x1840a10a11211881211841881841210a10a11420c40611211480611421481421210c40c41210a40621421280621211281211420a40a40c21480c00a10c40a10c20c40c20a11480a10a11280a00c20a40a00a10a40a10c21280c28040a40680c48030688028018000c40a40a4) [(8,2),(18,13),(18,10),(3,10),(3,13)],
  row 4 [0xaaaa,0xcccc,0xeaea,0xf0f0,0xff00] 4 (0xa11211840a11211421211420611211420611211421211420a10c20a11880610a18000610a11880a11880c4061061148062000000000061148061148) [(9,11)],
  row 4 [0xaaaa,0xcccc,0xf8f8,0xff88] 3 (0xa11211840a10c41211420c40a41201210a40c00a10c20a10a00a00a10c20a40c48000a4) [(10,6)],
  row 4 [0xaaa,0xf0f0,0xfccc,0xff00] 3 (0x611211420610a11218000a10621201210620a10610c20610600600610a40620a00a1062) [(11,3)],
  row 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff88] 4 (0xa11211840a10c41211420c40a41201210a48050000000000c00a10c20a10a00a00a10c28040a18030a10a40c4802000801000000000800000000000) [(3,10),(3,13),(12,3),(26,3),(27,2),(20,1)],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xff08] 3 (0xa11211840a10610611420c40620621210a40c00a10c20a10a00a00a10c20680688000a4) [(13,2)],
  row 4 [0x8aaa,0xcccc,0xf0f0,0xff00] 3 (0xa11211840a10611211420610621201210620610a10c20610620a00a10620600600610a4) [],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xff88] 3 (0xa11211840a10610611420c40620621210a40c00a10c20a10a00a00a10c20680688000a4) [(2,2)],
  row 4 [0x88,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (0xa11211840a10c41211420c40a41201210a40000008030000c00a10c20a10a00a00a10c28020a18010a10a40c48000a4061000000000062000000000) [(14,3),(29,8),(30,2),(31,3)],
  row 4 [0xaaa,0xcccc,0xf0f0,0xff00] 4 (0x1840a10a11211881211841881841210a10a11420610611211481211421481421210610611210620621421281201211281211420620620c20610610a10c40a10c20c40c20a10610610a10620620c20a40a00a10a40a10c20620620610a40600c40620600610620610c40a40a4) [],
  row 4 [0xaaa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (0xa11211840a10611211420611211421211421211421211420610a10c20610a10c20a10c20a10c20a10c20610c40610c40610c40610c4062000000000) [],
  row 4 [0xaaa,0xccc,0xf0f0,0xff00] 3 (0xa11211840a10611211420610621201210620610a10c20610620a00a10620600600610a4) [],
  row 4 [0xaaa,0xcccc,0xf000,0xf0f0,0xff00] 4 (0xa11218030001840000000000611211420610621201210621880000000000610a10c20610620a00a10620618028010610000008000000600600610a4) [(31,14),(27,3),(35,3),(15,3)],
  row 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff00] 5 (0x1840a10a11211881211841881841210a10a11420c40c41211481211421481421210c40c41210a40a41421281201211281211420a40a481681581412181312181281181012180f1210c21480c00a10c40a10c20c40c20a11480a10a11280a00c20a40a00a10a40a10c21280c280e80d80c0a180b0a180a8098080a18070a18030a40a40c48010c4806805804000000000803802061000000000000000000000000000801800062000000000000000000000000000) [(0,9),(5,9),(0,15),(5,15),(16,3),(19,7),(19,3),(23,3),(24,8),(25,6),(28,8),(32,8),(33,2),(34,2),(36,2),(23,5),(24,3),(25,5),(28,3),(32,3),(33,1),(34,1),(36,1)],
  row 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xffaa] 4 (0xc20a10a10c20c40610610c41200000000008010000000000610a10c20610a10c20a10c20a10c20a10c20610c40610c40610c40610c4800000000000) [(4,5),(1,3)],
  row 4 [0xaaaa,0xfcfc,0xffcc,0xfff0] 3 (0xc20c40c28020a10a10c28010620a40a40620610610c48000a40620620a40e80620620c8) [(2,3),(2,4),(2,11)],
  row 4 [0xaaaa,0xfcec,0xfff0] 2 (0x610a10c20610620a21210620600600610c4) [],
  row 4 [0xa8a8,0xcccc,0xfafa,0xff00] 3 (0xc21201210c20c11211420c10a11218010a10c00c00c11280620000000000610618000a1) [(2,16),(40,12)],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xffaa,0xffcc] 4 (0x1211421218030a10c20c20a10610000000001211281218020c20a10a10c21421481428010620000000000c20a10c20a10a10c20a10c2068068800128) [(39,6),(41,17),(41,8),(31,3)],
  row 4 [0xaa,0xcccc,0xeeee,0xf0f0,0xff00] 4 (0xa11421840a11201201281840611841220610000001210000a11880a11280610a10c20610620c20a10620c40000000000a4000000000061062061800) [(14,3)],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xffa8] 3 (0xa10a11840c20610611420c40620621211420c00c00c21480a80a88010c20680688000c4) [(40,2),(40,12)],
  row 4 [0x2aa,0xcccc,0xf0f0,0xff00] 3 (0xa11211840a10611211420610621201210620610a10c20610620a00a10620600600610a4) [],
  row 4 [0xa8a8,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (0xc21211840c20c41211420c41201201211428051218041210c00c00c21481280c28030c20a10a18020c21280c48010c40610618000c4062000000000) [(31,18),(41,4),(31,8),(41,3),(44,3),(45,14)],
  row 4 [0xaaa8,0xcccc,0xf0f0,0xff00] 3 (0xc21421840c20c41401420c40621201280620c00c00c21480620a00a40620600600620a4) [],
  row 4 [0xfe,0xaaaa,0xcccc,0xf0f0] 3 (0x610a10c20610620a40a10620a11800a11210610620610a4061140061121062120062120) [],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xfefe,0xff00] 4 (0x1218011218000a11211840a10611211420610621421210621880000000001480000000001280000000000610a10c20610620a40a10620610620610a4) [(47,5),(48,3)],
  row 4 [0xee,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (0xa11801840a10611401480610621201280620000001210000610a10c20610620c20a10620a11880a11880610620611280610c40611480620a4062128) [],
  row 4 [0xa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (0xc21421840c20611401420610a41201280a40000001210000610c00c20610a00a00a40c20000000a10000610c40610a40610c40610c4062000000000) [],
  row 4 [0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00] 5 (0x1840a10a11211881211841881841210a10a112181612118481518412181412118481318414206106112181212114281114212106106112106206214281014212180f1211420620620a180e0a118880d1880a180c0a118880b1880c20610610a180a0a10c28090c20a10610610a10620620c28080c20a18070a10c20620628068030c40000000000000000000000000008058040a4000000000000000000000000000061804061803062062000000000802801800) [(16,3),(19,7),(19,3),(38,9),(38,15),(0,15),(0,9),(42,19),(43,8),(42,18),(43,17),(46,6),(49,3),(50,8),(51,2),(42,20),(43,3),(42,21),(43,7),(46,5),(49,5),(50,3),(51,1)],
  row 4 [0x8888,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (0xa11211840a10c41211420c40a41201210a48041218031210c00a10c20a10a00a00a10c28020a18010a10a40c4800000061000000000062000000000) [(4,3),(31,8),(20,2),(31,3),(20,1)],
  row 4 [0xaaaa,0xaaee,0xcccc,0xf0f0,0xff00] 4 (0xa11211840a10611211480611211841211420621621210620610a10c20610a11880a11880620c20a10620610c40611480610620611480a4000000000) [],
  row 4 [0x88aa,0xaaaa,0xcccc,0xf0f0,0xff00] 4 (0xa11421840a10611401420611201201281428001421211210610a10c20610a10c20a10c20a10c20a10c20610c40610c40610c40610c4062000000000) [(20,1)],
  row 4 [0xaa,0xa0a,0xcccc,0xf0f0,0xff00] 4 (0xc21421840c20611401420611201201281420000001210000610c00c20610000000a10000a00a00a40c20610c40610c40610c40610a40620628000a4) [(20,3)],
  row 4 [0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00] 4 (0xa11211840a11211841211840611211420610621421210620a11880a11880610a10c20610620c20a10620c40000000000a4000000000061062000800) [(4,3)],
  row 4 [0xaa,0x5500,0xaaaa,0xcccc,0xf0f0] 4 (0x610a10c20610a10c20a10c21420a11840a10a10c20a10c20610c40610c41400611420610610c40610c4000000128000062000000000000000800000) [(17,22)],
  row 4 [0xaa,0xaaaa,0xcccc,0xf0f0,0xff00] 5 (0x1840a10a11421881421841881841420a10a114206106118414814014214814218406106181181012000000000080f12812814280114200000000000000000080f80e1210000000000c20610610a10c40a10c20c40c20a10610610a11280a10c280d0c20a180c0a10c21280c20a180b0a10c280a0c20a18090a10c28080c20611280610c48070c40618060610c41280c40618050610c48040c40618030610c48020c4801800062000000000000000000000000000) [(53,5),(5,3),(32,3),(54,7),(51,4),(55,15),(43,3),(56,4),(32,6),(54,6),(51,3),(55,23),(43,4),(56,3),(57,5),(38,3),(58,14),(58,3)],
  row 4 [0xaaaa,0xcccc,0xf0f0,0xff00] 6 (0x8171840a10a18161211881218151841881848141210a10a181314206106181212114812181114214814281012106106180f12106206280e14212812080d12112812180c14206206280b0c206106180a0a10c40a18090c20c40c28080a10610618070a10620628060c20a40a08050a10a40a18040c20620628030610a40608020c40620608010610620618000c40a40a4) [(37,3),(52,3),(59,9),(59,15),(37,6),(52,6),(59,11),(59,23),(37,22),(52,22),(59,12),(59,2),(37,5),(52,5),(59,3),(59,14),(37,16),(52,16),(59,7),(59,1),(37,1),(52,1),(59,6),(59,5)]
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
def seven : Sig := (BitVec.ofNat 512 (0xfffffffffffffffefffffee8fee8fee8fffffffffffffffefffffee8fee8fee8fffffffffffffffefffffee8fee8fee8fffffffffffffffefffffee8fee8fee8))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def branchA : Sig := (BitVec.ofNat 512 (0xfffffffeffe8e8e8fffffffeffe8e8e8fffffffeffe8e8e8fffffffeffe8e8e8fffffffeffe8e8e8fffffffeffe8e8e8fffffffeffe8e8e8fffffffeffe8e8e8))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def branchB : Sig := (BitVec.ofNat 512 (0xfffffffefee8fee8fffffffefee8fee8fffffffefee8fee8fffffffefee8fee8fffffffefee8fee8fffffffefee8fee8fffffffefee8fee8fffffffefee8fee8))
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
def base3Goal : Sig := (BitVec.ofNat 512 (0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def base4Goal : Sig := (BitVec.ofNat 512 (0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def bowGoal : Sig := (BitVec.ofNat 512 (0xffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8ffeaeae8))
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
def vf8a2 : Sig := (BitVec.ofNat 512 (0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem f8a2 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 2) vf8a2 1 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,2,3), (raw 1,1,3)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vfea2 : Sig := (BitVec.ofNat 512 (0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem fea2 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 2) vfea2 1 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,0,2)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vfa8a3 : Sig := (BitVec.ofNat 512 (0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem fa8a3 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 3) vfa8a3 2 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,2,3), (raw 1,1,3), (raw 2,1,5)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vfe8a3 : Sig := (BitVec.ofNat 512 (0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem fe8a3 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 3) vfe8a3 4 := by
  exact lift_ok (ms:=[]) (xs:=[]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vfeaa3 : Sig := (BitVec.ofNat 512 (0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem feaa3 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 3) vfeaa3 2 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,4,6), (raw 2,2,6)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffea3 : Sig := (BitVec.ofNat 512 (0xfefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefe))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffea3 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 3) vffea3 2 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,0,2), (raw 2,0,4)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vfeac0a4 : Sig := (BitVec.ofNat 512 (0xeac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0eac0))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem feac0a4 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 4) vfeac0a4 3 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,8,9), (raw 1,4,6), (raw 2,2,6), (raw 3,1,9)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vfeae8a4 : Sig := (BitVec.ofNat 512 (0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem feae8a4 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 4) vfeae8a4 5 := by
  exact lift_ok (ms:=[forceLow 3]) (xs:=[(raw 3,1,9)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffee8a4 : Sig := (BitVec.ofNat 512 (0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffee8a4 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 4) vffee8a4 7 := by
  exact lift_ok (ms:=[]) (xs:=[]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffeeaa4 : Sig := (BitVec.ofNat 512 (0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffeeaa4 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 4) vffeeaa4 5 := by
  exact lift_ok (ms:=[forceLow 3, swapNext 2, swapNext 1, swapNext 0]) (xs:=[(raw 0,0,1)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffeeea4 : Sig := (BitVec.ofNat 512 (0xfeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeeefeee))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffeeea4 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 4) vffeeea4 3 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,0,2), (raw 2,8,12), (raw 3,4,12)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffffea4 : Sig := (BitVec.ofNat 512 (0xfffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffefffe))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffffea4 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 4) vffffea4 3 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,0,2), (raw 2,0,4), (raw 3,0,8)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffeeafcc0a5 : Sig := (BitVec.ofNat 512 (0xfeeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffeeafcc0a5 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 5) vffeeafcc0a5 6 := by
  exact lift_ok (ms:=[forceLow 3, forceLow 4, swapNext 2, swapNext 1, swapNext 0]) (xs:=[(raw 0,16,17), (raw 4,1,17)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffeeafee8a5 : Sig := (BitVec.ofNat 512 (0xfeeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8feeafee8))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffeeafee8a5 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 5) vffeeafee8a5 8 := by
  exact lift_ok (ms:=[forceLow 4]) (xs:=[(raw 4,1,17)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffeeefaa8a5 : Sig := (BitVec.ofNat 512 (0xfeeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffffefeeea5 : Sig := (BitVec.ofNat 512 (0xfffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeee))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffffefeeea5 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 5) vffffefeeea5 6 := by
  exact lift_ok (ms:=[forceLow 3, forceLow 4, swapNext 2, swapNext 1, swapNext 0, swapNext 3, swapNext 2, swapNext 1]) (xs:=[(raw 0,0,1), (raw 1,0,2)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) base3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffffefefea5 : Sig := (BitVec.ofNat 512 (0xfffefefefffefefefffefefefffefefefffefefefffefefefffefefefffefefefffefefefffefefefffefefefffefefefffefefefffefefefffefefefffefefe))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem ffffefefea5 (base4 : Lower true (inputs.take 4) base4Goal 7) : Lower true (inputs.take 5) vffffefefea5 4 := by
  exact lower_count (by unfold proper; decide +kernel) [(raw 0,0,1), (raw 1,0,2), (raw 2,0,4), (raw 3,16,24), (raw 4,8,24)] (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def vffffffffea5 : Sig := (BitVec.ofNat 512 (0xfffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffefffffffe))
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
  row 5 [0xa0a0a0a,0xaaaaaaaa,0xcccccccc,0xfafafafa,0xff00ff00,0xffff0000] 5 (0x1212213081210c22c20d20c20612210d40610a42a40b40a40a13082210a10c21c20ca0c20611210cc0610a41a40ac0a40a13101210a10c00610614010a00000000004000000000000610c40610a40610c40610a112c000000000) [],
  row 5 [0xeeeeeeee,0xfafafafa,0xfcfcfcfc,0xff00ff00,0xffff0000] 4 (0x12122130812106122134a06106226207206206426407406406112135206106216206a06206416406c06406106206112a06106406112c062064062400) [],
  row 5 [0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xfafafafa,0xff00ff00,0xffff0000] 5 (0x1212213081210622620720620a122138c0a10a42a40b40a406122134a06106216206a0620a11213940a10a41a40ac0a40611213520610c20000000000620a406240006206106112a0a10a40a112c0610a18000610c4000000000) [(1,0)],
  row 5 [0xa0a0a0a,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1212213081210c22210d20c20a42a40b40a406122134a0610622620720620c21210ca0c20a41a40ac0a406112135206106216206a0620a00a00a44020614010a20610000000a10000c400000000012800000000006106206112a) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfafafafa,0xfcfcfcfc,0xff00ff00,0xffff0000] 5 (0x1212213081210a122134a0a10c22c20d20c20c42210d40c40a42a40b40a40a11213520a10c21c20ca0c20c41210cc0c40a41a40ac0a40a10c20a14000610000000000a10a40a112c0c20c40c24000620000000000640648000a4) [(1,0)],
  row 5 [0xaaaaaaaa,0xc8c8c8c8,0xf0f0f0f0,0xfafafafa,0xff00ff00,0xffff0000] 5 (0x1212213081212213082213080a122138c0a10612210d40610a42a40b40a41213101213100a11213940a10611210cc0610a41a40ac0a44010000000004030000000001280000000000610a10c40610a10a400012c0610c40610a4) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfefefefe,0xff00ff00,0xffff0000] 5 (0x1212213081212213082213080a12210d20a10612210d40610622620720621213101213100a11210ca0a10611210cc06106216206a0624010000000004030000000001280000000000610a10c20610620a40a10620610620610a4) [],
  row 5 [0xe0e0e0e,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] 5 (0x30812112122131022130831030822112112134a0610612212d022134a2d00d02210610612210620623082722622212720723080620622210a10a13082d20d22212d22213080a10a13520610611211c81213521c80c812106106112106206231016a16212116a06a3100620621210a10a13101ca0ca1211ca1213100a10a10610a00610c00620620610620610c00a00a00610a10610c00c20c00610c20610c00a10a10620c20620a00a10a00620a10620a00c20a0) [],
  row 5 [0xe0e0e0e,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x12122130812138822130c2210612210d40610622620720622213082213083901213141210611210cc06106216206a0621213101213100610c00c40610620a00a40620000000a10000610620610a40610c40610c40620a40620a4) [],
  row 5 [0xe0e0e0e,0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xff00ff00,0xffff0000] 5 (0x12122130812122130822130806122134a0610622620720620a10d22210a112131012131006112135206106216206a0620a10ca1210a10c00000000000a000000000040400000000006106200012a0610c20610a10620a10620c2) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfafafafa,0xff00ff00,0xfff0fff0,0xffff0000] 5 (0xa12213080a13082213082211ca3082211ca0612210d40610a42a40b40a41210000000000a10c20a14060610a10c40610a10a40a12343941ca0ca0ca0611c40cc0610a41240ac0a41c80610614050620000000000610c40610a4) [],
  row 5 [0xf0e0f0e,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] 4 (0x1212213081210612210d00610622620720620a10d22210a10611210cc06106212806a0620a10ca1210a10610620610a00610c00610a10620a00620a0) [],
  row 5 [0xffee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 4 (0xa11210ca0a10611210cc06106212806a0621213001212210610a10c20610620c20a10620a10d20a12210610620611280610c4061221062072062220) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffeeffee,0xffff0000] 5 (0x2218012214071212213081210a12210d20a106122130a0610622620720623100000000008000a10a14020c40000000000a40000000000a11210ca0a10611210cc06106212806a0620610a10c20610620c20a1062061062061128) [(11,0),(12,0)],
  row 5 [0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1213003081210a12d22d20a10612c42d40610622202300620000002210000a11210ca0a106112131206106216206a0621213101213100610a10c20610620c20a10620a12d20a12d206106206112a0610c40612d40620a4062230) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (0x30812112122131022130831030822112112138c0a10a12212d222138c2d20d22210a10a122140722130880e30822180d22130840730834a06106122140022134a80c34a2210610612210620623082722622212720723080620623940a10a11211ca1213941ca0ca1210a10a112140612131080b31012180a12131040631035206106112140012135280935212106106112106206231016a16212116a06a3100620620a14020a18088078060a18050a18044024020c20610610a14000a10c28030c20a10610610a10620620c28020c20a18010a10c20620624008000c40000000000000000000000000004004000a400000000000000000000000000006140006180006206200000000040040012a) [(0,1),(2,0),(3,0),(4,1),(5,1),(6,0),(7,0),(8,0),(9,0),(10,1),(13,0),(14,2),(10,3),(13,2),(14,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xcececece,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1212213081210c22210d20c222130822130806122134a0610622620720620c21210ca0c212131012131006112135206106216206a0620c24010a10a10610e10c20610620a00a40620c40000000000a40620620a40610620610a4) [],
  row 5 [0x2020202,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1212213081210c22210d20c20c42210d40c40622620720622213082213080c21210ca0c20c41210cc0c406216206a0621213101213100c00c00c24010620a00a40620000000a10000600600620a4000000061000128000000000) [],
  row 5 [0xa0a0a0a,0x22222222,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1212213081210c22210d20c20c42210d40c40a42a40b40a40622620720620c21210ca0c20c41210cc0c40a41a40ac0a406216206a0620c00c00c24010a00a00a40c20000000a10000000000610000600600620c40620a4400062) [],
  row 5 [0xff0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 4 (0xc21211ca0c20611211cc0610a412806a06a1213001212210610c00c20610a00a00a40c21ca0c20a10a10610c40610a40610c40610c40620621280a4) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xff0aff0a,0xffff0000] 5 (0x2218002214071212213081210c22210d20c20612210d40610a42a40b40a43100000000000c21ca0a10a10c40610610c40620621280a40c21211ca0c20611211cc0610a412806a06a0610c00c20610a00a00a40c20610c40610a4) [(19,0)],
  row 5 [0xa0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1213003081210c22c20d20c20612c40d40610a42200b40a40000002210000c21210ca0c20611210cc0610a41a40ac0a41213101213100610c00c20610a00a00a40c20000000a10000610c40610a40610c40610c4062000000000) [],
  row 5 [0xa0a0a0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (0x30812112122131022130831030822112112138c0c20c22212d222138c2d20d22210c20c234a0610612212d422134a2d40d42210610612210a40a43082b42a42212b40b43080a40a42214072213088083082218072213084073083940c20c21211ca1213941ca0ca1210c20c23520610611211cc1213521cc0cc1210610611210a40a43101ac1a41211ac0ac3100a40a41214061213108063101218051213104063100c20610614010c40c00c20c40c24010610614024020a00000000008040a40a40c24020c20000000000000000008044020a10000000000610a40610c48030c40618020610c40a40a40614000610c48010c40618000610c44000c4402402062000000000000000000000000000) [(16,0),(17,0),(3,0),(18,0),(0,0),(20,0),(21,2),(20,2),(21,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffa8a8] 4 (0x1212213081210a10a10d20c20610610d40c40620620721280c21210ca0c20c41210cc0c40721201210720c00c00c24080720b00b40720700700720b4) [],
  row 5 [0xa8a8a8a8,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1212213081210c22210d20c20c42210d40c41282202211284072218012210c21210ca0c20c41210cc0c41201201212304061218001210c00c00c24041280c212c0c20a10a14000c21280c412a0c40610614020c4062000000000) [(23,2),(23,0)],
  row 5 [0x54545454,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1212213081210a12210d20a10612210d406112822022112834a22134a2210a11210ca0a10611210cc0611201201212303521213521210610a10c20610a00a00a10c20c20a10c20a10600600610c40c40610c4061000000062000) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfffcfffc,0xffff0000] 5 (0x3082213082213082213082210c22210d20c20c42210d40c40622200720621210000000000a10000000000610000000002300620622300c21c20ca0c20c41c40cc0c406212806a0620c20c40c24050620a40a40620a40620620a4) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff00fc] 4 (0x1212213081210a10a10c21ca0610610c41cc1280620621280c21211ca0c20c41211cc0c40621201210620c20c40c24090620a40a40620700620620a4) [],
  row 5 [0xfcfc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1212213081210c22212d20c20c42212d40c406222022106200000034a0000c21210ca0c20c41210cc0c406212006a0624061218001210c20c40c240a0620a40a40620a10a10c22d20a40620620a40610610c42d4062128062128) [(27,2)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfcfcfcfc,0xff00ff00,0xffff0000] 6 (0x30812112122131022130831030822112112134a40734a22180922134a80834a22140722138c0c20c22212d222138c2d20d22210c20c234a0c40c42212d422134a2d40d42210c40c42210620623082302202212300723080620623524063521218071213528063521214061213940c20c21211ca1213941ca0ca1210c20c23520c40c41211cc1213521cc0cc1210c40c412106206231012812012112806a3100620624004000a10000000000000000000000000004004020610000000000000000000000000008051281288040620628030620628021281280c24020c24000c40c40000000004004004004020620620c20a40a48010a40a40c20620624000a40a40c40620628000620620c40a40a4) [(4,1),(4,0),(24,0),(6,0),(17,0),(25,0),(26,0),(28,2),(26,2),(28,0)],
  row 5 [0xaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa] 5 (0x30012112140b0c20a10a10c20c40610610c42200000000004000000000000a11210ca0a10611210cc0611213101212301213101212210610a10c20610a10c20a10c20a10c20a10c20610c40610c40610c40610c4072000000000) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa,0xffffcccc] 5 (0x2213082214001212213101210a10c20c20a10610000000002210720720b434212112140c0c20a10a10c234a2d40d40d40620000000000a11210ca0a12d41213121210721721210720c20a10c20a10720c20a1072070070072230) [],
  row 5 [0xf0a0f0a,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1212213081210c22210d20c20612210d40610a42a40b40a422138c22138c0c21213940c20611210cc0610a412806a06a1213101213940610c00c20610a00a00a40c20000000a10000610c40610a40610c40610c40620621280a4) [],
  row 5 [0xcccccccc,0xf0f0f0f0,0xffaaffaa,0xffffaaaa,0xffffff00] 4 (0x12112806a06a1211300720720a11211ca0a10611211cc0610620621284060c20a10a10c20c40610610c40c20a10a10c20c40610610c40610a10c2061) [],
  row 5 [0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffaaffaa,0xffff0000,0xffffaaaa] 5 (0x30800000000006206212840612812106a06a0c20a10a10c20c40610610c42212300720721212218001210a12212d20a10612212d40613100000000000c20a10a10c20c40610610c40a11211ca0a10611211cc0610610a10c2061) [(33,0)],
  row 5 [0xaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffaaffaa,0xffff0000] 5 (0x22022023040712140b2281210a12c20d20a10612c40d40610000002210003100000000000c20a10a10c20c40610610c40620000000000a11211ca0a10611211cc06112112806a06a0610a10c20610a10c20a10c20610c40610c4) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa,0xffffff00] 5 (0x2213082214061210000000000a11ca1ca0a10611cc1cc0612212300720723083103084060c20a10a10c20c40610610c40620000000000a11ca1ca0a10611cc1cc0611301308002300610a10c20610a10c20a10c20610c40610c4) [(33,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00aa00,0xffff0000,0xffffaaaa] 5 (0x40b00000000040d0000000000c20a10a10c20c40610610c40620000000001212213101210a12212d20a10612212d40612212300000720a11213140a10611213120611213101212300610a10c20610a10c20a10c20610c40610c4) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xffffffaa] 5 (0x40b00000000040d0000000000c20a10a10c20c40610610c40620000000001212213081210a12212d20a10612212d40611282300720720a11211ca0a10611211cc06112112806a06a0610a10c20610a10c20a10c20610c40610c4) [],
  row 5 [0xffaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 5 (0x3840a10a11211ca1213841ca1ca1210a10a13420610611211cc1213421cc1cc12106106112122012130012812812112806a30022006a1212211213003083001213081213002212210c20610610a10c40a10c20c40c20a10610610a11280a10c21ac0c20a11ac0a10c21280c20a12210a10c238c0c20a138c0a10c22210c20611280610c416a0c406116a0610c41280c40612210610c434a0c406134a0610c42210c4128308062220221062128221128220308220) [],
  row 5 [0xffaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1213003101210a12c20d20a10612c40d40611282202301280000002210000a11211ca0a10611211cc06112112806a06a1213101213100610a10c20610a10c20a10c20a10c20a10c20610c40610c40610c40610c4062062128230) [],
  row 5 [0xffaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffaaffaa] 5 (0x3000000000000c20a10a10c20c40610610c422000000000040e0000000000a11211ca0a10611211cc06112112800006a1213081212210610a10c20610a10c20a10c20a10c20a10c20610c40610c40610c40610c4128221128308) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffaaffaa,0xffff0000] 6 (0x22140722180e80d80c22180b22180a40740730812112122140622130880930822112112138c0a10a12212d222138c2d20d22210a10a134a0610612212d422134a2d40d42210610612211281283088083082218072213081281284068003100000000000000000000000000008060c20c24020a10a18050a10a14020c20c28040c40c44000610618030610614000c40c44064060620000000000000000000000000004060a10a11211ca1218021ca1ca1210a10a14060610611211cc1218011cc1cc12106106112140612180012812800000000040640606a0c20610610a10c40a10c20c40c20a10610610a11280a10c21ac0c20a11ac0a10c21280c20611280610c416a0c406116a0610c41280c4) [(30,2),(31,2),(31,3),(13,0),(32,1),(13,1),(32,0),(34,0),(35,0),(36,2),(37,2),(38,0),(39,0),(40,0),(41,0)],
  row 5 [0xc0c0e0e,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xffff0000] 4 (0x1213003081210612610d00610622200720620a10d22210a10611210c806106216206a0620a10ca1210a10610620610a00610c00610a10620a00620a0) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xcccceeee,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1213003081210a12c20d20a134a30822122106126134a0610622200720620a11210ca0a112131012131006112135206106216206a0620a18000a14020610a10c20610620c20a10620c40000000000a406206223006106206112a) [(43,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xff00ffaa,0xffff0000] 5 (0x30840b2212211213213081210a12c20d20a10612c40d40611282202301283100000000000c20a10a10c20c40610610c40620621282300a11211ca0a10611211cc06112112806a06a0610a10c20610a10c20a10c20610c40610c4) [],
  row 5 [0xaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x30030030840b0a12c20d20a10612c40d40611282202301280000002210000a11c20ca0a10611c40cc0611201201282300000001210000610a10c20610a10c20a10c20a10c20a10c20610c40610c40610c40610c4062000000000) [],
  row 5 [0xaaaa,0xaa00aa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x30030030840b0a12c20d20a10612c40d40612202202303080000002210000a11c20ca0a10611c40cc0610000001210001201201283100610a10c20610a10c20a10c20a10c20a10c20610c40610c40610c40610c4062062406128) [],
  row 5 [0xaaaa,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (0x30812112140b31030030831030840b12112138c0a10a13082d22c238c2d20d23080a10a134a0610613082d42c434a2d40d43080610614074072200000000008082302303084073080000000000000000008084072210000000003940a10a11211ca1213941ca0ca1210a10a13520610611211cc1213521cc0cc1210610611212301213108073101218061213102302301214061213108053101218041213104063100c20610610a10c40a10c20c40c20a10610610a12300a10c22b40c20a12b40a10c22300c20a14020a10c28030c20a18020a10c24020c20612300610c42720c40612720610c42300c40614000610c48010c40618000610c44000c4407407062000000000000000000000000000) [(44,0),(21,1),(44,1),(21,0),(45,0),(46,0),(35,0),(47,0),(30,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffcccc,0xfffff0f0] 5 (0x22122134a4001213103101210a100000000034a0d40d430a0620a407206212131031012138c0d20d230c0610000000000a40620620a40d21213140d20d41213120d406212006a0620d00d00d240f0620a40a40620a40620620a4) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfaf8faf8,0xff00ff00,0xffff0000] 4 (0x3002213082210a12210d20a10c42210d40c40a42200b40a40a11210ca0a10c41c40cc0c40a41240ac0a40610610c20a10620620a10c20640642320a4) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaa88] 4 (0x1211213082210a12210d20a10610610d40c40620620720a40a11c20ca0a10c41c40cc0c40721300ac0720c00a10c20a10720a00a10720700700720a4) [],
  row 5 [0xaa88aa88,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x3002213082210a12210d20a10c42210d40c40a42200b40a44072218012210a11c20ca0a10c41c40cc0c40a43100ac0a41211214003100c00a10c20a10a00a00a10c24020a18000a10a40c42320a40610614060c4062000000000) [(50,0),(51,0)],
  row 5 [0x55445544,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1212213081210a12210d20a106122130a0610a42200b40a43082213082210a11210ca0a10611210cc0610a41201210a43101213521210610a10c20610a00a00a10c20c20a10c20a10600600610a40c40611cc061000000062000) [],
  row 5 [0xf0c0f0c,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x3082213082210a122138c0a10c42210d40c40622200720623082213082210a11a13940a10c41c40cc0c406212806a0621211213523940c00a10c40a10620a00a10620000000c20000a40620620a40610614100c40620a40620a4) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xff00ff00,0xfff0fff0,0xffff0000,0xfffff0f0] 5 (0x2210000000000a10a11ca4061ca3140ca0ca0610c40c40610620a40a406230c2d20d20d230430430c4110612c40d40610622300b40621210000000000610c40c40610620a40a40620611c40cc0610621280ac0620600600610a4) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xffffffcc] 5 (0x2210000000001210000000000a10c20c20a10610000000000a40620620a430831030840c0a12c20d20a11cc2d40d40d40622300720620a11c20ca0a12d41cc0cc0cc06212806a0620c20a10c20a10620a00a10620a40620620a4) [],
  row 5 [0xffcc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x3002213102210a12212d20a11cc2212d41cc0622200b40620000003080000a11c20ca0a12d41cc0cc0cc06212806a0621211214003100c20a10c20a10620a00a10620c20a10c20a10a40620620a40610611cc2d40620a40620a4) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffccffcc,0xffff0000] 6 (0x30840730822180b22130880a30822140722130841230822135222130835230822140622138c0a10a12212d222138c2d20d22210a10a134a1cc1cc22140022134a80930a2211cc1cc2210620623082302202212300723080620624004001210000000000000000000000000008080a10a14020c20c28070c20c24020a10a14004060610000000000000000000000000008060a40a48050620628040620628030a40a44060a10a13521ca1c28021ca0ca3520a10a13524063524001cc1cc0000000004004000cc40606206235212812880112806a3520620620c24100c20a11cc0a10c21cc0c20a14000a10a10620620c20a40a00a10a40a10c20620624000a40a41cc0620628000620621cc0a40a4) [(10,1),(31,2),(49,2),(52,0),(13,0),(21,3),(53,0),(26,0),(54,0),(55,1),(56,0),(57,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfafafaf0,0xff00ff00,0xffff0000] 4 (0x3003003084130a12210d20a10612c40d40610622240720620a11210ca0a10611c40cc06106212406a0620610a10c20610620a00a10620600600610a4) [],
  row 5 [0xaaaaaa00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x30030030840e0a12c20d20a10612c40d40610623080720622212214063080a11c20ca0a10611c40cc06106231006a0621211214073100610a10c20610620a00a10624020a18010a10600600610a4400061800061128000000000) [(59,1),(59,0)],
  row 5 [0x55555500,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x1212213081210a12212d20a10612212d40610622202210623082213082210a11211ca0a10611211cc0610621201210623101213101210610a10c20610620a00a10621ca0a11ca0a10600600610a41cc0611cc061000000128000) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf3f3f3f0,0xff00ff00,0xffff0000] 4 (0x3043043084140a12210d20a10612610d00610622240720620a11210ca0a10611610c806106212406a0620610a10c20610620a00a10620600600610a4) [],
  row 5 [0xf0f0f00,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (0x3083103084150a12a138c0a10612c40d40610622300b406222122130838c0a11a13940a10611c40cc0610621280ac0621211213103940610a10c20610620a00a10620000001ca0000600600610a4400061800061128062128062) [(62,1)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xffffff00] 6 (0x4064062210000000000000000000000000004064071210000000000000000000000000008090a10a14021ca1ca8081ca1ca4020a10a18070610614001cc1cc8061cc1cc40006106180506206280412812880312812880206206230840730840631031000000000040640640638c0a10a13082d22d238c2d22d23080a10a134a0610613082d42d434a2d42d43080610614070620623082302308012302303080620623940a10a13101ca1ca3941ca1ca3100a10a13520610613101cc1cc3521cc1cc3100610614060620623101281288001281283100620620c20610610a10c40a10c20c40c20a10610610a10620620c20a40a00a10a40a10c20620620610a40600c40620600610620610c40a40a4) [(36,2),(36,0),(60,0),(38,0),(46,0),(61,0),(56,0),(63,1),(56,1),(63,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (0x40730812112140622131022180d30831030840622112112140738c0a10a14022212d222180c38c2d20d24022210a10a140734a0610614002212d422180b34a2d40d440022106106140722106206280a3082302208092212300724073080620624063940a10a14021211ca1218083941ca0ca4021210a10a14063520610614001211cc1218073521cc0cc40012106106140612106206280631012812080512112806a4063100620624020c20610614000a10c40a18040c20c40c24000a10610614020a10620628030c20a40a08020a10a40a14020c20620624000610a40608010c40620608000610620614000c40a40a4) [(15,0),(22,1),(15,1),(22,0),(29,0),(42,0),(48,2),(58,0),(58,1),(42,2),(48,0),(58,2),(58,3),(64,0)]
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
  mk [0,1,6,9,7,5] 5 (0xc000000000000000000000201012) [(1,0)],
  mk [0,1,6,2,4,8] 5 (0xc0000000000000201012) [(1,0)],
  mk [10,0,1,6,2,4] 5 0x201000100002 [],
  mk [0,1,6,9,2,4,5] 6 (0xb0a00000000000000090000000000000000000000000000000000870065004300002000100014) [(0,1),(0,2),(0,0),(2,0),(3,0),(4,0)],
  mk [0,1,6,2,4,7,5] 6 (0x30000000000000201012) [(2,0)],
  mk [11,0,1,6,2,4,5] 6 0x201000100002 [],
  mk [12,0,2,4,5,13] 5 (0x240000000000000000000002) [],
  mk [0,1,2,4,5,14] 6 (replayWords [0x8,0x700000000000000,0x0,0x603000003,0x250403000003210,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4]) [(8,1),(8,2)],
  mk [0,1,2,15,4,5] 5 0x2020000012 [],
  mk [0,1,6,2,16,5] 5 0x201012 [],
  mk [17,0,1,6,4,5] 5 0x201000100002 [],
  mk [0,1,6,18,2,4,5] 6 (0xa09000000000000000000000000000000870065004300002000100014) [(10,1),(10,2),(10,0),(11,0),(12,3)],
  mk [0,1,6,19,4,5] 5 0x201012 [],
  mk [20,0,1,6,2,5] 5 0x201000100002 [],
  mk [0,1,6,2,4,5,21] 6 (replayWords [0x8,0x30000000000000,0x0,0x0,0x20010013]) [(14,3),(15,0)],
  mk [22,0,1,6,2,4,5] 6 0x201000100002 [],
  mk [0,1,23,2,4,5] 5 0x1101 [],
  mk [24,0,1,6,2,4,5] 6 (0x8000570600005403020104) [(18,1),(18,2),(18,0)],
  mk [0,1,6,2,4,5] 7 (0xc8000c0000b8000b0000a8000a0000980009000040000501004022050000400004810040200480004000038100401e0380007000068000600005800040000500004000050000400004800040000480004000038000400003800040000500004000050000400004800040000480004000038000400003800020060314001000021063100203140010000108211002020c0010000108215) [(5,0),(6,0),(7,0),(7,3),(9,1),(9,2),(9,0),(13,0),(16,0),(17,0),(19,3),(13,3),(16,3),(17,3),(19,0)],
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
  mk [28,30,0,2,4,5,13] 6 (0x300000000000800000000000000000000102) [(8,0),(24,0)],
  mk [12,29,30,2,4,5,13] 6 (replayWords [0x40006000,0x100000000,0x0,0x80000003]) [(8,0),(25,0)],
  mk [29,30,1,2,4,5,14] 7 (replayWords [0xed00000000000,0x0,0xc07000,0x73ba900000000,0x807000007370,0x0,0x0,0x0,0x3000303650000,0x0,0x0,0x0,0x0,0x0,0x0,0x4400000000,0x2000203210004]) [(9,0),(26,2),(27,2),(31,6),(32,1),(33,2)],
  mk [20,29,30,1,6,2,5] 6 (0x20003000200000400002) [(15,0)],
  mk [29,30,1,6,2,4,5,21] 7 (replayWords [0xc050000,0x0,0x0,0x0,0x40,0x30020000083]) [(16,0),(35,0)],
  mk [29,33,1,6,2,4,5] 6 0x200042 [(18,1)],
  mk [29,30,1,23,2,4,5] 6 0x200020000042 [(18,0)],
  mk [24,29,30,1,6,2,4,5] 7 (0xc0000000ba0900008000070600050403020104) [(37,2),(37,0),(19,0),(38,2),(38,0)],
  mk [29,30,1,6,2,4,5] 8 (0xa000058000980005800090000480008800048000500004014050200400005000030140501e0300000800008020081c0080001800018060181a018000580004800060000580005800040000500005800058000300005000058000580000800008000580005800018000180005800048000400005000048000480003000050000480004800008000080004800048000180001800048000080a019c0008000084a5210800000000000000001810019c000800019c67080c009400080000942521080000000000000000084000802008c22080005) [(20,0),(30,6),(30,5),(34,2),(34,0),(36,0),(39,3),(36,3),(39,0)],
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
  mk [24,29,30,36,34,2,4,5] 7 (0x97870000000060500000403020104) [(49,4),(49,1),(49,0),(51,0)],
  mk [29,30,36,34,2,4,5] 8 (0xc800068000c000068000b800048000b0000480006028060180602a060280100001004010260100000800008020082400800028000280a0282202800068000480008000068000681c0601e0601e0681c0680001000010000680006800008000080006800068000280002800068000481406016060160481404800010000100004800048000080000800048000480002800028000480001090000000000000000009cc0000000000000000290600000000000000001000010000100001000010000100001000010000080000800010000080005) [(44,4),(44,1),(44,0),(46,0),(48,0),(52,3),(48,3),(52,0)],
  mk [29,30,2,40,4,5,41] 6 0x0 [],
  mk [42,2,40,4,25,27] 5 0x0 [],
  mk [42,29,2,40,4,5,27] 6 0x2000000000001 [(55,0)],
  mk [42,29,30,2,43,5,44] 6 (0x3020000000000000000000000400000000000002) [],
  mk [29,30,2,45,4,5] 5 0x0 [],
  mk [42,29,2,46,4,5] 5 0x0 [],
  mk [42,29,30,2,47,5] 5 0x0 [],
  mk [42,29,30,2,48,4,5] 6 (0x280000000000000200180100080000000000000000003) [(58,0),(59,2),(59,0),(60,0)],
  mk [49,42,29,30,2,4,5] 6 0x21 [(50,0)],
  mk [42,29,30,2,40,4,5] 7 (replayWords [0xd00000000c00000,0x300b00000000500,0xa00000000400900,0x200800000,0x700700000700,0x300000000,0x0,0x700700003,0x600000000005000,0x5000004000004,0x3110002000,0x103000005000003,0x4000003100,0x2000100000000,0x0,0x4]) [(54,0),(56,2),(56,0),(57,3),(61,0),(62,3)],
  mk [50,29,30,2,4,5,41] 6 0x80000000000000001 [],
  mk [31,29,30,2,4,5,41] 6 0x0 [],
  mk [29,30,36,2,4,5,41] 7 (replayWords [0xb,0x54000000000000a,0x130028004c009,0x1100240044001,0x41ee00040034406,0xb00040028004,0x80080004001c000,0x0,0x1,0x180000040000400,0x0,0x0,0x0,0x10005000000,0x0,0x0,0x10004000000,0x0,0x1,0x60000001,0x20000000,0x5]) [(54,0),(54,3),(64,0),(65,0)],
  mk [29,51,2,4,27,26] 5 0x0 [],
  mk [42,28,2,4,25,27] 5 0x0 [],
  mk [42,36,2,4,25,27] 6 (0xd00000000500c00000000b00000000000000000000000000a00000000500900000000800000000000000000500700000000600600000000500400000000300300000000002100004) [(55,0),(55,3),(67,1),(68,0),(67,4),(68,2)],
  mk [42,50,2,4,25,27] 5 0x0 [],
  mk [42,36,2,4,5,25,27] 6 0x80400000000000002 [(70,0)],
  mk [42,50,52,2,4,27] 5 0x0 [],
  mk [42,50,29,2,4,27] 6 (replayWords [0x8c00,0x0,0x0,0x0,0x0,0x0,0x2002110000000,0x3]) [(72,0)],
  mk [42,50,29,2,4,5,27] 6 (0xc0000000240000000000000000000000002) [(70,0)],
  mk [29,51,36,2,4,5,27] 6 0x20000000000001 [(67,0)],
  mk [42,28,30,2,4,5,25] 6 (0x80100000000000000000000002) [(68,0)],
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
  mk [24,42,29,30,36,2,4,5] 7 (0x9080000000070600000504031214) [(86,0),(87,2),(87,0),(62,0)],
  mk [42,29,30,36,2,4,5] 8 (0xe000080000d800080000d000060000c800060000103001000010000100402000020080202e0200005000050140502c0500004828048120482a04828080000600009800080000800001004010240800008000020000200008000080000500005000080000801e04822048220801e06000010040101c060000600002000020000600006000050000500006000060160481a0481a0601601080010000110001000010800100001280010000000000000012440000002000020000100002000010100200e010040100c0100a02006010040100205) [(63,0),(63,3),(66,0),(77,2),(77,0),(82,0),(85,0),(88,3),(85,3),(88,0)],
  mk [58,29,30,36,2,4,5] 7 (replayWords [0x7800a000000,0x500000000001800,0x68014000000,0x58014000000,0x4c00a0014002600,0x480000000001e00,0x60012000000,0x0,0x0,0x440090012002200,0x7800f000000,0x0,0x0,0x40007800f001c06,0x1a0000006,0x160000000,0x149000000,0x0,0x200038006000a00,0x100018002000205]) [],
  mk [29,30,36,2,59,4,5] 8 (0xb000a000b000a00050e050d0505050e02000202020502000d0003000d00030001000101010d010004000404040d04000a0c0b0b0b0b0a0c0a0a020002000a0a0a0003000b000a000a00010001000a000a00040004000a00022500000000000005900380055003800175000000000000046500000000000002200200025002000200020002000200020002000200020003000100010003000300040004000300010001000200010004) [(90,0)],
  mk [29,6,2,60,4,27,26] 6 (0x70001850000000000001030000000000000000000000000000000810000003) [],
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
  mk [69,0,2,61,4,5] 5 (0x8000000000000040000002) [(103,0),(104,0)],
  mk [29,30,0,2,61,4,5] 6 (replayWords [0xa200180100,0x0,0x0,0x13]) [(105,0),(93,2),(93,0),(97,0)],
  mk [70,6,2,71,5] 4 0x0 [],
  mk [29,6,2,71,72] 4 0x0 [],
  mk [69,0,36,2,73,5] 5 (0x8000000000000000004002) [(107,1),(108,1)],
  mk [29,30,0,36,2,73,5] 6 0x11 [(109,0)],
  mk [29,30,0,36,2,65,4,5] 7 (replayWords [0x9,0x22000200001e07,0x1a000000000000,0x0,0x18002d404a0e60,0x148000c40000000,0x0,0x0,0x15]) [(106,0),(110,0),(94,6),(94,5),(98,0)],
  mk [74,0,2,4,5] 4 0x0 [],
  mk [75,0,2,4,68] 4 0x0 [],
  mk [75,69,0,2,4,5] 5 (0x800000000000000000000102) [(112,0),(113,0)],
  mk [75,29,30,0,2,4,5] 6 0x1001 [(114,0)],
  mk [76,0,77,2,5] 4 0x0 [],
  mk [76,0,36,2,68] 4 0x0 [],
  mk [76,69,0,36,2,5] 5 (0x800000000000004000000002) [(116,0),(117,0)],
  mk [76,29,30,0,36,2,5] 6 0x1001 [(118,0)],
  mk [29,30,0,36,2,4,5,78] 7 (replayWords [0x8007,0x60054000300,0x20000000000000,0x0,0x0,0x0,0x0,0x14]) [(115,0),(119,0)],
  mk [63,29,30,0,36,2,4,5] 7 (replayWords [0xd0c000b000a,0x0,0x0,0x0,0x0,0x98,0x760005040302014]) [(95,2),(95,0),(99,0)],
  mk [79,29,30,36,6,2,4,5] 7 (0x200030000100000080003) [],
  mk [29,30,0,36,2,59,4,5] 8 (replayWords [0x6400c0017002c00,0x30015000000,0x0,0x4c0028014002600,0x8012000000,0x10011000000,0x40007800f002000,0x380000000001c00,0x0,0x38007800f001c00,0x0,0x3,0x140000000000001,0x800d00060034003,0x198000000000000,0xad4000000000004,0x250000000000003,0x60000000,0x180531c00018c60,0x0,0x0,0x100028003000800,0x8003000000,0x10003000000,0x880000000000000,0x840000000000000,0x40200000004215]) [(96,6),(96,5),(101,0),(102,3),(111,0),(120,0),(121,0),(122,7)],
  mk [29,30,36,2,80,5] 7 (0x800800800800400400400400c00c00c00c00200208230200600618630600400400400a008008008008002004004004006004004004004004004004004004004004004004004004002002002002006006006006002002004002003) [],
  mk [81,29,30,36,2,4,5] 8 (0x1000010000100001000070000600007000060000800003800080000380002000020080202002000050000501405020050000481e04812048200481e010000100001000010000100001000010000100001080010000110001000010800100001280010000000000000012440000006000038000700006000060000200002000060000600005000050000600006396b701c0725cd601603800020000200003800038000500005000038000380c04812048100380c02000020000100002000010020200a01004010020100202006010040100205) [(124,3)],
  mk [29,6,2,82,4,27,26] 6 (0x300000000000000000000000000000028000800402) [(55,4)],
  mk [29,0,2,40,4,27,26] 6 0x202001 [],
  mk [29,30,1,2,83,4,5,26] 7 (replayWords [0x60000050000,0x200180,0x0,0x900000000100,0x2000000003]) [(56,5),(126,2),(127,5)],
  mk [29,30,2,40,4,32,26] 6 (0x1000000000000000000001) [],
  mk [31,29,30,2,40,4,5] 6 0x80000001 [],
  mk [29,30,36,2,82,4,5,14] 7 (replayWords [0x9a61,0x600000006020000,0x80,0x0,0x0,0x3]) [(129,4),(130,4)],
  mk [29,30,0,2,40,4,5,26] 7 (replayWords [0xa00000909000,0x0,0x8070006000500,0x0,0x4020000,0x3020000000,0x14]) [(127,2),(127,0),(129,0)],
  mk [29,30,0,36,2,43,5,44] 7 (replayWords [0x8,0x700006040000,0x0,0x0,0x50400000,0x0,0x302000000,0x14]) [(57,0)],
  mk [29,30,1,2,84,4,5] 6 0x300030000008100002 [(59,5)],
  mk [70,2,85,4,5] 4 0x0 [],
  mk [29,2,85,4,72] 4 0x0 [],
  mk [69,36,2,86,4,5] 5 (0x8000000000000000000042) [(135,1),(136,1)],
  mk [29,30,36,2,86,4,5] 6 0x200000000000000012 [(137,0)],
  mk [70,6,2,87,5] 4 0x0 [],
  mk [29,6,2,87,72] 4 0x0 [],
  mk [69,0,36,2,47,5] 5 (0x8000000000000000004002) [(139,1),(140,1)],
  mk [29,30,0,36,2,47,5] 6 0x3200000000012 [(141,0),(60,0)],
  mk [29,30,0,36,2,48,4,5] 7 (replayWords [0xe0d0000000,0x0,0xc000b08a980760,0x54000000000000,0x302000000,0x14]) [(61,0),(134,6),(134,5),(138,0),(142,0)],
  mk [88,70,2,4,5] 4 0x0 [],
  mk [88,29,2,4,72] 4 0x0 [],
  mk [88,29,89,2,4,5] 5 (0x80000000000000000000400002) [(144,0),(145,0)],
  mk [88,29,30,36,2,4,5] 6 0x1000001 [(146,0)],
  mk [90,70,6,2,5] 4 0x0 [],
  mk [90,29,6,2,72] 4 0x0 [],
  mk [90,29,89,6,2,5] 5 (0x80000000000000000000400002) [(148,0),(149,0)],
  mk [90,29,30,36,6,2,5] 6 0x1000001 [(150,0)],
  mk [29,30,0,36,2,4,5,91] 7 (replayWords [0xe060000,0xa940000000000,0x0,0x0,0x6100000000000,0x13]) [(147,1),(151,1)],
  mk [92,29,30,36,6,2,4,5] 7 (0xc2800000000000000000000071a0010000000000000003) [],
  mk [29,30,93,1,2,4,5] 6 0x1000101 [],
  mk [29,30,94,36,2,4,5] 6 0x4000001 [(50,0)],
  mk [49,29,30,0,36,2,4,5] 7 (0xa090000000000000000000086760005403020104) [(154,6),(154,5),(155,0),(62,0)],
  mk [29,30,0,36,2,40,4,5] 8 (0x7800e801c00360000004801a0000000000280190000005c0060018002e000000080160000000000100150000005000900120028004c0000000002600000028012000000440090012002200000000000000000000000000000004940000000000004a400000000000063df05ad8b5c1ef0800e00020038001000d00040034000240500000025204a94048189581404800000020000004800000040000000180829c05014c60000028005000000000028005000002080000000000001840000000000000040200000004215) [(63,0),(128,6),(128,5),(131,1),(132,0),(133,3),(143,0),(152,0),(153,1),(156,3)],
  mk [29,95,2,4,27,26] 5 0x1000000000000001 [],
  mk [96,0,36,2,4,25,27] 6 (replayWords [0x40,0x0,0x0,0x0,0x180000000004083]) [(158,1)],
  mk [97,6,2,4,27,26] 5 0x1000000000000001 [],
  mk [98,29,6,2,4,27,26] 6 (replayWords [0x8000000,0x70600,0x0,0x504000000000000,0x0,0x3020104]) [(160,0)],
  mk [0,2,99,4,25,27] 5 (0x300000000000000000000080000042) [],
  mk [29,2,3,4,27,26] 5 0x1000000000000001 [],
  mk [29,6,9,7,27,26] 5 (0x200000000000000000004000000002) [],
  mk [29,6,2,4,27,100] 5 0x1000000000000001 [],
  mk [101,30,1,2,4,26] 5 0x100000000001 [],
  mk [29,6,9,2,4,27,26] 6 (replayWords [0xc000000,0xb0a0000000000,0x90800000,0x700000006,0x5000,0x430021000004]) [(162,4),(163,0),(164,0),(165,5),(166,2),(165,0),(166,1)],
  mk [29,6,2,4,7,27,26] 6 (0x300000000000000000000000028000100000000002) [(164,0)],
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
  mk [29,6,2,4,27,26] 7 (0x5c06009e80005c00005d7618c00000bc0000b80000b40000b00000ac0000a80000a400006806409e80005c00009e89c09a50000c00009230000c00008800008400008000007c00007800007400007000006c00006806405d80005c00005d85c05950000c00005130000c00004800004400004000003c00003800000403003403000400002c00000c00002800000c00002400000401c02001c00400001800000c00001400000c00000440000c00000c20000400006) [(41,0),(69,4),(126,0),(159,4),(92,0),(161,0),(126,3),(159,8),(92,3),(161,3),(167,0),(168,0),(169,0),(169,3),(26,5),(171,0),(173,6),(174,6),(175,0),(177,0),(180,0),(181,5),(182,9),(177,3),(180,3),(181,10),(182,2),(26,0),(171,5),(173,4),(174,4),(177,5),(180,5),(181,0),(182,7),(177,10),(180,10),(181,3),(182,1)],
  mk [28,0,2,4,27,26] 5 0x0 [],
  mk [29,6,2,4,25,27,26] 6 (replayWords [0x4008000,0x760000,0x50000000000004,0x300000000000200,0x0,0x104]) [(42,0),(170,0),(184,6),(184,4)],
  mk [50,0,36,2,4,25,27] 6 (replayWords [0x30,0x40000,0x30000,0x0,0x800000403]) [(70,0)],
  mk [0,2,109,4,25,27] 5 0x1000000000000001 [],
  mk [29,6,2,16,27,26] 5 0x1000000000000001 [],
  mk [17,29,6,4,27,26] 5 0x1000000000000001 [],
  mk [29,6,18,2,4,27,26] 6 (replayWords [0x70,0x0,0x0,0xc280000000000,0x1180880003]) [(187,4),(176,0),(188,0),(189,3)],
  mk [29,6,19,4,27,26] 5 (0x200000000000000000004000000002) [],
  mk [20,29,6,2,27,26] 5 0x1000000000000001 [],
  mk [29,6,2,4,27,26,21] 6 (0xa040006000000020000000000000000000000000000000000080000003) [(191,3),(192,0)],
  mk [22,29,6,2,4,27,26] 6 (0x200000000000000000000000000000400000044002) [],
  mk [24,29,6,2,4,27,26] 6 (replayWords [0x200000000000,0x0,0x10002]) [],
  mk [28,102,0,2,4,5] 5 0x0 [],
  mk [28,0,36,2,4,5,27] 6 (replayWords [0x8000000030,0x100000080,0x0,0x3]) [(184,0),(196,0)],
  mk [29,6,2,4,5,27,26] 7 (replayWords [0x581b0000002ad65,0x280000000000000,0x0,0x0,0x201b0000006efbd,0x32000000c,0x5c0000000000000,0x0,0x0,0x20160000005956a,0x800000280000009,0x801200220040007,0x800e001a0030005,0xa10900140025003,0x8005000c0014000,0x0,0x20004000000,0x0,0x18003000000,0x1,0x20000005]) [(43,0),(71,4),(185,0),(186,4),(175,0),(190,0),(193,0),(194,0),(195,3),(190,3),(193,3),(194,3),(195,0),(27,5),(197,6),(27,0),(197,4)],
  mk [29,6,2,4,25,27,13] 6 (replayWords [0x300000003800,0x40,0x2]) [(25,0),(184,4)],
  mk [52,0,2,4,27,26] 5 0x0 [],
  mk [50,29,0,2,4,27,26] 6 0x20042 [(200,0)],
  mk [12,29,30,2,4,25,26] 6 (0xc0000000000000000000800102) [(21,0),(25,5)],
  mk [28,110,0,2,4,26] 5 0x0 [],
  mk [28,30,1,2,4,25,27] 6 (0x300000008000000000000000000000102) [(21,5),(203,5)],
  mk [28,30,0,2,4,25,26] 6 (0xc000000000000000000020102) [(21,0),(203,0)],
  mk [29,30,1,2,4,27,26] 7 (replayWords [0x500000000002800,0x0,0x0,0x4c0000000000600,0x480000000000400,0x440000000000600,0x0,0x0,0x400f0000003cc07,0x340000000000001,0x80001806c580000,0x0,0x5000a000000,0x10009000000,0x0,0x40008000000,0x10007000000,0x1,0x10046280002,0x100000000000001,0x10062080005]) [(22,0),(41,0),(127,5),(127,10),(26,6),(199,6),(201,5),(202,2),(204,4),(205,1)],
  mk [12,29,30,2,4,5,26] 6 (0x300800000040000000000000000000000002) [(170,0)],
  mk [28,30,0,2,4,5,26] 6 (replayWords [0x320000,0x400000000,0x2]) [(184,0)],
  mk [29,30,1,2,4,5,27,26] 7 (replayWords [0x801e00,0x0,0xe680000000c0,0x5,0x800a00000025000,0x380073,0x501060000000,0x0,0x0,0x4000000000205]) [(23,0),(43,0),(185,2),(201,5),(27,6),(207,2),(208,1)],
  mk [29,111,6,2,4,26] 6 (replayWords [0x700000,0xc00b00000000,0xa00000000000000,0x0,0x900900000000000,0x0,0x800800000,0x0,0x507000,0x6504300004000,0x302000001000004]) [],
  mk [50,52,0,36,2,4,27] 6 (0x1000000180020400003) [(200,0),(72,0)],
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
  mk [29,113,6,2,4,5,27] 6 (0xc0800000001000000000000000000000002) [(221,6)],
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
  mk [90,116,0,36,2,5] 5 (0x800000000000004000000002) [(232,0)],
  mk [90,30,0,36,2,5,25] 6 (replayWords [0x302000,0x400000000,0x2]) [(179,5),(233,0)],
  mk [29,30,1,2,4,5,26,91] 7 (replayWords [0x8000,0x700600005003000,0x40030000000000,0x2000000020,0x0,0x1000000000000,0x0,0x4]) [(180,6),(231,4),(234,1)],
  mk [108,30,0,36,2,4,5,25] 7 (replayWords [0x40040000000,0x180000,0x0,0x0,0x810003]) [(182,5)],
  mk [29,30,1,2,4,5,26] 8 (0x1041000000000000000000009c00003400009800003400009400002400009000002400006406000de0000c00000de0de8e20000400008600000400000c07c00de0000c00000de0de7400003400007000003400006c00002400006800002400006406002080000c00002086005d60000400005540000400000c30000c00c00c34d20c00003400002400004400003400003400002003c04003c03400003400000400003800003400003400000c00000c00003400002400002002c03002c02400002400000400002800002400002400000c00000c00002400002070000400001850000400001041000000000000000000000400000c00c00c00800400006) [(30,2),(44,0),(77,5),(128,0),(96,0),(128,3),(96,3),(183,2),(198,2),(206,0),(209,0),(213,5),(215,5),(216,2),(218,0),(220,3),(218,3),(220,0),(225,4),(34,0),(227,0),(229,1),(230,1),(235,0),(236,7),(235,3),(236,1)],
  mk [29,30,117,2,4,5] 7 (0xa00a00a00a00a00a00a00a00a00c00a00a002402082682004804104a82008008008008008008008008002002002002004004004004006006006006002002002002004004004004002002002002004004004004002002002002003) [],
  mk [29,30,36,2,118,5] 7 (0xc00e00c00c00c00600c00600c00c00c00c00200208230200400410430200a00600a00600a00a00a00a002002002002004004004004006008008006002002002002004004004004002002002002004004004004002002002002003) [],
  mk [29,30,119,36,2,4,5] 8 (0x6800098000680009800068000700006800070000680004800068000480006b7200000000000000000840008020085a0080002100020080211a0080009800070000c0000980009800048000b8000980009b694681a06b6d598280980000800008000980009800020000200009800070000480009000070000735ef681a06b630701e070000080000800070000700002000020000700004b54a681a06b58b481404800008000080004800048000200002000048000084000a020084870980008c002148008c2308800080000800008000080005) [(238,0),(239,3),(239,0)],
  mk [50,29,30,2,4,32,26] 6 (0x1000000000000000000001) [],
  mk [31,29,30,2,4,32,26] 6 (replayWords [0x300000000000,0x0,0x20102]) [(25,6),(25,5)],
  mk [28,29,30,2,4,27,13] 6 (replayWords [0x300000000000,0x0,0x810002]) [(25,0),(24,0)],
  mk [29,30,36,2,4,25,14] 7 (replayWords [0x400a000000286f0,0x0,0x2,0xb80000000000006,0xb00000000000000,0x2c0a00000028600,0x0,0x0,0x0,0x4,0xa00000000000000,0x0,0x0,0x0,0x18007000000,0x0,0x0,0x18006000000,0x2,0x800028065200001,0x10062080005]) [(26,1),(26,2),(129,4),(129,8),(241,4),(242,4),(243,1),(243,2)],
  mk [31,29,30,2,4,5,26] 6 0x80000000000000001 [],
  mk [29,30,36,2,4,5,25,14] 7 (replayWords [0xa9870000,0x0,0x60050000000000,0x0,0x0,0x400300000000000,0x0,0x2000104]) [(27,1),(27,2),(241,4),(245,4)],
  mk [50,110,29,36,2,4,32] 6 (0x10000000000000000001) [],
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
  mk [31,29,30,2,131,4,5] 6 (0x2100000000000000000000000000002) [(272,3),(273,0)],
  mk [132,31,29,30,2,4,5] 6 0x0 [],
  mk [31,29,30,133,2,4,5] 6 0x0 [],
  mk [29,30,2,134,4,5] 5 0x0 [],
  mk [135,29,30,2,4,5] 5 0x0 [],
  mk [31,29,2,136,4,5] 5 0x0 [],
  mk [31,29,30,7,8] 4 0x0 [],
  mk [31,29,30,9,7,5] 5 0x200000000000001 [(280,0)],
  mk [31,29,30,2,4,8] 5 0x20000000001 [(280,0)],
  mk [10,31,29,30,2,4] 5 0x0 [],
  mk [31,29,30,9,2,4,5] 6 (0x90800000000000000070000000000000000000000000000000000650043002100000000000004) [(277,0),(278,0),(279,2),(279,0),(281,0),(282,0),(283,0)],
  mk [31,29,30,2,4,7,5] 6 0x10000000001 [(281,0)],
  mk [11,31,29,30,2,4,5] 6 0x0 [],
  mk [137,29,30,2,4,5] 5 0x0 [],
  mk [31,29,2,138,4,5] 5 0x0 [],
  mk [31,29,30,2,16,5] 5 0x0 [],
  mk [17,31,29,30,4,5] 5 0x0 [],
  mk [31,29,30,18,2,4,5] 6 (0x807000000000000000000000000000000650043002100000000000004) [(287,3),(288,2),(288,0),(289,0),(290,3)],
  mk [22,31,29,30,2,4,5] 6 0x0 [],
  mk [31,29,30,2,4,5] 7 (0xd0000c8000c0000b8000b0000a8000a000098000180001800018000180000800008000180000800010000900008800080000780007000068000600001800018000180001800008000080000800008000580005000048000400001800018000180001800008000080000800008000380003000028000200001800018000180001800010000180001800018000100000800008000080005) [(271,0),(274,0),(275,3),(276,0),(271,3),(274,3),(275,0),(276,3),(284,0),(285,0),(286,0),(286,3),(78,0),(65,0),(291,0),(253,0),(292,0),(256,3),(291,3),(253,3),(292,3),(256,0)],
  mk [12,139,2,4,5,32] 5 (0x8040000000000000000000002) [],
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
  mk [29,30,36,2,4,5,32] 8 (0x9a798000000000000000000096300022200092300022200085f00019e00081f00019e00075c6da0960006580000965d60415400000000000000000001144c00000000000000000004800002000004400002000004000001800003c000018000038d00008000030b0000800000400000400000400000400001000001000000400001000002000001800002800002000002000000800002400002000002000000400000400002000002000001000001000002000001800000800001c00001800001800000400000400001800001800001000001000001800000800000400400401400800000800001001001000c00800000400000400000400000400006) [(34,4),(34,1),(131,1),(131,7),(244,1),(246,1),(249,0),(250,0),(255,0),(257,3),(255,3),(257,0),(262,6),(262,5),(268,1),(46,0),(270,0),(293,0),(302,0),(304,0),(305,0),(309,0),(310,3),(309,3),(310,0)],
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
  mk [147,29,30,36,2,4,5] 8 (0xb800080000b000080000a800068000a00006800050000480005000048000108001000010800100002940010000294002800000000000005ae600000080000680009000080000800004800050000800008000010000100008000080000280002800080000801e05822058220801e068000480005000068000680001000010000680006800028000280006800068180581c0581c0681804800010040101404800048000280a028140480004810058160581404810010000100001000010000100e01004010040100c0280801006010060100205) [(328,0),(329,3),(328,3),(329,0)],
  mk [29,148,30,36,2,4,5] 7 (replayWords [0x40001000000,0x18001000000,0x5400a0013002400,0x40000000001800,0x0,0x0,0x0,0x400088011002000,0x6000f000000,0x0,0x0,0x34007000e001a00,0x6000b000000,0x0,0x280040008001200,0x40008000000,0x1c0030005000800,0x18003000001,0x40000000000005]) [],
  mk [103,29,30,36,2,4,25] 7 (replayWords [0xa300000000,0x3900000000000,0x0,0x0,0x200800,0x0,0x0,0x200,0x700000000000000,0x0,0x600600000000,0x3600000000500,0x500000000003400,0x103000002104]) [],
  mk [103,29,30,36,2,4,5] 8 (0x200006800020000680002000048000200004800038000380e0380803800038000300c030080300002100010000248001000021220000000000000000680004800080000680006800038000380006800068000300003000068000680001000078000680006818020080201c0681804800038000380004800048000300003000048000480001000058000480004810020080201404810038000380003800038000380003800038000380000000000000390e000000300003000030000300000000000000310a000000100202008020060100205) [(331,0),(332,0)],
  mk [29,53,149,6,2,4,5] 6 0x1001 [],
  mk [103,29,30,149,6,2,4,5] 7 (replayWords [0x1c60,0xa000000,0x0,0x0,0x40000000000030,0x4000000080003]) [(334,0)],
  mk [150,70,6,2,5] 4 0x0 [],
  mk [150,29,6,2,72] 4 0x0 [],
  mk [150,29,89,6,2,5] 5 (0x80000000000000000000400002) [(336,0),(337,0)],
  mk [150,29,30,36,6,2,5] 6 0x1000001 [(338,0)],
  mk [29,30,0,36,2,151,4,5] 7 (replayWords [0x807000000,0x0,0x36540000,0x3020000,0x0,0x14]) [(339,1)],
  mk [103,29,30,36,6,2,4,5] 8 (replayWords [0xb5ac0902f390,0x38018000000,0x28017000001,0x40000005,0xd80000000000000,0x0,0x5000a8015002800,0x0,0x0,0x0,0x440098012002200,0x3c0080010001e00,0x0,0x0,0x0,0x30007000d001803,0x940000000000003,0x9c0000000000005,0x800a00040028000,0x123180000,0x1c050000001ce73,0x800000040000000,0x107300002,0x800000040000000,0x83180000,0x40010002000205]) [(335,5),(335,0),(313,0),(340,4),(122,3),(340,8),(122,0),(216,5),(216,0)],
  mk [29,53,0,2,4,5,26] 6 (0x300000000800004000000000000000000002) [(200,2)],
  mk [29,30,144,2,4,5,26] 6 (0x1000000000000000001) [],
  mk [50,29,30,0,2,4,5,26] 7 (replayWords [0xa0a0000000,0x90000000000050,0x800070006000000,0x0,0x0,0x5,0x400003002000104]) [(342,2),(342,0),(343,0),(201,2),(201,0),(241,0)],
  mk [29,6,2,4,5,32,13] 6 (replayWords [0x100000002000,0x100000000,0x2]) [],
  mk [29,30,1,2,4,5,27,14] 7 (replayWords [0xb000a000,0x9800,0x70000000000,0x6005000004300,0x0,0x2000000000000,0x0,0x104]) [(28,0),(199,2),(345,2),(33,2),(208,1)],
  mk [29,30,36,2,4,5,25,35] 7 (replayWords [0xa008000000,0x6004002000000,0x0,0x0,0x0,0x3]) [(245,4)],
  mk [12,29,30,112,2,4,5] 6 0x200400000002 [],
  mk [12,29,30,36,2,4,5] 7 (replayWords [0x48014000000,0x40013000000,0x0,0x480088010001e00,0x0,0x0,0x0,0x0,0x34007000e001a00,0x0,0x0,0x0,0x2c006000c001600,0x240800000025294,0x8000000e0000000,0x149000004,0xe0000000,0xc5000000,0x100018002000205]) [(348,5),(348,0),(207,5),(207,0)],
  mk [12,29,30,36,2,4,5,25] 7 (replayWords [0x5d00cb0000,0xa0000000000000,0x900080000007060,0x0,0x0,0x5004000,0x30000002014]) [(29,5),(29,0),(202,5),(202,0),(33,5),(33,0)],
  mk [29,30,152,6,2,4,5] 6 0x1001001 [],
  mk [29,30,153,36,2,4,5] 6 0x2100000000002 [(50,0)],
  mk [108,29,30,36,6,2,4,5] 7 (0x86760005000040300000201000004) [(351,5),(351,0),(352,4)],
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
  mk [54,69,0,36,2,5] 5 (0x800000000000004000000002) [(362,0),(363,0)],
  mk [54,29,30,0,36,2,5] 6 (0x320000000000000100002) [(364,0),(80,0)],
  mk [29,30,0,36,2,55,4,5] 7 (replayWords [0x908000000,0x0,0x74460000,0x5040000,0x302000000,0x14]) [(81,0),(365,0)],
  mk [50,29,30,0,36,2,4,5] 8 (replayWords [0x104000110100003,0x92403003248c02,0x401c00001c01e28,0x400000c00000c00,0xe07c00004100000,0x0,0x0,0x0,0x1d00078001e0,0x7400000000000,0x0,0x1a0,0x70001b0006800,0x0,0x180006400190,0x6000000000000,0x0,0x150,0x5c00160005400,0x120144130100104,0x920000004000100,0x4000,0x100000000000000,0x4500000003c30,0x3,0x870000000000000,0x30a28930934c2,0xc92890070030000,0x71c71c51401,0xc02071801400c10,0x400c01030800406]) [(356,6),(358,2),(356,5),(358,0),(360,0),(361,0),(344,0),(82,0),(366,0),(156,3),(366,3),(156,0),(213,2),(215,2),(213,0),(215,0),(249,0),(250,0)],
  mk [29,30,37,1,2,5,44] 6 (0x100000000000000000001) [],
  mk [38,29,30,19,5] 4 0x0 [],
  mk [38,29,30,2,5,44] 5 0x100000000000001 [(369,0)],
  mk [29,30,158,36,2,5,44] 6 (0x2000000000000000000000000001000000000002) [(370,0)],
  mk [24,29,30,0,36,2,5,44] 7 (replayWords [0x70000,0xc000000,0x0,0x0,0x0,0x1600030100083]) [(368,6),(368,5),(371,0)],
  mk [159,29,30,36,6,2,4,5] 7 (0x200030000100000080003) [],
  mk [29,30,160,36,2,4,5] 6 0x4000001 [],
  mk [56,29,30,0,36,2,4,5] 7 (0x807000000000000006050000000000000000000024320001000000004) [(374,0),(83,0)],
  mk [20,29,30,0,36,2,5] 7 (replayWords [0x400090011002000,0x800f000000,0x1000e000000,0x0,0x0,0x30006800d001800,0x0,0x0,0x0,0x24005800a001200,0x8008000000,0x10007000000,0x3,0x80000000000002,0x840000000000002,0x30008000c000,0x40200000004210,0x0,0x5]) [(35,4),(35,1),(47,0),(84,0),(217,6),(217,5),(254,0),(327,0)],
  mk [20,29,30,0,36,2,5,21] 7 (replayWords [0xa,0x950000008000000,0x0,0x6100000000000,0x0,0x10000003]) [],
  mk [29,30,0,36,2,4,5,21] 8 (replayWords [0x28a0000000,0x4238a10,0x4000214212960,0x8,0x1e0007c001e0,0x75a71930c6cc3,0x196990400180000,0x400180000800170,0x800170004000,0x4000000000,0x1600a00000000a2,0x800000000000000,0x130005400,0x140004c00000000,0x400120000000000,0x800110000000,0x2800100000,0x0,0xf0004000,0x100003c00000000,0x0,0x2,0x800000003800000,0x28b2c028034a3,0x2c02800000000,0x400000002800000,0x800000000070,0x2400080001c00,0x400060000,0x800050,0x1020000000,0xc10000,0x10,0x20000000010416]) [(36,4),(36,1),(48,0),(85,0),(102,3),(133,3),(218,6),(218,5),(255,0),(328,0),(372,3),(120,0),(373,1),(152,0),(375,0),(376,0),(377,0)],
  mk [161,162,30,1,2,4,5] 6 0x81 [],
  mk [163,164,0,2,4,5] 5 0x0 [],
  mk [161,30,0,36,2,4,5] 6 0x20000000012 [(380,2)],
  mk [29,30,37,1,2,4,5] 7 (replayWords [0x70011000000,0x0,0x300000000001800,0x8000e000000,0x0,0x1000f000000,0xd00000038000,0x7000e000000,0x0,0x0,0x0,0x6800d000000,0x0,0x0,0x0,0xc0c000000086b5,0x120000004,0x1c0000000000003,0xa0000000,0x10030000000c430,0x10001000005]) [(37,6),(379,4),(38,0),(381,1),(49,0),(87,5),(219,6),(368,0)],
  mk [29,33,37,6,2,4,5] 6 0x201000100002 [],
  mk [24,29,30,37,1,2,4,5] 7 (0x380000000000000000060000001450000046000000004083) [(383,2),(368,0)],
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
  mk [38,69,0,2,4,5] 5 (0x800000000000000000000102) [(396,0),(397,0)],
  mk [38,29,30,0,2,4,5] 6 0x1001 [(398,0)],
  mk [29,30,0,158,36,2,4,5] 7 (0x1850000000008006004000000000013) [(399,0)],
  mk [24,38,29,30,2,4,5] 6 0x200000000001 [(370,0)],
  mk [24,29,30,158,36,2,4,5] 7 (0x200000000000000000c20000000000000002000000000003) [(401,0),(371,0)],
  mk [24,29,30,170,36,2,4,5] 7 0x20001 [],
  mk [171,70,2,4,5] 4 0x0 [],
  mk [171,29,2,4,72] 4 0x0 [],
  mk [171,29,89,2,4,5] 5 (0x80000000000000000000400002) [(404,0),(405,0)],
  mk [171,29,30,36,2,4,5] 6 0x1000001 [(406,0)],
  mk [29,162,30,36,6,2,4,5] 7 (0xacba09800007605000403020001000004) [(37,1),(38,1),(37,2),(38,2),(49,4),(51,0),(407,0)],
  mk [24,29,30,0,36,2,4,5] 8 (replayWords [0x1d7400,0x1e01d0006c00000,0x6c00000000000,0x0,0x90009000230002,0x400000001c00220,0xc00,0x2100000075d0000,0x0,0x2000000001d0000,0x0,0x1f00074001d0,0x7c00000000000,0x0,0x0,0x79d0000000,0x0,0x1c0006c001b0,0x7000000000000,0x0,0x1a0,0x6c001b0006800,0x170006400180005,0xc00000001c00160,0xc00,0x150000000120005,0x130004804430,0x4,0x70000000000000,0x3ca28938934c2,0xc92890070030000,0x71c71c51401,0xc02071801400c10,0x400c01030800406]) [(382,6),(384,6),(382,5),(384,5),(395,0),(400,0),(402,0),(122,1),(403,0),(408,1),(156,0),(39,4),(39,1),(52,0),(88,0),(372,0),(220,6),(220,5),(257,0),(329,0)],
  mk [29,30,0,36,2,4,5] 9 (0x9400004400009000004400008c00002c00008800002c00008400000c00008000000c00007c07802807407006c02806800400000400400406400400000800000800800806000800004400002c00005c00004400004400000c00005800004400004404802805405004c04404804400000400000400004400004400000800000800004400002c00000c00004000002c00002c03002803c03803402c03002c00000400000400002c00002c00000800000800002c00000c01802802402001c00c01800c00000400400401400c00000c00000800800801000c00000410800000000000000000000410400000000000000000000400400420000000000410416) [(40,4),(40,1),(53,0),(89,0),(91,0),(123,0),(125,3),(157,0),(91,3),(123,3),(125,0),(157,3),(237,6),(237,5),(240,0),(311,0),(326,0),(330,0),(333,1),(341,1),(354,0),(367,0),(378,0),(409,3),(378,3),(409,0)],
  mk [172,29,30,36,83,4,5] 7 (replayWords [0xe00400000000,0xc00,0xe00000000500e00,0xe00e00000,0xd00000000d00000,0xc00,0xb00000000000000,0xa00000000a00,0x9900,0x0,0x800000000,0x700000000000006,0x5000000000,0x4300000000000,0x200000000,0x200000100100004]) [],
  mk [29,30,36,2,173,174,5] 8 (0x800080e080808000800080e0808080005000400050004000e0002000e00020001000101010e010003000303030e0300010703b001000117750004d0050004d008c00200088002000666000000000000030803b0010003b3050004a0050004a008900200088002000108017001000171066600000000000004000200050004000400010101050400040003030305040002000100010002000200030003000200010001000100010004) [(411,3),(411,9)],
  mk [29,175,2,4,27,26] 5 0x0 [],
  mk [29,30,176,2,4,5,26] 6 (replayWords [0x200000,0x4000000,0x2]) [(413,6)],
  mk [29,30,36,2,4,5,177] 6 (0x8000000000000000001) [],
  mk [178,29,30,36,2,4,5] 6 0x0 [],
  mk [29,179,36,2,4,5,27] 6 0x200000000001 [(413,1)],
  mk [29,179,30,36,4,5,21] 6 (0x100000000000000000001) [],
  mk [29,179,30,36,2,4,5] 7 (replayWords [0x70018000000,0x0,0x18017000000,0x5000b0015002800,0x98012000000,0x440000000001c00,0x0,0x0,0x400088011002000,0x0,0x0,0x0,0x3c007000e001a00,0x4,0x60000000,0x30005800a001200,0x40008000000,0x1c0030005000800,0xc0000000000601,0x40000000000005]) [(414,6),(415,0),(416,0),(417,0),(418,0)],
  mk [180,29,30,36,2,4,5] 6 0x0 [],
  mk [29,30,36,2,4,5,181] 7 (replayWords [0xa,0xd00000000000009,0x801200260048002,0x1100080040007,0x800e001a0030005,0x800900140024004,0x7000c0014000,0x0,0x1,0x40000000,0x0,0x0,0x0,0x0,0x0,0x0,0x20004000002,0x60000000,0x0,0x1,0x20000000,0x5]) [(415,2),(420,5)],
  mk [172,102,30,2,4,25] 5 0x0 [],
  mk [172,30,36,2,4,25,27] 6 (0xc000000000000000000000000008000000042) [(413,4),(422,0)],
  mk [29,182,30,2,4,5,26] 6 0x0 [],
  mk [172,30,36,2,4,5,25] 7 (replayWords [0xdc00000000000,0x0,0x0,0x0,0xb00000000500,0x0,0x50060000a00000a,0x6000009000,0x802000006800,0x700000000500000,0x0,0x700700,0x500500005,0x6000000000,0x500500000000000,0x4300,0x200100004]) [(417,2),(423,0),(424,8)],
  mk [29,183,30,36,2,4,5] 6 (0x8000000000000040000000002) [],
  mk [172,102,29,30,2,4,5] 6 (replayWords [0x800000,0x0,0x42]) [(422,0)],
  mk [172,29,30,36,2,4,5,27] 7 (replayWords [0xba090080000000,0x75650000000000,0x4000000,0x0,0x30000,0x0,0x201000004]) [(414,5),(423,0),(415,2),(426,8),(427,0)],
  mk [172,184,29,30,36,4,5] 6 0x0 [],
  mk [172,29,30,36,4,5,21] 7 (replayWords [0xdd00000000000,0x50c00000c8c0000,0xb000005,0x0,0x500000000608,0x8000000000,0x0,0x600a00,0x900000000900,0x0,0x0,0x800800,0x7,0x6000000000,0x5400000000000,0x300200,0x100100004]) [(418,2),(429,0)],
  mk [172,29,30,36,2,4,5] 8 (0x900008800090000880001000010040103001000028000280002800028000a000038000b8000380005000050140502c050000a026048120482a0a0260882201000010000882208800028000280008800088000380009000088000880005000050000880008820090240902408820010000100401004010000108001000013c001000010000100001000010000101c01004010040101a02800028000280002800029400100002a8002800000000000002b1600000038000500005000038000380c04812048100380c0280801006010060100205) [(419,2),(411,0),(421,0),(425,0),(428,0),(430,0)],
  mk [28,29,36,2,83,4,27] 6 0x8000000001 [(422,2)],
  mk [29,30,2,185,4,25,26] 6 (0x40000000000000c00080004002) [],
  mk [28,30,2,82,4,25,26] 6 0x200010002 [],
  mk [29,30,2,40,4,25,26] 7 (replayWords [0xf00000000f00,0xe00,0x400300000,0x400000000000,0xd00000000200,0x303,0x3c00000400,0x30000b00000a000,0x9300000000000,0x800800000800,0x400000000,0x200800,0x4700000000006,0x3000002000,0x202530004000003,0x4000402430,0x200100004]) [(127,2),(423,1),(129,0),(432,5),(433,0),(434,4)],
  mk [31,29,2,83,4,5,27] 6 (0x10000000000000000001) [(288,0)],
  mk [29,30,2,40,4,5,26,13] 7 (replayWords [0xe00000c,0x5c058030000000,0x20000000010,0x0,0x0,0x3]) [(436,5)],
  mk [28,30,36,2,82,4,5,25] 7 (replayWords [0x800000000000,0x0,0x70000006050,0x0,0x0,0x4030000000002,0x10000000000004]) [(434,0)],
  mk [29,30,2,40,4,5,26] 8 (0x4d1200000000000000005ac00500005ac0050000301c024c002000024c93200a024c002000024c80900000800088000080008000018000780001800058000500005800050000301c02940020000295c02000020080200a02000029400080002b4000800029400180002b0001800050000581605816050000501402000020000501405000008000580005000050000180005800050000211200000000000000002a00008000314000800029c001800031400180002100020000214002000021000200002140020000080001800010000080005) [(132,0),(425,4),(425,1),(435,0),(435,2),(437,0),(438,4),(437,2),(438,1)],
  mk [29,30,36,2,82,4,27,26] 7 (replayWords [0x50000000,0x0,0x0,0x0,0x1100d00000100,0x100000080000003]) [(126,0)],
  mk [28,29,30,36,2,83,4,5] 7 (replayWords [0x300000000000,0x0,0xa0400000064b0,0x4080000,0x3]) [(427,2),(432,0)],
  mk [29,30,36,2,186,4,5,27] 7 (0xe001880000000000000000000000000280000000000000000200000d00000000080000000000003) [(433,6)],
  mk [187,29,30,36,2,4,5,26] 7 (replayWords [0xc0000000000080,0x0,0x40000002]) [],
  mk [29,30,36,2,82,4,5,27] 8 (0xd880000000000005001a0014006800b16c5cdec5b17172001525485b5400a0012002600480089400000000000008010000200400000000000000000003c0028005001e000000200050000028000001c000000014020000000840080000802568000030005000a0018002c000000000160000000000000000000001000a00000000000800a0000020400000000000048008000a00200010006118472980021000000000000020000000a0000002000020044280000100100000010800000010003000000000000000000001000000020000005) [(128,1),(428,0),(435,6),(440,0),(131,0),(441,2),(442,0),(443,5)],
  mk [29,188,30,36,83,4,5] 6 0x0 [],
  mk [56,29,30,36,82,4,5] 7 (replayWords [0xf00e00000000000,0xc00e00,0xd00d00000,0x0,0x0,0xc00b00,0xa00000000a00,0x9000,0x5000008800000,0x700000000,0x600000000000000,0x0,0x5400000000000,0x300200,0x100000000104]) [(445,2),(429,5)],
  mk [29,30,36,2,173,5,44] 8 (0x39ce00000000000000004018013400100001344d301002c000300002c0d043c001800042000180004380008000420000800010100134001000013440401804200010000421803180028000318002800058000180005800018000580000800058000080001000010040101601000031800280003180028000428001800042000180004240008000420000800039ce000000000000000028000180003000028000280000800030000280002800010040100c0280001800008000200001800018000100001000018000080001000010000080005) [(133,4),(430,10),(430,3),(446,10),(446,3)],
  mk [189,2,85,4,5] 4 0x0 [],
  mk [29,190,2,84,4,5] 5 0x20001 [(448,2)],
  mk [191,36,2,86,4,5] 5 (0x8000000000000000000042) [(448,1),(136,1)],
  mk [191,29,36,2,46,4,5] 6 (replayWords [0x90800,0x0,0x706000000000005,0x40,0x300000201000004]) [(449,5),(450,0)],
  mk [192,29,2,46,4,5] 5 0x0 [],
  mk [29,30,2,193,85,4,5] 6 0xc20001000000002 [(450,6),(452,6)],
  mk [194,29,30,2,4,195,5] 6 0x0 [],
  mk [196,30,36,2,197,4,5] 6 0x0 [],
  mk [29,30,2,193,4,5] 7 (0x7000700070007000800090008000800020002020208020008000800080008000110010101180200070007000700070002070200020002020700070007000700010001000100010002000200020002000600050004000300010001000100010002000200020002000200020002000200010001000100010004) [(451,6),(453,0),(454,9),(455,1)],
  mk [163,29,30,2,84,4,5] 6 0x80000001 [],
  mk [196,29,30,36,2,4,5] 6 0x21 [],
  mk [29,30,36,2,197,4,5] 7 (replayWords [0x5800a8014002600,0x28006000000,0x0,0x800008026000000,0x180010006000400,0x480088011002400,0x440000000000a00,0x0,0x0,0x440010011000402,0x8010000a003c007,0xc001a0030005,0x800a00120020003,0x980000000000000,0x0,0x0,0x140028005000a00,0x0,0x100010003000400,0x40008001000205]) [(134,4),(457,4),(138,1),(458,0)],
  mk [29,30,77,2,47,5] 5 0x21 [(139,1)],
  mk [29,30,36,2,87,72] 5 0x2001 [(140,0)],
  mk [69,29,30,36,2,47,5] 6 (0x90800000000000000000706000000000000050400000000030200010000000004) [(141,0),(460,0),(461,1)],
  mk [163,29,30,36,2,198,5] 6 0x0 [],
  mk [29,30,36,2,87,5] 7 (0x8000a00090009000660060606680600080008000800080008000800080008000100010101080600060706000600060607000700070007000700070007000700010001000100010006000600060006000600060006000600060006000600060005000400030002000100010001000100010001000100010004) [(462,4),(142,4),(463,2),(463,1)],
  mk [29,30,36,2,199,4,5] 8 (0xa000098000a0000980005aee000000000000000029400280a029560280005800018000580001800058000080005800008000108001004010960280009d2b5a0280a2e96982a0982602800028000982609800018000a0000980009800008000a00009800098000100001000098000294002c8a0294512c0005ac001b56d5bd6e1b4005ac000a5695b16a0a40029c001204029ca7298002800028000280002800028000280002800028000280002800028000280001800008000200001800018000100001000018000080001000010000080005) [(143,4),(456,5),(459,2),(456,0),(459,1),(464,0)],
  mk [29,200,30,36,2,4,5] 6 0x400001 [],
  mk [163,201,29,30,2,4,5] 6 0x21 [],
  mk [114,29,30,36,2,4,5] 7 (replayWords [0x58016000000,0x0,0x0,0x5400a0013002400,0x0,0x0,0x0,0x0,0x400088011002000,0x7000e000007,0x120000000,0x0,0x3c007000e001a00,0xc0000002c005,0x800000140000000,0x128000000,0x0,0x140038006000a00,0x100018002000205]) [(466,2),(147,0),(467,2)],
  mk [90,30,70,36,2,5] 5 0x200001 [(148,0)],
  mk [90,29,30,36,2,72] 5 0x2000001 [(149,0)],
  mk [90,29,89,30,36,2,5] 6 (replayWords [0x9080000000000,0x70600000,0x500000000,0x0,0x430021000004]) [(469,0),(150,0),(470,0)],
  mk [90,202,29,30,36,2,5] 6 0x0 [],
  mk [90,29,30,36,2,5] 7 (0x8000800080008000a000a000a000a000a000a000a000a0001000100080001000200030009000900080008000800080008000800080008000800080008000800020008000800080007000600050004000100010001000100030003000300030001000100010001000300030003000300020001000100010004) [(471,0),(151,0),(472,0),(472,5)],
  mk [29,30,36,2,4,5,203] 8 (0x344c0000000000000000420d03bc00420003bd0f294c0000000000000000338001b400318001b400330000ac00318000ac00128c00000000000000004000038000400003800028000280002800028000480001800048000180004800008000480000800010000100002800010000380002800028000380003800018000400003800038000080004000038000380001004010100380002940028000298002800029400280002980028000280002800028000280001800008000200001800018000100001000018000080001000010000080005) [(152,4),(468,5),(468,0),(473,0)],
  mk [92,29,30,36,2,4,5] 8 (0x880008000088000800001080010000108001000040000580004000058000400003800040000380002940010000294002800000000000009ce400000080000100001000080000800005800088000800008000038000880008000080000280a02822080000801e08822088220801e0108001000012000100001080010000120001000010000100001000010000101c01004010040101a058000380006000058000580002800028000580005814040120401005814038000280002800038000380c04012040100380c0280801006010060100205) [(153,0)],
  mk [204,29,30,36,2,4,5] 6 0x0 [],
  mk [29,205,30,36,2,4,5] 7 (replayWords [0x78001000000,0x0,0x40001000000,0x0,0x500098012002200,0x40000000000800,0xd0000003c000,0x0,0x0,0x40007800f002000,0x7800f000000,0x0,0x0,0x38006800d001c00,0x2000d000000,0x0,0x30005800a001200,0x40008000000,0x140038006000a00,0x20003000001,0x40000000000005]) [(154,6),(155,0),(476,5)],
  mk [49,29,30,36,2,4,5] 8 (0xe000e0e0e040e000d000c000d000c000e000a0a0a040a0004000600040006000400020004000200044f0000000000000e000ec00e000ee00e000e000e000e000e000e000e000e000e000e000e000e00000000000e4e00000c000a000a000c000c0006000d000c000c0002000d000c000c0b0d0d0d0d0c0b0a000a000a000a000a000a000a000a00000000000a49000006000200080006000605040404070605020104040403020104) [(477,0),(477,2),(156,0)],
  mk [29,30,36,2,82,4,5] 9 (0x8800080000880008000050360a834050320a830028000280a0282e028000a800018000b000018000a800008000a0000080001000010040102601000080240882208822080240802002800028000802008000018000880008000080000080008800080000800001004010220800002944000000000000000063c001b400538001b40062c000a000524000a000294a0000000000000000294002800029c002800029400280002980028000280a02880000000294a01800008000200001800018000100001000018000080001000010000080005) [(157,4),(412,3),(412,7),(91,0),(431,5),(91,1),(431,0),(439,4),(444,0),(444,5),(447,3),(465,0),(474,0),(475,0),(478,8)],
  mk [154,29,2,4,27,26] 5 0x0 [],
  mk [154,29,36,2,4,5,27] 6 0x20000000000001 [(480,0)],
  mk [28,29,149,2,4,27] 5 0x0 [],
  mk [29,52,30,2,4,27,26] 6 (0xc0000000000000002004002) [(200,0),(480,5),(482,6)],
  mk [28,30,156,2,4,5,25] 6 0x100000000001 [],
  mk [29,52,30,2,4,5,26] 7 (replayWords [0xbb00000000000,0x0,0x0,0xf00000000,0xc00e00000000400,0x0,0x100000d,0xbc0000b000,0xc0411000b000400,0x0,0xa00,0xa00000000400900,0x0,0x800800000000,0x400700000000600,0x500000000400300,0x2100000000004]) [(342,2),(343,0),(481,5),(483,0),(484,4)],
  mk [50,110,29,30,2,4,26] 6 0x20001 [(482,5)],
  mk [50,206,29,2,4,27,26] 6 0x11 [],
  mk [50,29,30,2,4,25,26] 7 (replayWords [0x400000000002000,0x0,0x0,0x0,0x3c0000000000207,0x340000000000000,0x0,0x6,0x160000005,0xc0000000000004,0xa00000000000000,0x0,0x0,0x8007000000,0x18007000000,0x0,0x8006000000,0x18006000000,0x8005000000,0x18004000000,0x308c02004005]) [(483,2),(201,2),(241,0),(486,0),(487,2)],
  mk [50,122,29,2,4,5,26] 6 0x80000000000000001 [],
  mk [50,29,30,2,4,5,26,13] 7 (replayWords [0x6000000,0xa040006000000,0x22000,0x0,0x0,0x3]) [(489,0)],
  mk [50,206,29,30,2,4,5,26] 7 (replayWords [0xc000000,0x280001010000,0x0,0x0,0x180000004013]) [(484,1),(487,0)],
  mk [50,29,30,2,4,5,26] 8 (0x631800000000000000005000048000500004800040000380004000038000a800020000a000020000980000800090000080006460f000000000000000180004800018000480001800038000180003800018c00200001b8002000018c00080001b400080006318000000000000000048000380005800048000480002000050000480004800008000500004800048000180601814048000380002000040000380003800008000400003800038000180601810038000200000800030000200002000018060180a020000080001806018040080005) [(485,0),(485,2),(344,0),(488,0),(488,2),(490,0),(491,2),(490,2),(491,0)],
  mk [103,102,29,2,4,27,26] 6 0x800000000001 [],
  mk [28,29,112,2,4,27] 5 0x0 [],
  mk [29,113,30,2,4,27,26] 6 (0x80000000000000001000002) [(480,5),(494,6)],
  mk [28,29,30,2,4,32,26] 6 (replayWords [0x200000000000,0x0,0x10002]) [(25,5)],
  mk [28,110,29,30,2,4,26] 6 0x800040000002 [(494,5),(203,0)],
  mk [28,120,30,2,4,25,26] 6 (0x1000000000000000000011) [],
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
  mk [29,30,36,2,4,25,27] 8 (0x404800dc0000400000414929800002c00009400002c00009000001c00008c00001c00008a100010000081f0001000000417800000000000000000000c07400dc0000400000dc0c06c00002c00006800002c00006400001c00006000001c00005d60001000005540001000000404c00520000400000520400d14000000000000000000002c00001c00003c00002c00002c00001000003800002c00002c00000400400403402c00002c00000c00c00c03002c00001c00001000002800001c00001c00000400400402401c00001c00000c00c00c02001c00001000000400400401801000001000000c00c00c01401000000410000400400430420400006) [(183,1),(206,4),(206,1),(435,6),(435,5),(440,1),(435,11),(435,10),(440,7),(488,6),(499,5),(244,2),(502,0),(505,0),(506,0),(509,0),(510,3),(509,3),(510,0),(499,6),(488,5),(244,0),(502,2),(505,2),(506,2),(509,2),(510,9),(509,9),(510,2)],
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
  mk [154,207,29,30,2,4,26] 6 (0x800000000000000000000004000000002) [(480,0)],
  mk [50,110,29,53,36,2,4] 6 0x20000001 [(482,5)],
  mk [50,29,52,30,36,2,4,27] 7 (replayWords [0xa090800,0x0,0x0,0x0,0x0,0x700605004002,0x30000000002014]) [(211,0),(528,5),(483,0),(529,2)],
  mk [50,31,29,30,2,4,25] 6 0x0 [],
  mk [50,29,30,36,2,4,25,32] 7 (replayWords [0xc,0x50008006000000,0x4010000000,0x0,0x0,0x3]) [(247,0),(513,2),(531,0)],
  mk [50,110,29,30,36,2,4] 7 (0xa00000000a00000a00a00000c00000000c0000000ba00006000009000000000008700006000005000000000400300000000000000002000001000004) [(529,0),(247,0),(486,0)],
  mk [50,110,29,30,36,2,4,25] 7 (replayWords [0x380000000000000,0x0,0x0,0x300,0x281030004013]) [(526,5),(212,0),(247,0)],
  mk [50,29,30,36,2,4,25] 8 (0x7000068000700006800060000580006000058000180001e000180001e000bd80028000ad0002800014c80000000000000000946000000000000000006800058000780006800068000180001800068000680002800070000680006800010040101c0680006800020000700006800058000180001800058000580002800060000580005800010040101805800058000200006000058000180001800018000180001800018060180601800000000000001a86000000280001004010120280002800020100380c028000100201100018000108205) [(527,2),(530,2),(332,0),(213,2),(488,0),(249,0),(532,0),(533,0),(534,0)],
  mk [154,29,30,2,4,5,26] 6 (0x800000040000000000000000000000002) [(480,0)],
  mk [28,29,30,149,2,4,5] 6 (replayWords [0x800000,0x0,0x400000002]) [(482,0)],
  mk [29,52,30,36,2,4,5,27] 7 (replayWords [0xfed,0xcb00a0000000000,0x905008007650040,0x0,0x0,0x0,0x302001000004]) [(214,1),(536,5),(483,0),(537,6)],
  mk [50,110,29,30,36,2,4,5] 7 (replayWords [0x9000800000002,0x700000000000000,0x0,0x0,0x0,0x60,0x500000000043214]) [(537,5),(513,0),(486,0)],
  mk [50,29,30,36,2,4,5,25] 8 (replayWords [0x8,0x880000000000005,0x801900160064004,0x801800120060001,0x80170006005c00b,0x14002a0050009,0x900000000000008,0xca2000000000002,0x1000160040002,0xf0012003c000,0x31806470c002,0xc001a0030001,0x108200000008421,0x8c0000000000000,0x0,0x0,0x0,0x1000b000000,0x28002000b001400,0x0,0x0,0x10009000000,0x200020009001000,0x0,0x18003000000,0x83000000,0x10007000000,0x140020006000a00,0x40411003008215]) [(538,2),(215,2),(514,0),(488,0),(250,0),(539,0)],
  mk [20,28,29,30,36,2,5] 6 0x0 [],
  mk [28,29,30,36,2,4,5,21] 7 (replayWords [0x8007,0x0,0x65430000000000,0x0,0x0,0x0,0x2010000000000,0x4]) [(541,0)],
  mk [20,29,30,36,2,5,25] 7 (replayWords [0x9,0x840000000000002,0x800a000a0028009,0x1000220040007,0x800d001c0034006,0x180000000000005,0x800a000a0028000,0x4,0x120000004,0xe0000000,0x180100000004200,0x0,0x0,0x0,0x28005000000,0x0,0x0,0x8004000000,0x0,0x8003000000,0x0,0x200000004005]) [(217,6),(217,4),(515,0),(515,1),(254,0),(541,5),(254,1),(541,0)],
  mk [29,30,36,2,4,5,25,21] 8 (0x2c635a50a52963129400000000000031359000c0064d929c000000000000b00180008006000b00170008005c00112d5000a005455a0800000000000030013000c004c0029251000a0044b18000e001e0038006800b0018002c0051c00000000000030000000c00000001c0500000014a020000001200000020000001000000001c0200000008400000028006000000000000000000000000000000000000000010006000002800000080000002800000080000002800028045200000000000000000000000010003000000000010001000005) [(218,6),(218,4),(516,0),(516,1),(255,0),(542,5),(255,1),(542,0),(543,0)],
  mk [161,29,30,2,4,5,26] 6 0x80000000000000001 [],
  mk [28,29,30,37,2,4,5] 6 0x80001 [],
  mk [29,162,30,36,2,4,5,27] 7 (replayWords [0xba9,0x870060000000000,0x5040000,0x0,0x0,0x0,0x302001000004]) [(219,1),(545,5),(546,6)],
  mk [24,28,29,30,36,2,4,5] 7 (0xc280000000000000008d13) [(546,0)],
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
  mk [12,31,29,2,4,5,27] 6 (0xc0800000001000000000000000000000002) [],
  mk [31,29,30,209,2,4,5] 6 0x200001 [(288,2)],
  mk [107,122,29,36,2,4,5] 6 0x0 [],
  mk [31,29,30,2,4,5,25] 7 (replayWords [0x840000000000008,0x8010001e0038006,0x800c00160028001,0x80030006000c000,0xa00000000000004,0x80030006000c000,0x0,0x1,0x800000060000000,0x200100000004200,0x700000018000,0x0,0x0,0x8005000000,0x0,0x0,0x8004000000,0x0,0x18003000000,0x0,0x200000004005]) [(565,2),(436,2),(436,9),(531,0),(489,6),(566,0),(555,0),(567,6),(559,3),(566,3),(555,3),(567,11),(559,0)],
  mk [31,29,30,2,4,5,25,32] 7 (replayWords [0x200a000000,0x8006000000,0x4010000000,0x0,0x0,0x3]) [(261,5),(562,6)],
  mk [31,29,30,36,2,4,5,25] 7 (replayWords [0xeada0000000,0xcba90000000080,0x700000000006050,0x0,0x0,0x43000,0x2014]) [(207,6),(226,2),(501,0),(531,0),(269,0)],
  mk [29,30,36,2,4,5,25,32] 8 (replayWords [0x418c00000,0x8628400,0x8000,0x1f00080001f0007,0x8001d00078001d0,0x71b6970006400,0x1761704b0000000,0xd65400,0xc30,0x5,0x120004c00120,0x44000f0004000,0xf00038000c0003,0x4000c00004b2810,0x10410c70,0x0,0x0,0x0,0x2400000002,0x400000,0x400000000070,0x30000000030c00,0x0,0x0,0x0,0x0,0xc00060000000000,0x0,0x0,0xc00050,0x400,0x40000000000000,0xc00020000000000,0x400010000006]) [(227,4),(346,1),(437,6),(437,11),(490,6),(502,5),(532,0),(262,5),(550,5),(551,0),(552,0),(558,0),(560,3),(558,3),(560,0),(520,6),(563,6),(564,1),(347,0),(568,0),(569,0),(570,0)],
  mk [29,113,30,36,2,4,5] 7 (replayWords [0x20013000000,0x0,0x480088004002000,0x0,0x0,0x0,0x0,0x38007800f001c00,0x0,0x0,0x0,0x30006800d001800,0x2,0x160000000,0x280722404011000,0x720004010000,0x180028004000600,0x1,0x40000000000005]) [(348,6),(518,0)],
  mk [28,29,30,210,36,2,4,5] 7 (0x450400000200000006000000810003) [(348,5),(258,2)],
  mk [28,29,30,112,2,4,5] 6 (replayWords [0xc00000,0x0,0x800400002]) [(221,0),(494,0)],
  mk [12,28,29,30,36,2,4,5] 7 (replayWords [0x800000000,0x0,0x0,0x0,0x70000006,0x500040302000,0x10004]) [(348,5),(228,0),(574,0),(33,0),(503,0)],
  mk [211,28,29,30,36,2,5] 6 0x0 [],
  mk [28,29,30,36,2,212,4,5] 7 (replayWords [0x1440,0x0,0x6000,0x810000,0x3]) [(576,0)],
  mk [28,29,30,152,2,4,5] 6 0x80001 [],
  mk [213,28,29,30,36,2,4,5] 7 (replayWords [0x8180000,0x0,0x100000,0x2003]) [(578,0)],
  mk [28,29,30,36,2,4,5] 8 (0x9800005400009400005400009000003c00008c00003c00000800000800800808800800008600001c00007de0001c00001000001000000800001000000807401007000800800806c05400003c00006800005400005400000800000800005400005400001c00006400005400005400001000001000005400005405006005805c05805405003c00000800000800003c00003c00001c00004c00003c00003c00001000001000003c00003c03804804004404003c038008000008700008000008200008200008000008400008000000000000000008d0800000001c00001001001003001c00001c01802c02802402001c01800801401000c00800800800406) [(572,2),(573,0),(349,0),(575,0),(229,0),(262,0),(577,0),(579,3),(441,0),(577,3),(579,0),(441,3),(505,0),(523,0),(533,5),(539,5),(520,0),(542,0),(548,3),(542,3),(548,0)],
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
  mk [108,29,30,36,2,4,5] 8 (0x100001004010100100007800070000780007000088000500008800050000880003000088000300002000020000100002000010020202001004010020100001380010000108001000010000100001000010000100001000010000108001000011000100000000000000120400000070000500007800070000700003000078000700007000020080201e070000701a0781e0781e0701a050000300006000050000500002000020000500005012040100401605012030000200002000030000300a040100400e0300a0100202006010040100205) [(596,2),(596,1),(353,0)],
  mk [29,218,30,36,2,4,5,27] 7 (replayWords [0x690,0x876,0x150040000000000,0x0,0x300000,0x0,0x0,0x201000000004]) [(545,5),(578,6)],
  mk [108,29,30,36,2,4,5,25] 8 (replayWords [0x1,0x8c0000000000000,0x108427c84006,0x800e001a003800c,0x16002e005800a,0x80130028004c001,0x9c0000000000000,0x864000000000000,0x8007000000,0x3,0x800000220000003,0x800000200000000,0x1c030000000c600,0x40078001000200,0xe00000004000,0x0,0x0,0x800008061380000,0xe1000000,0x0,0x0,0x1800d000000,0x30006800d001800,0x0,0x1800b000000,0x24003800a001200,0x18008000000,0x140038006000a00,0x40418801004215]) [(598,2),(236,0),(598,1),(236,5),(510,0),(510,5),(560,0),(586,5),(560,5),(586,0)],
  mk [29,30,36,2,4,5,25] 9 (0xc30c0000000000000000000c2f0002ec000bad0002ec000aea0001e7000a680001e70009a500012200092300012200086000005d0007de00005d0000c34000000000000000000007000002c00006c00002c00006800001c00006400001c00006170001000005950001000005130000400004910000400000c04000c30000000000c30c02c00001c00003c00002c00002c00001000003800002c00002c00000400003400002c00002c00000c00c00c03002c00001c00001000002800001c00001c00000400002400001c00001c00000c00c00c02001c00001000000400001800001000001000000c00c00c01401000000400000c00c00c00800400006) [(237,6),(237,4),(354,4),(439,4),(444,2),(444,1),(439,8),(444,9),(444,7),(492,4),(511,0),(524,0),(535,5),(540,5),(511,1),(524,1),(535,0),(540,0),(544,0),(549,3),(544,3),(549,0),(311,0),(571,0),(580,5),(587,5),(311,1),(571,5),(580,0),(587,0),(474,0),(594,0),(597,3),(599,3),(474,3),(594,3),(597,0),(599,0)],
  mk [154,29,30,149,2,4,5] 6 0x80001 [],
  mk [31,29,52,30,2,4,5] 6 0x0 [],
  mk [29,52,30,144,36,2,4,5] 7 (0x1850000000000008006000810000003) [(359,5),(601,6),(602,0)],
  mk [154,29,30,36,2,4,5] 7 (replayWords [0x10015000000,0x48014000000,0x0,0x4c0090011002000,0x0,0x0,0x0,0x0,0x38007800f001c00,0x0,0x0,0x0,0x30006800d001800,0x900000008001,0x160000000,0x142000000,0x48009000000,0x200038006000a00,0x100018002000205]) [(359,0),(481,0),(536,0)],
  mk [154,29,155,30,36,2,4,5] 7 (replayWords [0x300,0x0,0x0,0x0,0x2280200000000,0x6000813]) [(355,0),(359,0),(525,0)],
  mk [50,29,155,30,36,2,4] 7 (replayWords [0x100c00,0x0,0x0,0x0,0x100b00,0x0,0xa00,0xa00000900,0x900000000002900,0x800700000,0x600600006000,0x2000005200000,0x4000003000,0x2000001004]) [],
  mk [29,52,30,36,2,4,5] 8 (0x8000900009800090000080007000078000700005800058160583a0580000f00020000de80020000582e01832058300582e0180201800058000180609000070000b000090000900005800058000900009000020000980009000090280982a0982a090280900001806018260900007000058000580007000070000200007800070000702007822078220702007000018060181e07000058000580005800058000581a058160581605818058000581605816058000200c050120400e0200c02000018060180a020000188200000000000000005) [(356,6),(360,0),(603,0),(604,5),(605,5),(527,0),(538,0),(606,5),(485,0)],
  mk [29,52,30,53,36,2,4,5] 7 (replayWords [0xb0a00000b,0xa0000000000000,0x0,0x0,0x0,0x987650,0x40302001000004]) [(357,1),(601,5),(601,6)],
  mk [154,207,29,30,36,2,4,5] 7 (replayWords [0x9000000000000,0x80700000000000,0x0,0x0,0x206,0x5000,0x43214]) [(481,0),(601,0),(528,0)],
  mk [50,29,52,30,36,2,4,5] 8 (replayWords [0xc60002030001,0x280000006,0x35a01818c601a00,0x884000180000206,0x300000000000000,0x0,0x0,0x0,0x4c0090012002600,0x8012000000,0x440010012002200,0x0,0x0,0x40007800f002000,0x800f000000,0x38001000f001c00,0x0,0x34006000c001a00,0x6000c000000,0x4c580000,0x200050009001000,0x8007000000,0x140010006000a02,0x80000000000001,0x846000000000000,0x40208800004215]) [(608,0),(358,2),(361,0),(609,5),(485,0),(530,0)],
  mk [54,29,30,77,2,5] 5 0x2001 [(362,0)],
  mk [54,29,30,36,2,68] 5 0x2001 [(363,0)],
  mk [54,69,29,30,36,2,5] 6 (replayWords [0x908000000,0x7060,0x504,0x30000000,0x2104]) [(364,0),(611,0),(612,0)],
  mk [54,219,29,30,36,2,5] 6 0x0 [],
  mk [54,29,30,36,2,5] 7 (0x6000600060006000b000707070a070009000a000a00090009000a000a0009000900060006000600060006000600060006000600060006000600060006000600080006000600060007000700070007000700070007000700060006000700060005000400030002000100010001000100010001000100010004) [(613,0),(365,0),(614,0),(614,2)],
  mk [29,30,36,2,55,4,5] 8 (0x78000700007800070000202a02828028260280a0281a02800028000280a028000200802024020000680000800090000080006800018000900001800070200799f1781e073e1070000280a0281e070000700002000020000700007000008000780007000070000180007800070000295a0000000000000000294002b00022c002a800320000a400318000a4003200019c003180019c002940028000290002800029400280002980028000294002800029800280002000020000200002000020000200002000020000080001800010000080005) [(366,0),(615,0)],
  mk [50,207,29,30,36,2,4] 8 (0xc000a000e000c000c00010001000c000c00040004000c000c0005000d000c000c00070007000c000c00070007000c000a00010001000a000a00040004000a000a0005000b000a000a00070007000a000a00070007000a00010001000100010001000100010001000112010001700102000000000171000004000400040004000000000004790000044301000470040305000707070805000500070707060500012004030121210004) [(606,5),(606,0)],
  mk [50,29,30,36,2,4,5] 9 (0x30000a8000b8000a800030000800009000080000000006b5a0681c06b40037c0040000f7400400003700010000de800100006b5a0000000000000000a800080000c8000a8000a80006800068000a8000a800040000b8000a8000a800010000b8000a8000a828030300b82c0a8280800006800068000800008000040000900008000080000100009000080000801e03026090220801e0680006800068000680006800068000680006800000000000006b9a00000040000100006000040000400e03016050120400e010020300a020060100205) [(607,0),(610,0),(333,2),(607,2),(610,2),(333,0),(367,0),(492,0),(616,0),(478,3),(616,3),(478,0),(535,0),(540,0),(617,2),(535,2),(540,2),(617,0)],
  mk [161,29,30,36,2,5,44] 6 (0x100000000000000000001) [],
  mk [29,162,30,36,2,5,44] 7 (replayWords [0xee00000000000,0xc0d00000dad0000,0x0,0xb00000000,0xb00c0000000040a,0xa000000000,0x0,0xb00000000,0xb00100000000400,0x0,0xa00,0xa00000000400a00,0x0,0x900800000000,0x400700000000600,0x500000000400300,0x2100000000004]) [(368,6),(371,0),(619,5),(368,4),(371,1),(619,0)],
  mk [24,29,30,36,2,5,44] 8 (0xddd0000000000000c0e0bf00c000bfcfe0007000e0007000e0004000e0004000e0001000e0001000dddd000000000000cc00b000cc00b000300070003000700030004000300040003000100030001000ddd0000000000000b0007000c000b000b0004000c000b000b0001000c000b000b000c0c0c0c0b00070004000a0007000700010009000700070003030308070004000100060004000400030303050400010003030302010004) [(620,0),(620,2),(372,0),(620,1),(372,1),(372,4)],
  mk [220,29,30,36,2,4,5] 6 0x0 [],
  mk [29,188,30,36,2,4,5] 7 (replayWords [0x30016000000,0x0,0x5400a0013002400,0x0,0x0,0x0,0x0,0x44007800f002200,0x8000f000000,0x6,0x1c0000000,0x34006000c001600,0x0,0x0,0x280048008000e00,0x30006000000,0xc0028004000600,0x1,0x40000000000005]) [(374,0),(622,5),(445,0)],
  mk [56,29,30,36,2,4,5] 8 (0xa000098000a0000980007000070000700007000070000601806008060000c0000380002000038000c0000100002000010000602e0702c0702c0702a098000700007000098000980006000060000980009800038000a0000980009800010000a00009800098240a0280a02809824070000701c0701c0700007380070000744007000073800700007400070000701e0701c0701c0701a06000060000600006000060000600006000060000000000000062d400000038000100004800038000380c02808020100380c0100202808020060100205) [(623,0),(623,2),(375,0),(446,0),(446,2)],
  mk [20,29,30,36,2,5] 8 (0x9000900090009000c0006000e0006000c0004000d0004000c0001000b0001000a000900090009000900090009000900090009000900090009000900090009000a0009000900090006000400080006000600010007000600060003000200060004000100050004000400030002000400010003000200010004) [(376,0),(376,1),(376,4),(543,0),(543,2),(543,1)],
  mk [20,29,30,36,2,5,21] 8 (0x999000000000000099a0000000000000ae006600aa006600ae004400aa004400ae001100aa001100bbbd00000000000090a099000000999030006000c000600030004000c000400030001000c0001000b000990090009900990090009a009000990090009a009000990090009a009000b0009a00900099006000400080006000600010007000600060003000200060004000100050004000400030002000400010003000200010004) [(377,0),(377,1),(377,4)],
  mk [29,30,36,2,4,5,21] 9 (0x39ce0000000000000000633fe5f400630005f59d39e20000000000000000b700026800a6c0026800b64000dc00a60000dc00b54001c800a4c001c800630005800063000580003822039c000000039ce070000200008000020000700000800078000080007000018000680001800058000380e0381805800058000200006000058000580000800060000580005800018000600005800039c00380003a8003800039c00380003a4003800039c00380003a000380002000008000300002000020000180002800020000080001800010000080005) [(378,0),(378,1),(378,4),(447,3),(447,9),(447,7),(544,0),(544,2),(544,1),(621,3),(474,0),(624,4),(474,2),(624,1),(474,1),(624,0),(625,0),(626,0)],
  mk [161,29,30,37,2,4,5] 6 0x80001 [],
  mk [38,29,162,30,2,4,5] 6 0x0 [],
  mk [29,162,30,158,36,2,4,5] 7 (0x1850000000000008006000810000003) [(386,5),(628,6),(629,0)],
  mk [29,221,30,36,2,4,5] 6 0x400001 [(50,0)],
  mk [163,164,29,30,2,4,5] 6 0x800000000042 [(50,0),(380,0)],
  mk [161,29,30,36,2,4,5] 7 (replayWords [0x88017000000,0x0,0x60016000000,0x0,0x0,0x5400a0013002400,0xf00000044000,0x0,0x0,0x0,0x400088011002000,0x0,0x0,0x0,0x38007800f001c00,0xd00000030006,0x120000000,0x16a000000,0x48008000000,0x140038006000a00,0x100018002000205]) [(631,2),(407,0),(381,0),(386,0),(632,2),(545,0),(619,0)],
  mk [161,29,162,30,36,2,4,5] 7 (0xc280200000000000000006000813) [(379,0),(386,0)],
  mk [29,162,30,36,2,4,5] 8 (0xb0000b02c0b0360b0000a000098000a0000980000800058000d0000580000800020000c800020000b02e018300b02c0b02e01802018000b000018060b0000b4c00b0000b5800b0000b0000b0000b0000b0000b0000b0000b0000b02e0b02c0b02c0b02e0b0000b02c0b02c0b00009800058000a0000980009800020000a000098000982a0a0280a0280982a09800018060182809800058000200009000058000581a088200781c0581a058000180601818058000200c050120400e0200c02000018060180a020000188200000000000000005) [(382,6),(395,0),(630,0),(633,5),(634,5),(382,4),(395,1),(630,5),(633,0),(634,0),(408,0),(547,0),(547,5),(620,0)],
  mk [29,162,30,33,36,2,4,5] 7 (0x987650040302001000004) [(383,1),(628,5),(628,6)],
  mk [24,161,29,30,36,2,4,5] 7 (replayWords [0x380,0x0,0xc280000,0x8d13]) [(628,0),(619,0)],
  mk [24,29,162,30,36,2,4,5] 8 (replayWords [0x15a8002054009,0x240000000,0x0,0x0,0x580018015002c00,0x8000000000020a,0xd40000000000000,0x1100000054000,0x0,0x0,0x5800a8015002c00,0xa8015000000,0x55a00000,0x0,0x0,0x4c0090012002600,0x8012000000,0x440090012002200,0x0,0x38008000f001c00,0x800d000000,0x2c001000c001600,0x200050009001000,0x8007000000,0x140010006000a02,0x80000000000001,0x846000000000000,0x40208800004215]) [(636,0),(384,6),(402,0),(637,5),(636,1),(384,4),(402,1),(637,0),(620,0)],
  mk [24,29,30,36,2,4,5] 9 (0xbdee0b8300bdc00b5800a8000b5800a80003000070000d8000700003000040000d0000400003000010000c800010000bdee0000000000000000b8000bd400b8000bdc00b8000b8000b8000b8000b8000b8000b8000b8000b8000b8000b8000b80000000000000be2e000000a800070000b0000a8000a800040000b0000a8000a800010000b0000a8000a8280b02c0b02c0a82807000040000980007000070000100009000070000701a030220801e0701a040000100006000040000400e03016050120400e010020300a020060100205) [(635,0),(638,0),(478,4),(635,2),(638,2),(478,1),(409,0),(635,1),(638,1),(478,0),(409,1),(409,4),(621,0),(549,0),(549,2),(549,1)],
  mk [29,30,36,2,4,5] 10 (0xc800058000c000058000b800038000b000038000a800020000a0000200009800008000900000800088000180008000018000580003800078000580005800020000700005800058000080006800058000580001800060000580003800020000500003800038000080004800038000380001800040000380002000008000300002000020000180002800020000080001800010000080005) [(410,0),(410,1),(410,4),(479,0),(479,2),(479,1),(479,3),(479,9),(479,7),(600,0),(618,4),(600,2),(618,1),(600,1),(618,0),(627,0),(639,3),(627,3),(639,0)]
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
end PEqualNP.Outside.L_meta_32097.Certificate10782_aux

namespace PEqualNP.Outside.L_meta_32097.Certificate14788

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace ForestCore
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core

def graph : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffcfffffffefffffffaffffffeeffffffaafefefcfcfafaf0f0eeeeccccaaaa0000

theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl

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

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none

def vars (m : Nat) := (selected m).map Prod.snd

def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)

def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]

def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 1 &&& x 8) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8) ||| (x 6 &&& x 8) ||| (x 7 &&& x 8)

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
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 1 &&& x 8) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 5 &&& x 8) ||| (x 6 &&& x 8) ||| (x 7 &&& x 8)

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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951

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

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
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

def initialSegmentWidth (d : Nat) := 10*(d-1)

def denseRowWidth (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16

def denseRowStart (d raw dict : Nat) :=
  (dict % 65536)*initialSegmentWidth d + (dict/65536)*(raw+d)

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then packedAt word (i*width) width else
    let off := denseRowStart d raw dict+i*denseRowWidth d flags
    let pre := packedAt word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := packedAt word (off+flags % 16) lastBits
    let mask := packedAt word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*initialSegmentWidth d
    packedAt word (pre*initialSegmentWidth d) (initialSegmentWidth d) |||
      (last <<< initialSegmentWidth d) ||| (packedAt word (base+mask*(raw+d)) (raw+d) <<< (10*d))

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
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951

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

def g145Y : Array (Bits × Bits) := ([(0xffffffffffffffffffffffffffffffffffffdd,0xffffffffffffffffffffffffffffffffffffd1),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffe7,0x24),(0x0,0x0),(0x0,0x0),(0x3a,0xa),(0x0,0x0)].toArray)

def g145C : List ColumnInfo := []

def g145A : List (List Nat) := [[]]

def g145D3 (j : Nat) : Nat := 0x7

def g145L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g145D3)
  | _ => emptyPacking

def g145I (_ _ : Nat) : Option (Nat × Nat) := none

def g145 : Forest := ⟨145,3,fun i => g145Y[i]?.getD (0,0),g145C,g145A,g145L,g145I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g145P3_0 : block g145 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g145B3 : block g145 3 0 1=true := g145P3_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g145T : checkedTables g145 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g145 0 0 0 = true)
  · exact (rfl : block g145 1 0 0 = true)
  · exact (rfl : block g145 2 0 0 = true)
  · exact g145B3

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g145G : graphValid g145 (boundsBefore []) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low145 : Lower true (varsX 145) (graphGoal 145) 4 := lower_forest (g:=g145) (i:=0) (hints:=4) (before_sound [] baseKnown) g145G g145T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K145 := extendKnown [] 4 [(145,[]),(290,[135,84,16]),(324,[135,100,32]),(392,[116,132,48])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V145 : Known true K145 := extend_ok (m:=145) baseKnown low145 (by decide +kernel)

def g387Y : Array (Bits × Bits) := ([(0xfffffffffffffffffffffffffffffffffd3663,0xfffffffffffffffffffffffffffffffffdbea1),(0x23ccc,0x254e4),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffc773,0x24052),(0x3f99c,0x1ab08)].toArray)

def g387C : List ColumnInfo := []

def g387A : List (List Nat) := [[]]

def g387D3 (j : Nat) : Nat := 0xf

def g387L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g387D3)
  | _ => emptyPacking

def g387I (_ _ : Nat) : Option (Nat × Nat) := none

def g387 : Forest := ⟨387,3,fun i => g387Y[i]?.getD (0,0),g387C,g387A,g387L,g387I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g387P3_0 : block g387 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g387B3 : block g387 3 0 1=true := g387P3_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g387T : checkedTables g387 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g387 0 0 0 = true)
  · exact (rfl : block g387 1 0 0 = true)
  · exact (rfl : block g387 2 0 0 = true)
  · exact g387B3

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g387G : graphValid g387 (boundsBefore K145) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low387 : Lower true (varsX 387) (graphGoal 387) 4 := lower_forest (g:=g387) (i:=0) (hints:=4294967431) (before_sound K145 V145) g387G g387T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K387 := extendKnown K145 4 [(387,[]),(402,[135,16,64]),(417,[81]),(432,[81,64]),(449,[97])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V387 : Known true K387 := extend_ok (m:=387) V145 low387 (by decide +kernel)

def g358Y : Array (Bits × Bits) := ([(0x0,0x0),(0x24987acb91e,0x18a9e380e),(0xfffffffffffffffffffffffffffc0e78152e95,0xfffffffffffffffffffffffffff00698c52a11),(0x0,0x0),(0x0,0x0),(0x87007e1f652,0xf745561c610),(0xffffffffffffffffffffffffffff80783bdc25,0xfe1663ad404),(0x0,0x0),(0xfff806e43e8,0x8000001e0)].toArray)

def g358C : List ColumnInfo := [(34,0,324,0,4),(68,0,290,0,4)]

def g358A : List (List Nat) := [[],[98],[81],[33,101],[81,98],[97,33,82]]

def g358D4 (j : Nat) : Nat := 0x25f63547409bd89544426d6215110

def g358D5 (j : Nat) : Nat := 0x208048080dc812000c6302faa3a07bd4940bfa8a81fb40502fea8885f95110beaa2217c54443f280885bd4940

def g358H5 (j : Nat) : Nat := 0xc000000000000008000000000000000000005a00e17b00000

def g358D6 (j : Nat) : Nat := 0x102ff40fd40fd10

def g358H6 (j : Nat) : Nat := 0x8300000000000000000000000000000000000000000000000001000000000006500000000000000000d6200000000001624000000000000000050e00000000000e44000000000008080000000000000000000002850000000000000000000000904e5c0000000000000784000000000000000000000000000000000000000001830000228c80000004c00000

def g358D7 (j : Nat) : Nat := 0x105f

def g358H7 (j : Nat) : Nat := 0x293ce000000000000000000080000000e500000000000000cd0038401e2000000000000000000000002aa4000000000000000000003800000000000000000000000000000000000000000000000000000000000eb003d000

def g358L : Nat → Packing
  | 4 => (3,3,1,0,0,0,0,g358D4)
  | 5 => (10,2,1,0,0,5,0,g358D5)
  | 6 => (3,1,1,0,0,0,0,g358D6)
  | 7 => (1,0,1,0,0,0,0,g358D7)
  | _ => emptyPacking

def g358I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 22 0 9 2 3 g358H5
  | 6 => lookupWord 3 103 0 11 4 3 g358H6
  | 7 => lookupWord 2 79 0 9 2 3 g358H7
  | _ => fun _ => none

def g358 : Forest := ⟨358,7,fun i => g358Y[i]?.getD (0,0),g358C,g358A,g358L,g358I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P4_0 : block g358 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g358B4 : block g358 4 0 3=true := g358P4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P5_0 : block g358 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P5_1 : block g358 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g358B5 : block g358 5 0 10=true := (@block_merge g358 5 0 1 9 g358P5_0 g358P5_1)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P6_0 : block g358 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g358B6 : block g358 6 0 3=true := g358P6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P7_0 : block g358 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g358B7 : block g358 7 0 1=true := g358P7_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358T : checkedTables g358 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g358 0 0 0 = true)
  · exact (rfl : block g358 1 0 0 = true)
  · exact (rfl : block g358 2 0 0 = true)
  · exact (rfl : block g358 3 0 0 = true)
  · exact g358B4
  · exact g358B5
  · exact g358B6
  · exact g358B7

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358G : graphValid g358 (boundsBefore K387) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low358 : Lower true (varsX 358) (graphGoal 358) 8 := lower_forest (g:=g358) (i:=0) (hints:=4329571920) (before_sound K387 V387) g358G g358T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K358 := extendKnown K387 8 [(358,[]),(409,[134,118,84,50,16]),(426,[118,50]),(460,[101,117,33,49])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V358 : Known true K358 := extend_ok (m:=358) V387 low358 (by decide +kernel)

def g403Y : Array (Bits × Bits) := ([(0x403fcce9c,0x4432a4e0c),(0xffffffffffffffffffffffffffffe8c26127a3,0xffffffffffffffffffffffffffffe90a6143a1),(0x0,0x0),(0x0,0x0),(0x103c7da934,0x12ac55a110),(0x0,0x0),(0x0,0x0),(0x1f3f8651e8,0x9108000e0),(0xffffffffffffffffffffffffffffffc007be43,0x16e11ebc02)].toArray)

def g403C : List ColumnInfo := [(16,0,387,0,4),(256,2,145,0,4),(258,0,145,0,4),(1,0,402,0,4)]

def g403A : List (List Nat) := [[],[64]]

def g403D4 (j : Nat) : Nat := 0x5bd4930

def g403D5 (j : Nat) : Nat := 0x88401900ff30fd30fd20

def g403H5 (j : Nat) : Nat := 0xc000000000

def g403D6 (j : Nat) : Nat := 0x5889f

def g403H6 (j : Nat) : Nat := 0x8005500a80260000079

def g403L : Nat → Packing
  | 4 => (1,2,2,0,0,0,0,g403D4)
  | 5 => (3,1,2,0,0,4,0,g403D5)
  | 6 => (1,0,2,0,0,0,0,g403D6)
  | _ => emptyPacking

def g403I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 8 0 6 1 1 g403H5
  | 6 => lookupWord 1 12 0 7 2 1 g403H6
  | _ => fun _ => none

def g403 : Forest := ⟨403,6,fun i => g403Y[i]?.getD (0,0),g403C,g403A,g403L,g403I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403P4_0 : block g403 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g403B4 : block g403 4 0 1=true := g403P4_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403P5_0 : block g403 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g403B5 : block g403 5 0 3=true := g403P5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403P6_0 : block g403 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g403B6 : block g403 6 0 1=true := g403P6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403T : checkedTables g403 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g403 0 0 0 = true)
  · exact (rfl : block g403 1 0 0 = true)
  · exact (rfl : block g403 2 0 0 = true)
  · exact (rfl : block g403 3 0 0 = true)
  · exact g403B4
  · exact g403B5
  · exact g403B6

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g403G : graphValid g403 (boundsBefore K358) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low403 : Lower true (varsX 403) (graphGoal 403) 7 := lower_forest (g:=g403) (i:=0) (hints:=4294967428) (before_sound K358 V358) g403G g403T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K403 := extendKnown K358 7 [(403,[]),(405,[33]),(419,[135,84,16]),(433,[81]),(434,[135,65,16,80]),(453,[135,100,32,16]),(465,[97]),(468,[135,65,97,32])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V403 : Known true K403 := extend_ok (m:=403) V358 low403 (by decide +kernel)

def g435Y : Array (Bits × Bits) := ([(0xe1ac8cbc4e8be,0x41002110acb04a0ae),(0xffffffffffffffffffffc07f01e11c38659075,0xffffffffffffffffffffc04f48a00910658031),(0x0,0x0),(0x0,0x0),(0x43f19cc0448e6352,0x2965918cc0048a4250),(0xffffffffffffffffffffcf8001e70c638b1f85,0x118001470463821f04),(0x0,0x0),(0x3003fe0663a5719f08,0x100a6c622120611d00),(0x3ffc0006733e3a64e8,0x2e308010d28c1860c8)].toArray)

def g435C : List ColumnInfo := [(144,1,290,0,4),(288,2,145,0,4),(16,0,419,0,7),(32,0,403,0,7),(145,0,290,0,4),(2,0,433,0,7),(258,32,145,0,4),(1,0,434,0,7),(129,16,290,0,4)]

def g435A : List (List Nat) := [[],[81],[64],[64,81],[16,84,135],[80,16,65,135]]

def g435D5 (j : Nat) : Nat := 0x333dcf6254540

def g435D6 (j : Nat) : Nat := 0x2983881d69a09faeda8e81bbd8b5150377b12a2a05df7354520

def g435H6 (j : Nat) : Nat := 0x0

def g435D7 (j : Nat) : Nat := 0x11080069c420020c080182005ae600663042c10a1185460c00ffd4740ffd4540ff54540ffd4520ff54520ff4c520bf59654bf59740be58054bb58b50bbd8940

def g435H7 (j : Nat) : Nat := 0x10000850000260000068e040000086e386

def g435D8 (j : Nat) : Nat := 0x608034182010e5188201841006430402183598051566400a10057742fad09c5e202001fe54feaa7f153fea1fd50ffa07f503fa41fd10

def g435H8 (j : Nat) : Nat := 0x10b000430000006040000000000000000000000a8fc2800352c0c00304417cb30640000000000080a0300000180242000000007a2000001248020000680018570e719c4800

def g435D9 (j : Nat) : Nat := 0x753213f

def g435H9 (j : Nat) : Nat := 0x2550000000000000000000000000003100040000000000000000000787000003a2800000000000000000000002200068c003c2000002018000000000000030000000000000000000000000000000000000000000000000000001820000000010a003040007a489124000000003c0e25e600000000082000381000c8800000386001b4c00343001150000000000000000000000000000

def g435L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g435D5)
  | 6 => (4,3,4,0,0,5,0,g435D6)
  | 7 => (11,2,4,0,0,7,0,g435D7)
  | 8 => (9,1,4,0,0,8,0,g435D8)
  | 9 => (1,0,4,0,0,0,0,g435D9)
  | _ => emptyPacking

def g435I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 8 0 8 1 3 g435H6
  | 7 => lookupWord 1 15 0 9 2 3 g435H7
  | 8 => lookupWord 4 53 0 11 4 3 g435H8
  | 9 => lookupWord 5 111 0 11 4 3 g435H9
  | _ => fun _ => none

def g435 : Forest := ⟨435,9,fun i => g435Y[i]?.getD (0,0),g435C,g435A,g435L,g435I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P5_0 : block g435 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g435B5 : block g435 5 0 1=true := g435P5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P6_0 : block g435 6 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g435B6 : block g435 6 0 4=true := g435P6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P7_0 : block g435 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P7_3 : block g435 7 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P7_5 : block g435 7 5 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g435B7 : block g435 7 0 11=true := (@block_merge g435 7 0 3 8 g435P7_0 (@block_merge g435 7 3 2 6 g435P7_3 g435P7_5))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P8_0 : block g435 8 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g435B8 : block g435 8 0 9=true := g435P8_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435P9_0 : block g435 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g435B9 : block g435 9 0 1=true := g435P9_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435T : checkedTables g435 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g435 0 0 0 = true)
  · exact (rfl : block g435 1 0 0 = true)
  · exact (rfl : block g435 2 0 0 = true)
  · exact (rfl : block g435 3 0 0 = true)
  · exact (rfl : block g435 4 0 0 = true)
  · exact g435B5
  · exact g435B6
  · exact g435B7
  · exact g435B8
  · exact g435B9

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g435G : graphValid g435 (boundsBefore K403) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low435 : Lower true (varsX 435) (graphGoal 435) 10 := lower_forest (g:=g435) (i:=0) (hints:=4296015956) (before_sound K403 V403) g435G g435T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def K435 := extendKnown K403 10 [(435,[]),(469,[101,33])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V435 : Known true K435 := extend_ok (m:=435) V403 low435 (by decide +kernel)

def g443Y : Array (Bits × Bits) := ([(0x1804022038211e1f043ff9a2061cb5470ff0,0x5022830011207442452aab654854607e0),(0x5c3800c211e1ffe304b9550f1e40ed0e,0x8004420004218611ae300e5570a1e40a906),(0x0,0x0),(0x20186fc44f03e001f83c034297cc909de1a4,0x201c6664eb031155f8be060a17cc900de120),(0xffe06070078ffc01fe003ffd014908507be031,0x247279168fe481f8909bad0109085039e010),(0x307f8007f00001ffffc0063a0064e18dd06a,0x313c8005fa08419ee510061a0044e18d5028),(0x0,0x0),(0xffff800007fffffe00000008446fd8eca43a0f,0xffd980000100086c000200005440002a80180f),(0x3ffffff80000000000000f87b1238b3a17d0,0x643199a04b080000000c900a831003206d0)].toArray)

def g443C : List ColumnInfo := [(152,1,290,0,4),(296,2,145,0,4),(34,0,409,0,8),(17,0,426,0,8),(137,16,290,0,4),(266,32,145,0,4),(8,0,435,0,10),(51,0,392,0,4),(24,0,419,0,7),(40,0,403,0,7)]

def g443A : List (List Nat) := [[],[81],[64],[64,81],[16,84,135],[80,16,65,135]]

def g443D5 (j : Nat) : Nat := 0x30c7d2726c0b01b92cba256916121b7354550

def g443D6 (j : Nat) : Nat := 0x1f182070c190f3cf3cf3cf3cf3cf3cf3cf3cf3d53cf3cf3c0cd3e1793603725971cf93e0580dc965c73e4d816037259719f94e0d715c165c6be53825c57059746f646487559560d1b591921d56558256ea91d78259560a6be9191e0976d431af94e09815db50cad6516121971d428eda2219765c75087be8998a1f61d421efa265e8654750cad6516121951d428eda22197654750967e9191d97735421efa266376d8550a73e8985dcf615432b5945848654550a67e9186dcd515429cfa261b7354550a6769086dcd515429cda221b7354550e3558486dcd515423eba266361d4150

def g443H6 (j : Nat) : Nat := 0xb061000000

def g443D7 (j : Nat) : Nat := (if j<1 then 0x40004200078f482030c0021973864561915b8032194a02d28190c864160b6ab28402b61880402b100ac560b158ac56b80c864320b3d9ec562b158ac162b0c82c321905ac4162b0ca9816190582c3219058ac162b4d82c560b15864162b058ac162b4d82cf6940c864168205a241682411ec320b2f1ecf67b3d9ec160b3a194bc5326130982b158ac160b10080320b158ac40200c90432320c8ac4019058641c0b05801b6f9261f65997cdf0dc2ee4b2f9be1665dc965f37baccbb92cbb6f85e0372596edf2ac06e4b2edbe1580dc965be7c9b01b92cb5ed96e03725973df03c06e4b2e7be0580dc965cf6c0b01b92cbb5f65e0d705976decbc12e0b2ef3e0f725c165cefc1ee2b82cb9ef82dc5705973bf06b8ae0b2e7be09715c165cf7c970eb28cb9ef87e09651973df2fc12ca32f5be4b8759465eb7cbf04b28cbd6f87e09651973df30b2ae432f7ae49655c065ee7c92cab9ec157e981d5655838fec83aacab071f5907559560eb7baf04b2ac1d6c75e09655833d92fc12cab073b25f8259560f37caf04b2ac1e6f85e0965582d7f28c0acab05bbe498159560cf7c930bb8ac19ed9221d51583cdf24b2aa2b067be49879db509dfca3033b6a19ef9261676d433df2fc12eda867b9db825db50cf7caf04bb6a19ed95e0976d433df23c12eda867b647825db50cf7c1702bb6a15bf9460576d42bdf24c0aeda867be09815db50af7c930fb2ea19ef9261f65d42bdf24bb6cba84efe5181d9750cf7c3f04b2ea19ef97e0965d4277b28432e3a84fb648865c750d7ab090cb8ea18ff865d971d431f90cbb2e3a857be49765c7508fecc50fb0ea15ef9261f61d433df24c3ec3a847fe5d85d87509f7c930bb0ea11fd97a1951d4277b28432a3a84fb6488654750d7ab090ca8ea18ff865d951d431f90cbb2a3a857be4976547509dfca303b2aa15dd91d9773543abecab2ee6a8773e4965dcd50aefc8acbb9aa15df9361f61542bdf24c3ec2a847f66376d85508ffcc2edb0aa15df935db61542bdf24bb6c2a84fbe4985d8550ceec2ee7b0aa19df85dcd61543b3f09b9ac2a84efe5186545509f7c930ca8aa13bd94219515427db24432a2a86bd5848654550cefc36e6a8aa19de86dcd515433bb0db9aa2a867721b7354550eaeb2ee6a8aa17bb94585605437d724c36a0a84fe66361d4150bddca2c3a82a15ed92a1d654433dd0fc12ca8867b21f8259510cf74bf04b2a219ec97e09654426df24c3ecb32e9be1b85dc965ae7c9b01b92cb9cf83dc9705972df25c3aca32e5be1f82594658f7cc2cab90cb96f9859572196bd724b2ae032f3ae49655c065ae7c92cab9ec1ccf9259573d82adb243aacab047be4985dc5608f6c910ea8ac11ef9261e76d423df24c2ceda847be4987d97508f7c930fb0ea15cf925977354333f09b9ac2a84fae4986d4150 else 0xd604101b2000ac8142b60414042720416c82040008c8100040b481e3056410407000d481c3010b0c1000508140004301)

def g443H7 (j : Nat) : Nat := 0xa06000000000f14238000a97f08904000000d10000817000000b37000000601702713918000911d19f00f0f000315000000000316e07000000e0d000000580000000000000c0980c00000000069500040b50e00000000000070500000021200080a803000810750

def g443D8 (j : Nat) : Nat := (if j<1 then 0x54d8f100022a6098c08014284020040b8c08010205038c00b8c0010f1800b1d2000446dc8006db900c6226c61408014001ed8e90b8c2000d9000bb0401484a4002860026c1420002284000430214006140800db00e58c4e400202002000420000008157f362f7df7bd7a278776c74a0007215652027066e46a162f62f6a16d06b50140146a101462f62f6a168d66b65753d63c62f61460e5ec5d15bd5a25875875650ec54a53d5294d84ec50e4d84ec1364d84bd49b47945743c42140d0000000000af0000003f93e53c33a137f3563340283192f00002c709400000000029e27c00025a05e2312162020000001e005e0001c51a305e05e17a1511361221221001000ec0d80000000af00002809400009400000001400000001400000007900005e02802800003c014014000000028028014000000fef85dc965fee65dc965fef80dc965fed80dc965f7f65dc165fef72dc165dff71dc165f7f655c165fef725c165dff715c165dfd715c165dff8759465fef8259465fef8259760fef8259560eff8159560efd8159560bfd819db50dfe765db50fef825db50bff815db50dff815db50dfd815db50dfd87d9750dfd76d9750bfd81d9750dff8759750f7f6559750fef8259750bff8159750bff865c750bfc865c750dfd765c750dfe87d8750dfd87d8750bfd85d8750bff8654750bfe8654750bfc8654750dfd7654750f7d6554750bfd81d9550f7f6559550fef8259550bff8159550dfe87d8550dfd87d8550dff76d8550dfd76d8550bfd85d8550fdf73d8550ff980d8550bff8558550fdf7358550bff8654550bfe8654550bfd8654550bfc8654550f7d6554550ffb6158150ff96158150ffb61d4150ff961d4150dfe8759510dfc8759510fef8259510def825da65b7d87d9665e7f7599565f6f85dc965eee65dc965def85dc965dee65dc965def80dc965ded80dc965def72dc165bdf835c165bef825c165def725c1659ff8759465bef8259465d7f8759465f6f8259465ded655c865df9655c065bef8259760eef8259760ddd655cf60d7f7559560d7c7559560bef8259560e7f8559560eef82595609fd85dc5609fc8754560e7d65545609fd879db509fd859db50bef825db50def825db509fd87d97509ff8759750bef82597509fd87d8750bef8259550ddf65dcd50ddd65dcd50ddf73d8550ddf7358550ddf7354550bf986d41509fd861d510bef82595109ef825da659ed829d6659df835c26597f8759465d6e655c865d6d655c865de9729c065df2719c065dda735c065dd9735c065de9725c065df2715c065df1715c065cfb655c065cf9655c065cdf655cf60cdd655cf609dd831d5609ed821d5609f5811d5609ef825db509dd831db509ed821db509f5811db509dd839d9509df835d9509ef825d9509f887581509bd849d5109df835d510 else 0x8cc00610033ac253001130005908100d30c05308187a6043a6000b211300c78808b8d9010c2b2c60046404200059060590548084100920021202152000430008700043002010e004001c086480058c0070f18008184c600088129280e90349405491810d1d208004018c224031878c9040026324002081e1b2022436414386019070d904580845800458200022160a0400815981002040acc08014281a6004a7c8006169810800)

def g443H8 (j : Nat) : Nat := (if j<1 then 0x3230d121000000000000000000000000001858000000000000000000000000000000000000000000000185200000000000000000000000000000000000000000000000000000000909de040000000000000000000000000000000000000000000000000000000012198000000000000000000000000000000000000000000000000000000000000000000000000000000000022ba00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050fc0000000000185f00000000000000018068000000000000000000205c00000000000000000000000000a102000341f000000000000000100a000000000000000000000000000000000000000000000000000002b10000000000000000000000000000000000000000000000000000000000000000a2a000000000000000000000000000000000000000000000000000000000000081a400000000001403c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a00800000000000000000000007a0d000000000000000000000000aa000000001435c09586e000000000000000000145d8000000000000000000597b0000000181d8000000000000000000000000000000d4c000000000000000000000000000000f0e600000000000000000000000000000000000002085b06b616c000000000000000000000000000003c1e8000000000000000000a0700000000000000000000000000040e80000000000020d800000000000f0c80003425000030bc00000000000000000000006263000000000003d3c0000000003b0000000080900000000302e0000000000000000000000283f00000000000583a0000000000000000000000000000000000000301820208837e17c000000000000000000000000000000000682600000000000000000000000000000000000000000306d0000402c000000000d400000000000000000000000000000000000006177000000000000000000000000000000000000000000000000000000000000000000000000000b4d800000000000305800000007867f818000202ee56c30f000000000000000000000000000000000000000000b06c0000000000000000000037800000000000000000000000000000000060ea00000000000400a0000000000000000000000000000000000000000060f8000000000000000000000000000000000000000008104000083b80000000000000000000000000000000000000d18800000000000000000078610000611c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005444004100080018260 else (if j<2 then 0x7839000000000000000000000012b00000000000000000000000000000000000000000000000000d0a600024208000f2a6000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002af8e06c00000000000000000000000000000000000000000b130000000000000000000000000000000000000001000000000000020fe00000000000000000000000000000000000000000000000000000000000111d4000000000000000000581d00000000000000000000000000000000000000000484bf04600000000000000000000000000f0a8c1440000000000000000000000000170f000000000000000000000000000000000000000000000000000006ac20000000000000000000000681600000000000000000000000000000000000000000000000000000000000000000000000000000000000000784d0000000000000000000000000000000000000000029330000000000000000000000000000000000000000050070000000000000140000000000000000000000282b800000000000000000000000000000603400000001e138000000000000000000000000000000000000000000000000000000030228000000000000000000000000000004c2600000003c10800000000000000000098e8000140895270000000000000000000000000000000000000000000000000a1ec0000000000160cf43e8000005000000000000000094980000000000000000000000000000000000003000000014248000000000000000000000000000000000000000034310000000000000000000000000000000000000041480000000000000000000000000000000000000000000000000000000000000000000000151800000000c05e000000040630000000000000000000000000000006018000000000000000000261600000000000000000000000000000000000001803800000000001620d400cc28000000000000000000000000000000000120f000000000000000000000000000000389b4282000040252960000000000000000000000000000000000000000000000000610894a00000000000054300000000000000000000000000000000000000000000000000000000000000000000000084e0000082700000000000000000000000000000000000000000000010e00000016800000000000000000000000000000000000000001c12800000000000000000000000000000000000013070000143d0000000000000000000a0ac0000000000000000000 else 0x791f80e400000000000000000038ba00000001f0780000000000000000000000000000000000000e0ca00000003044005400000000000f0aa000000000000001e0c80000000d0d60000000000000000000000000010800000000000000000000000000000000000000000000000000000000000000000c0f000000000000000000000000000000000000000000000000000000000000000072aa65114230000000000000000000000000000000000c0860120000000060b2000000000000000000000000000001c1580000000000164b4000000062440000000785a000000000000000000000000003829f0c00000000000000000000811000000016a000006d3d0000000000000000000c0180000000c8f80000000000000000000000000000010130000000000000000000000000000000000000002ea00000000000000000000000000000000000000000000000000000000000000004188000000000000000000000000000000000000190340000000000000000000000000000000000000000000000000000000000000000000000000000000000d0e2000000000000000000000000000000000000000000000000340d00000000c0dc00000000000000000000000000000000000000000000000000000000000369f80000000000000000000000000000000000000000000000000001a4b8000000000000000000104f000000000000000b08400000000000000000000000000000000000000000f0f200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000601100540000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a0d00000000281f00000000000000000000000000000000000000000000000000000000000000000000000681c00000000000000000000000000000000014173c3f000000000000000446c000190dc0000000000000000000000000000000000000d10c0000000000000000000000000000000000000000000014062c0c8000000000000003800000000000000000000000000003d37000000000000000000000000000000000000000000000000021e98098000000000000000000000000000000000000000000000000284a0000000000000000000000000000000000000000000000000000000032fa000000000000000000000068500000000000000000000000000000000000000000000000000000369280000000000000000000000000000000000000000000000000000000000000000000))

def g443D9 (j : Nat) : Nat := 0x5c81004141c930055850444f20079a38800458c4001105ca3040141c800c58c1c801414800f60018d21411d20048d2004104d810128c6144001da34878c04841070010f61440011460c2001140042084001112c800c5053c801450400c40010c60010c40400f60c00440c50401231410041050401058c10c6142043c801c48c10048f20030c1003141c801008c10c5040cb68c62020011128c10c5001c841451012320060c4c801011021430720050f20030070820010c30010c30401c40810035b3c831440011361320047c828b1e618bd1712d335ab04151f21fead47faa352ea153b2674ce9491d22b43e834fd9f23c6234eb81e38a6e4289ad342618ca9862ee5a08715921c5343913524c4687990e1fe3cc6f0cf1862c42289c108234420720cc1742884506c0a80f00f01e03c003ffb2ccbff5c665ffccab2fff70597feb82cbff59465ffacbb07ff65583feb2ac1ffdc560ffaa2b07fe76d43febb6a1ffd9750ffacba87fd71d43ffb0ea1ff54750ffecaa87fd65543ffb0aa1ff58550ffaa2a87fd65442febb4cb7f9d665efecb32dfd71996feb84cbbf99565fdee4b2dff70596ff3a8cbdf99465efaca32fed72197fd380cb7f5c065ff2e032dfe75d82febaec1bfd9760dfacbb07dd73d82feb8ec17fdd560bf8eab06ff655837eb2ac17fdc560ff6c0b05ff76d42ff3b6a17f5db50bf8eda85fd71d42ffbb2a17f9d950bfaeca85fc76543efb9aa17fdc550ff2c0a87fb50542ffbaa217f9d510bfaea885fc75443fcb02217bdc965bdae432df970196eeb9ec177dcd50

def g443H9 (j : Nat) : Nat := (if j<1 then 0x300012544000000000012050000000000000002ab6b079984c0003540000058c40001a328000c47384440000000c8a6a1b800000000000000000000000000000000000000000000000000000ab40000000000022e20000000000000000000000717f00000003aab000000000000000258a00000000000000000003064000000020e8000214300000000000000000000000000000000000000000000000000000e100029800000006190000000090af221000000000001f5a80000000a4c600000006d8100000000000528b00000001eab80000000000008b3011d0c60000000443c0000000182480000001001681000000000000000b80000000000000000000000000000000000000000240b5006000095ac0000000cae4a5e00000000a8b20003eaf0000d0b342000000000908e61400006532b2fc000004680008afe000122200001b0e0000000000080540000000607c00000003437e045a01e00000000000a0b00000c03948c0000206ac38800028b600000000000601bf4d0000387f0000000000000810001c0b000010230001b2280000000648a000000000000001254800000000001f19b006000000000000a468000000081e16398000000000000000000000141d800000000000000111900000000000280480000000000000000000000000262c000000000000000686600000000000000000000000000000000000000c0c0000000000000000000000000000000000000000000006d4300840002020c95f9311e08621c395e00019238000000000000000000000068c62078000000000000000000000000000000000745d603800025408000643c000008f0000000000000000000000000000000000000000000000000b87200000000000000000000000000c2d20002c91000000000000000000072cb421c4856954c0aa88a101a987d8aa8e0cc2b480000000000000000000001d5934250000c0b60002e280000000000018050000000000000002086000000014140000f42a0002a8b88320000d1b3c18800078bc4040000187e00015501c2415120000d6144358000000000000004c870001c038000000000000000000481900000000e0b800000002074000000000000000000000000000000813e85a000091a000065446886e0e3004000000000000844000000000000000207000000000e2d00001916000184744520000e1e88a9f428000031580005471204971d7c3600000000000000000000001223000071620000000000000000000000000051790001c0f40000000000000000000000c82400000006580000000000003075709c859c00044320000a85d00f9a8c48fe618000030440001e0b400000000001515ca2480000000000000000002201024030012412020080101002a10110101100201b0000001234330302300524 else 0x7e9514000000000000000000000000000000000000000000000000083c0000943ea1a00000001c5b80007a38000000000000000000000000000000000000000000000184400000000000000000000006555000088080000000000000000000000000000026c4a03e000000001218000a2acf40a98f000000000001a9319235ac0000000000000acc558b42680000000000042e0000000040eceb2b85182fa4934000614d000075f800000006ae600000000000025e0000000000060c4f20741b58520000612ec21b53300000000620000000000000405ec85e81e0000000000060040001c3980000001a1a40000000203600000000000000000000000272000000000000000842600000000000000000006010000000021c80002460000000024128000c0ef744c0000000000000000000000aa2000000003586000101500000000000000000000000000000000000000d8d511b411a00000000000043d8000000000000000000d09800000000000a224000000000000000a0b800000000000000000001508b1652240000000000086168acd013000000000000000b20dc1a8000000030240002a390000d045a0ac0000000000000000006d38000051ac000000050536902a2a0000000040c0000000000000001cab8464582600000000000000000000002410000000000000000000000000000000d44c000000000000000000029cea440000000000000000000422c0000000000000000000000000000000000000004c00000002d68d106363000000000000000082b000000000000000000000000003e942815c0ba0001e403558000000000004c1800000003c338000000175c44c26834000000032ba800000000000000000000000000c230a3a000000000000000000000000000000000080040000882000094e80000000769a0003544800000000000a240000588ba214eb18000000000038450000baba0000000000070be60e4000000000000000000106d909f65d4000285e12cc01a00000000000000024308000000100000000000000145ea0448000000000016237c51e90c21940000000000000000000000307400000000000324200000000000000000000000000f06e0003e3f000000000000000000000000000000000000000003017f469000000000000000000050cc0000000e8740003e2a800000006013e23800000000000000195c0000000000058)

def g443D10 (j : Nat) : Nat := 0x24ed200b39583288961c80120b6900611ad200c4b486010969006282c21845d9c49672583e1f00ff997fd65ff197ff60ff583ff50ff543fd10

def g443H10 (j : Nat) : Nat := 0x3ec60000000832000000000000002a33a03a81320aca2a988000000016b7da948c0090800000000000000000000000084c8000927400000000000000849000000000000000000000d2d4000000000000000000000000501e41c7a90000000183d60b4000000000000000000001e2700000000000c850000000e518000cb0400000000000000000b891427910c0006824ab5d057438c2e800000000000000000d06c000f0a80000000000e4b7c3c00000000000000000002100039250000000000340f0000000000000010800000002030000000000000000003c87000000000000005b0800000000000000000e0a0000000000094d80000003c3a00000000001e0feae000098940000000000450c000e05c0000000000000000000000000000000d43f63b0002c1922d0000d0cc0000000000b08c0000000000000000000000000003e13f0dc0000000000203492422e0000f864000f0580000002810000000000000000000000b050000000000018b0000a4efc180000000f50504748d81b2a2b800000002c368f000000000000000000000000000000000000000ea40492300800000000000000000990c000d030000912140a48a4000886b22f7002c40000000000000004047916000368f8918000000282f000000000000000002aaa3acf637000383f00008b3000043b844c000d823404000000030e5c260000000010800040480000000000307c287000000000000004a640000000000f48c00000000000000000000000000000000000000000000000016930000000f0040000003809000000070c8000000000000000000002a35000000094a800051180000000000f88c00000200000003c03000000000000008aec0000000c45da680000000000000000010d9d02e11391f00000000000c35000000000000000001088000000000000000000cbf00000002a8c000000040600000000000000d9140000000000000000068a000000000000000000c01400078080001af00000000d450000000000000000000000000000a0d201d0000000000000060c4000000382c94640000000000000000000000005818000602c00000000004840000aa08000c09629f90f8000000000000000000002c2e000000000000000000000f81400000000002105424187c000e2e4e0700012380000000dada24100000000000000f0a4000000000000000000000c1e0001c980002a47a232022000000000000000000000a0686a03b17cb20a2014c8400061011248049000000

def g443D11 (j : Nat) : Nat := 0xc641ff

def g443H11 (j : Nat) : Nat := 0xa1fc0fb1abc46d0000000006700000da7420000000000001ea001450000000000000003900000000a1000000000000000000b500000000000000000000000000000014600000b480000201000000002300121888000000000253000002200066143b002

def g443L : Nat → Packing
  | 5 => (2,6,4,0,0,0,0,g443D5)
  | 6 => (26,5,4,0,0,6,0,g443D6)
  | 7 => (135,4,4,0,0,9,0,g443D7)
  | 8 => (143,3,4,0,0,12,0,g443D8)
  | 9 => (74,2,4,0,0,11,0,g443D9)
  | 10 => (8,1,4,0,0,8,0,g443D10)
  | 11 => (1,0,4,0,0,0,0,g443D11)
  | _ => emptyPacking

def g443I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 9 0 8 1 3 g443H6
  | 7 => lookupWord 6 69 4 12 5 3 g443H7
  | 8 => lookupWord 40 1615 2 15 8 3 g443H8
  | 9 => lookupWord 66 997 4 15 8 3 g443H9
  | 10 => lookupWord 34 523 3 14 7 3 g443H10
  | 11 => lookupWord 4 79 4 10 3 3 g443H11
  | _ => fun _ => none

def g443 : Forest := ⟨443,11,fun i => g443Y[i]?.getD (0,0),g443C,g443A,g443L,g443I⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P5_0 : block g443 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g443B5 : block g443 5 0 2=true := g443P5_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P6_0 : block g443 6 0 26=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g443B6 : block g443 6 0 26=true := g443P6_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P7_0 : block g443 7 0 22=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P7_22 : block g443 7 22 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P7_70 : block g443 7 70 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P7_118 : block g443 7 118 17=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g443B7 : block g443 7 0 135=true := (@block_merge g443 7 0 70 65 (@block_merge g443 7 0 22 48 g443P7_0 g443P7_22) (@block_merge g443 7 70 48 17 g443P7_70 g443P7_118))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P8_0 : block g443 8 0 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P8_30 : block g443 8 30 47=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P8_77 : block g443 8 77 48=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P8_125 : block g443 8 125 18=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g443B8 : block g443 8 0 143=true := (@block_merge g443 8 0 77 66 (@block_merge g443 8 0 30 47 g443P8_0 g443P8_30) (@block_merge g443 8 77 48 18 g443P8_77 g443P8_125))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P9_0 : block g443 9 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P9_5 : block g443 9 5 45=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P9_50 : block g443 9 50 24=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g443B9 : block g443 9 0 74=true := (@block_merge g443 9 0 5 69 g443P9_0 (@block_merge g443 9 5 45 24 g443P9_5 g443P9_50))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P10_0 : block g443 10 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g443B10 : block g443 10 0 8=true := g443P10_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443P11_0 : block g443 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

theorem g443B11 : block g443 11 0 1=true := g443P11_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443T : checkedTables g443 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g443 0 0 0 = true)
  · exact (rfl : block g443 1 0 0 = true)
  · exact (rfl : block g443 2 0 0 = true)
  · exact (rfl : block g443 3 0 0 = true)
  · exact (rfl : block g443 4 0 0 = true)
  · exact g443B5
  · exact g443B6
  · exact g443B7
  · exact g443B8
  · exact g443B9
  · exact g443B10
  · exact g443B11

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g443G : graphValid g443 (boundsBefore K435) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low443 : Lower true (varsX 443) (graphGoal 443) 12 := lower_forest (g:=g443) (i:=0) (hints:=4296044628) (before_sound K435 V435) g443G g443T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end ForestCore
end PEqualNP.Outside.L_meta_32097.Certificate14788

namespace PEqualNP.Outside.L_meta_32097

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

private theorem signed_av {s : Set F} (point : PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Row → X)
    {bank : List (PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Wire PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Row)}
    (hs : ∀ v ∈ s, PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Available true bank (fun r => v (point r)))
    {f : F} (h : Av s f) :
    PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Available true bank (fun r => f (point r)) := by
  rcases h with ⟨b,rfl⟩ | ⟨a,ha,rfl | rfl⟩
  · exact Or.inr (Or.inl ⟨b,rfl⟩)
  · exact hs _ ha
  · exact PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.avail_inv rfl (hs _ ha)

private theorem signed_prog {s : Set F} {f : F} {k : Nat} (p : Prog s f k)
    (point : PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Row → X) (roots : List (PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Wire PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Row)) :
    ∀ m bank, PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Reach true roots m bank →
      (∀ v ∈ s, PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Available true bank (fun r => v (point r))) →
      ∃ pool, PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Reach true roots (m+k) pool ∧
        PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Available true pool (fun r => f (point r)) := by
  induction p with
  | done h => intro m bank hm hs; exact ⟨bank,hm,signed_av point hs h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro m bank hm hs
    let a' := fun r => a (point r)
    let b' := fun r => b (point r)
    let w := PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.combine (!tag) a' b'
    have hl : (fun r => comb tag a b (point r)) = w := by
      cases tag <;> rfl
    have hr : PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Reach true roots (m+1) (w :: bank) :=
      PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Reach.two (!tag) hm (signed_av point hs ha) (signed_av point hs hb)
    obtain ⟨pool,hp,hv⟩ := ih (m+1) (w :: bank) hr (by
      intro v h
      rcases Set.mem_insert_iff.mp h with rfl | h
      · rw [hl]
        exact Or.inl (List.mem_cons_self)
      · exact PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.available_cons w (hs _ h))
    exact ⟨pool,by simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hp,hv⟩

private theorem from_signed_block_floor {f : F} {L : Nat}
    {roots : List PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Sig} {targetWord : PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Sig}
    (cols : Fin 8 → PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Sig)
    (hcols : ∀ i, cols i ∈ roots ∨ cols i = PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.zero)
    (he : ∀ r : PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Row, PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.bit r targetWord =
      f (fun i => PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.bit r (cols i)))
    (h : PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Lower true roots targetWord L) : Low L f := by
  intro k p
  let point := fun r i => PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.bit r (cols i)
  obtain ⟨pool,hp,hv⟩ := signed_prog p point (roots.map PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.observe) 0
    (roots.map PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.observe) PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.Reach.start (by
      rintro _ ⟨i,rfl⟩
      rcases hcols i with hmem | hz
      · exact Or.inl (List.mem_map.mpr ⟨cols i,hmem,rfl⟩)
      · apply Or.inr; apply Or.inl
        exact ⟨false,by funext r; change PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.bit r (cols i) = false
                        rw [hz]; simp [PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.bit,PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.zero]⟩)
  have eq : PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core.observe targetWord = fun r => f (point r) := funext he
  rw [← eq] at hv
  exact h k pool (by simpa using hp) hv

namespace BlockCertificate
open PEqualNP.Outside.L_meta_32097.Certificate10782_aux PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Core PEqualNP.Outside.L_meta_32097.Certificate10782_aux.GateForest12127 PEqualNP.Outside.L_meta_32097.Certificate10782_aux.Compact10782

open PEqualNP.Outside.L_meta_32097.Certificate14788

def truthWord0 : Sig := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def truthWord1 : Sig := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def truthWord2 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def truthWord3 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def truthWord4 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def truthWord5 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def truthWord6 : Sig := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def truthWord7 : Sig := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000
def truthWord8 : Sig := 0xfffffffffffffffffffffffffffefffafffffffeffffffeefefcfaf0eeccaa00fffffffffffffffffffffffffffefffafffffffeffffffeefefcfaf0eeccaa00
def truthWord9 : Sig := 0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333
def truthWord10 : Sig := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def truthWord11 : Sig := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def truthWord12 : Sig := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def truthWord13 : Sig := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def truthWord14 : Sig := 0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555
def truthWord15 : Sig := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff
def truthWord16 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def truthWord17 : Sig := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff
def truthWord18 : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000

def raw : List Sig := [truthWord0, truthWord1, truthWord2, truthWord3, truthWord4, truthWord5, truthWord6, truthWord7]

def goal : Sig := truthWord8

def vars0 : List Sig := [truthWord0, truthWord2, truthWord3, truthWord4, truthWord5, truthWord6, truthWord7]
def word0 : Sig := 0xfffffffffffffffffffffffffffafffafffffffaffffffaafaf0faf0aa00aa00fffffffffffffffffffffffffffafffafffffffaffffffaafaf0faf0aa00aa00
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem floor0 : Lower true vars0 word0 12 := by
  exact lift_ok (ms := [Bound10782.swapNext 5, Bound10782.swapNext 4, Bound10782.swapNext 3, Bound10782.swapNext 2, Bound10782.swapNext 1, Bound10782.swapNext 3, Bound10782.swapNext 2, Bound10782.swapNext 6, Bound10782.swapNext 5, Bound10782.swapNext 4, Bound10782.swapNext 5, Bound10782.forceLow 4]) (xs := [(truthWord4, 64, 80)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) ATable10782.lowerA
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem sl0 : Slice true raw goal truthWord9 12 := by
  exact slice_correct (ms := [Bound10782.forceLow 1]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) floor0
def vars1 : List Sig := [truthWord0, truthWord1, truthWord3, truthWord4, truthWord5, truthWord6, truthWord7]
def word1 : Sig := 0xffffffffffffffffffffffffffeeffaaffffffeeffffffeeeeccaa00eeccaa00ffffffffffffffffffffffffffeeffaaffffffeeffffffeeeeccaa00eeccaa00
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem floor1 : Lower true vars1 word1 12 := by
  exact lift_ok (ms := [Bound10782.swapNext 2, Bound10782.swapNext 1, Bound10782.swapNext 5, Bound10782.swapNext 4, Bound10782.swapNext 3, Bound10782.swapNext 2, Bound10782.swapNext 4, Bound10782.swapNext 6, Bound10782.swapNext 5, Bound10782.swapNext 6, Bound10782.forceLow 5]) (xs := [(truthWord5, 128, 160)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) ATable10782.lowerA
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem sl1 : Slice true raw goal truthWord10 12 := by
  exact slice_correct (ms := [Bound10782.forceLow 2]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) floor1
def vars2 : List Sig := [truthWord0, truthWord1, truthWord2, truthWord4, truthWord5, truthWord6, truthWord7]
def word2 : Sig := 0xfffffffffffffffffffffffffefefafafffffefeffffeeeefcfcf0f0cccc0000fffffffffffffffffffffffffefefafafffffefeffffeeeefcfcf0f0cccc0000
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem floor2 : Lower true vars2 word2 12 := by
  exact lower_map (ms := [Bound10782.swapNext 2, Bound10782.swapNext 1, Bound10782.swapNext 0, Bound10782.swapNext 6, Bound10782.swapNext 7]) (by decide +kernel) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) ForestCore.low443
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem sl2 : Slice true raw goal truthWord11 12 := by
  exact slice_correct (ms := [Bound10782.forceLow 3]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) floor2
def vars3 : List Sig := [truthWord0, truthWord1, truthWord2, truthWord3, truthWord5, truthWord6, truthWord7]
def word3 : Sig := 0xfffffffffffffffffffffffffffafffafffefffeffeeffeefaf0faf0aa00aa00fffffffffffffffffffffffffffafffafffefffeffeeffeefaf0faf0aa00aa00
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem floor3 : Lower true vars3 word3 12 := by
  exact lift_ok (ms := [Bound10782.swapNext 5, Bound10782.swapNext 4, Bound10782.swapNext 3, Bound10782.swapNext 2, Bound10782.swapNext 1, Bound10782.swapNext 3, Bound10782.swapNext 2, Bound10782.swapNext 6, Bound10782.swapNext 5, Bound10782.swapNext 4, Bound10782.swapNext 5, Bound10782.forceLow 1]) (xs := [(truthWord1, 64, 66)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) ATable10782.lowerA
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem sl3 : Slice true raw goal truthWord12 12 := by
  exact slice_correct (ms := [Bound10782.forceLow 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) floor3
def vars4 : List Sig := [truthWord0, truthWord1, truthWord2, truthWord3, truthWord4, truthWord6, truthWord7]
def word4 : Sig := 0xfffffffffffffffffffefffafffefffaffffffeeffffffeeeeccaa00eeccaa00fffffffffffffffffffefffafffefffaffffffeeffffffeeeeccaa00eeccaa00
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem floor4 : Lower true vars4 word4 12 := by
  exact lift_ok (ms := [Bound10782.swapNext 2, Bound10782.swapNext 1, Bound10782.swapNext 5, Bound10782.swapNext 4, Bound10782.swapNext 3, Bound10782.swapNext 2, Bound10782.swapNext 4, Bound10782.swapNext 6, Bound10782.swapNext 5, Bound10782.swapNext 6, Bound10782.forceLow 2]) (xs := [(truthWord2, 128, 132)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) ATable10782.lowerA
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem sl4 : Slice true raw goal truthWord13 12 := by
  exact slice_correct (ms := [Bound10782.forceLow 5]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) floor4
def vars5 : List Sig := [truthWord1, truthWord2, truthWord3, truthWord4, truthWord5, truthWord6, truthWord7]
def word5 : Sig := 0xfffffffffffffffffffffffffffcfff0fffffffcffffffccfcfcf0f0cccc0000fffffffffffffffffffffffffffcfff0fffffffcffffffccfcfcf0f0cccc0000
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem floor5 : Lower true vars5 word5 12 := by
  exact lower_map (ms := [Bound10782.swapNext 1, Bound10782.swapNext 0, Bound10782.swapNext 6, Bound10782.swapNext 7]) (by decide +kernel) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) ForestCore.low443
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem sl5 : Slice true raw goal truthWord14 12 := by
  exact slice_correct (ms := [Bound10782.forceLow 0]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) floor5
def vars6 : List Sig := [truthWord0, truthWord1, truthWord2, truthWord3, truthWord4, truthWord5, truthWord7]
def word6 : Sig := 0xfffffffffffefffafffffffffffefffafefcfaf0eeccaa00fefcfaf0eeccaa00fffffffffffefffafffffffffffefffafefcfaf0eeccaa00fefcfaf0eeccaa00
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem floor6 : Lower true vars6 word6 10 := by
  exact lift_ok (ms := [Bound10782.swapNext 0, Bound10782.swapNext 4, Bound10782.swapNext 3, Bound10782.swapNext 5, Bound10782.swapNext 7, Bound10782.forceLow 1, Bound10782.forceLow 4]) (xs := [(truthWord1, 16, 18), (truthWord4, 2, 18)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) ForestCore.low358
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem sl6 : Slice true raw goal truthWord15 10 := by
  exact slice_correct (ms := [Bound10782.forceLow 6]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) floor6
def vars7 : List Sig := [truthWord0, truthWord1, truthWord2, truthWord3, truthWord4, truthWord5, truthWord6, truthWord7]
def word7 : Sig := truthWord8
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem floor7 : Lower true vars7 word7 13 := by
  exact lift_ok (ms := [Bound10782.swapNext 1, Bound10782.swapNext 0, Bound10782.swapNext 6, Bound10782.swapNext 7, Bound10782.forceLow 0]) (xs := [(truthWord0, 8, 9)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) ForestCore.low443
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem sl7 : Slice true raw goal truthWord16 13 := by
  exact slice_correct (ms := []) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) floor7
def vars8 : List Sig := [truthWord0, truthWord1, truthWord2, truthWord3, truthWord4, truthWord5, truthWord6]
def word8 : Sig := 0xfffffffeffffffeefefcfaf0eeccaa00fffffffeffffffeefefcfaf0eeccaa00fffffffeffffffeefefcfaf0eeccaa00fffffffeffffffeefefcfaf0eeccaa00
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem floor8 : Lower true vars8 word8 10 := by
  exact lift_ok (ms := [Bound10782.swapNext 0, Bound10782.swapNext 1, Bound10782.swapNext 4, Bound10782.swapNext 3, Bound10782.swapNext 5, Bound10782.swapNext 4, Bound10782.swapNext 7, Bound10782.swapNext 6, Bound10782.forceLow 2, Bound10782.forceLow 5]) (xs := [(truthWord2, 32, 36), (truthWord5, 4, 36)]) (by decide +kernel) (by unfold proper; decide +kernel) (by unfold proper; decide +kernel) ForestCore.low358
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem sl8 : Slice true raw goal truthWord17 10 := by
  exact slice_correct (ms := [Bound10782.forceLow 7]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) floor8
def mins : List (Sig × Nat) := [(truthWord9, 12), (truthWord10, 12), (truthWord11, 12), (truthWord12, 12), (truthWord13, 12), (truthWord14, 12), (truthWord15, 10), (truthWord16, 13), (truthWord17, 10)]
set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem mins_ok : ∀ p ∈ mins, Slice true raw goal p.1 p.2 := by
  intro p hp
  simp only [mins, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sl0
  · exact sl1
  · exact sl2
  · exact sl3
  · exact sl4
  · exact sl5
  · exact sl6
  · exact sl7
  · exact sl8

def negatives : List Row := [7, 14, 21, 35, 130, 68, 42, 28, 49, 144, 96, 56, 6, 5, 3, 12, 10, 20, 17, 34, 33, 64, 128]

def specs : Array Spec := #[(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (0, [(0, 6, 7)]), (1, [(0, 6, 7)]), (2, [(0, 6, 7)]), (3, [(0, 6, 7)]), (4, [(0, 6, 7)]), (5, [(0, 6, 7)]), (1, [(0, 6, 7), (1, 0, 8)]), (2, [(0, 6, 7), (1, 0, 8)]), (3, [(0, 6, 7), (1, 0, 8)]), (4, [(0, 6, 7), (1, 0, 8)]), (0, [(0, 6, 7), (1, 0, 8)]), (6, []), (7, [(0, 6, 7), (1, 0, 8)]), (8, []), (1, [(0, 6, 7), (1, 1, 8)]), (2, [(0, 6, 7), (1, 1, 8)]), (3, [(0, 6, 7), (1, 1, 8)]), (4, [(0, 6, 7), (1, 1, 8)]), (5, [(0, 6, 7), (1, 1, 8)]), (7, [(0, 6, 7), (1, 1, 8)]), (0, [(0, 6, 7), (1, 2, 8)]), (2, [(0, 6, 7), (1, 2, 8)]), (3, [(0, 6, 7), (1, 2, 8)]), (4, [(0, 6, 7), (1, 2, 8)]), (5, [(0, 6, 7), (1, 2, 8)]), (7, [(0, 6, 7), (1, 2, 8)]), (0, [(0, 6, 7), (1, 3, 8)]), (1, [(0, 6, 7), (1, 3, 8)]), (3, [(0, 6, 7), (1, 3, 8)]), (4, [(0, 6, 7), (1, 3, 8)]), (5, [(0, 6, 7), (1, 3, 8)]), (7, [(0, 6, 7), (1, 3, 8)]), (0, [(0, 6, 7), (1, 4, 8)]), (1, [(0, 6, 7), (1, 4, 8)]), (2, [(0, 6, 7), (1, 4, 8)]), (4, [(0, 6, 7), (1, 4, 8)]), (5, [(0, 6, 7), (1, 4, 8)]), (7, [(0, 6, 7), (1, 4, 8)]), (0, [(0, 6, 7), (1, 5, 8)]), (1, [(0, 6, 7), (1, 5, 8)]), (2, [(0, 6, 7), (1, 5, 8)]), (3, [(0, 6, 7), (1, 5, 8)]), (5, [(0, 6, 7), (1, 5, 8)]), (7, [(0, 6, 7), (1, 5, 8)]), (0, [(1, 6, 7)]), (1, [(1, 6, 7)]), (2, [(1, 6, 7)]), (3, [(1, 6, 7)]), (4, [(1, 6, 7)]), (5, [(1, 6, 7)]), (5, [(2, 6, 7)]), (0, [(2, 6, 7)]), (1, [(2, 6, 7)]), (2, [(2, 6, 7)]), (3, [(2, 6, 7)]), (4, [(2, 6, 7)]), (0, [(2, 6, 7), (1, 6, 7)]), (1, [(2, 6, 7), (1, 6, 7)]), (2, [(2, 6, 7), (1, 6, 7)]), (3, [(2, 6, 7), (1, 6, 7)]), (4, [(2, 6, 7), (1, 6, 7)]), (5, [(2, 6, 7), (1, 6, 7)]), (7, [(2, 6, 7), (1, 6, 7)]), (5, [(3, 6, 7)]), (0, [(3, 6, 7)]), (1, [(3, 6, 7)]), (2, [(3, 6, 7)]), (3, [(3, 6, 7)]), (4, [(3, 6, 7)])]

def spec (i : Nat) : Spec := specs[i]?.getD (0, [])

def entries : Array Entry := #[([truthWord1, truthWord2, truthWord3, truthWord4, truthWord5, truthWord6, 0xffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, truthWord7], 11, 0x90006000600060009900909097908000400040004000400030003000300030002000200020002000100010001000100050005000500050006000700060006000400040004000400030003000300030002000200020002000100010001000100050005000500050004000400040004000300030003000300020002000200020001000100010001000500050005000500040004000400040004000400040004000400040004000400040004000400040003000300030003000300030003000300030003000300030002000200020002000200020002000200010001000100010004, []), ([truthWord0, truthWord2, truthWord3, truthWord4, truthWord5, truthWord6, 0xffffffffffffffffccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccccccccccccccccccc, truthWord7], 11, 0x90006000600060009900900097008000400040004000400030003000300030002000200020002000100010001000100050005000500050006000700060006000400040004000400030003000300030002000200020002000100010001000100050005000500050004000400040004000300030003000300020002000200020001000100010001000500050005000500040004000400040004000400040004000400040004000400040004000400040003000300030003000300030003000300030003000300030002000200020002000200020002000200010001000100010004, []), ([truthWord0, truthWord1, truthWord3, truthWord4, truthWord5, truthWord6, 0xfffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, truthWord7], 11, 0x90006000600060009000909090908000400040004000400030003000300030002000200020002000100010001000100050005000500050006000700060006000400040004000400030003000300030002000200020002000100010001000100050005000500050004000400040004000300030003000300020002000200020001000100010001000500050005000500040004000400040004000400040004000400040004000400040004000400040003000300030003000300030003000300030003000300030002000200020002000200020002000200010001000100010004, []), ([truthWord0, truthWord1, truthWord2, truthWord4, truthWord5, truthWord6, 0xffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, truthWord7], 11, 0x90006000600060009900909097908000400040004000400030003000300030002000200020002000100010001000100050005000500050006000700060006000400040004000400030003000300030002000200020002000100010001000100050005000500050004000400040004000300030003000300020002000200020001000100010001000500050005000500040004000400040004000400040004000400040004000400040004000400040003000300030003000300030003000300030003000300030002000200020002000200020002000200010001000100010004, []), ([truthWord0, truthWord1, truthWord2, truthWord3, truthWord5, truthWord6, 0xffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, truthWord7], 11, 0x90006000600060009900900097008000400040004000400030003000300030002000200020002000100010001000100050005000500050006000700060006000400040004000400030003000300030002000200020002000100010001000100050005000500050004000400040004000300030003000300020002000200020001000100010001000500050005000500040004000400040004000400040004000400040004000400040004000400040003000300030003000300030003000300030003000300030002000200020002000200020002000200010001000100010004, []), ([truthWord0, truthWord1, truthWord2, truthWord3, truthWord4, truthWord6, 0xffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000, truthWord7], 11, 0x90006000600060009000909090908000400040004000400030003000300030002000200020002000100010001000100050005000500050006000700060006000400040004000400030003000300030002000200020002000100010001000100050005000500050004000400040004000300030003000300020002000200020001000100010001000500050005000500040004000400040004000400040004000400040004000400040004000400040003000300030003000300030003000300030003000300030002000200020002000200020002000200010001000100010004, []), ([truthWord0, truthWord1, truthWord2, truthWord3, truthWord4, truthWord5, 0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff000000000000000000000000000000000000000000000000, truthWord6, truthWord7], 12, 0x880080808e800000888000000000000050005000500050004000400040004000300030003000300020002000200020001000100010001000600060006000600088e000000000000050005000500050004000400040004000300030003000300020002000200020001000100010001000600060006000600055005555558d550044004444448c440033003333338b330022002222228a2200110011111189110066006666668766005000500050005000500050005000500050005000500050005000500050005000500050005000500040004000400040004000400040004000400040004000400040004000400040003000300030003000300030003000300030003000300030002000200020002000200020002000200010001000100010004, [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0)]), ([truthWord0, truthWord1, truthWord2, truthWord3, truthWord4, truthWord5, truthWord6, truthWord7, truthWord18], 12, 0x8880000000000000777000000000000055005500550055004400440044004400330033003300330022002200220022001100110011001100660066006600660070708800000078705000500050005000440040004400400033003000330030002000200020002000110010001100100066006000660060005500500055005000400040004000400033003000330030002200200022002000100010001000100066006000660060005000500050005000500050005000500050005000500050005000500050005000500050005000500040004000400040004000400040004000400040004000400040004000400040003000300030003000300030003000300030003000300030002000200020002000200020002000200010001000100010004, []), ([truthWord0, truthWord1, truthWord2, truthWord3, truthWord4, truthWord5, truthWord6, truthWord7, truthWord18], 11, 0x8880000000000000777000000000000055005500550055004400440044004400330033003300330022002200220022001100110011001100660066006600660070708800000077705000500050005000440040004400400033003000330030002000200020002000110010001100100066006000660060005500500055005000400040004000400033003000330030002200200022002000100010001000100066006000660060005000500050005000500050005000500050005000500050005000500050005000500050005000500040004000400040004000400040004000400040004000400040004000400040003000300030003000300030003000300030003000300030002000200020002000200020002000200010001000100010004, []), ([0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000, truthWord0, truthWord1, truthWord2, truthWord3, truthWord4, truthWord5, truthWord6, truthWord7], 12, 0x7970000099007070600060006000600050005000500050004000400040004000300030003000300020002000200020001000100010001000000000009980000066006000660060005000500050005000440040004400400033003000330030002000200020002000110010001100100077700000000000006000600060006000600060006000600060006000600060006000600060006000600060006000600060606060606060605000500050005000500050005000500050005000500050005000500050005000505050505050505040004000400040004000400040004000400040004000400040404040404040403000300030003000300030003000300030303030303030302000200020002000202020202020202010101010101010104, [(8, 0)]), ([0xffffffffffffffff000000000000000000000000000000000000000000000000ffffffffffffffff00000000000000000000000000000000, truthWord0, truthWord1, truthWord2, truthWord3, truthWord4, truthWord5, truthWord6, truthWord7], 12, 0x898080808800600060006000600055005000550050004400400044004000300030003000300022002000220020001100100011001000888000000000000060006000600060005000500050005000400040004000400030003000300030002000200020002000100010001000100000000000887000006000600060006000600060006000600060006000600060006000600060006000600060006000600060606060606060605000500050005000500050005000500050005000500050005000500050005000505050505050505040004000400040004000400040004000400040004000400040404040404040403000300030003000300030003000300030303030303030302000200020002000202020202020202010101010101010104, [(8, 0)]), ([truthWord0, truthWord1, truthWord2, truthWord3, truthWord4, truthWord5, truthWord6, truthWord7], 13, 0xa0009000800070005000500050005000400040004000400030003000300030002000200020002000100010001000100060006000600060005000500050005000400040004000400030003000300030002000200020002000100010001000100060006000600060005000500050005000500050005000500050005000500050005000500050005000500050005000500040004000400040004000400040004000400040004000400040004000400040003000300030003000300030003000300030003000300030002000200020002000200020002000200010001000100010004, [(6, 0), (7, 0), (9, 0), (10, 0)])]

def state (i : Nat) : Entry := entries[i]?.getD ([], 0, 0, [])

def books : Array (List Nat) := #[[24, 26, 28, 30, 32, 22, 34, 36, 38], [40, 42, 44, 46, 48, 12, 34, 50, 38], [52, 54, 56, 58, 60, 14, 34, 62, 38], [64, 66, 68, 70, 72, 16, 34, 74, 38], [76, 78, 80, 82, 84, 18, 34, 86, 38], [88, 90, 92, 94, 96, 20, 34, 98, 38], [12, 14, 16, 18, 20, 22, 1, 38, 3, 5, 7, 9, 11, 34], [100, 102, 104, 106, 108, 110, 38, 34], [124, 126, 128, 130, 132, 134, 38, 136], [112, 114, 116, 118, 120, 122, 38, 1, 34], [138, 140, 142, 144, 146, 148, 1, 38, 34], [0, 2, 4, 6, 8, 10, 1, 3, 5, 7]]

def keyBook (i : Nat) := books[i]?.getD []

def perm (_ : Nat) : List Move := []

def test (i : Nat) := good goal negatives raw mins spec state keyBook perm i

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem test0 : test 0 = true := by decide +kernel

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem test1 : test 1 = true := by decide +kernel

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem test2 : test 2 = true := by decide +kernel

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem test3 : test 3 = true := by decide +kernel

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem test4 : test 4 = true := by decide +kernel

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem test5 : test 5 = true := by decide +kernel

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem test6 : test 6 = true := by decide +kernel

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem test7 : test 7 = true := by decide +kernel

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem test8 : test 8 = true := by decide +kernel

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem test9 : test 9 = true := by decide +kernel

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem test10 : test 10 = true := by decide +kernel

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem test11 : test 11 = true := by decide +kernel

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem tests : ∀ i < 12, test i = true := by
  intro i hi
  interval_cases i
  · exact test0
  · exact test1
  · exact test2
  · exact test3
  · exact test4
  · exact test5
  · exact test6
  · exact test7
  · exact test8
  · exact test9
  · exact test10
  · exact test11

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem blocked : Impossible true goal 13 raw.toFinset :=
  certifiedA (perm := perm) (N := 12) (fun _ y => ⟨y,rfl⟩) mins_ok tests 11 (by decide)

def req : List (Sig × Row × Row) := [(truthWord0, 8, 9), (truthWord1, 16, 18), (truthWord2, 32, 36), (truthWord3, 1, 9), (truthWord4, 2, 18), (truthWord5, 4, 36), (truthWord6, 1, 65), (truthWord7, 1, 129)]

set_option maxRecDepth 95000 in
set_option maxHeartbeats 0 in
theorem finalFloor : Lower true raw goal 14 := by
  apply lower_impossible (L := 13) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs := req) (by decide +kernel) a
    exact (show (req.map Prod.fst).toFinset = raw.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact blocked
end BlockCertificate

def target32097 : F := fun x => (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem lower32097 : Low 14 target32097 := by
  exact from_signed_block_floor (f := target32097) ![0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000]
    (by decide +kernel) (by decide +kernel) BlockCertificate.finalFloor

def witness32097 : List Gate := [⟨.or, [0, 1]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [4, 13]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [18, 21]⟩]

theorem basis32097 : ∀ g ∈ witness32097, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness32097]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witnessEval32097 : ∀ x : X, Circuit.eval ⟨witness32097, 22⟩ (List.ofFn x) = target32097 x := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem targetEq32097 : ∀ x : X, target32097 x = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_32097

open PEqualNP.Outside.L_meta_32097 in
theorem PEqualNP.Outside.L_meta_32097 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hg _ he
  by_cases hs : 15 ≤ gates.length
  · exact ⟨witness32097, 22, basis32097, hs, fun x => (witnessEval32097 x).trans (targetEq32097 x)⟩
  · exact ⟨gates, o, all_not_not_of_guillabert_pr42591 lower32097 gates o hg (by omega)
      (fun x => (he x).trans (targetEq32097 x).symm), le_rfl, he⟩
