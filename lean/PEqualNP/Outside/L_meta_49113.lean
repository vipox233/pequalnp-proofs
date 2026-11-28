import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49113.Threshold

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

namespace TabKfive
open Core GateForest12127 CertBlocks12127 Bound12127
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def root := inputs.take 5
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def target := stamp 5 0xfffefee8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd0 : Sig := ~~~raw 0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl0 : Slice true root target sd0 7 :=
  slice_correct (ms:=[forceLow 4,swapNext 3,swapNext 2,swapNext 1,swapNext 0]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfee8.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd1 : Sig := raw 0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl1 : Slice true root target sd1 3 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3,swapNext 2,swapNext 1,swapNext 0]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfffe.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd2 : Sig := ~~~raw 1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl2 : Slice true root target sd2 7 :=
  slice_correct (ms:=[forceLow 4,swapNext 3,swapNext 2,swapNext 1]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfee8.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd3 : Sig := raw 1
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl3 : Slice true root target sd3 3 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3,swapNext 2,swapNext 1]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfffe.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd4 : Sig := ~~~raw 2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl4 : Slice true root target sd4 7 :=
  slice_correct (ms:=[forceLow 4,swapNext 3,swapNext 2]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfee8.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd5 : Sig := raw 2
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl5 : Slice true root target sd5 3 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3,swapNext 2]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfffe.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd6 : Sig := ~~~raw 3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl6 : Slice true root target sd6 7 :=
  slice_correct (ms:=[forceLow 4,swapNext 3]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfee8.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd7 : Sig := raw 3
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl7 : Slice true root target sd7 3 :=
  slice_correct (ms:=[forceHigh 4,swapNext 3]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfffe.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd8 : Sig := ~~~raw 4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl8 : Slice true root target sd8 7 :=
  slice_correct (ms:=[forceLow 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfee8.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def sd9 : Sig := raw 4
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem sl9 : Slice true root target sd9 3 :=
  slice_correct (ms:=[forceHigh 4]) (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) Tabfffe.lower
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def mins : List (Sig × Nat) := [(sd0,7),(sd1,3),(sd2,7),(sd3,3),(sd4,7),(sd5,3),(sd6,7),(sd7,3),(sd8,7),(sd9,3)]
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
  row 5 [0xeaeaeaea,0xfffcfcfc,0xffffff00] 2 (replayWords [0x61121,0x142061062120121,0x62060060061128]) [],
  row 5 [0xeeeeeeee,0xfafafafa,0xfffcfcfc,0xffffff00] 3 (replayWords [0x61121142061,0x62142121062064,0x164121064061062,0x61308061064061,0x308062064062800]) [(0,0)],
  row 5 [0x88888888,0xeeeeeeee,0xfff0fff0,0xfffff0f0,0xffffff00] 4 (replayWords [0x184188184401121,0x1211844010a4128,0x1280a4061184802,0x610a10a1188400,0x1280a40a4128061,0x1888010611b00a4,0xa4190061190800,0x61060000000000]) [(1,1),(1,2),(1,3)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xfffff0f0,0xffffff88] 4 (replayWords [0x184188184403121,0x121184403061061,0x1480c4062062128,0xa40a10a1188402,0x1480c40c4148128,0xa40a41281d00c4,0xc41901b00a40a4,0x1900a40c48000a4]) [(1,3)],
  row 5 [0xeeeeee,0xfafafafa,0xfcfcfcfc,0xff00ff00,0xffff0000] 4 (replayWords [0x121221308121061,0x221242061062242,0x221062064264221,0x64061121142061,0x62142121062064,0x164121064061062,0x61405061064061,0x405062064062404]) [],
  row 5 [0x88888888,0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xfffff0f0,0xffffff00] 5 (replayWords [0x184188184407121,0x1211844070c4148,0x1480c40a4128128,0xa4806184805184,0xa10a1188406148,0xc40c41481280a4,0xa4128804188803,0x1881d00c40c4190,0x1b00a40a4190802,0x1908011900a40c4,0x800000061000000,0x62000000000]) [(2,0),(3,4),(4,5),(3,6),(4,7),(3,0),(4,1)],
  row 5 [0xeeeeeeee,0xfff0fff0,0xfffffac8] 2 (replayWords [0xa1061,0x184061060060061,0xa40700a00a1070]) [],
  row 5 [0xeeeeeeee,0xfff0fff0,0xfffffafa,0xffffffcc] 3 (replayWords [0x61062061800,0xa1061142061061,0x700610a40c2062,0xa1062062070062,0x1480700a40a1070]) [(6,0)],
  row 5 [0xaaaaaaaa,0xeeeeeeee,0xfff0fff0,0xfffff0f0,0xffffffcc] 4 (replayWords [0x184061184061121,0x611420610610c4,0x61184061062061,0x1840a10a1188142,0xc80c8242148062,0x1888010620d00d0,0x142190062122800,0x620a4000000000]) [(7,8),(7,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xfffff0f0,0xffffffee] 4 (replayWords [0x184188184403184,0x1211214030c4000,0xa4000000,0xa10a1188121,0x610c8242061062,0xa82210620610d0,0x1420610620b0121,0x62061062061128]) [],
  row 5 [0xee,0xfafafafa,0xfcfcfcfc,0xff00ff00,0xffff0000] 4 (replayWords [0x164264308164061,0x240224061062220,0x230062000000221,0x61140124061,0x62120128062000,0x121000061062,0x61128061064061,0x148062064062128]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xfff0fff0,0xfffff0f0,0xffffff00] 5 (replayWords [0x184188184409121,0x12118440980c184,0x80b18406118480a,0x61062184809062,0xa10a1188408808,0x188807188061188,0x806061062188805,0x62804190803190,0x61190802061062,0x1908010620c4000,0xa4000000,0x61062000800]) [(2,0),(8,9),(8,4),(9,4),(10,5),(8,10),(8,6),(9,6),(10,7),(8,11),(8,0),(9,0),(10,1)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xfffff0f0,0xffffff22] 4 (replayWords [0x184188184403142,0x1211214030c4148,0x610610620a4128,0x620a10a1188121,0x1480c40c4148062,0xa82210621610c4,0xc41210620b0121,0x620600600620c4]) [],
  row 5 [0xa8a8fcfc,0xaaaaaaaa,0xffccffcc,0xfff0fff0,0xffff0000] 4 (replayWords [0xc22212480c20c4,0x2212500c4062220,0x2210620c8221242,0xc80c20c40c2250,0x620a40a40620a1,0xa10c22900a4062,0x620a40610610c4,0x2500620e80620c8]) [],
  row 5 [0xaaaa,0xfcfcfcfc,0xffccffcc,0xfffafffa,0xffff0000] 4 (replayWords [0xc22202300c20c4,0x2642280c40a1268,0x2240a1000000221,0xc20c40c2230,0xc20a10a1230062,0x61061,0xc40a1064064121,0xa40680680a10c8]) [],
  row 5 [0xaaaa,0xaaaaaaaa,0xfcfcfcfc,0xffccffcc,0xfff0fff0,0xffff0000] 5 (replayWords [0xc22422840c20c4,0x2842420c40c82c8,0x2420c8220000230,0x242000000221000,0xc20c40c240b0a1,0xa10c240b2300c2,0x8080c28070c2806,0xc20610610c440a,0x2300c48050c4804,0xc48030c42300c8,0x8020c88010c8800,0xc8062000000000]) [(12,12),(13,13),(14,14),(12,15),(13,16),(14,17),(12,18),(13,19),(14,0)],
  row 5 [0xeaeaeaea,0xfffcff00,0xfffffcfc] 2 (replayWords [0x121061,0x142061060060061,0x128062120121062]) [],
  row 5 [0xeeeaeeea,0xfffcfffc,0xfffff0f0,0xffffff00] 3 (replayWords [0x182182184800,0x61121184061062,0x1220680620610a1,0x1880610620a2064,0x62060060061190]) [(16,1)],
  row 5 [0xa8a8a8a8,0xfefefefe,0xff00ff00,0xffffcccc,0xfffff0f0] 4 (replayWords [0xc10c10c240c121,0xc21240c20c20d0,0xc21280620a10a4,0x621210c41220c4,0xc40d00c4128061,0x610620a40d0120,0x1210d0062121800,0x620f0000000000]) [(17,20)],
  row 5 [0xaaaaaaaa,0xeeeceeec,0xfff0fff0,0xfffff0f0,0xffffff00] 4 (replayWords [0x18418818440e142,0x14218440e061148,0x148061062184230,0x620c20c218840d,0x610c40c4061062,0x1882300620610c4,0xc4061062190800,0x620600600610c4]) [(17,11)],
  row 5 [0xaaaaa,0xfcfcfcfc,0xffccffcc,0xfff0fff0,0xffff0000] 4 (replayWords [0xc22212840c20c4,0x2212420c40c8221,0x2420c8062220221,0x620c20c40c240f,0xa10a10c2410062,0xa40a4062061061,0xc440f0a4062062,0xa40e80620620c8]) [],
  row 5 [0xa8a8a8a8,0xaaaaaaaa,0xfcfcfcfc,0xff00ff00,0xffffcccc,0xfffff0f0] 5 (replayWords [0xc20c40c2416121,0xc21840c20c20d0,0xc24161280c2230,0xc24150c24140c2,0x1210c41420c40c4,0xd00c44071280c4,0x2300c44130c4412,0xc40d01211420d0,0x120120121142802,0x1218011211280d0,0x800000411000000,0x62000000000]) [(18,0),(19,14),(20,21)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xfffffac8] 3 (replayWords [0xa10c21840a1,0x61061242144062,0x622210a40d00a1,0x1420a10a00a00a1,0x1420700708000a4]) [(6,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xfffffafa,0xffffffcc] 4 (replayWords [0x1841881848010a1,0x1211420a1061000,0xa4124221,0xa40c20a10a1142,0xc80c8242148062,0xd00a1,0x1420a10a10a40a1,0x1420700708000a4]) [(7,0),(22,0)],
  row 5 [0xeeee,0xf0f0f0f0,0xffaaffaa,0xfffcfffc,0xffff0000] 4 (replayWords [0x61240228061062,0x2202300620c2268,0x2440c2000000221,0x61062061230,0xa1000000000061,0x680612500a2062,0x184062062068062,0xc40680a80c2068]) [],
  row 5 [0xeeee,0xf0f0f0f0,0xffaaffaa,0xffccffcc,0xffffeeee] 4 (replayWords [0x240061061228220,0x620622481880a1,0xa1188068000000,0x61062061230,0xa10610c2061061,0x2420612210c2062,0xa1062062221062,0x2300a11880a1188]) [],
  row 5 [0xfefe,0xaaaaaaaa,0xffccffcc,0xfff0fff0,0xffff0000] 4 (replayWords [0xa12802480a1061,0x240250061062220,0x230062000000221,0x610a10c2061,0x620a40a10620a1,0xc80a1290061062,0x610a40610c8061,0x2500620e80620c8]) [],
  row 5 [0xee,0xaaaaaaaa,0xf0f0f0f0,0xffccffcc,0xffffeeee] 4 (replayWords [0x140061061184188,0xa10a1148128000,0x417000000,0xa10610c2061,0x61062061150061,0x1420611210620c2,0xa10620a11880a1,0x142062221062122]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xfffff0f0,0xffffffaa] 5 (replayWords [0x18480a184403188,0x188184188184403,0x419403184809142,0x403121121184121,0x121403419403808,0xc40c4184061061,0x8070610611840c4,0xc4418806062000,0x0,0x188121,0xa12211900a1188,0x190188221121121,0x8050610611880c4,0xc48040c40c4188,0x610612211280a8,0x1882300a8221230,0x221188128128803,0x610611210c40c4,0x8020c40c4121061,0x611212300b0190,0x1280b0121128121,0x190230190061128,0x610c48010c4061,0x8000610c41280c4]) [(8,11),(14,22),(23,4),(24,23),(23,11),(24,24),(25,16),(9,0),(26,25),(27,18),(27,14)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xfffafffa,0xfffff0f0,0xffffff00] 5 (replayWords [0x18418818441d184,0x41f18441e121121,0x18441d061148148,0x610a41281280a4,0x18841c18841b0a1,0xa118841a0610c4,0xc40611280a40a4,0x128190000000000,0x250061061250062,0x610c4,0xc40618010a4000,0x8000610c40610a4]) [(18,26),(25,27)],
  row 5 [0xaa,0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xfffff0f0,0xffffff00] 5 (replayWords [0x18418818441f142,0x14218441f061148,0x1480611a4000128,0x184000000419000,0xa10a1188423061,0xc40c4061128188,0x230128421188422,0x1880610c40c4061,0x1b0128128190421,0x1904201900610c4,0x610c40610c4061,0xc4062000000000]) [],
  row 5 [0xaaaaaaaa,0xaaaafefe,0xffccffcc,0xfff0fff0,0xffff0000] 4 (replayWords [0xa12212480a1061,0x2212500610c82c8,0x2210c8062262221,0x620610a10c2061,0xa10c80a1290062,0xa40a10620610c8,0x61250061062061,0xa40e8000000000]) [],
  row 5 [0xeeee,0xfa00fa,0xfcfcfcfc,0xff00ff00,0xffff0000] 4 (replayWords [0x142264308142061,0x240224061062220,0x230062000000221,0x61180122061,0x121000064,0x120128064061062,0x61188061064061,0x128062064062128]) [],
  row 5 [0xeeee,0xf0f0f0f0,0xffaaffaa,0xffccffcc,0xffff0000] 5 (replayWords [0x268061061284250,0x240268250228284,0x61061268062062,0x284230220268230,0x230284062062284,0xa10a1268290268,0x2842902842680a1,0xa1000000000000,0x806428221,0x61230,0x61250062062061,0x62061250230230,0x8050a10a10610c2,0x618040c20c2061,0xa1061061427061,0x250068068061068,0x61250426250803,0xc20c20620a1062,0x8020a10a10620c2,0x62062425062230,0x68068062068062,0x2304242300a1068,0x681888010e80a1,0x8000a1188068068]) [(31,28),(10,6),(24,11),(32,6),(24,0),(32,10),(25,0)],
  row 5 [0xeeee,0xeeeeeeee,0xf0f0f0f0,0xffaaffaa,0xffccffcc,0xffff0000] 5 (replayWords [0x61284308061062,0x2843080620a1280,0x2840a1268000800,0x284000000221000,0x6106206142a0a1,0x610c2061061250,0x6142a06142b061,0x42a0c20620a1062,0x6223006240b062,0x42906240b0a1188,0xa11880a11880a1,0x188068000000000]) [(25,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xfffff0f0,0xffffff00] 6 (replayWords [0x42d18442c184421,0x403188188421184,0x188184421403421,0x40342f18442e121,0x421403190121421,0x184190184421403,0x421403827826061,0x61825184148148,0x824823148148822,0x184061061821820,0x6206281f184128,0x12881e81d128128,0x81c18406206242f,0x18842e0a142d42c,0x1900a1421188190,0x18842d42c42d42c,0x81b81a061061819,0x1880c40c4818817,0xc40c4816188061,0x61815814062062,0x8131880a40a4812,0x8110a40a4810188,0x6206280f80e061,0x6180d1900c40c4,0x80c80b0c40c480a,0x190061061809808,0x620628071900a4,0xa48068050a40a4,0x804190062062803,0x610a40608020c4,0x62060801061062,0x618000c40a40a4]) [(5,0),(11,0),(15,25),(15,29),(21,26),(28,4),(29,0),(30,4),(33,27),(34,27),(21,30),(28,9),(29,11),(30,9),(33,31),(34,31),(21,15),(28,6),(29,4),(30,6),(33,13),(34,13),(21,32),(28,10),(29,9),(30,10),(33,33),(34,33),(21,12),(28,0),(29,34),(30,0),(33,16),(34,16),(21,35),(28,11),(29,36),(30,11),(33,37),(34,37)],
  row 5 [0xaaaaaaaa,0xfcfcfca8,0xffccffcc,0xfffff0f0] 3 (replayWords [0xc00c00c2121,0xa10a12840c2122,0xc22210c2061061,0x1420c41200c4121,0xc4062062800122]) [(6,38)],
  row 5 [0xaaaaaaaa,0xfcfcfcfc,0xffccffcc,0xfffff0f0,0xffffffaa] 4 (replayWords [0xc21422210c20c4,0x1211210c4142148,0x142801062000000,0xc20c40c2121,0xa10a10c2148128,0xc22210c2061061,0xc41211210c4121,0xc4068068800128]) [(7,38),(36,0)],
  row 5 [0xeee0,0xfafafafa,0xffccffcc,0xffff0000] 3 (replayWords [0x61221242061,0x62220221062000,0x800000060060,0x612300a1061142,0x610a00620a1062]) [(6,39)],
  row 5 [0xeeee,0xfff0,0xfafafafa,0xffccffcc] 3 (replayWords [0x61062061220,0xa1061142061061,0xc40610a40c2062,0xa10620620a4062,0x1480a10a40a1221]) [],
  row 5 [0xeeee,0xfafafafa,0xffccffcc,0xfff0fff0,0xffff0000] 4 (replayWords [0xa18012240a1061,0x240250061062220,0x230062000000221,0x610a1142061,0x620c20a10620a1,0xa40a1800061062,0x612300610c4061,0xa40620a4062148]) [(38,0),(39,0)],
  row 5 [0xeeeeeeee,0xfff0fff0,0xfffffac8] 3 (replayWords [0x184,0xa10a1061190061,0x1841901840610a1,0x610610a4060184,0x70060061070061,0x1840a40a40a1070,0x701900a40a00a1,0xa40a1190070070]) [],
  row 5 [0xeeeeeeee,0xfff8fff8,0xfffffac8] 2 (replayWords [0x61061,0x1840a1064064221,0xa40700700a1190]) [],
  row 5 [0xeee0eee0,0xfafafafa,0xffccffcc,0xffffeee0] 3 (replayWords [0x61221242061,0x622202210620a1,0x60060,0x61230150061801,0x610b0062800062]) [(42,39),(42,17)],
  row 5 [0xaaaaaaaa,0xfcfcfcfc,0xffeefaea,0xffffff00] 3 (replayWords [0xc21421210c2,0x61121142061121,0x1421211420c0061,0x61148062000000,0x611480610c1]) [],
  row 5 [0xa222a,0xfcfcfcfc,0xfff0ccc0,0xffffff00] 3 (replayWords [0xc21213080c2,0x61121182061062,0x1201210620610c0,0xc2061000000800,0x60060061128]) [(6,16)],
  row 5 [0xaaaaaaaa,0xfffcfcfc,0xffffffc0] 2 (replayWords [0x610c0,0xc20610620c2121,0x620600600610c8]) [],
  row 5 [0xaaaaaaaa,0xfcfcfc00,0xffccffcc,0xfffffcf0] 3 (replayWords [0x610a10c2061,0x142000000000062,0xa00a1062144061,0x801061060060061,0xa4062284800062]) [(42,40),(46,14)],
  row 5 [0xa505a,0xcccccccc,0xfff0aaa0,0xffffff00] 3 (replayWords [0xa01200a80a0,0x61140142061062,0x1421810620610a0,0xa20610000000a1,0x60060061148]) [],
  row 5 [0xaaaaaaaa,0xfcfcfc00,0xffccffcc,0xfffff0f0] 4 (replayWords [0xc2061,0x610a10c40a10c2,0xc40c20a1061061,0x8081421420a1284,0xa18072842840a1,0x1420a10a1062062,0xc20a40a00a10a4,0xa10c2062062806,0x284140061142061,0x805142142061284,0x610610a40600c4,0x62060061062061,0xc40a40a4804062,0x62142803142802,0x801800142062062]) [(41,38),(43,19),(44,41),(45,14),(38,19),(47,25),(48,20),(47,0),(48,42)],
  row 5 [0xeeeeeeee,0xfafafafa,0xffccffcc,0xffffeee0] 3 (replayWords [0x610a1142061,0x620c20a10620a1,0xa40a1281061062,0x61290061064061,0x181062068062182]) [],
  row 5 [0xaaaaaaaa,0xfcfcfc00,0xfcfcfcfc,0xffccffcc,0xfffff0f0] 4 (replayWords [0xc20c40c21210a1,0xa10c22211420c2,0x2840c20620a40a4,0x620610610c4121,0x1840c41420c40a4,0x620620a4148000,0x68062062,0x122062142800062]) [(50,43)],
  row 5 [0xaaaaaaaa,0xfcfcfc00,0xffccffcc,0xfffff0f0] 3 (replayWords [0x610a10c2061,0x1420a12840a1062,0xa00a1062140061,0x142061060060061,0xa4062142800062]) [(6,38)],
  row 5 [0xee,0xeeeeeeee,0xf0f0f0f0,0xffaaffaa,0xffffcccc] 4 (replayWords [0x610620611840a1,0x610c2061061148,0x61128061242061,0x1210c20620a1062,0x62120062184062,0x1210621420a1188,0xa11280a11880a1,0x121800000000000]) [(52,28)],
  row 5 [0xaaaaaaaa,0xfcfcfcfc,0xffccffcc,0xfffff0f0,0xffffff00] 5 (replayWords [0x2840c20c2142308,0x142284308284142,0xc20c21420c40c4,0x284310121142310,0x1422840c40c4142,0x811142810148148,0x14214814280f80e,0x80d80c062062142,0x12812880b128128,0x1420620620c280a,0xc28090c40c40c2,0xc40c2808807806,0xc21480a1308290,0xa10c22900c2308,0x148148805062062,0xc20a40a48040a4,0xa40c20620620c4,0x290061310148061,0xc41480c4310290,0x2908030a40a40c4,0x62062802062062,0xc40a40a4801128,0x128148062062800,0x62062148128128]) [(37,25),(40,43),(37,41),(40,40),(37,6),(40,38),(49,41),(51,41),(51,6),(53,44),(53,33),(37,0),(40,19),(49,0),(51,25),(51,0),(53,45),(53,37)],
  row 5 [0xeeeeeeee,0xfafafafa,0xffccffcc,0xfffff0f0,0xffffff00] 4 (replayWords [0xa11422840a1061,0x121142061062122,0x2840620a4148142,0xa40610a1308061,0x620c20a10620a1,0xa40a1148061062,0x612900610c4061,0xa40620a4062148]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfafafafa,0xffccffcc,0xfffff0f0,0xffffff00] 5 (replayWords [0xa11422840a1121,0x121142284284142,0x284142142148142,0x2840a41428050a4,0x3080a13080a10a1,0xc20a13081480a1,0x8040a10a10a40a1,0x308190190803290,0x610000000000a4,0x3108020a4148290,0x801148062000000,0xa41488000a4]) [(55,0),(37,25),(37,46),(9,4),(8,47),(8,30)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfafafafa,0xfff0fff0,0xfffffafa,0xffffff00] 5 (replayWords [0x1842421844310a1,0x1211840a1184800,0x184304061148148,0x610a41242210a4,0x3080a10a141a188,0x148061,0x61148430000000,0xa11900a1310,0x610a10c40610a1,0xa40a1310148061,0x61148230000000,0x610c40610a4]) [(27,17)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffaafca8,0xffffff00] 4 (replayWords [0x1421213081210c2,0x1212840c20c4121,0x2420c4120120121,0x2420a10a18030c2,0x610618020c4062,0x6242c1280c00c0,0xc22481280c2801,0xc21280c48000c4]) [(36,48),(36,10),(22,49),(22,36)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffaaffaa,0xfffffcfc,0xffffff00] 5 (replayWords [0x221121242121121,0x1421212420c2121,0x2840c20c4121242,0xc4121128121242,0x3083103088050a1,0x61000,0x128228804,0x1280c21908030c2,0xc41508020c4062,0xc20c4,0xc22501280c2801,0xc21280c48000c4]) [(37,48),(37,10),(23,49),(23,36),(9,50),(58,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf3f2f3f2,0xfffff0f0,0xffffff00] 4 (replayWords [0xa11211840a1121,0x1421211420c4121,0x1420c4062128121,0x620a10c20a142e,0xe10a10c40a1062,0xa40a10621d00c4,0x610610620a40a4,0x620600600620a4]) [],
  row 5 [0xeee0,0xaaaaaaaa,0xf0f0f0f0,0xffccffcc,0xffff0000] 4 (replayWords [0x61221242061182,0x221284182062220,0x221062000000801,0x180061182061,0x600600611840c4,0x61142061062182,0x8000620a10a142c,0x1420a4062429062]) [(38,0),(22,17)],
  row 5 [0xeeee,0xfff0,0xaaaaaaaa,0xf0f0f0f0,0xffccffcc] 4 (replayWords [0x184061184061061,0x62061184121061,0x1420610610c4061,0x184062188800062,0xa10a11881420c8,0xc82a1148122062,0x2680620620a4062,0x148142148142221]) [(39,0)],
  row 5 [0xeeee,0xaaaaaaaa,0xf0f0f0f0,0xffccffcc,0xfff0fff0,0xffff0000] 5 (replayWords [0x142804248142061,0x2402500611882c8,0x284188062220230,0x62000000221000,0x611211420610a1,0x62122,0x803062142148142,0x802184061184061,0x61062061184061,0xc4061184062188,0x8010620c80c8800,0x1480620a4062148]) [(60,15),(40,0),(61,0),(24,11),(62,0)],
  row 5 [0xaaaaaaaa,0xeeeeeeee,0xfff0fff0,0xfffffac8] 3 (replayWords [0xa1061184061,0x610c4061144061,0x620611840a10d0,0xa11900a10a20a1,0x141070000000000]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfafafa00,0xffaaffaa,0xfffff0f0] 4 (replayWords [0xa10c20a10c2121,0xa12840a10610a1,0xc20610a10a80a1,0xc2184121121142,0xc40610610c4062,0x61121,0x800061121128121,0x2840610680610c4]) [(64,51)],
  row 5 [0xaaaa,0xfcfcfcfc,0xffeeffe0,0xffff0000] 3 (replayWords [0xc22202280c2,0x61228282061000,0x8000000610a1,0xc20610620a2121,0x620600600610c8]) [(6,42)],
  row 5 [0xaaaa,0xcccccccc,0xfafafa00,0xfff0fff0,0xffff0000] 4 (replayWords [0xa12423040a1184,0x220230184061240,0x242061000000801,0x1210a11840a1,0x610a10c2061062,0xa00a1062061184,0x800061062124403,0x620600600610a4]) [(66,47),(52,45)],
  row 5 [0xaaaaeeee,0xfffcfaf8,0xffffff00] 2 (replayWords [0x61121,0x184061064124141,0x64060060061148]) [],
  row 5 [0xaa,0xfefefecc,0xff00ff00,0xfffff0f0] 3 (replayWords [0x1220a13040a1,0x610a10c2061062,0xa00a1062061120,0x122061000000800,0x600600610a4]) [(68,20)],
  row 5 [0xaaaaaaaa,0xccccfcfc,0xfff0ccc0,0xffffff00] 3 (replayWords [0xc21212880c2,0x61121182061062,0x1201210620610c0,0xc20610620c2800,0x62060060061128]) [(68,45)],
  row 5 [0xaa,0xcccccccc,0xfafafa00,0xff00ff00,0xfffff0f0] 4 (replayWords [0x1420a13040a1128,0xa12240a10610a1,0xc20610620a00a1,0x62120120128142,0x61140142061000,0x801000061128,0x800061000000403,0x600600610a4]) [(69,0),(70,44)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xfffffac8] 4 (replayWords [0x1840a1,0xa12211900c2184,0x1901842210a10a1,0x242144061184250,0x61242250242184,0x1441442210a4062,0x184230062221230,0x2211840a40a4142,0x2500d00a11440a1,0x1421441420a1250,0xa10a12300a0142,0xa40a00a10a40a1,0x1422301428040a4,0x70144803070802,0x8018001440a40a4]) [(41,0),(64,10),(64,0),(66,52),(66,53)],
  row 5 [0xaaaaaaaa,0xfcecfcec,0xfff0fff0,0xfffffca8] 3 (replayWords [0xc21422840c2,0x610612420c4062,0x622211240c00c0,0xc21211200c2121,0xc20700708000c4]) [(42,54)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfff8fff8,0xfffffac8] 3 (replayWords [0xa10c21840a1,0xc40c42421440a4,0x1242210a40d00a1,0x1420a10a00a00a1,0x1420a41448000a4]) [(42,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfac8fac8,0xfff0fff0,0xfffffac8] 4 (replayWords [0xa12212840a1184,0x144221,0x2421440a4220221,0xa41900a18050a1,0x1400a11420a10a0,0xa00a1142144804,0x8031440a4802801,0xa40a41448000a4]) [(43,39),(73,11),(69,15),(73,6),(69,35),(74,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffeefaea,0xffffff00] 4 (replayWords [0x1211421211420a1,0x1212840a1061121,0x142061121142121,0x1420c20a10a1288,0xc4061061148062,0x610a1,0x8000610a12880a1,0x288061148061148]) [(44,0)],
  row 5 [0xa222a,0xcccccccc,0xfff0fcf0,0xffffff00] 3 (replayWords [0xa11211840a1,0x61121242061062,0x1201210620610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 5 [0xa222a,0xcccccccc,0xf0f0f0f0,0xfff0ccc0,0xffffff00] 4 (replayWords [0x1421213081210a1,0x1211840a1061121,0x242061062120121,0x620a10c28030a1,0x610c4802061000,0x8010000610a1,0x8000610620a00a1,0x620600600610a4]) [(45,0),(22,55),(77,56),(77,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffaacc88,0xffffff88] 4 (replayWords [0x1420000000000a1,0x1211840a10c4121,0x2420c40a4120121,0xa40a13088010a1,0xc41484320c40a4,0x2284020a40c00a1,0xc20a10a00a00a1,0xc20a40c48000a4]) [(47,48),(74,36)],
  row 5 [0xa505a,0xcccccccc,0xff00ff00,0xfff0aaa0,0xffff0000] 4 (replayWords [0xa02210b00a0142,0x221800142061221,0x242061062220221,0x621200a00a80a0,0x610a00a2061000,0xa1000061140,0x142061062142181,0x62060060061148]) [(48,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffaacc88,0xffffff00] 5 (replayWords [0x80d437142121308,0x12180c308308121,0x4251211840a10a1,0x121188121184188,0x1841210a10a1242,0xc40c4121248121,0x2422482421210c4,0xc41210a40a4184,0x128120121128121,0x1840a40a480b0a1,0xa130880a308809,0x8088073080a10a1,0x4360c4061308806,0x61434435434308,0xc40c442c0a4062,0x30880506242c433,0x42c3080a40a40c2,0x2480c00a10c40a1,0xc20c40c20a1248,0xa10a11280a00c2,0xa40a00a10a40a1,0xc21280c28040a4,0xa40c48030c4802,0x8018000c40a40a4]) [(49,57),(65,58),(65,47),(67,52),(67,55),(71,47),(71,58),(72,36),(75,36),(76,28),(78,59),(61,60),(79,0),(80,7)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfafafafa,0xfff0fff0,0xfffffac8] 4 (replayWords [0xa11211840a1184,0x188184242061061,0x2421480a4124221,0xa40a11420a1142,0x1400a11420a10a1,0xa40a1142148801,0x1441440a8000000,0xa41488000a4]) [(50,17),(69,35)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffaacc88,0xffaaffaa,0xffffff00] 5 (replayWords [0x121184121242221,0x1213081210a1121,0x1880a10c4121242,0xc4121128121242,0x3100000000000c2,0xa10a10c20c4802,0x2480c40a4000000,0xa13088010a1,0x610614340c4128,0x22842c1280c00a1,0xc20a10a10c20a1,0xc21280c48000c4]) [(51,48),(82,61),(71,58)],
  row 5 [0xee,0xaaaaaaaa,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffffcccc] 5 (replayWords [0x1840613080610a1,0x610c2061061148,0x61284061062061,0x284061242061221,0xa11801840a1150,0x150801184062184,0x800062000000121,0xa11880a1188,0x620c20a10620a1,0x1880a1188128000,0x438000000,0x62429062222]) [(53,0),(27,62)],
  row 5 [0xeeee,0xee00ee,0xf0f0f0f0,0xffaaffaa,0xffffcccc] 4 (replayWords [0x610620611840a1,0x610c2061061228,0x61121061148061,0x1280c20620a1062,0x62121062142062,0x1200621840a1188,0xa11210a11880a1,0x128121242121128]) [],
  row 5 [0xeeee,0xeeeeeeee,0xf0f0f0f0,0xfafafafa,0xff00ff00,0xffffcccc] 5 (replayWords [0x121061142061061,0x620613080a1061,0x284061061240061,0x284061242061221,0x621421210620a1,0x1211840a1121184,0x121184121184121,0x1840c2000000000,0x62230062250062,0x4290622220a1801,0xa12500a18000a1,0x2420a4000000000]) [(53,6),(85,6)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffaaffaa,0xffffcccc,0xfffffff0] 5 (replayWords [0x221121242121121,0x1421212420a1000,0x242121242,0x121121128121242,0x184284308184188,0x290284188061000,0x128228804,0x128184188184290,0x150150803184062,0xd00d0,0x8021880a80a8801,0x128128250800128]) [(37,28),(8,63),(8,14),(23,64),(23,45)],
  row 5 [0xeeee,0xf0f0f0f0,0xfafafafa,0xff00ff00,0xffccffcc,0xffff0000] 5 (replayWords [0x61240250061142,0x284248142062220,0x2300620a1308224,0xa1000000221000,0x121000000000061,0x620612300a1061,0x8020610610c4061,0xa4062122801062,0xa11428000a10a4,0x1481420a40c2000,0x620a4062,0x1480a10a40a1148]) [(40,0),(24,11),(24,6)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffaaffaa,0xffffcccc,0xffffff00] 6 (replayWords [0x24242c221121308,0x121242308242121,0x43912112142e121,0x242310142121310,0x12124243a242813,0xa10a1121188121,0x8121881881210a1,0xa1242811242121,0x250121242250242,0x121439121121810,0x121242128128121,0x12812124243a242,0x30880f30880e310,0x31030831030880d,0x80c80b80a0a10a1,0x3080c20c28090c2,0xc23080a10a143d,0x43c061000000000,0x0,0x43a128128308,0x43a22843a808807,0x3081281288060c2,0xc23100a10a1805,0xa10a13100c20c2,0x439250150310439,0x150439804803310,0x25025043a43b062,0x0,0xc2,0x2500c20a14390a1,0xc28020c20a1250,0xa10a11280a10c2,0x43a0c20a18010a1,0xc21280c243a128,0x12825043a25043a,0x439800250128128]) [(54,28),(56,58),(56,28),(28,65),(57,52),(59,66),(63,67),(28,68),(57,55),(59,0),(63,60),(81,0),(83,66),(83,0),(84,26),(84,32),(86,16),(86,69),(87,0),(88,70)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa,0xfffffffc] 5 (replayWords [0x22124222142b121,0xa1000,0x61000000,0x22123022142b,0x1422423081420c2,0x2422840c20c4250,0x2420c4062000000,0xc21421840c2,0xc41481420c4130,0x1308021420c20c4,0xc21480b00b0801,0xc20700708000c4]) [(9,54),(9,71),(9,59)],
  row 5 [0xee,0xaaaaaaaa,0xf0f0f0f0,0xfcfcfcfc,0xff00ff00,0xffff0000] 5 (replayWords [0x184284308184061,0x2402500610c2308,0x2440c2062220230,0x62000000221000,0x611401480610c2,0x3101440c2062120,0x128062000000121,0xa1000000000,0x61062061128061,0xc40611480620a2,0x8000620c20c40c2,0x4030620a40620c4]) [(10,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xfffff0f0,0xffffff00] 6 (replayWords [0x22122128443f,0x121000000000284,0x29028440980e284,0x80d28406128480c,0x6106228480b062,0x3083103084080a1,0x80a308,0x809308061308808,0x61062308807062,0x19019080629042d,0x310805310061310,0x804061062310803,0x62421290802290,0x61290801061062,0x2908000620c4000,0xa4000000,0x6106200043e]) [(56,72),(56,73),(59,74),(56,75),(56,64),(59,76),(11,0),(87,30),(87,26),(90,20),(91,3),(87,68),(87,47),(90,28),(91,2)],
  row 5 [0xeeee,0xaaaaaaaa,0xf0f0f0f0,0xffccffcc,0xffff00ee] 4 (replayWords [0x142061061121188,0xa10a1142220062,0x62122142221142,0x1480a10610c2061,0x61062061184061,0x1400611840620c2,0xa10620a11880a1,0x148062128062148]) [],
  row 5 [0xaaaaaaaa,0xaaaafefe,0xcccccccc,0xfcfcfcfc,0xff00ff00,0xfffff0f0] 5 (replayWords [0x1210c21840c20a1,0xa10c22210c20c4,0xc22210c22840c2,0x2420620a40a4062,0x1421211421210c4,0x1211420c4121310,0x121284062142121,0x62061000000000,0x441284284290800,0x620622240c4440,0xc42440a4062062,0xa4128000000000]) [(93,77)],
  row 5 [0xeeee,0xaaaaaaaa,0xf0f0f0f0,0xfefefefe,0xff00ff00,0xffffcccc] 5 (replayWords [0x121061142061061,0x2400613080a1061,0xc2061061062061,0x2840610c4061221,0x1213101212500a1,0x1211840a1062142,0x121062121184121,0x184188000000000,0x230000000000442,0x620c2,0xa10620a18000a1,0x2420620a4062222]) [(27,61)],
  row 5 [0xeeee,0xee00ee,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffffcccc] 5 (replayWords [0x1840613080610a1,0x610c2061061062,0x61284061240061,0x284061148061221,0xa11801840a1062,0x184801062000000,0x121000150150800,0x1840620c20a1062,0xa11880a11880a1,0x1880a1188062230,0x62250062128062,0x222443242242250]) [(93,62),(85,0)],
  row 5 [0xeeee,0x33332222,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffffaaaa] 5 (replayWords [0x1420621210620c2,0x620a1062062230,0x62444284000000,0x62221062242,0xa11211840a1121,0x184121184061142,0x121061121184121,0x1840a11880a1188,0x610c20a10610a1,0x1880a1188230061,0x612500c4000000,0x6122106142b]) [],
  row 5 [0xeeee,0xaaaaaaaa,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffffcccc] 6 (replayWords [0x308121121061142,0x61308142142061,0x1210612840a10a1,0x610c20612840c2,0xc20610a1061061,0x447061284250240,0x61250061284445,0x28406180a061284,0x62062061062061,0x284445284061448,0x61284242242061,0x242061284445221,0x1840a10a1121188,0x121184188184121,0xa10a1121250121,0x184809184121808,0x121184250184121,0x62062142445142,0x121807121142062,0x62121242121184,0x806184121805121,0x1842421840a1250,0xa11888041880a1,0x8030a1188250188,0xa10620620c2445,0xc20a18020a10c2,0x620620a12420a1,0x1888011880a1800,0xa1188242188445,0x40b230000000000,0x0,0x447446446000,0x0,0x62242,0x6240b445429062,0x445062445242222]) [(94,28),(84,6),(86,0),(95,0),(96,6),(94,20),(84,0),(86,6),(95,6),(96,0),(97,11)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffeee0] 4 (replayWords [0x1211213081840a1,0xa12841880610c4,0x2420610620a4221,0x62180180184290,0x61150803061062,0x1308020620610d0,0x8010610620b0800,0x62060060061230]) [(22,39),(22,78),(22,45),(22,17)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffeeee,0xfffffff0] 5 (replayWords [0x221284221804121,0xa1000,0x61221242,0x61062230221062,0x184284308184188,0x2902841880c4000,0xa4000000,0x184188184290,0x61150803061062,0x1308020620610d0,0x8010610620b0800,0x62061062061230]) [(23,39),(23,78),(23,45),(23,17),(99,0)],
  row 5 [0xeeee,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xfffcfffc,0xffff0000] 5 (replayWords [0x61240250061142,0x2842481420c2308,0x2440c2062220230,0x62000000221000,0x1210000000000a1,0x61062,0x612300610c4061,0x2500c21421840c2,0x621228010620c4,0x1481420c40620a2,0x8000620c20c40c2,0x1480620a40620c4]) [(24,6),(24,0)],
  row 5 [0xfefe,0xaaaaaaaa,0xcccccccc,0xfefefefe,0xff00ff00,0xfffff0f0] 5 (replayWords [0x1210a11840a10a1,0x2800a13080610a1,0xc20610620a40a1,0x620a12840a1221,0x121310121290061,0x121142061062142,0x121062121310121,0x284250000000000,0x230000000000449,0x61062,0x610a4061801061,0x244062800062224]) [(27,77),(27,52)],
  row 5 [0xeeee,0xaaaaaaaa,0xf0f0f0f0,0xfcfcfcfc,0xff00ff00,0xffffeeee] 5 (replayWords [0x184121121184240,0x610613082840c2,0xc2244220000000,0xc4000000000,0x611211420610c2,0x1211840c2062142,0x121062121184121,0x1840a1000000000,0x61062061230061,0x2420612210620a2,0x8010620c28000c2,0x221062221062230]) [(27,6),(25,6)],
  row 5 [0xaaaa,0xfffc,0xcccccccc,0xf0f0f0f0,0xffaaffaa] 4 (replayWords [0xc21421840c20c4,0x1481420c4142121,0x121220062000000,0xc20c40c2148,0xa10a10c21210a8,0xa82a10c2061061,0xc4121068068261,0xc4121128121221]) [],
  row 5 [0xfefe,0xaaaaaaaa,0xcccccccc,0xff00ff00,0xfff0fff0,0xffff0000] 5 (replayWords [0xa12802900a1184,0x802288184061240,0x250061062220230,0x62000000221000,0x121000000000061,0xa10c20610620a4,0xa10620a11880a1,0x290061144801061,0x62124800062184,0x18818442c061062,0x610a4061148061,0x188062128062188]) [(26,11),(26,0),(104,20)],
  row 5 [0xee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffeeee] 5 (replayWords [0x184284308184188,0xa10a1188148000,0x128000000,0x44a000000000,0xa11801840a1061,0x150801061062130,0x800062000000121,0x610a10c2061,0x620c20a10620a1,0x1880a1188061062,0x61230061242061,0x221062221062230]) [(27,11),(27,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa,0xfffffcfc] 6 (replayWords [0x22180c22142b242,0x24222124222142b,0x44c42b80b121121,0x22114214280a142,0x142221121121450,0x8090a1000000000,0x0,0x44f808061000,0x0,0x221807,0x22142b230230221,0x23022142b44c42b,0x806142142242121,0x121805121121242,0x1421422840c20c2,0x242290242284290,0x2842420c20c2242,0xc40c4284250250,0x2422502422840c4,0xc444c44e062000,0x0,0x1840c2,0xc212144d121184,0x8041841210c20c2,0x1420c40c412144b,0x121142803142121,0xc40c4121230121,0x14244c142121802,0x1211422301420c2,0x2500c22900c40c4,0xc20c40c2290250,0x25044c2300b00c2,0x44c0b044c44d801,0xc22300c244c230,0x700c444c07044c,0x44b8000c42300c4]) [(28,79),(28,44),(59,80),(87,78),(87,20),(100,59),(101,18),(102,43),(103,24),(103,60),(90,0),(105,75),(106,50)],
  row 5 [0xfefe,0xaaaaaaaa,0xcccccccc,0xfafafafa,0xff00ff00,0xfffff0f0] 5 (replayWords [0x1210a11840a10a1,0xc20a13080610a1,0xc40610a10a40a1,0x3080a12840a1221,0x121142121142061,0x1211420610a4142,0x1210a4121310121,0x284250061061250,0x62000000000452,0x2842842900610c4,0x610a4061148061,0x2500a44510a4224]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa,0xffffcccc,0xfffffafa] 6 (replayWords [0x458221221457,0x242000000000142,0x1211211420c2000,0x804250250,0x456455000000000,0x221284221454121,0x1421421210a1221,0x2900a1061000000,0x221230221454,0x142121121142803,0xa100044d802250,0x2504530a4000000,0xa11211840a1,0x142121142121121,0x1421211422500a1,0x8010a10a12900a1,0x230070070800230]) [(29,81),(57,82),(95,41),(103,83),(108,22)],
  row 5 [0xee,0xeeee,0xaaaaaaaa,0xf0f0f0f0,0xffccffcc,0xffff0000] 5 (replayWords [0x612402480610a1,0x2482840a1062220,0x230062000000801,0x800000,0xa10610c2061061,0x62061184061140,0x61184061142061,0x1210620c20a1062,0xa11880a11480a1,0x1880a1142062128,0x62148062230062,0x122459000000000]) [(93,0),(27,0)],
  row 5 [0xaaaaaaaa,0xaaaafefe,0xcccccccc,0xff00ff00,0xfff0fff0,0xffff0000] 5 (replayWords [0xa12212900a1184,0x221288184061221,0x250061188308221,0x188062262221062,0x121000000000061,0xa10c20610a1188,0xa12900620a40a1,0x62061144801061,0x18418818442c062,0x124800062061148,0x61188061062061,0xa4128000000000]) [(60,63),(31,0)],
  row 5 [0xeeee,0xfa00fa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1422843081420a1,0x3082240a1061240,0x250061062220230,0x62000000221000,0xa11421880a1061,0x310122061000000,0x1210000a4120128,0xa40610a1800061,0x620c20a10620a1,0xa40a1128061062,0x612300610c4061,0xa40620a4062128]) [(32,0)],
  row 5 [0xeeee,0xaaaaaaaa,0xf0f0f0f0,0xfcfcfcfc,0xff00ff00,0xffff0000] 6 (replayWords [0x308121121284310,0x284308310308284,0x121121284061061,0x308250240284250,0x250308061061284,0xc20c230845b308,0x28445f2443080c2,0xc245a062062284,0x23022045a230230,0x284062062000000,0x808,0x45e221000000000,0x142061061121807,0x121142806142121,0x610611840c20c2,0x12145b121184805,0x1841210c20c2121,0x6206214245a142,0x121804121142062,0x621210c40c4184,0x803184121802121,0x1840c40c445d40b,0xa1000000000000,0x0,0x61230061250062,0x62061062061250,0x23023006145c061,0x2500c40c40610c4,0x6125045a25045a,0x620620c245a0a2,0x45a45b8010c2062,0x620c24030c2800,0xc40c40c20c40c2,0x45b4034030620c4,0x6223045a0a4062,0x45a0622300c40c4]) [(110,6),(33,6),(111,20),(91,0),(88,11),(63,6),(101,0),(112,11),(103,0)],
  row 5 [0xeeee,0xaaaaaaaa,0xeeeeeeee,0xf0f0f0f0,0xfcfcfcfc,0xff00ff00,0xffff0000] 6 (replayWords [0x121284308121,0x613082840610c2,0x3082840c22c4000,0x804284062284803,0x62000000221000,0x611211420610c2,0x1211840c2121184,0x121184062142121,0x62121184121184,0xa1000000000061,0x25006142a061062,0x6142a06142b061,0x42a0c28020c245b,0x620a28010620c2,0x8000c2409230000,0xc4000000,0x62429062460]) [(84,61),(34,6),(96,61),(86,11),(103,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa,0xffffcccc] 7 (replayWords [0x456221429221448,0x42b242242448221,0x24222144842b448,0x42b817816121121,0x461221142142815,0x814142142461221,0x1211218138120a1,0xa144d2210c20c2,0x8118100c20c244d,0x2210a10a1456462,0x42e061000000000,0x0,0x448,0x22180f22144842b,0x230230448221230,0x22144842b44842b,0x80e80d142142461,0x24212112180c80b,0x121121461242142,0x14280a8090c20c2,0x44d2420a10a1808,0x8070a10a144d242,0xc20c2456242806,0x242456429250250,0x448242250242456,0x429456429448448,0x42e062000000000,0x0,0x461,0x1840a10a144d121,0x188121805184188,0x18444d1210a10a1,0x456142250142456,0x121456121456142,0x804142456121250,0x121448121230121,0x448142448142448,0x121803121448142,0x2301424560c2250,0xc24560a14560a1,0x4560c28020c2456,0xa12500a14480a1,0x2300a14480c2448,0xc24480a18010a1,0x4480c22300c2448,0x448230070448250,0x448070448448456,0x800448250230230]) [(35,54),(89,50),(89,48),(89,39),(89,78),(92,54),(98,25),(107,11),(109,0),(113,83),(114,83),(107,44),(109,6),(113,18),(114,18),(98,29),(107,0),(109,11),(113,60),(114,60),(107,14),(109,10),(113,63),(114,63)],
  row 5 [0xaaaaaaaa,0xaaaafefe,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfffffcfc] 5 (replayWords [0x1211421421210a1,0x61000,0x221242221,0x308221062062308,0xc21211840c20c4,0x1211420c4121310,0x121242062142121,0x620c20c40c2250,0xc22840c2242062,0xa40a40620c4242,0xc42500a4062062,0xa4128000000000]) [],
  row 5 [0xeeee,0x33332222,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffffeeee] 5 (replayWords [0x184121121184188,0xa10a1188260000,0x284000000,0xc4000000000,0xa11211840a1062,0x142121062061142,0x121061121184121,0x1840620c20a1062,0x610c20a10610a1,0x1880a1188230061,0x61062062221062,0x230061221061242]) [],
  row 5 [0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffeeee] 6 (replayWords [0x308184184284121,0x121308121121284,0x184184284188188,0x3080a10a12840a1,0xa1308188188463,0x809240000000000,0x0,0x445808220000,0x0,0x42a448,0x42b000000000000,0x0,0x1840a10a1121188,0x121184188184121,0xa10a1142061061,0x121444121142807,0x142121061061121,0x62062142445142,0x121806121142062,0x62121221121184,0x805184121804121,0x1842211840c2061,0x610a14440a10c2,0x8030c20a1061061,0xa10620620c2445,0xc20a18020a10c2,0x620620a12210a1,0x1888011880a1800,0xa1188221188061,0x230061250062062,0x61062061250230,0x230061221061250,0x242242061242061,0x250221221062242,0x62230221221062,0x221062230242230]) [(116,28),(106,6),(103,11),(103,0),(116,20),(106,0),(103,10),(103,6),(117,11),(117,0)],
  row 5 [0xfefe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00fe00] 4 (replayWords [0xa11211840a1061,0x121142061062142,0x121062121300121,0x2210610a10c2061,0x620a40a10620a1,0x2800a1221061062,0x610a4061240061,0x221062220062220]) [],
  row 5 [0xfefe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfffffefe] 5 (replayWords [0x300121121800280,0x240000,0x220000000,0x42b000000000,0xa11211840a1061,0x121142061062142,0x121062121310121,0x2210610a10c2061,0x620a40a10620a1,0x2840a1221061062,0x610a4061242061,0x221062221062230]) [(119,0)],
  row 5 [0xfffe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 4 (replayWords [0xa11211840a1061,0x121142061062128,0x121062121300121,0x2210610a10c2061,0x620a40a10620a1,0x2800a1221061062,0x610a4061240061,0x221062220062220]) [],
  row 5 [0xaaaaaaa8,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xfffffffc] 5 (replayWords [0x804000000000803,0x802000,0x801000000,0x800000000000,0x1422423081420c2,0x2422840c20c4250,0x2420c4062230230,0x620c21421840c2,0xc41481420c4062,0x1281280620c20c4,0xc21480620a40a4,0x620a40620620a4]) [(121,19),(119,1),(119,70),(119,8),(119,80)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xfffffffe] 5 (replayWords [0x804000000000803,0x802000,0x801000000,0x800000000000,0x1212213081210a1,0x2212840a1061221,0x242061062230221,0x620a11211840a1,0x61121142061062,0x1281210620610a1,0xc20610620a40a1,0x620610620610a4]) [(121,19),(121,1),(121,84),(121,85),(121,0)],
  row 5 [0xfffe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 5 (replayWords [0x1840a10a1121188,0x121184188184121,0xa10a1142061061,0x121148121142148,0x142121061061121,0x62062142128128,0x121128121142062,0x62121221121300,0x308300121308121,0x3002212210c2061,0x610a10c40a10c2,0xc40c20a1061061,0xa10620620c20a4,0xa40a10a40a10c2,0x620620a12210a1,0x2802842800a1284,0xa1280221221061,0xa40610c4062062,0x610620610c40a4,0xa4061221061240,0x242240061242061,0x240221221062242,0x62220221220062,0x221062220242220]) [],
  row 5 [0xfffe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1213003101210a1,0x2802900a1061240,0x250061062220230,0x62000000221000,0xa11211840a1061,0x121142061062128,0x121062121310121,0x3100610a10c2061,0x620a40a10620a1,0x2900a1290061062,0x610a4061250061,0x250062230062230]) [],
  row 5 [0xfffe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfffefffe] 5 (replayWords [0x300000000000280,0x240000,0x220000000,0x42e000000000,0xa11211840a1061,0x121142061062128,0x121062121308121,0x2210610a10c2061,0x620a40a10620a1,0x2840a1221061062,0x610a4061242061,0x221062221062242]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfffefffe,0xffff0000] 6 (replayWords [0x22142e22180c80b,0x80a221809221808,0x42e42e308121121,0x22146a221308807,0x308221121121284,0xa10a1221469221,0x2848062842210a1,0xa1242061061221,0x468221242805242,0x221061061221062,0x62242464242221,0x804221242062062,0x467803310000000,0x0,0x466802290,0x0,0x465,0x801250000000000,0x0,0x464800230000,0x0,0x1840a1,0xa1121188121184,0x1881841210a10a1,0x142061061121148,0x121142148142121,0x61061121062062,0x142128128121128,0x1211420620620c2,0x610610a10c40a1,0xc20c40c20a1061,0x610a10620620c2,0xa40a40a10a40a1,0xc20620620610a4,0x610c4062062061,0x620610c40a40a4]) [(120,27),(120,31),(120,74),(120,62),(90,19),(90,1),(90,84),(90,85),(122,85),(123,0),(124,0),(125,0),(126,0)],
  row 5 [0xfefe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffeeee] 5 (replayWords [0x184121121184280,0xa10a13080c4000,0xa4000000,0x42b221221284,0xa11211840a1061,0x121142061062142,0x121062121310121,0x2210610a10c2061,0x620c20a10620a1,0x1880a1221061062,0x61230061242061,0x221062221062230]) [],
  row 5 [0xfffe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfefefefe,0xff00ff00] 5 (replayWords [0x1213001213000a1,0x1211840a1061121,0x142061062142121,0x62121300121221,0x188000000000148,0x128000,0x308221221,0x3080610a10c2061,0x620a40a10620a1,0x2840a1221061062,0x610a4061242061,0x221062221062242]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfefefefe,0xff00ff00,0xfffefffe,0xffff0000] 6 (replayWords [0x22180422146c,0x121221308121221,0x3082213080a1221,0x2840a1061221242,0x61062242221062,0x31000000000046b,0x803000,0x802000000,0x801000000000,0x12180000046a0a1,0x1211840a1061121,0x142061062142121,0x62188000000000,0x148000000000128,0x610a1,0xc20610620a40a1,0x620610620610a4]) [(120,62),(128,86),(128,87),(128,61),(129,0)],
  row 5 [0xaaaaaaaa,0xaaaafffe,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213101210a1,0x2212900a1061221,0x250061221800221,0x242062262221062,0xa11211840a1061,0x121142061121310,0x121310062128121,0x620610a10c2061,0xa12900a1290062,0xa40a1062061250,0x61250061062061,0xa4230000000000]) [(121,0)],
  row 5 [0xfe,0xaaaaaaaa,0xcccccccc,0xfff0f0f0] 3 (replayWords [0x610a10c2061,0x620a40a10620a1,0x1800a1121061062,0x610a4061140061,0x121062120062120]) [],
  row 5 [0xfe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff000000] 4 (replayWords [0xa13008020a1061,0x300801061062300,0x800062000000321,0x610a10c2061,0x620a40a10620a1,0x1800a1121061062,0x610a4061140061,0x121062120062120]) [(132,59),(132,28),(132,0)],
  row 5 [0xfe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x3003003088000a1,0x2802900a1061240,0x250061062220230,0x62000000221000,0xa11801880a1061,0x140148061062120,0x128062000000121,0x610a10c2061,0x620a40a10620a1,0x1880a1188061062,0x610a4061148061,0x148062128062128]) [(133,0)],
  row 5 [0xaaaa,0xfffc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 5 (replayWords [0xc21421840c20c4,0x1481420c4220142,0x803142121121142,0x242221142321142,0xc20c40c2148220,0xc28020c20a10a1,0xc22422210c22a1,0xc22200c48010c4,0x610610c4240221,0xc42610c4242220,0x262220062000000,0x221242800221]) [(121,0),(104,26),(104,14),(104,0)],
  row 5 [0xfefe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (replayWords [0x308121121806310,0x30030831030846c,0x12112145b0a10a1,0x30829028045b290,0x2903080a10a1474,0x61061308250240,0x474250250308061,0x6146d062062308,0x23022046d230230,0x308062062000000,0x805,0x44c221000000000,0x1840a10a112145b,0x121184804184121,0xa10a1142061061,0x121474121142803,0x142121061061121,0x6206214246d142,0x121802121142062,0x6212142c121310,0x801310121800121,0x31042c3100c2061,0x610a10c40a10c2,0xc40c20a1061061,0xa10620620c20a4,0xa40a10a40a10c2,0x620620a14730a1,0x2904721880a1471,0xa1290470290061,0xa40610c4062062,0x610620610c40a4,0xa406146f061250,0x45814806146e061,0x25042a25006242b,0x6223046d128062,0x46d06223042b230]) [(131,20),(134,0),(105,59),(105,28),(105,0),(120,0),(135,20)],
  row 5 [0xfefe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfefefefe,0xff00ff00,0xffff0000] 6 (replayWords [0x121300308121,0x46c0008063080a1,0x3088050a1061308,0x804061062308803,0x62000000221000,0x1213101213100a1,0x1211840a1061121,0x142061062142121,0x62121310121310,0x290000000000250,0x230000,0x476000000,0x610a10c2061,0x620a40a10620a1,0x8020a1475061062,0x610a4061801061,0x45a062800062460]) [(106,86),(106,87),(106,61),(102,59),(102,28),(102,0),(120,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfffefe00] 3 (replayWords [0xa11211840a1,0x61121142061062,0x1201210620610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 5 [0x88888888,0xeeeeeee0,0xf0f0f0f0,0xff00ff00,0xffff0000] 4 (replayWords [0x184284308184188,0x2802841880a4220,0x2300a4060284070,0x60180180184290,0xa41201280a4060,0x1840680600a00a0,0xa4128060188064,0x600600a4800060]) [(138,1)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeeeee0,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x184284308184188,0x280284188221221,0x809284061284808,0x61062284807062,0x180180184290121,0x121806184061184,0x805061062184804,0x620a10a1803188,0x61188802061062,0x1888010620610c4,0x42b0610620a4429,0x62060060061800]) [(139,0),(58,35),(58,12),(99,84),(58,32),(58,15),(99,88),(58,30),(58,26),(99,0)],
  row 5 [0xe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x184284308184188,0x280284188061240,0x250061062220230,0x62000000221000,0x180180184290061,0x140148061062120,0x128062000000121,0x610c00c4061,0x620a00a4062000,0xa1000061062,0x610a40610c4061,0xc40620a40620a4]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000,0xfffffff0] 6 (replayWords [0x221000000000,0x1210000000000a1,0x80e80d,0x80c80b06142980a,0x6106242b809062,0x184284308184188,0x29028418842f284,0x808284061284807,0x61062284806062,0x18418818429042d,0x184805184061184,0x804061062184803,0x62421188802188,0x61188801061062,0x1888000620c4000,0xa4000000,0x61062000477]) [(59,35),(59,12),(100,84),(59,32),(59,15),(100,88),(59,30),(59,26),(100,0),(90,29),(90,25),(140,0),(123,0),(141,0),(134,1)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfefefefe,0xff00ff00,0xffff0000] 7 (replayWords [0x46c30812112146a,0x221310221811308,0x31030846a221121,0x12146c22142e221,0x81030880f30880e,0x22180d22146c308,0x42e3084092840a1,0xa1409221409221,0x40928480c284409,0x2210a10a1478242,0x61061478221478,0x22147824280b242,0x478221061061460,0x221062062460242,0x46024246022180a,0x221460242062062,0x46a12142c121809,0x310808310807121,0x80612146a31042c,0x3104091840a10a1,0x409121409121409,0x184805184409121,0xa10a1478142061,0x61478121478121,0x478142804142478,0x121061061460121,0x62062460142460,0x142460121803121,0x460142062062409,0x47a802188000000,0x0,0x0,0x478479801148000,0x0,0x0,0x460460800128,0x0,0x0,0x4780c2061,0x614780a10c40a1,0x4600c20c40c2478,0xa10610614600a1,0x620624600c20a4,0xa44600a10a40a1,0x4600c2062062460,0x610a40614600c4,0x62062460061062,0x614600c40a40a4]) [(118,43),(118,49),(118,34),(107,27),(107,31),(107,74),(127,0),(130,0),(136,62),(137,62),(107,13),(107,33),(107,89),(127,85),(130,62),(136,0),(137,0),(142,84)],
  row 5 [0xeeee,0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffffeeee] 6 (replayWords [0x184121121184,0x1880a10a1188463,0x463000,0x47b000000,0x42b000000000,0xa11211840a1121,0x184121184061121,0x142061062142121,0x62121184121184,0xa11880a1188061,0xa10c20610620c2,0xa10620a11880a1,0x188250000000000,0x230000000000446,0x61062,0x445061242061,0x221062221062242]) [],
  row 5 [0xeeee,0x33332222,0xaaaaaaaa,0xf0f0f0f0,0xff00ff00,0xffffcccc] 5 (replayWords [0x1211421421210a1,0xc20c20a1260062,0x62240284240061,0x610c40c4221221,0xa11211840a1062,0x142121062121142,0x121142121184121,0x1840620c20a1062,0xa10c20a10c20a1,0x1880a1188230062,0x230062062230062,0x230242250456242]) [],
  row 5 [0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffaaaa,0xffffeeee] 6 (replayWords [0x284000000000,0x184121121184188,0xa10a1188463000,0x801000000,0x42b000000000,0x1421211211420c2,0xa10a10c2800061,0x444062000000,0x448221000242,0xa11211840a1061,0x121142061121142,0x121142121184121,0x1840610a10c2061,0xa10c20a10c20a1,0x1880a1188061250,0x61230061250061,0x221448221221230]) [(117,0),(145,11)],
  row 5 [0xeaeaeaea,0xfffcfffc,0xfffffcfc,0xffffff00] 3 (replayWords [0x142148142802,0x121121142801062,0x128128062061061,0x148800128062062,0x128170062062150]) [(0,0),(16,0),(16,62)],
  row 5 [0xaaaaaaaa,0xfffcfccc,0xfffffff0] 2 (replayWords [0x610a1,0xc20610620a00a1,0x620600600610a4]) [],
  row 5 [0xaaaaaaaa,0xfffcfcfc,0xffffffcc,0xfffffff0] 3 (replayWords [0xc20c40c2802,0xa10a10c2801062,0xa40a4062061061,0xc48000a4062062,0xa40e80620620c8]) [(148,0),(148,17),(46,0)],
  row 5 [0x88888888,0xf0f0f0f0,0xffeeffee,0xffffeeee,0xffffff00] 4 (replayWords [0x121128121400121,0x13012147c0a1121,0x1880a1061121801,0x610a40a4128400,0x1880a10a1128168,0x1b00a1,0xa1130170000000,0x610a1800061]) [(147,28),(149,3)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffeeffee,0xffffeeee,0xffffff00] 5 (replayWords [0x121284121408121,0x1841214470a1121,0x1880a1061121142,0x61062142121062,0x308310308408188,0xa10a1188148000,0x128000000,0x2900a10a1290,0x150000000000130,0x610a1,0xc20610620c20a1,0x62061062061800]) [(150,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfefefefe,0xff00ff00,0xffeeffee,0xffff0000] 6 (replayWords [0x221284221284,0x121221308121221,0x3082213080a1221,0x2840a1061221242,0x61062242221062,0x18400000000046b,0x47f46447e8020a1,0xa14090c4000000,0xa4000000000,0x1218011214080a1,0x1218000a1061121,0x142061062142121,0x62188000000000,0x148000000000128,0x610a1,0xc20610620c20a1,0x6206106206147d]) [(151,4),(128,62),(128,61)],
  row 5 [0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfefefefe,0xff00ff00,0xffff0000] 6 (replayWords [0x121284308121,0x2843082843080a1,0x3082840a1061284,0x802061062284801,0x62000000221000,0x1213101213100a1,0x1211840a1061121,0x142061062142121,0x62121184121184,0x188000000000250,0x230000,0x449000000,0x610a10c2061,0x620c20a10620a1,0x8000a1409061062,0x6145a0610c4061,0x45a0620a4062460]) [(106,61),(95,11),(95,0)],
  row 5 [0xaaaaaaaa,0xfffcfeec,0xfffffff0] 2 (replayWords [0x610a1,0xc20610620a2221,0x620600600610c4]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfff0faa0,0xfffffff0] 3 (replayWords [0xa1000000000,0x610c00c2061062,0xc2221062061184,0x8010610620a4800,0x620600600610c4]) [(148,11),(154,0)],
  row 5 [0xeaeaeaea,0xfffcffa8,0xfffffcfc] 2 (replayWords [0x61061,0x1420c10680680c1,0x1280620621210c2]) [],
  row 5 [0xaaaaaaaa,0xfcccfccc,0xfff0ccc0,0xfffffff0] 3 (replayWords [0xc2000000000,0x610a1182061062,0xa00a10620610c4,0x801061062284800,0x620600600610a4]) [(156,30),(148,0)],
  row 5 [0xaaaaaaaa,0xeee0eee0,0xfffcfffc,0xfffff000] 3 (replayWords [0x61180182061,0xc21828010c2062,0x1822210620a1000,0x60060061,0x1900620a2800062]) [(16,1),(154,25)],
  row 5 [0x88888888,0xf0f0f0f0,0xffeeffe0,0xffffeeee] 3 (replayWords [0xa40a4121184,0xa80a8281128060,0xa10a1,0x184121061121801,0x61061188800061]) [(156,28),(154,79)],
  row 5 [0x88888888,0xeee0eee0,0xf0f0f0f0,0xffeeffee,0xffff0000] 4 (replayWords [0x184220221184181,0x221284181121221,0x803121061221802,0x61180180181230,0xa4000000000060,0xa10a1,0x400121061181801,0x61061121800061]) [(155,90),(157,88),(158,79),(159,62)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffeeffe0,0xffffeeee] 4 (replayWords [0x184121121184188,0x280284188148000,0x128000000,0xa10a1184121,0x61121142061062,0x130121062061188,0x282061062188281,0x62061062061800]) [(159,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeee0eee0,0xf0f0f0f0,0xffeeffee,0xffff0000] 5 (replayWords [0x184284221184188,0x221284188121221,0x801121061221242,0x61062228221062,0x180180184290480,0x250000,0x230000000,0xa10a1408121,0x61188182061062,0x188181062061121,0x142061062128121,0x62061062061800]) [(160,0),(161,62)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffffeeee,0xfffff0f0] 6 (replayWords [0x221284221457,0x1211841841210a1,0x221804,0x221803061221242,0x61062242221062,0x184121121184284,0x290284409484000,0x484000000,0x483000000000,0x184121184121121,0x184121184061121,0x142061062142121,0x62482290802290,0x61290801061062,0x290800062250000,0x230000000,0x61062000481]) [(57,44),(57,14),(151,6),(162,62),(106,6)],
  row 5 [0xffe,0xaaaaaaaa,0xcccccccc,0xfff0fff0] 3 (replayWords [0x610a10c2061,0x620a40a10620a1,0x1800a1180061062,0x610a4061240061,0x184062220062184]) [],
  row 5 [0xfffe,0xaaaaaaaa,0xfcccfccc,0xfff0fff0] 3 (replayWords [0x610a10c2061,0x620a40a10620a1,0x2800a1221061062,0x610a4061240061,0x221062220062220]) [],
  row 5 [0xfffe,0x88888888,0xeeeeeeee,0xf0f0f0f0,0xff00ff00] 4 (replayWords [0xa11211840a10a4,0x1281210a4061121,0x802061121300121,0x2210a10a40a1128,0x610a18010610a1,0x2800a12210e4000,0xa42200a4,0x220061800061221]) [(164,54),(165,54),(165,79)],
  row 5 [0xfffe,0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00] 5 (replayWords [0xa11211840a1121,0x184121184061121,0x142061062142121,0x62121300121221,0xa11880a1188061,0xa10c20610620c2,0xa10620a12800a1,0x2210c4000000000,0xa4000000000284,0x221221284061062,0x800061242061,0x221062221062242]) [(166,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xfffefffe,0xffff0000] 6 (replayWords [0x221800221447,0x1212213081210a1,0x2212840a1221284,0x221284061221242,0x61062242221062,0x310000000000290,0x465000,0x465000000,0x485000000000,0xa11211840a1121,0x184121184061121,0x142061062142121,0x620a11880a1188,0x610a10c2061062,0xc20a10620c4000,0xa4000000,0x61062000464]) [(167,0)],
  row 5 [0xfefe,0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (replayWords [0x121300308121,0xa12802900a146c,0x308802308061308,0x801061062308800,0x62000000221000,0xa11211840a1121,0x184121184061121,0x142061062142121,0x62121310121310,0xa12900a1290061,0xa10c20610620c2,0xa10620a11880a1,0x2900c4000000000,0xa400000000046f,0x45846e42a061062,0x46d061458061,0x42a06248606242b]) [(108,45),(108,17),(128,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xfefefefe,0xff00ff00,0xffff0000] 7 (replayWords [0x308121,0x121221310221308,0x310308221121121,0x221447221308811,0x308221810221308,0x4473082840a10a1,0x22140922128480f,0x2842210a10a1221,0x46c22128480e284,0x22180d22128446c,0x284242061061221,0x47822124280c242,0x221061061221062,0x62242460242221,0x80b221242062062,0x12140812131080a,0x310121809121310,0x4083101840a10a1,0x121409121184808,0x1841210a10a1121,0x46a121184807184,0x12180612118446a,0x184142061061121,0x478121142805142,0x121061061121062,0x62142460142121,0x804121142062062,0x47a801188000000,0x0,0x479409479,0x0,0x479,0x803479000000000,0x0,0x460802487000,0x0,0xa1409,0xa1801409800000,0x409409409,0xc20610610a1478,0xa10c24600c20a1,0x610610a1062062,0xc24600c20a1478,0xa10c2062062460,0x4600c4000000000,0x0,0x4604780a4000,0x0,0x61478,0x61460062062000,0x460460460]) [(118,34),(144,34),(146,55),(146,22),(109,53),(109,51),(152,0),(153,62),(163,61),(168,0),(169,62),(109,46),(109,41),(152,4),(153,0),(163,34),(168,4),(169,0)],
  row 5 [0xee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff00ee] 5 (replayWords [0x184284308184188,0xa10a1188148061,0x61148128062062,0x12842b000000000,0xa11801840a1061,0x140148061062120,0x128062000000321,0x610a10c2061,0x620c20a10620a1,0x1880a1188061062,0x61128061148061,0x148062128062128]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff00ee,0xfffff0f0] 5 (replayWords [0x221284221403321,0x1841842210a1000,0x61221242,0x61062230221062,0x184284121121284,0x2902844030c4061,0x611480a4062062,0x128184310184290,0x61140148061062,0x1201280620610d0,0x8010610620b0800,0x62061062061128]) [(60,91),(60,82)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeefffe,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213101210a1,0x2212900a1221800,0x221284061221242,0x61062242221062,0xa11211840a1121,0x310121310061121,0x142061062128121,0x620a12900a1290,0x610a10c2061062,0xa40a1062250000,0x230000000,0x610620610a4]) [(121,0)],
  row 5 [0xaafe,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1213003081210a1,0x2802900a1061240,0x250061062220230,0x62000000221000,0xa11211880a1061,0x121148061062162,0x121062121310121,0x1420610a10c2061,0x620a40a10620a1,0x1880a1188061062,0x610a4061148061,0x148062128062230]) [],
  row 5 [0xaaaaaaaa,0xaaaafefe,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (replayWords [0x308121121221310,0x221308310308221,0x1211214890a10a1,0x221290221489290,0x2902210a10a1488,0x61061221250221,0x488250250221061,0x6122142b221308,0x46d30822144c221,0x30842b242221062,0x6230846d262221,0x46c221308062062,0x1840a10a1121489,0x121184805184121,0xa10a1142061061,0x121488121142804,0x142121061061121,0x42c121310803310,0x12180212131042c,0x310121062062142,0x46d142121801121,0x1420620620c2061,0x610a10c40a10c2,0xc40c20a1061061,0xa14730a1290472,0x1880a14710a1290,0x4702900a1062062,0xc20a40a40a10a4,0xa10c2062062061,0x46f061250458148,0x6146e06125042a,0x2500610a40610c4,0x62062061062061,0xc40a40a446d800,0x128000000000000,0x0]) [(171,86),(172,86),(173,20),(174,62),(111,17),(111,0)],
  row 5 [0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xf0f0fefe,0xff00ff00,0xffff0000] 6 (replayWords [0x121284308121,0x2843082843080a1,0x3082840a1061240,0x250061062220230,0x62000000801000,0x1213101213100a1,0x1211840a1061121,0x142061062142121,0x62121184121184,0x188000000000250,0x61061250230062,0x6223048a000000,0x610a10c2061,0x620c20a10620a1,0x80000045b061062,0x612300610c4061,0x2500620a4062230]) [(171,61),(116,28)],
  row 5 [0xaaaaaaaa,0xaaaaaafe,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210a1,0x2212900a1061221,0x250061221308221,0x242062262221062,0xa11211880a1061,0x121148061121310,0x121142062162121,0x620610a10c2061,0xa11880a1188062,0xa40a1062061148,0x61148061062061,0xa4128000000000]) [],
  row 5 [0xee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (replayWords [0x308184184284310,0x284308310308284,0x1841842840a10a1,0x308290280284290,0x2843080a10a148d,0x61061284250240,0x48d250250284061,0x6148b062062284,0x23022048b230230,0x284062062000000,0x805,0x48f221000000000,0x1840a10a1310188,0x180184188184310,0xa10a148d061061,0x18414814048d148,0x14818406106148b,0x62062184128120,0x48b128128184062,0x62000000000000,0x80448e121,0xc2061,0x610a148d0a10c2,0x8030c20a1061061,0xa10620620c248b,0xc20a18020a10c2,0x620620a14030a1,0x1888011880a1800,0xa1188403188061,0x128061148062062,0x61062061148128,0x12806148c061148,0x42b0c406142b061,0x14848b14806242b,0x6212848b0a4062,0x48b06212842b128]) [(177,28),(141,0),(91,11),(91,0),(171,62),(171,0)],
  row 5 [0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff00ee] 5 (replayWords [0x184284121121188,0xa10a1188240061,0x61284220062062,0x28442b221221284,0xa11801840a1061,0x184801061062184,0x800062221184321,0x1840610a10c2061,0x620c20a10620a1,0x1880a1188061062,0x61230061148061,0x221062128062230]) [(93,11),(93,0)],
  row 5 [0xee,0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (replayWords [0x184284308184,0xa12802840a1061,0x240250061062220,0x230062000000804,0x803000,0xa11801840a1061,0x184802061062184,0x801062491000800,0x184000000121000,0x610a10c2061062,0xc20a10620a1188,0xa11880a11880a1,0x188061062061230,0x61148061250061,0x250061250062128,0x62230062230062,0x230490000000000]) [(171,62),(110,11),(110,0),(179,0),(106,0)],
  row 5 [0xeee0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x184221308184188,0x221284188061221,0x242061062220221,0x62000000804000,0x180180184290061,0x184803061062184,0x802062121121403,0x184061188801061,0x621888000620a1,0xa142c188060060,0x612300c406142b,0x610a4062429062]) [(61,80),(61,54),(61,11),(61,0),(99,0)],
  row 5 [0xa8a8a8fc,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 5 (replayWords [0x1212213081210c2,0x2212900c20c4221,0x2500c4062220221,0x6242b221242221,0xc21211880c20c4,0x1211480c4062120,0x12106242b121142,0x1210c20c40c2148,0x620a40a40620a1,0xa10c21880a4062,0x620a40610610c4,0x148062128062128]) [],
  row 5 [0xeeee,0xfff0,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00] 5 (replayWords [0x184188184280061,0x184804061062184,0x803062121121184,0x284221184321184,0x61188802061062,0x1888010620a10a1,0x1882802211882a1,0x188061062061220,0x2840612c4061061,0xc4061221284062,0x2a40620620a4062,0x220221284800221]) [(121,0),(62,80),(62,54),(62,11),(62,0)],
  row 5 [0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 6 (replayWords [0x28480c284447,0x184284308184188,0x308284188061240,0x250061062220230,0x62000000221000,0x1210000000000a1,0x6140b,0x80b06106242a80a,0x62809808807806,0x18418800045b061,0x184805061062184,0x80406242c184803,0x184061188802061,0x62188801062403,0x188800188061062,0x612300610c4061,0x2500620a4062230]) [(172,61),(63,10),(63,6),(172,62),(63,11),(63,0),(181,0),(173,54),(141,0),(182,1),(101,11),(101,0),(183,0)],
  row 5 [0xeeee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (replayWords [0x447308121121491,0x284310284447308,0x310308491284121,0x1214472840a10a1,0x45b308290280447,0x28429028445b308,0xa10a140b40b061,0x6142a284250240,0x40b40b25025040b,0x28406106142a42a,0x6206242a284230,0x22042a42a230230,0x42a284062062000,0x0,0x44780d448,0x221000000000000,0x4911840a10a145b,0x12118812180c184,0x18818445b1210a1,0xa140b142061061,0x40b12140b12140b,0x14280b14240b121,0x6106142a121062,0x6242a14242a142,0x42a12180a12142a,0x142062062491121,0x42c121809184808,0x184807121806121,0x49118442c18440b,0xc206106140b0a1,0x40b0a140b0c2805,0xc240b0a1061061,0x42a0a106206242a,0xc242a0c242a0a1,0x8040a142a0c2062,0x6245b0a14030a1,0x803188802188801,0xa18000a145b188,0x40318842a061230,0x6142a250062062,0x42a06106206142a,0x25023023040b061,0x46f06142a25042b,0xc442a06142b061,0x42a25042a25042a,0x6242b06242a230,0x42a0a442a06242a,0x6242a23042b230]) [(175,28),(176,0),(178,6),(180,6),(113,11),(113,0),(175,20),(176,6),(178,0),(180,0),(113,10),(113,6),(184,0),(118,0)],
  row 5 [0xaaaaaaaa,0xaaaafefe,0xcccccccc,0xf0f0f0f0,0xfcfcfcfc,0xff00ff00,0xffff0000] 6 (replayWords [0x121221308121,0x46c2218032210c2,0x2218020c20c4221,0x8010c4221308221,0x242062262221062,0x1421211421210c2,0x1211840c20c4121,0x1420c4121310121,0x310062142121062,0xa1000000000061,0x47642b,0x46046d800062062,0x46d0c20c4000488,0xc24920c2475062,0xa40a40620c4440,0xc445a0a4062062,0xa4128000000000]) [(179,86),(94,17),(94,0),(116,0)],
  row 5 [0xee,0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (replayWords [0x184284308184,0xa12802840a1493,0x284805284061284,0x804061062284803,0x62000000221000,0xa11801840a1491,0x184802184061184,0x801061062184800,0x62000000121000,0xa11880a1188061,0xa10c20610620c2,0xa10620a11880a1,0x188148000000000,0x12800000000048c,0x61062,0x48b06142b061,0x48b06242906242b]) [(84,66),(84,62),(106,62),(84,11),(84,0),(106,0)],
  row 5 [0xeeee,0xee00ee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (replayWords [0x184284308184,0xa12802840a1061,0x284805061062284,0x804062447284803,0x284000000221000,0xa11801840a1061,0x184802061062184,0x801062000000121,0x408184800184,0x610a10c2061062,0xc20a10620a1188,0xa11880a11880a1,0x188061062061496,0x61250061496061,0x148061496062230,0x6242a062128062,0x49549449040548b]) [(179,62),(96,66),(96,62),(179,0),(96,11),(96,0)],
  row 5 [0xeeee,0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000] 7 (replayWords [0x308121,0x121284310284308,0x310308284121121,0x2840a10a1308290,0x280284290284308,0xa10a1447447447,0x80c447,0x80f28444728440b,0x6106128442a284,0x40b44780e284061,0x6142a062062284,0x42a28442a44780d,0x284062062000000,0x80c,0x448221000000000,0x1840a10a1121188,0x121184188184121,0xa10a1121491121,0x18480b18412180a,0x121184491184142,0x6106112140b121,0x142809142121061,0x61121062062142,0x42a142121808121,0x142062062121408,0x121184807184121,0x806121184408184,0xa145b0a1188805,0x1880a18040a1188,0x45b1880c2061061,0xa140b0a10c2803,0xc20a10610610a1,0x620620c242a0c2,0xa18020a10c2062,0x620a14090a1188,0x8011880a18000a1,0x18840918842a42a,0x250000000000000,0x0,0x42a40b230000000,0x0,0x44746f46f,0x0,0x61,0x40b06142a062062,0x42a42a,0x42a06146f06142a,0x42b42b06142b061,0x42a42a42a06242b,0x6240b42a429062,0x42a06242a42b42b]) [(186,28),(187,6),(114,11),(114,0),(153,0),(188,6),(186,20),(187,0),(114,10),(114,6),(153,6),(188,0),(144,0),(98,11),(98,0),(118,0)],
  row 5 [0xaaaa,0xcccccccc,0xfffafcf8,0xffffff00] 3 (replayWords [0xa11211840a1,0xc41212420c40a4,0x1201210a4061061,0xc20a10620620a1,0xc20640648000a4]) [(68,11)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffaaffaa,0xffffeee0] 4 (replayWords [0x1211421211840a1,0xa12841210610c4,0x242061121128121,0x242180180184290,0x150061061184062,0x610d0,0x801061800188181,0x181061068061250]) [(190,43),(64,14)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf3f0f3f0,0xfffffca8] 3 (replayWords [0xa10a11840c2,0x610611420c4062,0x622211240c00c0,0xc21210b00b0121,0xc20700708000c4]) [(68,81)],
  row 5 [0xaaaa,0xcccccccc,0xf0f0f0f0,0xffeeffe0,0xffff0000] 4 (replayWords [0x121220228121188,0x228284188061228,0x803061000000802,0xa10a1184121,0x610c4142061062,0xa41210620610c8,0x8010610620a8800,0x62060060061128]) [(192,32),(66,0),(22,75),(190,47)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffeee0] 5 (replayWords [0x308184121221310,0x121308310308221,0x1841842841880a1,0x2212900a1284290,0x284221188188242,0x610612212500c4,0x242250242221061,0x61221062062242,0x2300a4221230221,0x242062062184290,0x180310188180184,0x188184310290290,0x813061061184812,0x15081181080f184,0x6106180e062062,0x18480d13080c80b,0x80a184062062809,0x610611888080d0,0x807806805188061,0x61804062062188,0x8030b0802801800,0x188062062061230,0x60250062060061,0x62061250230230]) [(72,39),(191,92),(191,6),(193,61),(193,93),(72,78),(191,79),(191,10),(193,94),(193,23),(72,45),(191,80),(191,0),(193,62),(193,27),(72,17),(191,54),(191,11),(193,66),(193,31)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xfefefeaa,0xff00ff00,0xffff0000] 5 (replayWords [0x121221308121221,0x2422213080a1221,0x8030a1061221802,0x61221308221308,0x1211421213100a1,0x1218010a1061121,0x800061121310121,0x3100c20a10a10c2,0xc40610610c4062,0x610a1,0xc20610a10c20a1,0xc20610c40610c4]) [(76,41),(76,83),(76,47),(76,6)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xffa8ffa8,0xfffffca8] 4 (replayWords [0x1211423081210c2,0x1882840c20c4148,0x2420c4128220221,0x1280c21218030c2,0xc41218020c4120,0x1201212300c00c0,0xc22501280c2801,0xc21280c48000c4]) [(73,79),(73,44),(74,28),(74,11)],
  row 5 [0xaa,0xcccccccc,0xfefefef0,0xff00ff00,0xffff0000] 4 (replayWords [0x1242243081240a1,0x2202240a1061224,0x803061000000802,0xa11201240a1,0x61124801061000,0x8000000610a1,0xc20610620a00a1,0x620600600610a4]) [(192,35),(69,56),(192,91),(69,17)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeee0eee0,0xf0f0f0f0,0xff00ff00,0xffffeee0] 5 (replayWords [0x184221308184188,0x22128418842e000,0x61221242,0x61062220221062,0x18018018429080b,0x18480a184061184,0x809061062184808,0x62807188806188,0x61188805061062,0x188804062061803,0x802061062801800,0x62060060061230]) [(196,30),(197,4),(196,26),(197,9),(75,39),(75,78),(196,20),(197,81),(75,45),(75,17),(196,28),(197,5)],
  row 5 [0xa222a,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffffccc0] 4 (replayWords [0x1211423081210a1,0xc22840a10610c4,0x242061062220221,0x620a11211840a1,0x61121801061062,0x1201210620610a1,0x8000610620a00a1,0x620600600610a4]) [(77,82),(77,65)],
  row 5 [0xa222a,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xfff0ccc0,0xffff0000] 5 (replayWords [0x284221808221121,0x2218071210a1221,0x8060a1061221242,0x61062220221062,0x1211428051210a1,0xc28040a10610c4,0x803061000000802,0xa11211840a1,0x61121801061062,0x1201210620610a1,0x8000610620a00a1,0x620600600610a4]) [(78,25),(78,41),(99,95),(199,25),(199,82),(199,65),(78,6),(78,0),(199,0)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeee0eee0,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (replayWords [0x308184184221310,0x221308310308221,0x184184284188188,0x221290221284290,0x284221188188808,0x42e42e221807221,0x80680580422142e,0x221242061061221,0x250221242250242,0x221061061221062,0x62242230220221,0x230221242062062,0x184290180310188,0x180184188184310,0x29029049d4a2121,0x1844a112149a4a0,0x4a018449f184497,0x61061184497184,0x49749d803184061,0x61498062062184,0x49818449849d802,0x18406206249a479,0xa118849e0a149d,0x49c49c18849b188,0x497061061188497,0x18849749a801188,0x61061498062062,0x18849818849849a,0x80018806206242b,0x610614994970c4,0x42b49842b498061,0x6149806206242b,0x4980a4498497429,0x42b062062061230,0x60250062060061,0x62061250230230]) [(81,40),(81,96),(81,58),(81,65),(194,0),(195,85),(198,0),(181,0),(200,88)],
  row 5 [0xaaaaaaaa,0xfcccfccc,0xfff0fff0,0xffffeee0] 3 (replayWords [0xa10a1284182,0x610c4242061062,0xa42210620610d0,0x1820610620b0800,0x62060060061184]) [(156,53)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xfff0fff0,0xfffffee0] 3 (replayWords [0xa10a1184221,0x610c4242061062,0xa42210620610d0,0x8010610620b0800,0x62060060061230]) [(154,29),(154,25)],
  row 5 [0x88888888,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffffeee0] 4 (replayWords [0x1211213081840a1,0xa12841880a40a4,0x221284061221804,0x61180180184290,0x130130803184061,0x1848020610b00b0,0x801188061188800,0x61060000000000]) [(202,54),(159,61),(202,79),(159,62),(203,54)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffffeee0] 5 (replayWords [0x1211213081840a1,0xa1284188221284,0x221284061221242,0x61062242221062,0x180180184290808,0x184807184061184,0x806061062184805,0x62804188803188,0x61188802061062,0x188801062250000,0x230000000,0x61062000800]) [(204,0),(82,44),(82,14),(161,61),(197,81),(82,45),(82,17),(161,62),(197,5)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeee0eee0,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000] 6 (replayWords [0x184221308184,0x188221284188221,0x284221284447221,0x806221061221242,0x61062242221062,0x18018018429049d,0x184805184121121,0x4a0184061184804,0x61062184803062,0x49a1888021880a1,0xa149c188061188,0x801061062188800,0x62499000000000,0x250000000000230,0x61499,0x42b06106242b429,0x62061062000498]) [(83,91),(83,82),(162,6),(83,58),(83,65),(162,0),(205,0)],
  row 5 [0xee,0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000,0xffffff00] 6 (replayWords [0x284000000000,0x1840000000000a1,0x1881880a1061148,0x148061062128128,0x620000004a5000,0x3083100004910a1,0x2902900a1061250,0x250061062230230,0x620000004a4000,0xa11881880a1061,0x148148061062128,0x1280620000004a3,0x610a10c2061,0x620c20a10620a1,0x1880a1188061062,0x611280610c4061,0x1480620a4062128]) [],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xfff0fff0,0xffff0000] 7 (replayWords [0x284447,0x28422181f221284,0x81e284221447221,0x308184184221408,0x22130881d308221,0x184184284188188,0x22140922128481c,0x284221188188221,0x42f22128481b284,0x22181a22128442f,0x284242061061221,0x4a7221242819242,0x221061061221062,0x622424a6242221,0x818221242062062,0x4a9409121000000,0x0,0x4a84080a1,0x0,0x817,0x816815814813812,0x81181080f80e80d,0x80c4a7061061429,0x4a74294a780b80a,0x4290610614a6062,0x6242b4a642b4a6,0x80980842b062062,0x184408184409188,0x188000000000409,0x40940940842c42c,0x184408184807408,0x80618442c1844a7,0x610611844a7184,0x4a7408805184061,0x614a6062062184,0x4a61844a6408804,0x184062062409403,0x403188409188803,0x409802188403188,0x4a70610611884a7,0x1884a7409801188,0x610614a6062062,0x1884a61884a6409,0x8001880620624a6,0x4a60c4000000000,0x0,0x4a64a70a4000,0x0,0x614a7,0x614a6062062000,0x4a64a64a6]) [(89,40),(89,96),(107,74),(163,61),(89,58),(89,65),(107,76),(163,62),(107,53),(163,27),(107,51),(163,31),(201,0),(206,54),(206,0),(127,0),(168,54),(168,0),(178,4),(207,4),(187,4),(178,5),(187,5),(207,5),(92,97),(92,5),(142,54),(184,0),(92,34),(92,4),(142,0),(184,54)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xeeeeeeee,0xf0f0f0f0,0xff00ff00,0xffff0000] 8 (replayWords [0x447308121121408,0x221310221814308,0x310308408221121,0x1214472840a10a1,0x409221290221813,0x284290284409221,0xa10a144722142e,0x221812284811284,0x81022180f221447,0x28442e284429242,0x61061429221429,0x22142924280e242,0x42922106106142b,0x22106206242b242,0x42b24242b22180d,0x22142b242062062,0x4081840a10a1409,0x12118812180c184,0x1881844091210a1,0xa140812142c121,0x80b18480a184809,0x121808121408184,0x42c184429142061,0x61429121429121,0x429142807142429,0x12106106142b121,0x6206242b14242b,0x14242b121806121,0x42b142062062409,0xa14030a1805188,0x8041888030a1802,0xa1409188403188,0x4290c2061061429,0xa14290a14290c2,0x8010c24290a1061,0x6142b0a1062062,0x42b0c242b0c242b,0xa18000a142b0c2,0x6206242b42b42b,0xc4000000000000,0x0,0x42b42b,0x4290a4000000000,0x0,0x42b,0x6142906142b42b,0x62062000000000,0x42b42b42b42b]) [(115,43),(115,49),(143,0),(170,0),(185,34),(189,34),(115,40),(115,96),(143,20),(170,6),(185,4),(189,4),(208,0),(115,95),(115,98),(143,85),(170,4),(185,0),(189,0),(208,88),(208,84)],
  row 5 [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000] 9 (replayWords [0x42e30812112142c,0x221310221809308,0x31030842c221121,0x12142e2840a10a1,0x403221290221808,0x284290284403221,0xa10a142e242061,0x61429221250221,0x807242250242429,0x22106106142e221,0x6206242b242230,0x220806221230221,0x42b24206206242c,0x1840a10a1403121,0x188121805184188,0x1844031210a10a1,0x42c142061061429,0x121148121804142,0x148142429121061,0x6142c121062062,0x42b142128120803,0x12112812142b142,0x620624030c2061,0x614290a10c40a1,0x8020c20c40c2429,0xa10610614030a1,0x6206242b0c20a4,0xa08010a10a40a1,0x42b0c2062062429,0x610a406042b0c4,0x62060800061062,0x6142b0c40a40a4]) [(209,0),(209,28),(209,59),(209,20),(209,71),(209,54),(209,85),(209,99),(209,88),(209,84)]
]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def states (i : Nat) := ds[i]?.getD default
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def ms : Array (List (Fin 4)) := #[[],[0,1,2,3,0,1,2,0,1],[1,2,3,0,1,2,0,1],[1,2,3,1,2,0,1],[2,3],[2,3,0,1,2,0,1],[2],[0,1,2,3,1,2,0,1],[0,1,2,3,0,1,0],[2,3,0],[2,0],[0],[1,2,3,1,2],[0,1,2,3,2,0,1,0],[1,2],[1,2,3,1],[0,1,2,3,0,1,2,1,0],[1],[1,2,3],[0,1,2,3,0,1,2,0,1,0],[0,1,2],[1,2,3,0,1,2,0,1,0],[2,3,2,1],[3,1,2,0,1],[1,2,3,2,0,1],[1,2,3,1,2,1],[1,2,1],[3,0,1,2,0,1,0],[0,1],[1,2,3,1,2,1,0],[1,2,1,0],[3,0,1,2,0,1],[1,2,3,1,0],[0,1,2,3,2,0,1],[2,3,2],[1,2,3,1,2,0],[2,3,2,0],[0,1,2,3,0,1,2,1],[0,1,2,3,1,2,0,1,0],[0,1,2,1,0],[2,3,0,1,2,1,0],[1,2,3,2,1],[0,1,2,3,1],[2,3,2,0,1,0],[1,2,0],[1,0],[1,2,3,2,1,0],[2,1],[2,0,1],[2,3,2,0,1],[2,0,1,0],[3,1,2,1],[3,2,1],[3,1,2,1,0],[0,1,2,0,1],[2,3,2,1,0],[3,1],[1,2,3,2,0,1,0],[2,3,1,0],[0,1,0],[1,2,3,2,0],[3,2],[3],[1,2,3,0],[2,3,0,1],[2,3,1],[3,0],[3,1,2],[2,1,0],[1,2,3,0,1,2,1],[0,1,2,3,0,1,2,0],[0,1,2,0],[2,3,0,1,2,0],[2,3,0,1,2],[3,0,1,2],[2,3,0,1,0],[3,0,1],[3,2,1,0],[0,1,2,1],[1,2,0,1],[0,1,2,0,1,0],[2,3,1,2,0,1],[2,3,1,2],[1,2,3,2],[0,1,2,3,0,1,2],[0,1,2,3],[3,2,0,1,0],[3,2,0,1],[0,1,2,3,0,1],[0,1,2,3,2],[1,2,3,0,1],[2,3,1,2,0],[1,2,0,1,0],[3,1,2,0,1,0],[3,2,0],[0,1,2,3,1,2,1,0],[2,3,0,1,2,1],[2,3,0,1,2,0,1,0],[0,1,2,3,1,2,1],[0,1,2,3,0]]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def perm (i : Nat) := permitted (ms[i]?.getD [])
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def specTab : Array Spec := #[(6,[(0,0,1),(1,0,1)]),(4,[(0,0,1),(1,0,1)]),(6,[(0,0,1),(1,3,4)]),(4,[]),(2,[(0,2,3),(2,0,4)]),(0,[(0,2,3),(2,0,4)]),(6,[(0,0,1)]),(4,[(0,0,1)]),(6,[(1,0,1)]),(4,[(1,0,1)]),(4,[(2,0,3)]),(2,[(2,0,3)]),(2,[(0,0,1),(1,0,1)]),(6,[(0,0,2),(1,1,4)]),(4,[(0,0,2),(1,1,4)]),(4,[(0,2,3),(2,0,4)]),(6,[(0,2,3),(2,0,4)]),(2,[(3,0,1),(1,1,3)]),(4,[(1,1,3)]),(8,[(3,0,1),(1,1,2)]),(2,[(1,1,3)]),(8,[(3,0,2),(1,1,2)]),(2,[(0,0,1)]),(2,[(0,0,2),(1,3,4)]),(4,[(1,2,3),(3,0,4)]),(4,[(1,0,2),(1,3,4)]),(6,[(1,0,2)]),(6,[(0,0,3),(1,2,4)]),(6,[(2,0,2),(3,3,4)]),(4,[(1,0,2)]),(4,[(0,0,3),(1,2,4)]),(4,[(2,0,2),(3,3,4)]),(8,[(1,0,2),(1,3,4)]),(4,[(1,2,3)]),(6,[(1,0,2),(1,3,4)]),(6,[(2,0,3)]),(2,[(1,0,2),(2,0,3)]),(6,[(0,0,3)]),(0,[(1,0,2),(2,0,3)]),(6,[(0,1,3)]),(0,[(1,0,2),(1,0,3)]),(2,[]),(0,[(2,0,3)]),(0,[]),(6,[]),(6,[(1,2,3)]),(8,[]),(8,[(1,2,3)]),(4,[(3,0,3),(1,2,3)]),(4,[(0,0,2),(1,3,4)]),(8,[(0,0,1),(1,3,4)]),(6,[(1,1,3),(0,0,4)]),(6,[(0,0,3),(1,1,4)]),(8,[(1,0,3),(0,1,4)]),(6,[(2,0,1),(0,3,4)]),(6,[(3,0,3)]),(2,[(1,2,3),(0,0,4)]),(2,[(1,0,2),(1,2,3)]),(0,[(1,0,3),(1,2,3)]),(6,[(1,1,3)]),(8,[(1,0,3)]),(0,[(3,0,3),(1,2,3)]),(0,[(1,1,3),(1,2,3)]),(0,[(0,1,2),(1,3,4)]),(4,[(2,0,1)]),(4,[(3,0,1),(0,3,4)]),(8,[(1,0,1),(2,2,4)]),(2,[(2,0,2),(0,3,4)]),(2,[(1,0,3),(2,0,3)]),(0,[(1,0,3),(2,0,3)]),(0,[(0,0,3),(1,0,3)]),(8,[(1,0,1)]),(0,[(1,0,3)]),(4,[(1,0,1),(0,3,4)]),(0,[(0,0,2),(1,3,4)]),(2,[(1,0,3),(1,1,3)]),(0,[(1,0,1),(1,3,4)]),(4,[(1,0,3),(1,1,3)]),(8,[(1,1,2)]),(0,[(1,1,3),(3,0,4)]),(0,[(1,0,3),(3,1,4)]),(4,[(3,0,1),(3,3,4)]),(0,[(0,1,3),(1,1,3)]),(2,[(1,0,1),(1,3,4)]),(0,[(1,1,3)]),(8,[(3,0,2)]),(2,[(1,0,3)]),(0,[(0,0,1),(1,3,4)]),(0,[(3,0,1),(3,3,4)]),(2,[(0,0,2),(3,3,4)]),(0,[(1,0,1),(2,0,3)]),(4,[(1,0,1),(3,3,4)]),(4,[(0,1,3)]),(0,[(2,0,1),(2,0,3)]),(0,[(1,0,1),(1,0,3)]),(8,[(1,0,1),(1,1,2)]),(0,[(1,0,1)]),(6,[(1,0,3),(1,1,3)]),(0,[(3,0,3)]),(0,[(2,0,3),(3,0,3)]),(0,[(1,0,1),(1,2,4)]),(0,[(1,1,2),(3,0,4)]),(0,[(1,0,2),(3,1,4)]),(0,[(1,0,1),(3,2,4)]),(2,[(1,0,1),(1,2,4)]),(4,[(1,0,1),(1,2,4)]),(6,[(1,0,1),(1,2,4)]),(0,[(1,0,1),(2,2,4)]),(8,[(1,0,1),(1,2,4)]),(0,[(1,0,1),(3,3,4)]),(0,[(2,1,3),(1,0,4)]),(0,[(0,0,3)]),(0,[(2,1,3)]),(0,[(2,0,3),(1,1,4)]),(0,[(2,0,1),(3,3,4)]),(0,[(0,1,3)]),(2,[(1,0,1),(3,3,4)]),(0,[(1,0,1),(2,1,3)]),(0,[(1,0,1),(0,3,4)]),(0,[(1,1,2),(1,3,4)]),(2,[(1,0,1)]),(0,[(3,0,1)]),(0,[(2,0,1)]),(2,[(2,0,3),(3,0,3)]),(8,[(0,0,1),(1,0,1)]),(0,[(1,0,1),(1,0,2)]),(0,[(0,1,2),(1,0,4)]),(0,[(3,0,1),(3,2,4)]),(6,[(1,0,1),(3,2,4)]),(0,[(1,0,3),(1,1,3)]),(4,[(1,0,1),(1,3,4)]),(2,[(3,0,3),(1,1,3)]),(0,[(3,0,3),(1,1,3)]),(2,[(1,1,2),(3,0,4)]),(2,[(3,0,1),(3,3,4)]),(2,[(3,0,1)]),(2,[(2,1,3),(1,0,4)]),(4,[(2,1,3),(1,0,4)]),(0,[(2,0,3),(2,1,4)]),(0,[(2,0,2),(3,3,4)]),(0,[(1,2,3),(0,0,4)]),(2,[(2,0,2),(3,3,4)]),(0,[(2,0,3),(1,2,4)]),(0,[(2,0,2),(1,3,4)]),(0,[(0,0,2),(3,3,4)]),(6,[(1,0,1),(3,3,4)]),(2,[(2,0,1)]),(8,[(1,0,1),(3,3,4)]),(0,[(2,0,2),(0,3,4)]),(0,[(2,0,2)]),(0,[(2,0,2),(2,0,3)]),(2,[(1,1,2),(0,0,4)]),(0,[(1,1,2),(0,0,4)]),(0,[(2,0,1),(3,2,4)]),(4,[(1,0,1),(0,2,4)]),(0,[(0,0,1)]),(0,[(0,0,2),(1,1,4)]),(6,[(1,0,1),(0,2,4)]),(0,[(2,0,1),(0,2,4)]),(0,[(0,0,2)]),(0,[(0,0,1),(1,2,4)]),(0,[(0,0,1),(3,2,4)]),(0,[(3,0,2)]),(8,[(1,0,1),(1,3,4)]),(6,[(1,0,1),(1,3,4)]),(0,[(1,0,2),(1,3,4)]),(0,[(1,1,2)]),(2,[(1,1,2)]),(0,[(3,1,2)]),(0,[(2,1,2)])]
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
theorem block16 : Good checked 64 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block17 : Good checked 68 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block18 : Good checked 72 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block19 : Good checked 76 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block20 : Good checked 80 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block21 : Good checked 84 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block22 : Good checked 88 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block23 : Good checked 92 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block24 : Good checked 96 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block25 : Good checked 100 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block26 : Good checked 104 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block27 : Good checked 108 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block28 : Good checked 112 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block29 : Good checked 116 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block30 : Good checked 120 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block31 : Good checked 124 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block32 : Good checked 128 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block33 : Good checked 132 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block34 : Good checked 136 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block35 : Good checked 140 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block36 : Good checked 144 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block37 : Good checked 148 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block38 : Good checked 152 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block39 : Good checked 156 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block40 : Good checked 160 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block41 : Good checked 164 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block42 : Good checked 168 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block43 : Good checked 172 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block44 : Good checked 176 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block45 : Good checked 180 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block46 : Good checked 184 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block47 : Good checked 188 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block48 : Good checked 192 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block49 : Good checked 196 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block50 : Good checked 200 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block51 : Good checked 204 4 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem block52 : Good checked 208 3 := checkGood (by decide +kernel)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem total : Good checked 0 211 := (concatGood (concatGood (concatGood (concatGood (concatGood block0 (concatGood block1 block2)) (concatGood block3 (concatGood block4 block5))) (concatGood (concatGood block6 (concatGood block7 block8)) (concatGood (concatGood block9 block10) (concatGood block11 block12)))) (concatGood (concatGood (concatGood block13 (concatGood block14 block15)) (concatGood block16 (concatGood block17 block18))) (concatGood (concatGood block19 (concatGood block20 block21)) (concatGood (concatGood block22 block23) (concatGood block24 block25))))) (concatGood (concatGood (concatGood (concatGood block26 (concatGood block27 block28)) (concatGood block29 (concatGood block30 block31))) (concatGood (concatGood block32 (concatGood block33 block34)) (concatGood (concatGood block35 block36) (concatGood block37 block38)))) (concatGood (concatGood (concatGood block39 (concatGood block40 block41)) (concatGood (concatGood block42 block43) (concatGood block44 block45))) (concatGood (concatGood block46 (concatGood block47 block48)) (concatGood (concatGood block49 block50) (concatGood block51 block52))))))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem impossible : Impossible true target 9 root.toFinset := by
  have h := certified (states:=states) (perm:=perm) (specs:=spec) (N:=211) (fun j => perm_onto _) pri (fun i hi => total i (by omega) hi) 210 (by decide)
  exact h
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def essentials : List (Sig × Row × Row) := [(root.getD 0 zero,2,3),(root.getD 1 zero,1,3),(root.getD 2 zero,1,5),(root.getD 3 zero,1,9),(root.getD 4 zero,1,17)]
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem lower : Lower true root target 10 := by
  apply lower_impossible (L:=9) (by unfold proper; decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro a ha
    apply essential_ok (xs:=essentials) (by decide +kernel) a
    exact (show (essentials.map Prod.fst).toFinset = root.toFinset by decide +kernel).symm ▸ List.mem_toFinset.mpr ha
  · exact impossible

end TabKfive

end PEqualNP.Outside.L_meta_49113.Threshold

namespace PEqualNP.Outside.L_meta_49113

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 6 → Bool
abbrev F := X → Bool

def Cst (f : F) : Prop := ∃ b, f = fun _ => b

def Av (s : Set F) (f : F) : Prop := Cst f ∨ ∃ u ∈ s, f = u ∨ f = fun x => !u x

def comb (t : Bool) (a b : F) : F := fun x => if t then a x && b x else a x || b x

def rs (i : Fin 6) (c : Bool) (f : F) : F := fun x => f (Function.update x i c)

def Ind (i : Fin 6) (f : F) : Prop := ∀ x b, f (Function.update x i b) = f x

def Smp (i : Fin 6) (c : Bool) (f : F) : Prop := Ind i f ∨ Cst (rs i c f)

def LI (i : Fin 6) (f : F) : Prop := Ind i f ∨ ∃ e, f = fun x => xor (x i) e

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

theorem restrict {i : Fin 6} {c : Bool} {s : Set F} {f k} (p : Prog s f k) :
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

theorem strict {i : Fin 6} {c : Bool} {s : Set F} {f k} (p : Prog s f k) (t : Set F)
    (hs : ∀ u ∈ s, Av t (rs i c u)) (hi : ∀ u ∈ s, Smp i c u) (hf : ¬ Smp i c f) :
    ∃ j, j + 1 ≤ k ∧ Prog t (rs i c f) j := by
  obtain ⟨j, hj, q, h⟩ := restrict p t hs
  exact ⟨j, lt_of_le_of_ne hj (fun he => hf (h he hi)), q⟩

theorem li_smp {i c f} (h : LI i f) : Smp i c f := by
  rcases h with h | ⟨e, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨xor c e, by funext x; simp [rs]⟩

theorem kill {i : Fin 6} {t : Bool} {a b : F} (h : (∃ e, a = fun x => xor (x i) e) ∨
    ∃ e, b = fun x => xor (x i) e) : ∃ c, Cst (rs i c (comb t a b)) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]
  · refine ⟨xor e (!t), !t, ?_⟩
    funext x
    cases t <;> cases e <;> simp [rs, comb]

theorem double {i : Fin 6} {s : Set F} {f k} (p : Prog s f k) (hs : ∀ u ∈ s, LI i u)
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

def stock : Set F := Set.range fun (i : Fin 6) (x : X) => x i

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

theorem all_not_not {n : ℕ} {f : F} (hl : Low n f) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : gs.length ≤ n)
    (he : ∀ x : X, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = f x) :
    ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨k, hk, p⟩ := toProg gs hg o
    (List.ofFn fun (i : Fin 6) (x : X) => x i) stock (by
      intro u hu
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact av_mem ⟨i, rfl⟩)
  have e : rd (gs.foldl (fun w g => w ++ [gv w g])
      (List.ofFn fun (i : Fin 6) (x : X) => x i)) o = f := by
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

def sixTarget : F := fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3901261960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

namespace Projection
open Threshold.Core
def projectedWire (points : Row → X) (f : F) : Wire Row := fun r => f (points r)

theorem projectedAvailable {points : Row → X} {s : Set F} {bank : List (Wire Row)} {f : F}
    (all : ∀ u ∈ s, Available true bank (projectedWire points u)) (h : Av s f) :
    Available true bank (projectedWire points f) := by
  rcases h with ⟨b, rfl⟩ | ⟨u, hu, rfl | rfl⟩
  · exact Or.inr (Or.inl ⟨b, rfl⟩)
  · exact all _ hu
  · exact avail_inv rfl (all _ hu)

theorem projectedProgram (points : Row → X) (roots : List (Wire Row)) {s : Set F} {f : F} {k : Nat}
    (program : Prog s f k) :
    ∀ {spent : Nat} {bank : List (Wire Row)}, Reach true roots spent bank →
      (∀ u ∈ s, Available true bank (projectedWire points u)) →
      ∃ result, Reach true roots (spent + k) result ∧ Available true result (projectedWire points f) := by
  induction program with
  | done h =>
    intro spent bank built all
    exact ⟨bank, built, projectedAvailable all h⟩
  | @gate s f a b k tag ha hb rest ih =>
    intro spent bank built all
    let left := projectedWire points a
    let right := projectedWire points b
    have e : projectedWire points (PEqualNP.Outside.L_meta_49113.comb tag a b) = combine (!tag) left right := by
      cases tag <;> rfl
    have next := Reach.two (!tag) built (projectedAvailable all ha) (projectedAvailable all hb)
    obtain ⟨result, run, hit⟩ := ih next (by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact Or.inl (by rw [e]; exact List.mem_cons_self)
      · exact available_cons _ (all _ hu))
    exact ⟨result, by simpa only [Nat.add_assoc, Nat.add_comm 1 k] using run, hit⟩

end Projection
end PEqualNP.Outside.L_meta_49113

namespace PEqualNP.Outside.L_meta_49113.ReadPair
open Threshold.Core Projection

structure Binary (R : Type) where
  disj : Bool
  left : Wire R
  right : Wire R

def Binary.result (g : Binary R) : Wire R := combine g.disj g.left g.right

def stock (B : List (Wire R)) : List (Binary R) → List (Wire R)
  | [] => B
  | g::gs => stock (g.result :: B) gs

def Valid (B : List (Wire R)) : List (Binary R) → Prop
  | [] => True
  | g::gs => Available true B g.left ∧ Available true B g.right ∧ Valid (g.result::B) gs

theorem stock_append (B : List (Wire R)) (xs ys : List (Binary R)) :
    stock B (xs ++ ys) = stock (stock B xs) ys := by
  induction xs generalizing B with
  | nil => rfl
  | cons g gs ih => exact ih _

theorem valid_append (B : List (Wire R)) (xs ys : List (Binary R)) :
    Valid B (xs ++ ys) ↔ Valid B xs ∧ Valid (stock B xs) ys := by
  induction xs generalizing B with
  | nil => simp [Valid, stock]
  | cons g gs ih =>
    simp only [List.cons_append, Valid, stock, ih]
    tauto

theorem stock_mem {B : List (Wire R)} {gs : List (Binary R)} {v : Wire R} :
    v ∈ stock B gs ↔ v ∈ B ∨ ∃ g ∈ gs, g.result = v := by
  induction gs generalizing B with
  | nil => simp [stock]
  | cons g gs ih =>
    simp only [stock, ih, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((same | inBase) | inTail)
      · exact Or.inr (Or.inl same.symm)
      · exact Or.inl inBase
      · exact Or.inr (Or.inr inTail)
    · rintro (inBase | (same | inTail))
      · exact Or.inl (Or.inr inBase)
      · exact Or.inl (Or.inl same.symm)
      · exact Or.inr inTail

theorem trace_of_reach {base bank : List (Wire R)} {n : Nat}
    (h : Reach true base n bank) :
    ∃ steps : List (Binary R), steps.length = n ∧ Valid base steps ∧ stock base steps = bank := by
  induction h using Reach.ind with
  | start => exact ⟨[],rfl,trivial,rfl⟩
  | @two k bank a b op hr ha hb ih =>
    obtain ⟨gs,hk,hg,hB⟩ := ih
    refine ⟨gs ++ [⟨op,a,b⟩],by simp [hk],?_,?_⟩
    · rw [valid_append, hB]
      exact ⟨hg,ha,hb,trivial⟩
    · rw [stock_append, hB]
      rfl

theorem avail_weaken {B C : List (Wire R)} {v : Wire R} (sub : ∀ w ∈ B, w ∈ C)
    (h : Available true B v) : Available true C v := by
  rcases h with q | q | ⟨_,q⟩
  · exact Or.inl (sub _ q)
  · exact Or.inr (Or.inl q)
  · exact Or.inr (Or.inr ⟨rfl,sub _ q⟩)

theorem reach_includes {B C : List (Wire R)} {n : Nat}
    (h : Reach true B n C) : ∀ w ∈ B, w ∈ C := by
  induction h using Reach.ind with
  | start => exact fun _ h => h
  | two _ _ _ _ ih => exact fun _ h => List.mem_cons_of_mem _ (ih _ h)

def pull (f : S → R) (v : Wire R) : Wire S := fun x => v (f x)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pull_available {B : List (Wire R)} {C : List (Wire S)} {f : S→R} {v : Wire R}
    (haveAll : ∀ a ∈ B, Available true C (pull f a)) (h : Available true B v) :
    Available true C (pull f v) := by
  rcases h with q | ⟨c,rfl⟩ | ⟨_,q⟩
  · exact haveAll _ q
  · exact Or.inr (Or.inl ⟨c,rfl⟩)
  · have e : inv (pull f (inv v)) = pull f v := by
      funext x
      simp [inv,pull]
    rw [← e]
    exact avail_inv rfl (haveAll _ q)

def Cheap (f : S→R) (B : List (Wire S)) (g : Binary R) : Prop :=
  Constant (pull f g.left) ∨ Constant (pull f g.right) ∨ Available true B (pull f g.result)

noncomputable def dropCount (f : S→R) (B : List (Wire S)) (gs : List (Binary R)) : Nat := by
  classical exact gs.countP (fun g => decide (Cheap f B g))

theorem pull_result (f : S→R) (g : Binary R) :
    pull f g.result = combine g.disj (pull f g.left) (pull f g.right) := by
  funext x
  cases eq : g.disj <;> simp [pull, Binary.result, combine, eq]

theorem discard {f : S→R} {B C : List (Wire S)} {g : Binary R}
    (sub : ∀ w ∈ B, w ∈ C)
    (ha : Available true C (pull f g.left))
    (hb : Available true C (pull f g.right))
    (h : Cheap f B g) : Available true C (pull f g.result) := by
  rcases h with h | h | h
  · rw [pull_result]
    exact from_constant _ (Or.inl h) ha hb
  · rw [pull_result]
    exact from_constant _ (Or.inr h) ha hb
  · exact avail_weaken sub h

theorem project_steps {f : S→R} {base : List (Wire S)} {src : List (Wire R)}
    {gs : List (Binary R)} (hv : Valid src gs)
    {k : Nat} {bank : List (Wire S)} (hr : Reach true base k bank)
    (supply : ∀ v ∈ src, Available true bank (pull f v)) :
    ∃ n C, n + dropCount f base gs = k + gs.length ∧ Reach true base n C ∧
      ∀ v ∈ stock src gs, Available true C (pull f v) := by
  classical
  induction gs generalizing src k bank with
  | nil => exact ⟨k,bank,by simp [dropCount],hr,supply⟩
  | cons g gs ih =>
    obtain ⟨ha,hb,hv⟩ := hv
    have ha := pull_available supply ha
    have hb := pull_available supply hb
    by_cases cheap : Cheap f base g
    · have out := discard (reach_includes hr) ha hb cheap
      have next : ∀ v ∈ g.result :: src, Available true bank (pull f v) := by
        intro v h
        rcases List.mem_cons.mp h with rfl | q
        · exact out
        · exact supply _ q
      obtain ⟨n,C,eq,reach,sup⟩ := ih hv hr next
      refine ⟨n,C,?_,reach,sup⟩
      simp only [dropCount, List.countP_cons, decide_eq_true_eq, cheap, ite_true, List.length_cons] at eq ⊢
      omega
    · have nextReach := Reach.two g.disj hr ha hb
      rw [← pull_result] at nextReach
      have next : ∀ v ∈ g.result :: src, Available true (pull f g.result :: bank) (pull f v) := by
        intro v h
        rcases List.mem_cons.mp h with rfl | q
        · exact Or.inl List.mem_cons_self
        · exact available_cons _ (supply _ q)
      obtain ⟨n,C,eq,reach,sup⟩ := ih hv nextReach next
      refine ⟨n,C,?_,reach,sup⟩
      simp only [dropCount, List.countP_cons, decide_eq_true_eq, cheap, ite_false, List.length_cons] at eq ⊢
      omega

def SignedIn (B : List (Wire R)) (v : Wire R) : Prop := v ∈ B ∨ inv v ∈ B

def Reads (B : List (Wire R)) (g : Binary R) : Prop :=
  SignedIn B g.left ∨ SignedIn B g.right

def Agrees (r s : R) (a : Wire R) : Prop := a r = a s

def AgreesOutside (r s : R) (skip bank : List (Wire R)) : Prop :=
  ∀ a ∈ bank, a ∉ skip → Agrees r s a

theorem literal_agrees {r s : R} {skip bank : List (Wire R)} {a : Wire R}
    (all : AgreesOutside r s skip bank) (ha : Available true bank a)
    (avoid : ¬ SignedIn skip a) : Agrees r s a := by
  rcases ha with h | ⟨b,rfl⟩ | ⟨_,h⟩
  · exact all _ h (fun q => avoid (Or.inl q))
  · rfl
  · simpa [Agrees, inv] using (all _ h (fun q => avoid (Or.inr q)))

theorem result_agrees {r s : R} {g : Binary R}
    (a : Agrees r s g.left) (b : Agrees r s g.right) :
    Agrees r s g.result := by
  cases eq : g.disj <;> simp [Binary.result,combine,Agrees,eq,show g.left r = g.left s from a,show g.right r = g.right s from b]

theorem quiet {r s : R} {skip bank : List (Wire R)} {gs : List (Binary R)}
    (h : Valid bank gs) (base : AgreesOutside r s skip bank)
    (noRead : ∀ g ∈ gs, ¬ Reads skip g) :
    (∀ g ∈ gs, Agrees r s g.result) ∧ AgreesOutside r s skip (stock bank gs) := by
  induction gs generalizing bank with
  | nil => exact ⟨by simp,base⟩
  | cons g gs ih =>
    obtain ⟨hl,hr,h⟩ := h
    have no := noRead g List.mem_cons_self
    have eq := result_agrees (literal_agrees base hl (fun h => no (Or.inl h)))
      (literal_agrees base hr (fun h => no (Or.inr h)))
    have next : AgreesOutside r s skip (g.result::bank) := by
      intro v has outside
      rcases List.mem_cons.mp has with rfl | inTail
      · exact eq
      · exact base _ inTail outside
    obtain ⟨agreeTail,agreeBank⟩ := ih h next (fun g h => noRead g (List.mem_cons_of_mem _ h))
    refine ⟨?_,agreeBank⟩
    intro v h
    rcases List.mem_cons.mp h with rfl | q
    · exact eq
    · exact agreeTail _ q

theorem saturated {r s : R} {g : Binary R} {a : Wire R}
    (side : a = g.left ∨ a = g.right)
    (ha : a r = g.disj) (hb : a s = g.disj) :
    Agrees r s g.result := by
  rcases side with rfl | rfl
  · cases eq : g.disj <;> simp [Agrees, Binary.result, combine, eq, ha.trans eq, hb.trans eq]
  · cases eq : g.disj <;> simp [Agrees, Binary.result, combine, eq, ha.trans eq, hb.trans eq]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem quiet_split {r s : R} {skip bank : List (Wire R)} {pre suf : List (Binary R)} {g : Binary R} {F : Wire R}
    (h : Valid bank (pre ++ g::suf)) (base : AgreesOutside r s skip bank)
    (noPre : ∀ y ∈ pre, ¬ Reads skip y) (noSuf : ∀ y ∈ suf, ¬ Reads skip y)
    (center : Agrees r s g.result)
    (out : Available true (stock bank (pre ++ g::suf)) F)
    (notRaw : ¬ SignedIn skip F) : Agrees r s F := by
  rw [valid_append] at h
  obtain ⟨validPre, _, _, validSuf⟩ := h
  have before := (quiet validPre base noPre).2
  have after : AgreesOutside r s skip (g.result :: stock bank pre) := by
    intro a ha nmem
    rcases List.mem_cons.mp ha with rfl | q
    · exact center
    · exact before _ q nmem
  have eqTail := (quiet validSuf after noSuf).2
  rw [stock_append] at out
  exact literal_agrees eqTail out notRaw

noncomputable def tally (P : T → Prop) (gs : List T) : Nat := by
  classical exact gs.countP (fun g => decide (P g))

theorem tally_append (P : T → Prop) (ls rs : List T) :
    tally P (ls++rs) = tally P ls + tally P rs := by
  classical
  simp [tally, List.countP_append]

theorem tally_cons_yes (P : T → Prop) {a : T} (h : P a) (gs : List T) :
    tally P (a::gs) = tally P gs + 1 := by
  classical
  simp [tally, h]

theorem tally_cons_no (P : T → Prop) {a : T} (h : ¬ P a) (gs : List T) :
    tally P (a::gs) = tally P gs := by
  classical
  simp [tally, h]

theorem tally_one {P : T → Prop} {a : T} {gs : List T} (hi : a ∈ gs) (hp : P a) :
    1 ≤ tally P gs := by
  induction gs with
  | nil => simp at hi
  | cons x xs ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · rw [tally_cons_yes P hp]
      omega
    · have z := ih hi
      by_cases q : P x
      · rw [tally_cons_yes P q]
        omega
      · simpa [tally_cons_no P q] using z

theorem tally_disjoint_le {P Q L : T → Prop} (left : ∀ x, P x → L x)
    (right : ∀ x, Q x → L x) (disjoint : ∀ x, P x → ¬ Q x) (gs : List T) :
    tally P gs + tally Q gs ≤ tally L gs := by
  induction gs with
  | nil => simp [tally]
  | cons g gs ih =>
    by_cases a : P g
    · rw [tally_cons_yes P a, tally_cons_no Q (disjoint _ a), tally_cons_yes L (left _ a)]
      omega
    · rw [tally_cons_no P a]
      by_cases b : Q g
      · rw [tally_cons_yes Q b, tally_cons_yes L (right _ b)]
        omega
      · rw [tally_cons_no Q b]
        by_cases c : L g
        · rw [tally_cons_yes L c]
          omega
        · simpa [tally_cons_no L c] using ih

theorem tally_le_len (P : T → Prop) (gs : List T) :
    tally P gs ≤ gs.length := by
  classical
  exact List.countP_le_length

theorem read_once {A : List (Wire R)} {pre suf : List (Binary R)} {g : Binary R}
    (num : tally (Reads A) (pre ++ g::suf) ≤ 1) (h : Reads A g) :
    (∀ w ∈ pre, ¬ Reads A w) ∧ ∀ w ∈ suf, ¬ Reads A w := by
  rw [tally_append, tally_cons_yes _ h] at num
  constructor
  · intro w hw yes
    have := tally_one hw yes
    omega
  · intro w hw yes
    have := tally_one hw yes
    omega

def ix (p : Fin 2) : Fin 6 := ⟨p.val, by omega⟩

def var (i : Fin 6) : Wire Row := observe (inputs.getD i.val Threshold.Core.zero)

def rawBase : List (Wire Row) := List.ofFn var

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem raw_included (i : Fin 6) : var i ∈ rawBase := List.mem_ofFn.mpr ⟨i,rfl⟩

def whole (r : Row) : Bool := (4276676744 * 2 ^ 32 + 3901261960 : Nat).testBit (r.val % 64)

def coIndex (p : Fin 2) (i : Fin 6) : Fin 6 :=
  if i=ix p then 0 else if i=0 then ix p else i

def coCols : List Sig := Threshold.Core.zero :: Threshold.TabKfive.root

def coRow (p : Fin 2) (r : Row) : Row :=
  ⟨(List.range 6).foldl (fun n i =>
    let j : Fin 6 := Fin.ofNat 6 i
    let b := bit r (coCols.getD (coIndex p j).val Threshold.Core.zero)
    if j != ix p && !b then n + (1 <<< i) else n) 0 % 64,
    Nat.lt_trans (Nat.mod_lt _ (by decide : 0<64)) (by decide)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem var_co_false : ∀ p : Fin 2, ∀ r : Row, var (ix p) (coRow p r) = false := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coTarget : ∀ p : Fin 2, ∀ r : Row, whole (coRow p r) = !(bit r Threshold.TabKfive.target) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coRoot (p : Fin 2) {v : Wire Row} (member : v ∈ rawBase) :
    Available true (Threshold.TabKfive.root.map observe) (pull (coRow p) v) := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
  by_cases pin : i=ix p
  · subst i
    exact Or.inr (Or.inl ⟨false, funext (var_co_false p)⟩)
  · have memberCols : ∀ (p : Fin 2) (i : Fin 6), i ≠ ix p →
        coCols.getD (coIndex p i).val Threshold.Core.zero ∈ Threshold.TabKfive.root := by decide +kernel
    have signed : ∀ (p : Fin 2) (i : Fin 6), i ≠ ix p → ∀ r : Row,
        (!(var i (coRow p r))) = bit r (coCols.getD (coIndex p i).val Threshold.Core.zero) := by decide +kernel
    have eq : inv (pull (coRow p) (var i)) =
        observe (coCols.getD (coIndex p i).val Threshold.Core.zero) := funext (signed p i pin)
    exact Or.inr (Or.inr ⟨rfl,eq.symm ▸ List.mem_map_of_mem (memberCols p i pin)⟩)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pin_budget (h : Valid rawBase gs) (out : Available true (stock rawBase gs) whole)
    (p : Fin 2) : 10 + dropCount (coRow p) (Threshold.TabKfive.root.map observe) gs ≤ gs.length := by
  obtain ⟨n,B,e,reach,cover⟩ := project_steps h Reach.start (fun _ m => coRoot p m)
  have output := pull_available cover out
  have eq : pull (coRow p) whole = inv (observe Threshold.TabKfive.target) := funext (coTarget p)
  rw [eq] at output
  have makes := avail_inv rfl output
  rw [inv_inv'] at makes
  have lb := Threshold.TabKfive.lower n B reach makes
  omega

theorem cheap_pivot {g : Binary Row} (p : Fin 2) (read : Reads [var (ix p)] g) :
    Cheap (coRow p) (Threshold.TabKfive.root.map observe) g := by
  have constant {v} (h : SignedIn [var (ix p)] v) : Constant (pull (coRow p) v) := by
    simp only [SignedIn,List.mem_singleton] at h
    rcases h with rfl | z
    · exact ⟨false, funext (var_co_false p)⟩
    · have eq : v = inv (var (ix p)) := (inv_inv' v).symm.trans (congrArg inv z)
      rw [eq]
      exact inv_constant (⟨false, funext (var_co_false p)⟩)
  exact read.elim (fun h => Or.inl (constant h)) (fun h => Or.inr (Or.inl (constant h)))

theorem pivot_once (h : Valid rawBase gs) (out : Available true (stock rawBase gs) whole)
    (cap : gs.length≤11) (p : Fin 2) : tally (Reads [var (ix p)]) gs ≤ 1 := by
  have subset := tally_disjoint_le (P:=Reads [var (ix p)]) (Q:=fun _ => False)
    (L:=Cheap (coRow p) (Threshold.TabKfive.root.map observe)) (fun _ h => cheap_pivot p h)
    (fun _ => False.elim) (by simp) gs
  have lem : tally (Reads [var (ix p)]) gs ≤ dropCount (coRow p) (Threshold.TabKfive.root.map observe) gs := by
    simpa [tally,dropCount] using subset
  have k := pin_budget h out p
  omega

def fullRows : List Nat := [2, 0, 28, 2, 2, 6, 2, 10, 2, 18, 2, 34, 28, 1, 1, 0, 1, 5, 1, 9, 1, 17, 1, 33]

def samplePair (rows : List Nat) (p : Fin 2) (q : Fin 6) (b : Bool) : Row × Row :=
  let n := rows.getD (p.val * 12 + q.val * 2 + b.toNat) 0
  (Fin.ofNat 512 n, Fin.ofNat 512 (n + (1 <<< (ix p).val)))

def Apart (p : Fin 2) (l r : Row) : Prop :=
  ∀ i : Fin 6, i ≠ ix p → var i l = var i r

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem full_pair : ∀ (p : Fin 2) (q : Fin 6) (b : Bool), q ≠ ix p →
    let w := samplePair fullRows p q b
    Apart p w.1 w.2 ∧ var q w.1 = b ∧ var q w.2 = b ∧ whole w.1 ≠ whole w.2 := by
  unfold Apart
  decide +kernel

theorem apart_agree {p : Fin 2} {l r : Row} (h : Apart p l r) :
    AgreesOutside l r [var (ix p)] rawBase := by
  intro a ha hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  apply h
  intro q
  exact hx (List.mem_singleton.mpr (congrArg var q))

def lonely (i : Fin 6) : Row := Fin.ofNat 512 (1 <<< i.val)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem var_zero : ∀ i : Fin 6, var i 0 = false := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem var_lonely : ∀ i : Fin 6, var i (lonely i) = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem whole_raw : ∀ i : Fin 6, whole (lonely i) = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem not_signed_whole (L : List (Wire Row))
    (sub : ∀ a ∈ L, ∃ i : Fin 6, a = var i) : ¬ SignedIn L whole := by
  intro h
  rcases h with h | h
  · obtain ⟨i,e⟩ := sub _ h
    have bad := congrFun e (lonely i)
    simp [whole_raw,var_lonely] at bad
  · obtain ⟨i,e⟩ := sub _ h
    have bad := congrFun e 0
    have wzero : whole 0 = false := by decide
    simp [inv,wzero,var_zero] at bad

theorem not_signed_root (i : Fin 6) : ¬ SignedIn [var i] whole := by
  apply not_signed_whole
  intro a ha
  exact ⟨i,List.mem_singleton.mp ha⟩

theorem first_split {P : T → Prop} {steps : List T} (hit : ∃ g ∈ steps, P g) :
    ∃ pre g suf, steps = pre ++ g::suf ∧ P g ∧ ∀ a ∈ pre, ¬ P a := by
  classical
  induction steps with
  | nil => simp at hit
  | cons g gs ih =>
    by_cases already : P g
    · exact ⟨[],g,gs,rfl,already,by simp⟩
    · obtain ⟨w,haveW,hitW⟩ := hit
      rcases List.mem_cons.mp haveW with rfl | left
      · exact (already hitW).elim
      · obtain ⟨pre,g',suf,shape,hg,noPrev⟩ := ih ⟨w,left,hitW⟩
        refine ⟨g::pre,g',suf,?_,hg,?_⟩
        · rw [shape]
          rfl
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | q
          · exact already
          · exact noPrev _ q

theorem read_as_phase {B : List (Wire R)} {x : Wire R} :
    SignedIn B x ↔ ∃ w ∈ B, x = w ∨ x = inv w := by
  constructor
  · rintro (h | h)
    · exact ⟨x,h,Or.inl rfl⟩
    · exact ⟨inv x,h,Or.inr (inv_inv' x).symm⟩
  · rintro ⟨w,h,rfl|rfl⟩
    · exact Or.inl h
    · exact Or.inr ((inv_inv' w).symm ▸ h)

theorem signed_mono {K L : List (Wire R)} {v : Wire R}
    (subset : ∀ a ∈ K, a ∈ L) (h : SignedIn K v) : SignedIn L v :=
  h.elim (fun q => Or.inl (subset _ q)) (fun q => Or.inr (subset _ q))

theorem reads_mono {K L : List (Wire R)} {g : Binary R}
    (subset : ∀ a ∈ K, a ∈ L) (h : Reads K g) : Reads L g :=
  h.elim (fun q => Or.inl (signed_mono subset q)) (fun q => Or.inr (signed_mono subset q))

theorem raw_other {gs : List (Binary Row)} (h : Valid rawBase gs)
    (done : Available true (stock rawBase gs) whole) (cap : gs.length≤11)
    {g : Binary Row} (gm : g ∈ gs) (p : Fin 2) (q : Fin 6) (ne : q≠ix p)
    (hp : Reads [var (ix p)] g)
    {v : Wire Row} (side : v=g.left ∨ v=g.right) (how : v = var q ∨ v = inv (var q)) : False := by
  obtain ⟨pre,g',suf,split,hg,_⟩ := first_split (P:=fun x => x=g) ⟨g,gm,rfl⟩
  subst g'
  rw [split] at h done cap
  have count := pivot_once h done cap p
  obtain ⟨noPre,noSuf⟩ := read_once count hp
  rcases how with normal | negated
  · let w := samplePair fullRows p q g.disj
    obtain ⟨apart,left,right,hd⟩ := full_pair p q g.disj ne
    have center := saturated side (normal.symm ▸ left) (normal.symm ▸ right)
    exact hd (quiet_split h (apart_agree apart) noPre noSuf center done (not_signed_root _))
  · let w := samplePair fullRows p q (!g.disj)
    obtain ⟨apart,left,right,hd⟩ := full_pair p q (!g.disj) ne
    have a : v w.1 = g.disj := by simpa [negated,inv,w,left]
    have b : v w.2 = g.disj := by simpa [negated,inv,w,right]
    exact hd (quiet_split h (apart_agree apart) noPre noSuf (saturated side a b) done (not_signed_root _))

def Phase (u a : Wire R) : Prop := u=a ∨ u=inv a

theorem phase_in {B : List (Wire R)} {w v : Wire R} (ha : w ∈ B) (h : Phase v w) :
    SignedIn B v := read_as_phase.mpr ⟨w,ha,h⟩

theorem phase_av {B : List (Wire R)} {w v : Wire R} (ha : w ∈ B) (h : Phase v w) :
    Available true B v := by
  rcases phase_in ha h with q | q
  · exact Or.inl q
  · exact Or.inr (Or.inr ⟨rfl,q⟩)

theorem raw_other_read {gs : List (Binary Row)} (h : Valid rawBase gs)
    (done : Available true (stock rawBase gs) whole) (cap : gs.length≤11)
    {g : Binary Row} (gm : g ∈ gs) (p : Fin 2) (q : Fin 6) (ne : q≠ix p)
    (hp : Reads [var (ix p)] g) : ¬ Reads [var q] g := by
  intro hq
  rcases hq with l | r
  · have z := read_as_phase.mp l
    obtain ⟨v,ev,hv⟩ := z
    rw [List.mem_singleton.mp ev] at hv
    exact raw_other h done cap gm p q ne hp (Or.inl rfl) hv
  · have z := read_as_phase.mp r
    obtain ⟨v,ev,hv⟩ := z
    rw [List.mem_singleton.mp ev] at hv
    exact raw_other h done cap gm p q ne hp (Or.inr rfl) hv

theorem pivot_used (h : Valid rawBase gs) (done : Available true (stock rawBase gs) whole) (p : Fin 2) :
    ∃ g ∈ gs, Reads [var (ix p)] g := by
  classical
  by_contra no
  obtain ⟨hapart,_,_,dif⟩ := full_pair p 5 true (by intro e; have q := congrArg Fin.val e; simp [ix] at q; omega)
  have eq := quiet h (apart_agree hapart) (fun g mem use => no ⟨g,mem,use⟩)
  exact dif (literal_agrees eq.2 done (not_signed_root _))

theorem trace_eleven (h : Valid rawBase gs) (done : Available true (stock rawBase gs) whole) :
    11 ≤ gs.length := by
  obtain ⟨g,m,use⟩ := pivot_used h done 0
  have k := tally_one (P:=Cheap (coRow 0) (Threshold.TabKfive.root.map observe)) m (cheap_pivot 0 use)
  have lb := pin_budget h done 0
  change 1 ≤ dropCount (coRow 0) (Threshold.TabKfive.root.map observe) gs at k
  omega

theorem avoid_available {bank next : List (Wire R)} {a z : Wire R}
    (keep : ∀ w ∈ bank, w ≠ z → w ∈ next) (av : Available true bank a)
    (avoid : ¬ SignedIn [z] a) : Available true next a := by
  refine av.imp (fun m => keep _ m ?_) (Or.imp id (fun ⟨e,m⟩ => ⟨e,keep _ m ?_⟩))
  · intro r
    exact avoid (Or.inl (List.mem_singleton.mpr r))
  · intro r
    exact avoid (Or.inr (List.mem_singleton.mpr r))

theorem avoid_steps {src dest : List (Wire R)} {xs : List (Binary R)} {z : Wire R}
    (h : Valid src xs) (keep : ∀ w ∈ src, w ≠ z → w ∈ dest)
    (avoid : ∀ g ∈ xs, ¬ Reads [z] g) :
    Valid dest xs ∧ ∀ w ∈ stock src xs, w ≠ z → w ∈ stock dest xs := by
  induction xs generalizing src dest with
  | nil => exact ⟨trivial,keep⟩
  | cons g xs ih =>
    obtain ⟨l,r,tail⟩ := h
    have omitG := avoid g List.mem_cons_self
    have keepG : ∀ w ∈ g.result :: src, w ≠ z → w ∈ g.result :: dest := by
      intro w m ne
      rcases List.mem_cons.mp m with rfl|m
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (keep _ m ne)
    obtain ⟨tail,kept⟩ := ih tail keepG (fun g m => avoid g (List.mem_cons_of_mem _ m))
    exact ⟨⟨avoid_available keep l (fun e=>omitG (Or.inl e)),
      avoid_available keep r (fun e=>omitG (Or.inr e)),tail⟩,kept⟩

theorem result_used {pre suf : List (Binary Row)} {g : Binary Row}
    (h : Valid rawBase (pre ++ g::suf)) (done : Available true (stock rawBase (pre ++ g::suf)) whole)
    (cap : (pre ++ g::suf).length≤11) :
    SignedIn [g.result] whole ∨ ∃ d ∈ suf, Reads [g.result] d := by
  classical
  by_contra no
  push Not at no
  have sp := (valid_append _ _ _).mp h
  have sub : ∀ w ∈ g.result::stock rawBase pre, w ≠ g.result → w ∈ stock rawBase pre := by
    intro w m ne
    exact (List.mem_cons.mp m).resolve_left ne
  obtain ⟨valid,remain⟩ := avoid_steps sp.2.2.2 sub no.2
  have h' := (valid_append rawBase pre suf).mpr ⟨sp.1,valid⟩
  rw [stock_append] at done
  have output := avoid_available remain done no.1
  have lb := trace_eleven h' (by simpa only [stock_append] using output)
  simp only [List.length_append,List.length_cons] at cap lb
  omega

def signed (b : Bool) (f : Wire R) : Wire R := fun r => if b then !(f r) else f r

theorem signed_choice {a z : Wire R} (h : SignedIn [z] a) :
    ∃ b : Bool, a = signed b z := by
  obtain ⟨w,mem,phase⟩ := read_as_phase.mp h
  rw [List.mem_singleton.mp mem] at phase
  rcases phase with eq | eq
  · exact ⟨false,eq⟩
  · exact ⟨true,eq⟩

theorem signed_in {R} {z : Wire R} (b : Bool) : SignedIn [z] (signed b z) := by
  cases b
  · exact Or.inl List.mem_cons_self
  · exact phase_in List.mem_cons_self (Or.inr rfl)

theorem sign_constant (b : Bool) {z : Wire R} (c : Constant z) : Constant (signed b z) := by
  cases b
  · exact c
  · exact inv_constant c

theorem sign_available {B : List (Wire R)} {z : Wire R} (b : Bool)
    (h : Available true B z) : Available true B (signed b z) := by
  cases b
  · exact h
  · exact avail_inv rfl h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coVaries : ∀ p : Fin 2, whole (coRow p 0) ≠ whole (coRow p 511) := by
  decide +kernel

theorem mask_not_constant {pre suf : List (Binary Row)} {g : Binary Row}
    (h : Valid rawBase (pre ++ g::suf)) (done : Available true (stock rawBase (pre ++ g::suf)) whole)
    (cap : (pre ++ g::suf).length≤11) (p : Fin 2) (rd : Reads [var (ix p)] g) :
    ¬ Constant (pull (coRow p) g.result) := by
  intro const
  have constSig (v : Wire Row) (sv : SignedIn [g.result] v) :
      Constant (pull (coRow p) v) := by
    obtain ⟨k,eq⟩ := signed_choice sv
    rw [eq]
    exact sign_constant k const
  rcases result_used h done cap with eq|⟨y,ym,seen⟩
  · obtain ⟨b,e⟩ := constSig _ eq
    exact coVaries p (((congrFun e 0) : whole (coRow p 0) = b).trans
      (((congrFun e 511) : whole (coRow p 511) = b)).symm)
  · let cheap := Cheap (coRow p) (Threshold.TabKfive.root.map observe)
    have yg : cheap y :=
      seen.elim (fun m => Or.inl (constSig _ m)) (fun m => Or.inr (Or.inl (constSig _ m)))
    have lower := tally_one (P:=cheap) ym yg
    have upper := pin_budget h done p
    change 10 + tally cheap (pre ++ g::suf) ≤ _ at upper
    rw [tally_append cheap, tally_cons_yes cheap (cheap_pivot p rd)] at upper
    omega

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem reader_polarity {pre suf : List (Binary Row)} {g : Binary Row}
    (h : Valid rawBase (pre ++ g::suf)) (done : Available true (stock rawBase (pre ++ g::suf)) whole)
    (cap : (pre ++ g::suf).length≤11) (p : Fin 2) (sig : Bool)
    (side : signed sig (var (ix p)) = g.left ∨ signed sig (var (ix p)) = g.right) :
    g.disj = !sig := by
  have rd : Reads [var (ix p)] g := side.elim
    (fun e=>Or.inl (e ▸ signed_in sig)) (fun e=>Or.inr (e ▸ signed_in sig))
  have nonconst := mask_not_constant h done cap p rd
  by_contra mismatch
  have eq : g.disj = sig := by
    cases sig <;> cases tag : g.disj <;> simp_all
  apply nonconst
  refine ⟨sig,funext (fun r=> ?_)⟩
  have pin := var_co_false p r
  rcases side with left|right
  · change combine g.disj g.left g.right (coRow p r) = sig
    rw [← left,eq]
    cases sig <;> simp [combine,signed,pin]
  · change combine g.disj g.left g.right (coRow p r) = sig
    rw [← right,eq]
    cases sig <;> simp [combine,signed,pin]

theorem signs_compose {f : Wire R} (a b : Bool) :
    signed a (signed b f) = signed (xor a b) f := by
  funext r
  cases a <;> cases b <;> simp [signed]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem signs_inj {f : Wire R} [Nonempty R] {b c : Bool}
    (eq : signed b f = signed c f) : b=c := by
  let r : R := Classical.choice inferInstance
  have applyRow := congrFun eq r
  cases b <;> cases c <;> cases hr : f r <;> simp_all [signed]

theorem signed_phase {a z : Wire R} (b : Bool) (ph : SignedIn [z] a) :
    SignedIn [z] (signed b a) := by
  obtain ⟨c,eq⟩ := signed_choice ph
  rw [eq,signs_compose]
  exact signed_in _

theorem unsign_in {a z : Wire R} (b : Bool) (ph : SignedIn [z] (signed b a)) :
    SignedIn [z] a := by
  have eq : signed b (signed b a) = a := by cases b <;> rw [signs_compose] <;> rfl
  exact eq ▸ signed_phase b ph

theorem stock_contains {B : List (Wire R)} {xs : List (Binary R)} {v : Wire R}
    (m : v ∈ B) : v ∈ stock B xs := stock_mem.mpr (Or.inl m)

theorem stock_available {B : List (Wire R)} {xs : List (Binary R)} {v : Wire R}
    (h : Available true B v) : Available true (stock B xs) v :=
  avail_weaken (fun _ m => stock_contains (xs:=xs) m) h

theorem replay_same {src dest : List (Wire R)} {xs : List (Binary R)}
    (h : Valid src xs) (supply : ∀ v ∈ src, Available true dest v) :
    Valid dest xs ∧ (∀ v ∈ stock src xs, Available true (stock dest xs) v) := by
  induction xs generalizing src dest with
  | nil => exact ⟨trivial,supply⟩
  | cons g xs ih =>
    obtain ⟨l,r,tail⟩ := h
    have carried : ∀ v ∈ g.result::src, Available true (g.result::dest) v := by
      intro v m
      rcases List.mem_cons.mp m with rfl|m
      · exact Or.inl List.mem_cons_self
      · exact available_cons _ (supply _ m)
    obtain ⟨tail,cov⟩ := ih tail carried
    exact ⟨⟨pull_available (f:=id) supply l,pull_available (f:=id) supply r,tail⟩,cov⟩

theorem result_fresh {pre suf : List (Binary Row)} {g : Binary Row}
    (h : Valid rawBase (pre ++ g::suf)) (done : Available true (stock rawBase (pre ++ g::suf)) whole)
    (cap : (pre ++ g::suf).length≤11) : ¬ Available true (stock rawBase pre) g.result := by
  intro duplicate
  have sp := (valid_append _ _ _).mp h
  have cover : ∀ v ∈ g.result :: stock rawBase pre, Available true (stock rawBase pre) v := by
    intro v m
    rcases List.mem_cons.mp m with rfl|m
    · exact duplicate
    · exact Or.inl m
  obtain ⟨valid,mapped⟩ := replay_same sp.2.2.2 cover
  rw [stock_append] at done
  have target := pull_available (f:=id) mapped done
  change Available true (stock (stock rawBase pre) suf) whole at target
  have lb := trace_eleven ((valid_append rawBase pre suf).mpr ⟨sp.1,valid⟩)
    (by simpa only [stock_append] using target)
  simp only [List.length_append,List.length_cons] at cap lb
  omega

theorem combine_phases {B : List (Wire R)} {z : Wire R} (mz : z ∈ B) (l r tag : Bool) :
    Available true B (combine tag (signed l z) (signed r z)) := by
  cases l <;> cases r
  · have eq : combine tag (signed false z) (signed false z) = z := by
      funext a; cases tag <;> simp [signed,combine]
    exact eq.symm ▸ Or.inl mz
  · exact Or.inr (Or.inl ⟨tag,by funext a; cases tag <;> cases hr : z a <;> simp [signed,combine,hr]⟩)
  · exact Or.inr (Or.inl ⟨tag,by funext a; cases tag <;> cases hr : z a <;> simp [signed,combine,hr]⟩)
  · have eq : combine tag (signed true z) (signed true z) = signed true z := by
      funext a; cases tag <;> simp [signed,combine]
    exact eq.symm ▸ sign_available true (Or.inl mz)

def Masked (mask a b : Wire R) : Prop :=
  ∀ r, mask r = false → a r = b r

theorem masked_sign {mask a b : Wire R} (h : Masked mask a b) (sig : Bool) :
    Masked mask (signed sig a) (signed sig b) := by
  intro r hr
  simp [signed,h r hr]

theorem masked_bin {mask : Wire R} {a b : Binary R} (same : a.disj = b.disj)
    (l : Masked mask a.left b.left) (r : Masked mask a.right b.right) :
    Masked mask a.result b.result := by
  intro j hj
  cases tag : b.disj <;> simp [Binary.result,combine,same,tag,l j hj,r j hj]

def Corresponds (mask : Wire R) (src dest : List (Wire R)) : Prop :=
  ∀ a ∈ src, ∃ b, Available true dest b ∧ Masked mask a b

theorem translate_av {mask : Wire R} {src dest : List (Wire R)}
    (supply : Corresponds mask src dest) {a : Wire R} (hav : Available true src a) :
    ∃ b, Available true dest b ∧ Masked mask a b := by
  rcases hav with m | const | ⟨_,m⟩
  · exact supply _ m
  · exact ⟨a,Or.inr (Or.inl const),fun _ _=>rfl⟩
  · obtain ⟨b,offered,correspond⟩ := supply _ m
    refine ⟨inv b,avail_inv rfl offered,?_⟩
    have eq := masked_sign correspond true
    change Masked mask (inv (inv a)) (inv b) at eq
    simpa only [inv_inv'] using eq

theorem signed_symmetric {a z : Wire R} (h : SignedIn [z] a) : SignedIn [a] z := by
  obtain ⟨sig,eq⟩ := signed_choice h
  have res := signed_in (z:=a) sig
  have flip : signed sig a = z := by rw [eq,signs_compose]; cases sig <;> rfl
  rwa [flip] at res

theorem signed_trans {a y z : Wire R} (h₁ : SignedIn [y] a) (h₂ : SignedIn [z] y) :
    SignedIn [z] a := by
  obtain ⟨sig,eq⟩ := signed_choice h₁
  exact eq.symm ▸ signed_phase sig h₂

theorem translate_choice [Nonempty R] {mask z y protect : Wire R} {src dest : List (Wire R)}
    (supply : Corresponds mask src dest) (maskedSource : Masked mask z y)
    (haveY : Available true dest y) (keep : Available true dest protect)
    (distinct : ¬ SignedIn [z] protect) {a : Wire R} (hav : Available true src a) :
    ∃ b, Available true dest b ∧ Masked mask a b ∧
      (∀ bit : Bool, a = signed bit z → b = signed bit y) ∧ (SignedIn [protect] a → b = a) := by
  classical
  by_cases special : SignedIn [z] a
  · obtain ⟨c,eq⟩ := signed_choice special
    refine ⟨signed c y,sign_available c haveY,eq.symm ▸ masked_sign maskedSource c,?_,?_⟩
    · intro d hs
      have same := signs_inj (eq.symm.trans hs)
      rw [same]
    · intro seen
      exact (distinct (signed_trans (signed_symmetric seen) special)).elim
  · have imposs (bit : Bool) (eq : a = signed bit z) : False :=
      special (eq.symm ▸ signed_in bit)
    by_cases saved : SignedIn [protect] a
    · obtain ⟨c,eq⟩ := signed_choice saved
      exact ⟨a,eq.symm ▸ sign_available c keep,fun _ _=>rfl,
        fun bit hs => (imposs bit hs).elim, fun _=>rfl⟩
    · obtain ⟨b,m,same⟩ := translate_av supply hav
      exact ⟨b,m,same,fun bit eq => (imposs bit eq).elim,fun q => (saved q).elim⟩

def Align (z y protect : Wire R) (g w : Binary R) : Prop :=
  w.disj = g.disj ∧
    (∀ b : Bool, g.left = signed b z → w.left = signed b y) ∧
    (∀ b : Bool, g.right = signed b z → w.right = signed b y) ∧
    (Reads [protect] g → Reads [protect] w)

theorem aligned_read {z y a protect : Wire R} {g w : Binary R}
    (agree : Align z y protect g w) (raw : SignedIn [a] y) (seen : Reads [z] g) :
    Reads [a] w := by
  rcases seen with left|right
  · obtain ⟨sig,eq⟩ := signed_choice left
    exact Or.inl (agree.2.1 sig eq ▸ signed_phase sig raw)
  · obtain ⟨sig,eq⟩ := signed_choice right
    exact Or.inr (agree.2.2.1 sig eq ▸ signed_phase sig raw)

theorem translate_steps [Nonempty R] {mask z y a protect : Wire R} {src dest : List (Wire R)}
    {xs : List (Binary R)} (h : Valid src xs)
    (maskedSource : Masked mask z y) (haveY : Available true dest y) (raw : SignedIn [a] y)
    (keep : Available true dest protect) (distinct : ¬ SignedIn [z] protect)
    (supply : Corresponds mask src dest) :
    ∃ ys, ys.length = xs.length ∧ Valid dest ys ∧ List.Forall₂ (Align z y protect) xs ys ∧
      tally (Reads [z]) xs ≤ tally (Reads [a]) ys ∧
      Corresponds mask (stock src xs) (stock dest ys) := by
  induction xs generalizing src dest with
  | nil => exact ⟨[],rfl,trivial,.nil,le_rfl,supply⟩
  | cons g gs ih =>
    obtain ⟨l,r,rest⟩ := h
    obtain ⟨l',la,lmask,lphase,lkeep⟩ := translate_choice supply maskedSource haveY keep distinct l
    obtain ⟨r',ra,rmask,rphase,rkeep⟩ := translate_choice supply maskedSource haveY keep distinct r
    let v : Binary R := ⟨g.disj,l',r'⟩
    have saved : Reads [protect] g → Reads [protect] v :=
      fun q => q.elim
        (fun seen => Or.inl (show SignedIn [protect] l' from (lkeep seen).symm ▸ seen))
        (fun seen => Or.inr (show SignedIn [protect] r' from (rkeep seen).symm ▸ seen))
    have aligned : Align z y protect g v := ⟨rfl,lphase,rphase,saved⟩
    have nextSupply : Corresponds mask (g.result::src) (v.result::dest) := by
      intro old m
      rcases List.mem_cons.mp m with rfl|m
      · exact ⟨v.result,Or.inl List.mem_cons_self, masked_bin rfl lmask rmask⟩
      · obtain ⟨new,newA,newH⟩ := supply _ m
        exact ⟨new,available_cons _ newA,newH⟩
    obtain ⟨tail,len,valid,align,reads,final⟩ := ih rest (available_cons _ haveY) (available_cons _ keep) nextSupply
    refine ⟨v::tail, by simpa only [List.length_cons] using congrArg (·+1) len,
      ⟨la,ra,valid⟩, .cons aligned align, ?_, final⟩
    by_cases old : Reads [z] g
    · rw [tally_cons_yes _ old, tally_cons_yes _ (aligned_read aligned raw old)]
      omega
    · rw [tally_cons_no _ old]
      by_cases cur : Reads [a] v
      · rw [tally_cons_yes _ cur]
        omega
      · simpa only [tally_cons_no _ cur] using reads

theorem aligned_mem {R} {z y protect : Wire R} {xs ys : List (Binary R)} {g : Binary R}
    (h : List.Forall₂ (Align z y protect) xs ys) (m : g ∈ xs) :
    ∃ v ∈ ys, Align z y protect g v := by
  induction h with
  | nil => simp at m
  | cons eq rest ih =>
    rcases List.mem_cons.mp m with rfl | further
    · exact ⟨_,List.mem_cons_self,eq⟩
    · obtain ⟨v,vm,agree⟩ := ih further
      exact ⟨v,List.mem_cons_of_mem _ vm,agree⟩

def Matched (g : Binary R) (a b : Wire R) : Prop :=
  (g.left=a ∧ g.right=b) ∨ (g.left=b ∧ g.right=a)

theorem matched_comm {g : Binary R} {a b : Wire R} (h : Matched g a b) : Matched g b a :=
  h.elim Or.inr Or.inl

theorem matched_side {g : Binary R} {a b : Wire R} (h : Matched g a b) :
    a = g.left ∨ a = g.right :=
  h.elim (fun e => Or.inl e.1.symm) (fun e => Or.inr e.2.symm)

theorem matched_res {g : Binary R} {a b : Wire R} (h : Matched g a b) :
    g.result = combine g.disj a b := by
  rcases h with ⟨l,r⟩|⟨l,r⟩
  · simp only [Binary.result,l,r]
  · funext x
    cases tag : g.disj <;> simp [Binary.result,combine,l,r,tag,Bool.or_comm,Bool.and_comm]

theorem matched_available {g : Binary R} {a b : Wire R} {bank : List (Wire R)}
    (h : Matched g a b) (l : Available true bank g.left) (r : Available true bank g.right) :
    Available true bank b :=
  h.elim (fun e=>e.2 ▸ r) (fun e=>e.1 ▸ l)

theorem matched_reads {g : Binary R} {a b : Wire R} {bank : List (Wire R)}
    (h : Matched g a b) (seen : SignedIn bank a) : Reads bank g :=
  h.elim (fun e=>Or.inl (e.1.symm ▸ seen)) (fun e=>Or.inr (e.2.symm ▸ seen))

theorem operand_choice {g : Binary R} {z : Wire R} (h : Reads [z] g) :
    ∃ (sg : Bool) (other : Wire R), Matched g (signed sg z) other := by
  rcases h with l|r
  · obtain ⟨b,eq⟩ := signed_choice l
    exact ⟨b,g.right,Or.inl ⟨eq,rfl⟩⟩
  · obtain ⟨b,eq⟩ := signed_choice r
    exact ⟨b,g.left,Or.inr ⟨rfl,eq⟩⟩

theorem or_phase {a b : Wire R} (sg : Bool) :
    combine (!sg) (signed sg a) b = signed sg (combine true a (signed sg b)) := by
  funext r
  cases sg <;> cases aa : a r <;> cases bb : b r <;> simp [signed,combine,aa,bb]

def controls : List (Wire Row) := List.ofFn fun p : Fin 2 => var (ix p)

theorem control_mem (p : Fin 2) : var (ix p) ∈ controls := List.mem_ofFn.mpr ⟨p,rfl⟩

theorem no_ctrl_signed {v : Wire Row}
    (no : ∀ p : Fin 2, ¬ SignedIn [var (ix p)] v) : ¬ SignedIn controls v := by
  intro h
  obtain ⟨r,m,sg⟩ := read_as_phase.mp h
  obtain ⟨p,rfl⟩ := List.mem_ofFn.mp m
  exact no _ (phase_in List.mem_cons_self sg)

theorem has_ctrl {g : Binary Row} (see : Reads controls g) :
    ∃ p : Fin 2, Reads [var (ix p)] g := by
  classical
  by_contra no
  push Not at no
  exact see.elim
    (no_ctrl_signed (fun p hs=>no p (Or.inl hs)))
    (no_ctrl_signed (fun p hs=>no p (Or.inr hs)))

theorem control_reads {g : Binary Row} {p : Fin 2} (single : Reads [var (ix p)] g) :
    Reads controls g :=
  reads_mono (fun _ m=>(List.mem_singleton.mp m).symm ▸ control_mem p) single

theorem no_controls {g : Binary Row} (no : ¬ Reads controls g) (p : Fin 2) :
    ¬ Reads [var (ix p)] g := fun h=>no (control_reads h)

theorem contr_ix {p q : Fin 2} (same : ix p = ix q) : p=q :=
  Fin.ext (congrArg (fun i : Fin 6 => i.val) same)

def place (r : Row) (a b : Bool) : Row :=
  ⟨(r.val/4)*4+a.toNat+2*b.toNat,by cases a <;> cases b <;> simp <;> omega⟩

def settings (p : Fin 2) (r : Row) (a b : Bool) : Row :=
  if p=0 then place r a b else place r b a

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem place_rest : ∀ (i : Fin 6), 2 ≤ i.val → ∀ (r : Row) (a b : Bool),
    var i (place r a b) = var i r := by decide +kernel

theorem stable_settings (p : Fin 2) (r : Row) (a b : Bool) :
    AgreesOutside (settings p r a b) r controls rawBase := by
  intro v m missing
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp m
  have hi : 2 ≤ i.val := by
    by_contra! tooSmall
    let q : Fin 2 := ⟨i.val,tooSmall⟩
    have eq : ix q = i := Fin.ext rfl
    exact missing (eq ▸ control_mem q)
  by_cases p0 : p = 0
  · simpa only [settings,ite_eq_left p0,Agrees] using place_rest i hi r a b
  · simpa only [settings,ite_eq_right p0,Agrees] using place_rest i hi r b a

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem settings_apart : ∀ (p : Fin 2) (r : Row) (b : Bool),
    Apart p (settings p r false b) (settings p r true b) := by
  unfold Apart
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem insensitive_true : ∀ (p : Fin 2) (r : Row),
    whole (settings p r false false) = whole (settings p r true false) →
    whole (settings p r false true) = whole (settings p r true true) →
    whole r = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem first_mask_true {pre suf : List (Binary Row)} {g : Binary Row} {wg : Wire Row}
    (h : Valid rawBase (pre ++ g::suf)) (done : Available true (stock rawBase (pre ++ g::suf)) whole)
    (cap : (pre ++ g::suf).length≤11) (p : Fin 2) (sg : Bool)
    (raw : Reads [var (ix p)] g) (preQuiet : ∀ x ∈ pre, ¬ Reads controls x)
    (av : Available true (stock rawBase pre) wg) (wgQuiet : ¬ SignedIn controls wg)
    (eq : g.result = signed sg (combine true (var (ix p)) wg)) :
    ∀ r, wg r = true → whole r = true := by
  intro r hr
  obtain ⟨preNone,sufNone⟩ := read_once (pivot_once h done cap p) raw
  have preValid := (valid_append _ _ _).mp h |>.1
  have wgp (a b : Bool) : wg (settings p r a b) = true :=
    (literal_agrees ((quiet preValid (stable_settings p r a b) preQuiet).2) av wgQuiet).trans hr
  have midpoint (a b : Bool) : g.result (settings p r a b) = !sg := by
    rw [eq]
    cases sg <;> simp [signed,combine,wgp a b]
  have insensitive (b : Bool) : whole (settings p r false b) = whole (settings p r true b) :=
    quiet_split h (apart_agree (settings_apart p r b)) preNone sufNone
      ((midpoint false b).trans (midpoint true b).symm) done (not_signed_root _)
  exact insensitive_true p r (insensitive false) (insensitive true)

def otherPivot (p : Fin 2) : Fin 2 := if p=0 then 1 else 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem other_ne : ∀ p : Fin 2, otherPivot p ≠ p := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pivot_cases : ∀ (p q : Fin 2), q=p ∨ q=otherPivot p := by decide +kernel

theorem result_not_output {pre suf : List (Binary Row)} {g : Binary Row}
    (h : Valid rawBase (pre ++ g::suf)) (done : Available true (stock rawBase (pre ++ g::suf)) whole)
    (cap : (pre ++ g::suf).length≤11) (p : Fin 2)
    (raw : Reads [var (ix p)] g) (preQuiet : ∀ x ∈ pre, ¬ Reads controls x) :
    ¬ SignedIn [g.result] whole := by
  let q := otherPivot p
  have all := (valid_append _ _ _).mp h
  have spare := raw_other_read h done cap (List.mem_append.mpr (Or.inr List.mem_cons_self))
    p (ix q) (fun e=> other_ne p (contr_ix e)) raw
  obtain ⟨ar,_,_,ne⟩ := full_pair q 5 true (by intro e; have t := congrArg (fun i : Fin 6=>i.val) e; simp [ix] at t; omega)
  have preEqual := (quiet all.1 (apart_agree ar) (fun x m => no_controls (preQuiet x m) q)).2
  have gres := result_agrees
    (literal_agrees preEqual all.2.1 (fun e => spare (Or.inl e)))
    (literal_agrees preEqual all.2.2.1 (fun e => spare (Or.inr e)))
  intro sg
  obtain ⟨phase,eq⟩ := signed_choice sg
  apply ne
  rw [eq]
  change (if phase then !g.result _ else g.result _) = (if phase then !g.result _ else g.result _)
  cases phase
  · exact gres
  · exact congrArg Bool.not (show _ = _ from gres)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem unmask {pre suf : List (Binary Row)} {g : Binary Row} {mask : Wire Row}
    (h : Valid rawBase (pre ++ g::suf)) (done : Available true (stock rawBase (pre ++ g::suf)) whole)
    (cap : (pre ++ g::suf).length≤11) (p : Fin 2) (sg : Bool)
    (maskAvail : Available true (stock rawBase pre) mask)
    (safe : ∀ r, mask r = true → whole r = true)
    (eq : g.result = signed sg (combine true (var (ix p)) mask)) :
    ∃ rewired patch, rewired.length = suf.length ∧ Valid rawBase ((pre ++ rewired) ++ [patch]) ∧
      Available true (stock rawBase ((pre ++ rewired) ++ [patch])) whole ∧
      List.Forall₂ (Align g.result (signed sg (var (ix p))) (var (ix (otherPivot p)))) suf rewired ∧
      tally (Reads [g.result]) suf ≤ 1 := by
  let raw := var (ix p)
  let spared := var (ix (otherPivot p))
  let substitute := signed sg raw
  have rAvail : Available true (stock rawBase pre) raw :=
    Or.inl (stock_contains (raw_included (ix p)))
  have qAvail : Available true (stock rawBase pre) spared :=
    Or.inl (stock_contains (raw_included (ix (otherPivot p))))
  have substitute_av := sign_available sg rAvail
  have different : ¬ SignedIn [g.result] spared := by
    intro together
    obtain ⟨phase,hs⟩ := signed_choice (signed_symmetric together)
    exact result_fresh h done cap (hs.symm ▸ sign_available phase qAvail)
  have masked : Masked mask g.result substitute := by
    intro r hr
    change g.result r = signed sg raw r
    rw [eq]
    cases sg <;> simp [signed,combine,hr,raw]
  obtain ⟨preOK,leftOK,rightOK,tailOK⟩ := (valid_append _ _ _).mp h
  have supply : Corresponds mask (g.result :: stock rawBase pre) (stock rawBase pre) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact ⟨substitute,substitute_av,masked⟩
    · exact ⟨x,Or.inl hx,fun _ _=>rfl⟩
  obtain ⟨rewired,length,valid,align,counts,endSupply⟩ := translate_steps tailOK
    masked substitute_av (signed_in sg) qAvail different supply
  rw [stock_append] at done
  obtain ⟨rewiredOutput,partialAvail,agrees⟩ := translate_av endSupply done
  let patch : Binary Row := ⟨true, mask, rewiredOutput⟩
  have restores : patch.result = whole := by
    funext r
    cases b : mask r
    · simpa only [patch,Binary.result,combine,ite_true,b,Bool.false_or] using (agrees r b).symm
    · simp [patch,Binary.result,combine,b,safe r b]
  have firstOK := (valid_append _ _ _).mpr ⟨preOK,valid⟩
  have patchOK : Valid (stock rawBase (pre++rewired)) [patch] := by
    rw [stock_append]
    exact ⟨stock_available maskAvail,partialAvail,trivial⟩
  have wholeOK := (valid_append _ _ _).mpr ⟨firstOK,patchOK⟩
  have answer : Available true (stock rawBase ((pre ++ rewired) ++ [patch])) whole := by
    rw [← restores]
    exact Or.inl (stock_mem.mpr (Or.inr ⟨patch,by simp,rfl⟩))
  have limit : ((pre ++ rewired) ++ [patch]).length ≤ 11 := by
    simp only [List.length_append,List.length_cons,List.length_nil] at cap ⊢
    omega
  have count := pivot_once wholeOK answer limit p
  rw [tally_append, tally_append] at count
  change tally (Reads [g.result]) suf ≤ tally (Reads [var (ix p)]) rewired at counts
  exact ⟨rewired,patch,length,wholeOK,answer,align,by omega⟩

theorem polarity_in {gs : List (Binary Row)} (h : Valid rawBase gs)
    (done : Available true (stock rawBase gs) whole) (cap : gs.length≤11)
    {g : Binary Row} (mem : g ∈ gs) (p : Fin 2) (sig : Bool)
    (side : signed sig (var (ix p)) = g.left ∨ signed sig (var (ix p)) = g.right) :
    g.disj = !sig := by
  obtain ⟨pre,g',suf,split,here,_⟩ := first_split (P:=fun x => x=g) ⟨g,mem,rfl⟩
  subst g'
  rw [split] at h done cap
  exact reader_polarity h done cap p sig side

theorem signed_twice (sg : Bool) (v : Wire R) :
    signed sg (signed sg v) = v := by rw [signs_compose]; cases sg <;> rfl

theorem combine_or_assoc (x y z : Wire R) :
    combine true (combine true x y) z = combine true x (combine true y z) := by
  funext r
  simp [combine,Bool.or_assoc]

noncomputable def trail (P : T → Prop) : List T → Nat
  | [] => 0
  | g :: gs => by
    classical
    exact (if P g then gs.length else 0) + trail P gs

theorem trail_cons_yes (P : T → Prop) {x : T} (h : P x) (gs : List T) :
    trail P (x::gs) = gs.length + trail P gs := by
  classical simp [trail,h]

theorem trail_cons_no (P : T → Prop) {x : T} (h : ¬ P x) (gs : List T) :
    trail P (x::gs) = trail P gs := by
  classical simp [trail,h]

theorem trail_append (P : T → Prop) (pre suf : List T) :
    trail P (pre++suf) = trail P pre + trail P suf + tally P pre * suf.length := by
  induction pre with
  | nil => simp [trail,tally]
  | cons g pre ih =>
    change trail P (g::(pre++suf)) = _
    by_cases read : P g
    · rw [trail_cons_yes _ read,trail_cons_yes _ read,tally_cons_yes _ read,ih,
        List.length_append,Nat.add_mul]
      omega
    · rw [trail_cons_no _ read,trail_cons_no _ read,tally_cons_no _ read,ih]

theorem trail_moved (P : T → Prop) {g v j v' : T}
    (pre mid tail : List T) (r : P g) (no : ¬ P v) (quiet : ¬ P j) (now : P v') :
    trail P (pre ++ (mid ++ j::v'::tail)) < trail P (pre ++ g::(mid++v::tail)) := by
  rw [trail_append P pre,trail_append P pre]
  simp only [List.length_append,List.length_cons]
  rw [trail_append P mid,trail_cons_no _ quiet,trail_cons_yes _ now,trail_cons_yes _ r,
    trail_append P mid,trail_cons_no _ no]
  simp only [List.length_append,List.length_cons, Nat.mul_add, Nat.mul_one]
  have bound := tally_le_len P mid
  omega

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem move_first (h : Valid rawBase gs) (done : Available true (stock rawBase gs) whole)
    (cap : gs.length≤11) :
    ∃ later : List (Binary Row), later.length = gs.length ∧
      Valid rawBase later ∧ Available true (stock rawBase later) whole ∧
      trail (Reads controls) later < trail (Reads controls) gs := by
  obtain ⟨reader,found,seen⟩ := pivot_used h done 0
  obtain ⟨pre,g,suf,orig,hg,noPre⟩ := first_split ⟨reader,found,control_reads seen⟩
  subst gs
  obtain ⟨p,rd⟩ := has_ctrl hg
  let q := otherPivot p
  have gMem : g ∈ pre ++ g::suf := List.mem_append.mpr (Or.inr List.mem_cons_self)
  have ledger := (valid_append _ _ _).mp h
  obtain ⟨sg,side,operands⟩ := operand_choice rd
  have polarity := reader_polarity h done cap p sg (matched_side operands)
  have av := matched_available operands ledger.2.1 ledger.2.2.1
  have sideQuiet : ¬ SignedIn controls side := by
    apply no_ctrl_signed
    intro r sees
    rcases pivot_cases p r with same|other
    · subst r
      obtain ⟨phase,e⟩ := signed_choice sees
      have repeatBase := combine_phases
        (stock_contains (xs:=pre) (raw_included (ix p))) sg phase g.disj
      rw [← e, ← matched_res operands] at repeatBase
      exact result_fresh h done cap repeatBase
    · subst r
      exact raw_other_read h done cap gMem p (ix q) (fun e => other_ne p (contr_ix e))
        rd (matched_reads (matched_comm operands) sees)
  let mask := signed sg side
  have maskAvail : Available true (stock rawBase pre) mask := sign_available sg av
  have maskQuiet : ¬ SignedIn controls mask := by
    apply no_ctrl_signed
    intro r hs
    exact sideQuiet (signed_mono
      (fun _ m=>(List.mem_singleton.mp m).symm ▸ control_mem r) (unsign_in sg hs))
  have normalG : g.result = signed sg (combine true (var (ix p)) mask) := by
    rw [matched_res operands,polarity]
    exact or_phase sg
  have safe := first_mask_true h done cap p sg rd noPre maskAvail maskQuiet normalG
  obtain ⟨rewired,patch,nLen,nValid,nOutput,align,oneUse⟩ :=
    unmask h done cap p sg maskAvail safe normalG
  have newCap : ((pre ++ rewired) ++ [patch]).length ≤ 11 := by
    simp only [List.length_append,List.length_cons,List.length_nil] at cap ⊢
    omega
  have notOutput := result_not_output h done cap p rd noPre
  obtain ⟨mid,u,tail,shape,readsG,_⟩ := first_split ((result_used h done cap).resolve_left notOutput)
  have uMem : u ∈ suf := by rw [shape]; simp
  obtain ⟨u',inRewired,al⟩ := aligned_mem align uMem
  have newMem : u' ∈ (pre ++ rewired) ++ [patch] :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr inRewired)))
  have newReads := aligned_read al (signed_in sg) readsG
  have noQ : ¬ Reads [var (ix q)] u := fun qRead =>
    raw_other_read nValid nOutput newCap newMem p (ix q) (fun e=>other_ne p (contr_ix e))
      newReads (al.2.2.2 qRead)
  have neither : ¬ Reads controls u := by
    intro seen
    obtain ⟨r,rr⟩ := has_ctrl seen
    rcases pivot_cases p r with same|other
    · subst r
      exact (read_once (pivot_once h done cap p) rd).2 u uMem rr
    · subst r
      exact noQ rr
  obtain ⟨sReader,other,matched⟩ := operand_choice readsG
  let combo := xor sReader sg
  have freshSide : signed combo (var (ix p)) = u'.left ∨ signed combo (var (ix p)) = u'.right := by
    rcases matched with e|e
    · exact Or.inl ((al.2.1 sReader e.1).trans (signs_compose _ _)).symm
    · exact Or.inr ((al.2.2.1 sReader e.2).trans (signs_compose _ _)).symm
  have uTag : u.disj = !combo := al.1.symm.trans (polarity_in nValid nOutput newCap newMem p combo freshSide)
  rw [shape] at h done cap oneUse
  obtain ⟨midAvoid,tailAvoid⟩ := read_once oneUse readsG
  have middle := (valid_append _ _ _).mp ((valid_append _ _ _).mp h).2.2.2
  have sideNotG : ¬ SignedIn [g.result] other := by
    intro ph
    obtain ⟨sOther,eq⟩ := signed_choice ph
    have prefixShape : (pre ++ g::mid) ++ u::tail = pre ++ g::(mid++u::tail) := by
      simp [List.append_assoc]
    have refuse := result_fresh (prefixShape.symm ▸ h) (prefixShape.symm ▸ done) (prefixShape.symm ▸ cap) (g:=u)
    have gaIn : g.result ∈ stock rawBase (pre ++ g::mid) := by
      rw [stock_append]
      change g.result ∈ stock (g.result :: stock rawBase pre) mid
      exact stock_contains List.mem_cons_self
    have repeated := combine_phases gaIn sReader sOther u.disj
    rw [← eq,← matched_res matched] at repeated
    exact refuse repeated
  have midSupply : ∀ w ∈ g.result::stock rawBase pre, w ≠ g.result → w ∈ stock rawBase pre := by
    intro w wm ne
    exact (List.mem_cons.mp wm).resolve_left ne
  obtain ⟨midValid,midStock⟩ := avoid_steps middle.1 midSupply midAvoid
  have otherAvail := avoid_available midStock (matched_available matched middle.2.1 middle.2.2.1) sideNotG
  let joined : Binary Row := ⟨true,mask,signed combo other⟩
  let fresh : Binary Row := ⟨!combo,signed combo (var (ix p)),signed combo joined.result⟩
  have same : fresh.result = u.result := by
    have uEq : u.result =
        signed combo (combine true (combine true (var (ix p)) mask) (signed combo other)) := by
      rw [matched_res matched,uTag,normalG, signs_compose]
      simpa only [combo] using (or_phase (a:=combine true (var (ix p)) mask) (b:=other) combo)
    change combine (!combo) (signed combo (var (ix p))) (signed combo joined.result) = u.result
    rw [or_phase combo,signed_twice,uEq,combine_or_assoc]
    rfl
  let earlier := stock (stock rawBase pre) mid
  have jAvail : Available true earlier mask ∧ Available true earlier (signed combo other) :=
    ⟨stock_available maskAvail,sign_available combo otherAvail⟩
  have fAvail : Available true (joined.result::earlier) (signed combo (var (ix p))) ∧
      Available true (joined.result::earlier) (signed combo joined.result) :=
    ⟨sign_available combo (Or.inl (List.mem_cons_of_mem _
       (stock_contains (stock_contains (raw_included (ix p)))))),
      sign_available combo (Or.inl List.mem_cons_self)⟩
  have suffixSupply : ∀ w ∈ u.result :: stock (g.result :: stock rawBase pre) mid,
      w ≠ g.result → w ∈ fresh.result :: joined.result :: earlier := by
    intro w wMem different
    rcases List.mem_cons.mp wMem with rfl|signal
    · rw [same]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (midStock _ signal different))
  obtain ⟨tailValid,tailStock⟩ := avoid_steps middle.2.2.2 suffixSupply tailAvoid
  have newWhole : Available true (stock rawBase (pre ++ (mid ++ joined::fresh::tail))) whole := by
    rw [stock_append] at done
    change Available true (stock (g.result :: stock rawBase pre) (mid++u::tail)) whole at done
    rw [stock_append] at done
    rw [stock_append,stock_append]
    exact avoid_available tailStock done notOutput
  have newValid : Valid rawBase (pre ++ (mid ++ joined::fresh::tail)) := by
    refine (valid_append _ _ _).mpr ⟨ledger.1,(valid_append _ _ _).mpr ⟨midValid,?_⟩⟩
    exact ⟨jAvail.1,jAvail.2,fAvail.1,fAvail.2,tailValid⟩
  have newRead : Reads controls fresh :=
    control_reads (Or.inl (signed_in combo) : Reads [var (ix p)] fresh)
  have noJoin : ¬ Reads controls joined := by
    intro tr
    apply tr.elim maskQuiet
    apply no_ctrl_signed
    intro r ha
    have non := no_controls neither r
    exact non (matched_reads (matched_comm matched) (unsign_in combo ha))
  rw [shape]
  exact ⟨pre ++ (mid ++ joined::fresh::tail),by simp [Nat.add_assoc], newValid, newWhole,
    trail_moved (Reads controls) pre mid tail hg neither noJoin newRead⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem trace_twelve (h : Valid rawBase gs) (done : Available true (stock rawBase gs) whole) :
    12 ≤ gs.length := by
  classical
  suffices noBound : ∀ k (xs : List (Binary Row)), trail (Reads controls) xs = k →
      Valid rawBase xs → Available true (stock rawBase xs) whole → ¬ (xs.length ≤ 11) by
    have impossible := noBound _ gs rfl h done
    omega
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro xs r valid output cap
    obtain ⟨later,len,ok,ans,decreases⟩ := move_first valid output cap
    rw [r] at decreases
    exact ih _ decreases later rfl ok ans (len.symm ▸ cap)

def evalPoint (r : Row) (i : Fin 6) : Bool := var i r

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem evalWhole : ∀ r : Row, projectedWire evalPoint sixTarget r = whole r := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem highFloor : Low 12 sixTarget := by
  intro n program
  obtain ⟨bank,reach,out⟩ := projectedProgram evalPoint rawBase program
    (spent:=0) Reach.start (by
      rintro u ⟨i,rfl⟩
      exact Or.inl (raw_included i))
  rw [show projectedWire evalPoint sixTarget = whole from funext evalWhole] at out
  obtain ⟨gs,len,valid,stockEq⟩ := trace_of_reach reach
  rw [←stockEq] at out
  have deep := trace_twelve valid out
  omega

end PEqualNP.Outside.L_meta_49113.ReadPair

namespace PEqualNP.Outside.L_meta_49113
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sixWitness : Circuit := ⟨[⟨.and, [4, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [10, 13]⟩, ⟨.and, [9, 14]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [1, 14]⟩, ⟨.and, [16, 17]⟩], 18⟩

theorem basis : Monotone2 sixWitness := by simp [Monotone2, sixWitness]

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem correct : ∀ x : X, sixWitness.eval (List.ofFn x) = sixTarget x := by decide +kernel

end PEqualNP.Outside.L_meta_49113

open PEqualNP.Outside.L_meta_49113 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_49113 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676744 * 2 ^ 32 + 3901261960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676744 * 2 ^ 32 + 3901261960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  by_cases enough : 13 ≤ s
  · exact ⟨sixWitness, basis, enough, correct⟩
  obtain ⟨⟨gs,o⟩, fit, size, computes⟩ := h
  have hf : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    exact ⟨by simpa using (fit g hg).1, (fit g hg).2⟩
  change gs.length ≤ s at size
  exact ⟨⟨gs,o⟩, all_not_not ReadPair.highFloor gs o hf (by omega) computes, size, computes⟩
