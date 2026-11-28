import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49097.Threshold

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

end PEqualNP.Outside.L_meta_49097.Threshold


namespace PEqualNP.Outside.L_meta_49097.Atlas.Model
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 64
def zero : Sig := 0
def one : Sig := BitVec.allOnes 64
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

def bit (i : Fin 64) (a : Sig) : Bool := a.getLsbD i.val
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
theorem getRep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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
        exact Or.inl (getRep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (getRep w i) (getRep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (getRep w i)

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

theorem extractPlan {u target} (gs : List Gate) (w : List Sig)
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

theorem bRead (i) (w : List Sig) (j : Nat) :
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
  simp only [bRead]
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

theorem exeBits (gs : List Gate) (i) (w : List Sig)
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

theorem canalize_left {R u d} (hd : allowed u d) (w : Bool → Wire R) :
    ∃ t, Constant (comb d (fun _ => t) (w t)) := by
  rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨false, false, by funext r; simp [comb, combine]⟩
  · exact ⟨true, true, by funext r; simp [comb, combine]⟩
  · exact ⟨false, false, by funext r; simp [comb, combine]⟩
  · exact ⟨true, false, by funext r; simp [comb, combine, inv]⟩

theorem canalize_right {R u d} (hd : allowed u d) (w : Bool → Wire R) :
    ∃ t, Constant (comb d (w t) (fun _ => t)) := by
  rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact ⟨false, false, by funext r; simp [comb, combine]⟩
  · exact ⟨true, true, by funext r; simp [comb, combine]⟩
  · exact ⟨true, false, by funext r; simp [comb, combine, inv]⟩
  · exact ⟨false, false, by funext r; simp [comb, combine]⟩

theorem contract_two {R S : Type} {u} {goal pivot : Wire R} {s ws}
    (run : Run u goal s ws) (rows : Bool → S → R)
    (value : ∀ b, restrictRows (rows b) pivot = (fun _ => b))
    (nonconstant : ∀ b, ¬Constant (restrictRows (rows b) goal))
    (occurs : pivot ∈ ws)
    (roots : Bool → List (Wire S)) {p : Nat} (banks : Bool → List (Wire S))
    (reached : ∀ b, Reach u (roots b) p (banks b))
    (supplied : ∀ b, supply u (banks b) (ws.map (restrictRows (rows b)))) :
    ∃ b q next, Reach u (roots b) q next ∧
      Available u next (restrictRows (rows b) goal) ∧ q+2 ≤ p+s := by
  induction run using Run.ind generalizing p banks with
  | stop =>
    have e : pivot = goal := List.mem_singleton.mp occurs
    exact False.elim (nonconstant false ⟨false, e ▸ value false⟩)
  | perm permutation _ ih =>
    apply ih (permutation.mem_iff.mpr occurs) banks reached
    intro b a ha
    exact supplied b a ((permutation.map _).mem_iff.mp ha)
  | @two steps a b rest op hd ka kb tail ih =>
    let next := comb op a b :: kept ka a (kept kb b rest)
    have pairA (t : Bool) : Available u (banks t) (restrictRows (rows t) a) :=
      supplied t _ (List.mem_map_of_mem (by simp))
    have pairB (t : Bool) : Available u (banks t) (restrictRows (rows t) b) :=
      supplied t _ (List.mem_map_of_mem (by simp))
    have held (t : Bool) {pool} (stable : ∀ w, Available u (banks t) w → Available u pool w)
        (head : Available u pool (restrictRows (rows t) (comb op a b))) :
        supply u pool (next.map (restrictRows (rows t))) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      rcases List.mem_cons.mp hv with rfl | keep
      · exact head
      · apply stable
        apply supplied
        apply List.mem_map_of_mem
        rcases mem_kept keep with rfl | keep
        · simp
        · rcases mem_kept keep with rfl | keep
          · simp
          · simp [keep]
    by_cases used : pivot = a ∨ pivot = b
    · have choose : ∃ t, Constant (restrictRows (rows t) (comb op a b)) := by
        rcases used with eq | eq
        · subst a
          obtain ⟨t, hc⟩ := canalize_left hd (fun t => restrictRows (rows t) b)
          refine ⟨t, ?_⟩
          rw [restrict_comb, value]
          exact hc
        · subst b
          obtain ⟨t, hc⟩ := canalize_right hd (fun t => restrictRows (rows t) a)
          refine ⟨t, ?_⟩
          rw [restrict_comb, value]
          exact hc
      obtain ⟨t, hc⟩ := choose
      have sp := held t (fun _ h => h) (Or.inr (Or.inl hc))
      obtain ⟨q, out, reach, found, smaller⟩ :=
        contraction (nonconstant t) (restrict_run (rows t) tail) (roots t) (reached t) sp
      have one : 1 ≤ mass (next.map (restrictRows (rows t))) := by
        classical
        simp [next, mass_cons, cost, hc]
      dsimp only [next] at one
      exact ⟨t, q, out, reach, found, by omega⟩
    · have inRest : pivot ∈ rest := by simpa [List.mem_cons, not_or.mp used] using occurs
      have inNext : pivot ∈ next := by cases ka <;> cases kb <;> simp [next, kept, inRest]
      have all (t : Bool) : ∃ pool, Reach u (roots t) (p+1) pool ∧
          supply u pool (next.map (restrictRows (rows t))) := by
        obtain ⟨binOp, x, y, eq, hx, hy, _, _⟩ := comb_prime hd (pairA t) (pairB t)
        have new := Reach.two binOp (reached t) hx hy
        refine ⟨_, new, held t (fun _ h => available_cons _ h) ?_⟩
        rw [restrict_comb, eq]
        exact Or.inl (by simp)
      choose pools reach sp using all
      obtain ⟨t, q, out, rch, found, smaller⟩ := ih inNext pools reach sp
      exact ⟨t, q, out, rch, found, by omega⟩

abbrev Row := Fin 64
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
theorem input_list : List.ofFn (fun j : Fin 6 => inputs.getD j.val zero) = inputs := rfl
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
  if h : r.val < 64-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(64-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 64 (64-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 64-d.val <;> simp [shifted,h,r.isLt]

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
  (List.range 6).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def fixRows (z o : Nat) : List Move :=
  (List.range 6).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 64 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 64 d)

theorem lower_two_slices {u roots T pivot L}
    (properT : proper T) (plainT : plainWord T = true) (plainRoots : roots.all plainWord = true)
    (essential : Essential T roots pivot) (rows : Bool → Row → Row)
    (sub : Bool → List Sig) (goals : Bool → Sig)
    (mapTarget : ∀ b, rename (rows b) T = goals b)
    (mapRoots : ∀ b a, a ∈ roots → Available u ((sub b).map observe) (observe (rename (rows b) a)))
    (value : ∀ b, restrictRows (rows b) (observe pivot) = (fun _ => b))
    (properGoals : ∀ b, proper (goals b))
    (bounds : ∀ b, Lower u (sub b) (goals b) L) :
    Lower u roots T (L+2) := by
  intro p bank reachable hit
  obtain ⟨k, states, le, live, root⟩ := reach_live properT plainT plainRoots reachable hit
  obtain ⟨i, j, different, isolated⟩ := essential
  have pivotMem := raw_required live roots pivot root i j different isolated
  let front := states.toList.map observe
  have run : Run u (observe T) k front :=
    list_run live states.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have occurs : observe pivot ∈ front :=
    List.mem_map_of_mem (Finset.mem_toList.mpr pivotMem)
  have target (b : Bool) : restrictRows (rows b) (observe T) = observe (goals b) :=
    (observe_rename (rows b) T).symm.trans (congrArg observe (mapTarget b))
  have nonconstant (b : Bool) : ¬Constant (restrictRows (rows b) (observe T)) := by
    rw [target]
    exact observe_proper (properGoals b)
  let banks := fun b => (sub b).map observe
  have covered (b : Bool) : supply u (banks b) (front.map (restrictRows (rows b))) := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    rw [←observe_rename]
    exact mapRoots b w (root _ (Finset.mem_toList.mp hw))
  obtain ⟨b, q, out, reached, got, weighted⟩ :=
    contract_two run rows value nonconstant occurs banks banks (fun _ => Reach.start) covered
  rw [target] at got
  have enough := bounds b q out reached got
  omega

theorem lower_cubes_two {u raw base0 base1 T G0 G1 j L r s z0 o0 z1 o1}
    (essential : checkEssential T raw [(inputs.getD j zero, r, s)] = true)
    (lowMap : checkMap (fixRows z0 o0) raw T base0 G0 = true)
    (highMap : checkMap (fixRows z1 o1) raw T base1 G1 = true)
    (lowBit : movedWord (fixRows z0 o0) (inputs.getD j zero) = zero)
    (highBit : movedWord (fixRows z1 o1) (inputs.getD j zero) = one)
    (properT : proper T) (proper0 : proper G0) (proper1 : proper G1)
    (low : Lower u base0 G0 L) (high : Lower u base1 G1 L) : Lower u raw T (L+2) := by
  let moves : Bool → List Move := fun b => if b then fixRows z1 o1 else fixRows z0 o0
  let sub : Bool → List Sig := fun b => if b then base1 else base0
  let goal : Bool → Sig := fun b => if b then G1 else G0
  have maps (b : Bool) : checkMap (moves b) raw T (sub b) (goal b) = true := by
    cases b
    · exact lowMap
    · exact highMap
  apply lower_two_slices properT (essential_plain essential).1 (essential_plain essential).2
    (essential_ok essential (inputs.getD j zero) (by simp)) (fun b => movedRow (moves b)) sub goal
  · exact fun b => (map_correct (u:=u) (maps b)).1
  · exact fun b => (map_correct (u:=u) (maps b)).2
  · intro b
    rw [←observe_rename, ←moved_eq_rename]
    cases b <;> change observe (movedWord _ _) = _
    · rw [show movedWord (moves false) (inputs.getD j zero) = zero from lowBit]
      exact funext bit_zero
    · rw [show movedWord (moves true) (inputs.getD j zero) = one from highBit]
      exact funext bit_one
  · intro b
    cases b
    · exact proper0
    · exact proper1
  · intro b
    cases b
    · exact low
    · exact high

theorem lower_fix_two {u raw base0 base1 T G0 G1 j L r s}
    (essential : checkEssential T raw [(inputs.getD j zero, r, s)] = true)
    (lowMap : checkMap (fixRows (1 <<< j) 0) raw T base0 G0 = true)
    (highMap : checkMap (fixRows 0 (1 <<< j)) raw T base1 G1 = true)
    (lowBit : movedWord (fixRows (1 <<< j) 0) (inputs.getD j zero) = zero)
    (highBit : movedWord (fixRows 0 (1 <<< j)) (inputs.getD j zero) = one)
    (properT : proper T) (proper0 : proper G0) (proper1 : proper G1)
    (low : Lower u base0 G0 L) (high : Lower u base1 G1 L) : Lower u raw T (L+2) :=
  lower_cubes_two essential lowMap highMap lowBit highBit properT proper0 proper1 low high

theorem lower_weaken {u roots T m n} (lower : Lower u roots T m) (le : n ≤ m) :
    Lower u roots T n :=
  fun p bank reached hit => le.trans (lower p bank reached hit)

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
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

abbrev Bits := BitVec 128
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 128 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 128 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 128 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 128 → Row) (x : Decor) := x.2 = pairSig r s x.1
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
def asRow (cols : Nat → Bits) (i : Fin 128) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 6 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem input_coords : ∀ (j : Fin 6) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 128) (j : Fin 6) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 6 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<6 ∧ a=inputs.getD j zero := by
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
  ((n*n % 2305843009213693951)*(n+7)+971*n) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun n w => n+keyWord w) 0

theorem contract_two_cost {R S : Type} {u} {goal pivot : Wire R} {s ws}
    (run : Run u goal s ws) (rows : Bool → S → R)
    (value : ∀ b, restrictRows (rows b) pivot = (fun _ => b))
    (nonconstant : ∀ b, ¬Constant (restrictRows (rows b) goal))
    (occurs : pivot ∈ ws)
    (roots : Bool → List (Wire S)) {charges : Bool → Nat} (banks : Bool → List (Wire S))
    (reached : ∀ b, Reach u (roots b) (charges b) (banks b))
    (supplied : ∀ b, supply u (banks b) (ws.map (restrictRows (rows b)))) :
    ∃ b q next, Reach u (roots b) q next ∧
      Available u next (restrictRows (rows b) goal) ∧ q+2 ≤ charges b+s := by
  induction run using Run.ind generalizing charges banks with
  | stop =>
    have e : pivot = goal := List.mem_singleton.mp occurs
    exact False.elim (nonconstant false ⟨false, e ▸ value false⟩)
  | perm permutation _ ih =>
    apply ih (permutation.mem_iff.mpr occurs) banks reached
    intro b a ha
    exact supplied b a ((permutation.map _).mem_iff.mp ha)
  | @two steps a b rest op hd ka kb tail ih =>
    let next := comb op a b :: kept ka a (kept kb b rest)
    have pairA (t : Bool) : Available u (banks t) (restrictRows (rows t) a) :=
      supplied t _ (List.mem_map_of_mem (by simp))
    have pairB (t : Bool) : Available u (banks t) (restrictRows (rows t) b) :=
      supplied t _ (List.mem_map_of_mem (by simp))
    have held (t : Bool) {pool} (stable : ∀ w, Available u (banks t) w → Available u pool w)
        (head : Available u pool (restrictRows (rows t) (comb op a b))) :
        supply u pool (next.map (restrictRows (rows t))) := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      rcases List.mem_cons.mp hv with rfl | keep
      · exact head
      · apply stable
        apply supplied
        apply List.mem_map_of_mem
        rcases mem_kept keep with rfl | keep
        · simp
        · rcases mem_kept keep with rfl | keep
          · simp
          · simp [keep]
    by_cases used : pivot = a ∨ pivot = b
    · have choose : ∃ t, Constant (restrictRows (rows t) (comb op a b)) := by
        rcases used with eq | eq
        · subst a
          obtain ⟨t, hc⟩ := canalize_left hd (fun t => restrictRows (rows t) b)
          refine ⟨t, ?_⟩
          rw [restrict_comb, value]
          exact hc
        · subst b
          obtain ⟨t, hc⟩ := canalize_right hd (fun t => restrictRows (rows t) a)
          refine ⟨t, ?_⟩
          rw [restrict_comb, value]
          exact hc
      obtain ⟨t, hc⟩ := choose
      have sp := held t (fun _ h => h) (Or.inr (Or.inl hc))
      obtain ⟨q, out, reach, found, smaller⟩ :=
        contraction (nonconstant t) (restrict_run (rows t) tail) (roots t) (reached t) sp
      have one : 1 ≤ mass (next.map (restrictRows (rows t))) := by
        classical
        simp [next, mass_cons, cost, hc]
      dsimp only [next] at one
      exact ⟨t, q, out, reach, found, by omega⟩
    · have inRest : pivot ∈ rest := by simpa [List.mem_cons, not_or.mp used] using occurs
      have inNext : pivot ∈ next := by cases ka <;> cases kb <;> simp [next, kept, inRest]
      have all (t : Bool) : ∃ pool, Reach u (roots t) (charges t+1) pool ∧
          supply u pool (next.map (restrictRows (rows t))) := by
        obtain ⟨binOp, x, y, eq, hx, hy, _, _⟩ := comb_prime hd (pairA t) (pairB t)
        have new := Reach.two binOp (reached t) hx hy
        refine ⟨_, new, held t (fun _ h => available_cons _ h) ?_⟩
        rw [restrict_comb, eq]
        exact Or.inl (by simp)
      choose pools reach sp using all
      obtain ⟨t, q, out, rch, found, smaller⟩ := ih inNext (charges := fun t => charges t + 1) pools reach sp
      exact ⟨t, q, out, rch, found, by omega⟩

def dualPoolCut (c0 c1 : BoundPool) (cap : Nat) (ws : List Sig) : Bool :=
  decide (cap + c0.paid < c0.bound + 2) &&
  (decide (cap + c1.paid < c1.bound + 2) &&
  (ws.all (availableB true c0.domain c0.wires) &&
  (ws.all (availableB true c1.domain c1.wires) &&
  ws.any (fun pivot => masked c0.domain pivot == zero && masked c1.domain pivot == c1.domain))))

theorem dualPoolCut_sound {raw T c0 c1 cap ws}
    (valid0 : ValidPool true raw T c0) (valid1 : ValidPool true raw T c1)
    (nd : ws.Nodup) (test : dualPoolCut c0 c1 cap ws = true) :
    Impossible true T cap ws.toFinset := by
  intro steps hcap run
  simp only [dualPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, beq_iff_eq] at test
  obtain ⟨small0, small1, all0, all1, pivot, hpivot, zeroed, oned⟩ := test
  obtain ⟨f0, roots0, bank0, dom0, nc0, low0, paid0, avail0, _⟩ := valid0
  obtain ⟨f1, roots1, bank1, dom1, nc1, low1, paid1, avail1, _⟩ := valid1
  let rows : Bool → Row → Row := fun b => if b then f1 else f0
  let roots : Bool → List (Wire Row) := fun b => if b then roots1.map observe else roots0.map observe
  let banks : Bool → List (Wire Row) := fun b => if b then bank1 else bank0
  let charges : Bool → Nat := fun b => if b then c1.paid else c0.paid
  have nonconstant (b : Bool) : ¬Constant (restrictRows (rows b) (observe T)) := by
    cases b
    · exact nc0
    · exact nc1
  have value (b : Bool) : restrictRows (rows b) (observe pivot) = (fun _ => b) := by
    cases b
    · exact masked_zero dom0 zeroed
    · exact masked_one dom1 oned
  have reached (b : Bool) : Reach true (roots b) (charges b) (banks b) := by
    cases b
    · exact paid0
    · exact paid1
  have supplied (b : Bool) : supply true (banks b) ((ws.map observe).map (restrictRows (rows b))) := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    cases b
    · exact availableB_sound dom0 avail0 (all0 v hv)
    · exact availableB_sound dom1 avail1 (all1 v hv)
  have occurs : observe pivot ∈ ws.map observe := List.mem_map_of_mem hpivot
  obtain ⟨b, q, next, reach, hit, weighted⟩ :=
    contract_two_cost (list_run run ws nd rfl) rows value nonconstant occurs roots (charges := charges) banks reached supplied
  cases b
  · have enough := low0 q next reach hit
    change q + 2 ≤ c0.paid + steps at weighted
    omega
  · have enough := low1 q next reach hit
    change q + 2 ≤ c1.paid + steps at weighted
    omega

abbrev CutData := BoundPool × Option BoundPool
def ValidCut (u : Bool) (raw : List Sig) (T : Sig) (c : CutData) :=
  ValidPool u raw T c.1 ∧ ∀ b, c.2 = some b → u = true ∧ ValidPool true raw T b

def cutTest (u : Bool) (c : CutData) (k : Nat) (rest : List Sig) (op : Choice) :=
  match c.2 with
  | none => scalarPoolCut u c.1 k rest op
  | some b => dualPoolCut c.1 b k (choiceVal op :: rest)

theorem cutTest_sound {u raw T c k rest op} (v : ValidCut u raw T c)
    (nd : (choiceVal op :: rest).Nodup) (check : cutTest u c k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  cases h : c.2 with
  | none =>
    simp only [cutTest,h] at check
    exact scalarPoolCut_sound v.1 nd check
  | some b =>
    obtain ⟨rfl,hb⟩ := v.2 b h
    simp only [cutTest,h] at check
    exact dualPoolCut_sound v.1 hb nd check

def closeChild (u : Bool) (pools : Nat → List CutData) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || (pools (keySet ws)).any (fun p => cutTest u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ tag p, p ∈ pools tag → ValidCut u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact cutTest_sound (pValid _ _ hp) nd ok

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

abbrev NodeContext := Nat × Nat × List Decor × CovPair × (Nat → List CutData) × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 128 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ tag p, p ∈ pools tag → ValidCut u raw T p)
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 128) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 128 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
    (pv : ∀ tag p, p ∈ pools tag → ValidCut u raw T p)
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
  by_cases hj : j<6
  · let i : Fin 6 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 64 ≤ 2^j := by
      change 2^6 ≤ 2^j
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

theorem reflectState {u T k} (ws : List Sig) (p : List Move)
    (ok : autoOK T p = true) (low : Impossible u T k ws.toFinset) :
    Impossible u T k (ws.map (movedWord p.reverse)).toFinset := rotate_excluded low p ok

abbrev Observed (p q : Fin 128 → Row) := {v : Decor // faithful p q v}

def inputObserved (m : Nat) (p q : Nat → Bits) (i : Nat) :
    Observed (asRow p) (asRow q) :=
  ⟨(rawDecor m p q).getD i defaultDecor, faithful_get (raw_faithful m p q) i⟩

def combineObserved {p q} (d : Nat) (a b : Observed p q) : Observed p q :=
  ⟨dbin d a.val b.val, faithful_bin d a.property b.property⟩

abbrev Closed (T : Sig) (k : Nat) := { ws : List Sig // Impossible true T k ws.toFinset }
def rotateClosed {T k} (c : Closed T k) (p : List Move)
    (ok : autoOK T p = true) : Closed T k :=
  ⟨c.val.map (movedWord p.reverse), rotate_excluded c.property p ok⟩

abbrev Pool (raw : List Sig) (T : Sig) := { c : BoundPool // ValidPool true raw T c }

def checkedPool {raw T dom n} (slice : Slice true raw T dom n)
    (cs : List Choice) (c : BoundPool) (ok : materialize true raw cs dom n = some c) : Pool raw T :=
  ⟨c, materialize_sound slice ok⟩

def prefixPool {raw T d n} (slice : Slice true raw T d n) (cs : List Choice)
    (ok : makePool true d raw cs = some (cs.reverse.map choiceVal ++ raw)) : Pool raw T :=
  checkedPool slice cs (d,n,cs.length,cs.reverse.map choiceVal ++ raw)
    (by simp only [materialize,ok,Option.map_some,Option.some.injEq])

abbrev ChosenPool (raw : List Sig) (T : Sig) := {c : CutData // ValidCut true raw T c}
def usePool {raw T} (p : Pool raw T) : ChosenPool raw T :=
  ⟨(p.val,none),p.property,by simp⟩
def joinPools {raw T} (p q : Pool raw T) : ChosenPool raw T :=
  ⟨(p.val,some q.val),p.property,by
    intro b hb
    change some q.val = some b at hb
    cases Option.some.inj hb
    exact ⟨rfl,q.property⟩⟩
def stateCheck {p q T raw} (k : Nat) (ws : List (Observed p q))
    (route : Nat → List (ChosenPool raw T) × List (Closed T (k-1))) : Bool :=
  let items := ws.map Subtype.val
  let vs := items.map Prod.fst
  decide vs.Nodup && !vs.contains T &&
    testAll (k, items.length, items, preCov true items, (fun h => (route h).1.map Subtype.val),
      fun h => (route h).2.map Subtype.val) items

def closeState {T raw p q} (pairs : properPairs T p q) (k : Nat) (ws : List (Observed p q))
    (route : Nat → List (ChosenPool raw T) × List (Closed T (k-1)))
    (ok : stateCheck k ws route = true) : Closed T k := by
  let items := ws.map Subtype.val
  refine ⟨items.map Prod.fst, ?_⟩
  simp only [stateCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not] at ok
  apply node_sound (raw := raw) pairs _ ok.1.1 ok.1.2 _ _ ok.2
  · intro x hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    exact a.property
  · intro _ c hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
    exact a.property
  · intro _ ys hy
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hy
    exact a.property

def chooseRoute {α β : Type} (p : Array α) (below : Array β) (i : Nat) : List α × List β :=
  if i < p.size then ((p[i]?).toList, []) else ([],(below[i-p.size]?).toList)

theorem fromClosed {raw T k} (c : Closed T k)
    (names : c.val.toFinset = raw.toFinset) (xs : List (Sig × Row × Row))
    (pr : proper T) (check : checkEssential T raw xs = true) (all : xs.map Prod.fst = raw) :
    Lower true raw T (k+1) := by
  apply lower_impossible pr (essential_plain check).1 (essential_plain check).2
  · intro a ha
    exact essential_ok check a (List.mem_toFinset.mpr (all ▸ ha))
  · rw [← names]
    exact c.property

end PEqualNP.Outside.L_meta_49097.Atlas.Model
namespace PEqualNP.Outside.L_meta_49097.Atlas
open PEqualNP.Outside.L_meta_49097.Atlas.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace B0
def R : List Sig := vars 7
def T : Sig := 0xe8e8e8e8e8e8e8e8
def P : Nat → Bits
  | 0 => ((0xbecfbecfbecfbecf : BitVec 64) ++ (0xbecfbecfbecfbecf : BitVec 64))
  | 1 => ((0xdf73df73df73df73 : BitVec 64) ++ (0xdf73df73df73df73 : BitVec 64))
  | 2 => ((0xefbcefbcefbcefbc : BitVec 64) ++ (0xefbcefbcefbcefbc : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x4205420542054205 : BitVec 64) ++ (0x4205420542054205 : BitVec 64))
  | 1 => ((0x2412241224122412 : BitVec 64) ++ (0x2412241224122412 : BitVec 64))
  | 2 => ((0x1828182818281828 : BitVec 64) ++ (0x1828182818281828 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 7 P N 0
def w1 := inputObserved 7 P N 1
def w2 := inputObserved 7 P N 2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w1, w2]
  (fun _ => ([], [])) (by decide +kernel)
theorem low : Lower true R T 4 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B0

namespace B1
def R : List Sig := vars 15
def T : Sig := 0xe888e888e888e888
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 0 8) (raw := R)
    (T := T) (xs := [(0xff00ff00ff00ff00, 5, 13)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B0.low
  have he : (([(0xff00ff00ff00ff00, 5, 13)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B1

namespace B2
def R : List Sig := vars 23
def T : Sig := 0xe8e88888e8e88888
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 67]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B1.low
end B2

namespace B3
def R : List Sig := vars 27
def T : Sig := 0xee888888ee888888
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 66]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B1.low
end B3

namespace B4
def R : List Sig := vars 11
def T : Sig := 0xee88ee88ee88ee88
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B4

namespace B5
def R : List Sig := vars 19
def T : Sig := 0xeeee8888eeee8888
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 66]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B5

namespace B6
def R : List Sig := vars 13
def T : Sig := 0xfaa0faa0faa0faa0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B6

namespace B7
def R : List Sig := vars 14
def T : Sig := 0xfcc0fcc0fcc0fcc0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 48]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B7

namespace B8
def R : List Sig := vars 15
def T : Sig := 0xe880e880e880e880
def P : Nat → Bits
  | 0 => ((0xfc7fefee3fff8ff8 : BitVec 64) ++ (0xffdfdc7fff1ff1ff : BitVec 64))
  | 1 => ((0xff8ff7f7c7fff1ff : BitVec 64) ++ (0x1fefef8fffe3fe3f : BitVec 64))
  | 2 => ((0x1ff1fbfbf8fffe3f : BitVec 64) ++ (0xe3f7f7f1fffc7fc7 : BitVec 64))
  | 3 => ((0xe3fe3dfdff1fffc7 : BitVec 64) ++ (0xfc7bfbfe3fff8ff8 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x2436d021c9258248 : BitVec 64) ++ (0x6da043924b0490db : BitVec 64))
  | 1 => ((0x498b48407a4a9093 : BitVec 64) ++ (0x169080f49521262d : BitVec 64))
  | 2 => ((0x12d1848097932425 : BitVec 64) ++ (0xa309012f26484b46 : BitVec 64))
  | 3 => ((0x836c030124fc4906 : BitVec 64) ++ (0xd8060249f8920db0 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 15 P N 0
def w1 := inputObserved 15 P N 1
def w2 := inputObserved 15 P N 2
def w3 := inputObserved 15 P N 3
theorem s0 : Slice true R T 0xaaaaaaaaaaaaaaaa 4 :=
  slice_correct (ms := fixRows 0 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B7.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
theorem s2 : Slice true R T 0xcccccccccccccccc 4 :=
  slice_correct (ms := fixRows 0 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
def v0 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p2)] #[] ((((0x1442120181102 : Nat) >>> (((h / 8 + (((0xc189 : Nat) >>> ((h % 8) * 2)) &&& 3)) % 25) * 2)) &&& 3))) (by decide +kernel)
theorem low : Lower true R T 6 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 6, 7), (0xcccccccccccccccc, 5, 7), (0xf0f0f0f0f0f0f0f0, 3, 7), (0xff00ff00ff00ff00, 3, 11)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B8

namespace B9
def R : List Sig := vars 29
def T : Sig := 0xfaa0a000faa0a000
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B8.low
end B9

namespace B10
def R : List Sig := vars 11
def T : Sig := 0x8800880088008800
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 10, 11), (0xcccccccccccccccc, 9, 11), (0xff00ff00ff00ff00, 3, 11)] (by decide +kernel)
end B10

namespace B11
def R : List Sig := vars 15
def T : Sig := 0xe880e880e880e880
def P : Nat → Bits
  | 0 => ((0xfc7fefee3fff8ff8 : BitVec 64) ++ (0xffdfdc7fff1ff1ff : BitVec 64))
  | 1 => ((0xff8ff7f7c7fff1ff : BitVec 64) ++ (0x1fefef8fffe3fe3f : BitVec 64))
  | 2 => ((0x1ff1fbfbf8fffe3f : BitVec 64) ++ (0xe3f7f7f1fffc7fc7 : BitVec 64))
  | 3 => ((0xe3fe3dfdff1fffc7 : BitVec 64) ++ (0xfc7bfbfe3fff8ff8 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x2436d021c9258248 : BitVec 64) ++ (0x6da043924b0490db : BitVec 64))
  | 1 => ((0x498b48407a4a9093 : BitVec 64) ++ (0x169080f49521262d : BitVec 64))
  | 2 => ((0x12d1848097932425 : BitVec 64) ++ (0xa309012f26484b46 : BitVec 64))
  | 3 => ((0x836c030124fc4906 : BitVec 64) ++ (0xd8060249f8920db0 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 15 P N 0
def w1 := inputObserved 15 P N 1
def w2 := inputObserved 15 P N 2
def w3 := inputObserved 15 P N 3
theorem s0 : Slice true R T 0xcccccccccccccccc 4 :=
  slice_correct (ms := fixRows 0 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0xaaaaaaaaaaaaaaaa 4 :=
  slice_correct (ms := fixRows 0 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B7.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
def w4 := combineObserved 0 w0 w1
def w5 := combineObserved 0 w0 w2
def w6 := combineObserved 0 w1 w2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w4, w5, w6, w3]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0xff00ff00ff00ff00 4 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 2 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B10.low
def p3 : Pool R T := prefixPool s3 [] (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 4 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B4.low
def p4 : Pool R T := prefixPool s4 [(0, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (3, 0x8080808080808080, 0xff00ff00ff00ff00)] (by decide +kernel)
def w7 := combineObserved 0 w4 w2
def v1 : Closed T 4 := closeState (raw := R) properPN 4 [w7, w0, w1, w2, w3]
  (fun _ => ([(usePool p2), (joinPools p3 p4)], [])) (by decide +kernel)
def w8 := combineObserved 0 w2 w3
def w9 := combineObserved 3 w8 w0
def v2 : Closed T 4 := closeState (raw := R) properPN 4 [w9, w0, w1, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def p5 : Pool R T := prefixPool s4 [] (by decide +kernel)
def v3 : Closed T 4 := closeState (raw := R) properPN 4 [w4, w5, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p5)] #[v0] ((((0x84 : Nat) >>> ((h % 9) * 2)) &&& 3))) (by decide +kernel)
def a0 : List Move := [swapRows 33, swapRows 48]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 4 := rotateClosed v2 a0 a0ok
def a1 : List Move := [swapRows 49, swapRows 32]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def r1 : Closed T 4 := rotateClosed v2 a1 a1ok
def a2 : List Move := [swapRows 50]
theorem a2ok : autoOK T a2 = true := by decide +kernel
def r2 : Closed T 4 := rotateClosed v1 a2 a2ok
def a3 : List Move := [swapRows 16]
theorem a3ok : autoOK T a3 = true := by decide +kernel
def r3 : Closed T 4 := rotateClosed v3 a3 a3ok
def r4 : Closed T 4 := rotateClosed v3 a2 a2ok
def a4 : List Move := [swapRows 50, swapRows 16]
theorem a4ok : autoOK T a4 = true := by decide +kernel
def r5 : Closed T 4 := rotateClosed v3 a4 a4ok
def v4 : Closed T 5 := closeState (raw := R) properPN 5 [w4, w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p5), (usePool p2)] #[r0, r1, v1, r2, v3, r3, r4, r5] ((((((0x10b1119302 : Nat) <<< 64) ||| 0x8a21010740315600) >>> (((h / 8 + (((0xec000a : Nat) >>> ((h % 8) * 3)) &&& 7)) % 26) * 4)) &&& 15))) (by decide +kernel)
def a5 : List Move := [swapRows 32]
theorem a5ok : autoOK T a5 = true := by decide +kernel
def r6 : Closed T 5 := rotateClosed v4 a5 a5ok
def a6 : List Move := [swapRows 33]
theorem a6ok : autoOK T a6 = true := by decide +kernel
def r7 : Closed T 5 := rotateClosed v4 a6 a6ok
def r8 : Closed T 5 := rotateClosed v4 a0 a0ok
def a7 : List Move := [swapRows 48]
theorem a7ok : autoOK T a7 = true := by decide +kernel
def r9 : Closed T 5 := rotateClosed v4 a7 a7ok
def a8 : List Move := [swapRows 49]
theorem a8ok : autoOK T a8 = true := by decide +kernel
def r10 : Closed T 5 := rotateClosed v4 a8 a8ok
def v5 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p1), (usePool p0), (usePool p5), (usePool p2)] #[v4, r6, r7, r8, r9, r10] ((((((0x320367108 : Nat) <<< 64) ||| 0x2350104030391) >>> (((h / 8 + (((0x360b0231 : Nat) >>> ((h % 8) * 4)) &&& 15)) % 25) * 4)) &&& 15))) (by decide +kernel)
theorem low : Lower true R T 7 :=
  fromClosed v5 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 6, 7), (0xcccccccccccccccc, 5, 7), (0xf0f0f0f0f0f0f0f0, 3, 7), (0xff00ff00ff00ff00, 3, 11)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B11

namespace B12
def R : List Sig := vars 29
def T : Sig := 0xfaa0a000faa0a000
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B11.low
end B12

namespace B13
def R : List Sig := vars 21
def T : Sig := 0xfafaa0a0fafaa0a0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B13

namespace B14
def R : List Sig := vars 30
def T : Sig := 0xfcc0c000fcc0c000
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B8.low
end B14

namespace B15
def R : List Sig := vars 30
def T : Sig := 0xfcc0c000fcc0c000
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B11.low
end B15

namespace B16
def R : List Sig := vars 22
def T : Sig := 0xfcfcc0c0fcfcc0c0
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B16

namespace B17
def R : List Sig := vars 15
def T : Sig := 0xfee8fee8fee8fee8
def P : Nat → Bits
  | 0 => ((0xec33efee19e3bbd8 : BitVec 64) ++ (0x67dfdc33c777b0cf : BitVec 64))
  | 1 => ((0xf4ccf7f6667c3de9 : BitVec 64) ++ (0x99efecccf87bd333 : BitVec 64))
  | 2 => ((0xfb0f3bfb879fc1f6 : BitVec 64) ++ (0x1e77f70f3f83ec3c : BitVec 64))
  | 3 => ((0x3f03dfdf81ffe07 : BitVec 64) ++ (0xe07bfbf03ffc0fc0 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x20115020a2008840 : BitVec 64) ++ (0x22a0414401108045 : BitVec 64))
  | 1 => ((0x4044884108841080 : BitVec 64) ++ (0x8910821108210112 : BitVec 64))
  | 2 => ((0x810a048050290102 : BitVec 64) ++ (0x140900a052020428 : BitVec 64))
  | 3 => ((0x2a0030005522005 : BitVec 64) ++ (0x4006000aa4400a80 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 15 P N 0
def w1 := inputObserved 15 P N 1
def w2 := inputObserved 15 P N 2
def w3 := inputObserved 15 P N 3
theorem s0 : Slice true R T 0x5555555555555555 4 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B7.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0xff00ff00ff00ff 4 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
theorem s2 : Slice true R T 0x3333333333333333 4 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
def v0 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p0), (usePool p1), (usePool p2)] #[] ((((0x1442120181102 : Nat) >>> (((h / 8 + (((0xc189 : Nat) >>> ((h % 8) * 2)) &&& 3)) % 25) * 2)) &&& 3))) (by decide +kernel)
theorem low : Lower true R T 6 :=
  fromClosed v0 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B17

namespace B18
def R : List Sig := vars 11
def T : Sig := 0xffeeffeeffeeffee
theorem low : Lower true R T 2 := by
  exact lower_count (proper_of _ (by decide)) [(0xaaaaaaaaaaaaaaaa, 0, 1), (0xcccccccccccccccc, 0, 2), (0xff00ff00ff00ff00, 0, 8)] (by decide +kernel)
end B18

namespace B19
def R : List Sig := vars 15
def T : Sig := 0xfee8fee8fee8fee8
def P : Nat → Bits
  | 0 => ((0xec33efee19e3bbd8 : BitVec 64) ++ (0x67dfdc33c777b0cf : BitVec 64))
  | 1 => ((0xf4ccf7f6667c3de9 : BitVec 64) ++ (0x99efecccf87bd333 : BitVec 64))
  | 2 => ((0xfb0f3bfb879fc1f6 : BitVec 64) ++ (0x1e77f70f3f83ec3c : BitVec 64))
  | 3 => ((0x3f03dfdf81ffe07 : BitVec 64) ++ (0xe07bfbf03ffc0fc0 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0x20115020a2008840 : BitVec 64) ++ (0x22a0414401108045 : BitVec 64))
  | 1 => ((0x4044884108841080 : BitVec 64) ++ (0x8910821108210112 : BitVec 64))
  | 2 => ((0x810a048050290102 : BitVec 64) ++ (0x140900a052020428 : BitVec 64))
  | 3 => ((0x2a0030005522005 : BitVec 64) ++ (0x4006000aa4400a80 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 15 P N 0
def w1 := inputObserved 15 P N 1
def w2 := inputObserved 15 P N 2
def w3 := inputObserved 15 P N 3
theorem s0 : Slice true R T 0xff00ff00ff00ff 4 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
theorem s1 : Slice true R T 0x3333333333333333 4 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p1 : Pool R T := prefixPool s1 [] (by decide +kernel)
def w4 := combineObserved 1 w2 w1
def w5 := combineObserved 1 w3 w1
def w6 := combineObserved 1 w3 w2
def v0 : Closed T 3 := closeState (raw := R) properPN 3 [w0, w4, w5, w6]
  (fun _ => ([(usePool p0), (usePool p1)], [])) (by decide +kernel)
theorem s2 : Slice true R T 0x5555555555555555 4 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B7.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
def w7 := combineObserved 1 w3 w0
def a0 : List Move := [swapRows 32]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 3 := rotateClosed v0 a0 a0ok
def v1 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w7, w5]
  (fun h => chooseRoute #[(usePool p2), (usePool p1)] #[r0] ((((0x408 : Nat) >>> ((h % 6) * 2)) &&& 3))) (by decide +kernel)
theorem s3 : Slice true R T 0xf0f0f0f0f0f0f0f 4 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B4.low
def p3 : Pool R T := prefixPool s3 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xfefefefefefefefe, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s4 : Slice true R T 0xf0f0f0f0f0f0f0f0 2 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B18.low
def p4 : Pool R T := prefixPool s4 [] (by decide +kernel)
def w8 := combineObserved 1 w0 w1
def w9 := combineObserved 1 w8 w2
def v2 : Closed T 4 := closeState (raw := R) properPN 4 [w0, w1, w2, w9, w3]
  (fun _ => ([(usePool p0), (joinPools p3 p4)], [])) (by decide +kernel)
def w10 := combineObserved 2 w8 w3
def v3 : Closed T 4 := closeState (raw := R) properPN 4 [w10, w0, w1, w2, w3]
  (fun _ => ([], [])) (by decide +kernel)
def p5 : Pool R T := prefixPool s3 [] (by decide +kernel)
def a1 : List Move := [swapRows 50]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def r1 : Closed T 4 := rotateClosed v3 a1 a1ok
def r2 : Closed T 4 := rotateClosed v2 a1 a1ok
def a2 : List Move := [swapRows 48]
theorem a2ok : autoOK T a2 = true := by decide +kernel
def r3 : Closed T 4 := rotateClosed v1 a2 a2ok
def a3 : List Move := [swapRows 49]
theorem a3ok : autoOK T a3 = true := by decide +kernel
def r4 : Closed T 4 := rotateClosed v1 a3 a3ok
def a4 : List Move := [swapRows 50, swapRows 32]
theorem a4ok : autoOK T a4 = true := by decide +kernel
def r5 : Closed T 4 := rotateClosed v1 a4 a4ok
def a5 : List Move := [swapRows 50, swapRows 33]
theorem a5ok : autoOK T a5 = true := by decide +kernel
def r6 : Closed T 4 := rotateClosed v1 a5 a5ok
def v4 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w8, w2, w3]
  (fun h => chooseRoute #[(usePool p2), (usePool p1), (usePool p5), (usePool p0)] #[v3, r1, v2, r2, r3, r4, r5, r6] ((((((0x3010054b961 : Nat) <<< 64) ||| 0xa20003000071280) >>> (((h / 8 + (((0x9e2031001 : Nat) >>> ((h % 8) * 5)) &&& 31)) % 27) * 4)) &&& 15))) (by decide +kernel)
def r7 : Closed T 5 := rotateClosed v4 a0 a0ok
def a6 : List Move := [swapRows 33]
theorem a6ok : autoOK T a6 = true := by decide +kernel
def r8 : Closed T 5 := rotateClosed v4 a6 a6ok
def a7 : List Move := [swapRows 33, swapRows 48]
theorem a7ok : autoOK T a7 = true := by decide +kernel
def r9 : Closed T 5 := rotateClosed v4 a7 a7ok
def r10 : Closed T 5 := rotateClosed v4 a2 a2ok
def r11 : Closed T 5 := rotateClosed v4 a3 a3ok
def v5 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w2, w3]
  (fun h => chooseRoute #[(usePool p2), (usePool p1), (usePool p5), (usePool p0)] #[v4, r7, r8, r9, r10, r11] ((((((0x13934200 : Nat) <<< 64) ||| 0x1316710020080035) >>> (((h / 8 + (((0x40b1830 : Nat) >>> ((h % 8) * 4)) &&& 15)) % 25) * 4)) &&& 15))) (by decide +kernel)
theorem low : Lower true R T 7 :=
  fromClosed v5 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 1, 5), (0xff00ff00ff00ff00, 1, 9)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B19

namespace B20
def R : List Sig := vars 23
def T : Sig := 0xfefee8e8fefee8e8
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 67]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B17.low
end B20

namespace B21
def R : List Sig := vars 23
def T : Sig := 0xfefee8e8fefee8e8
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 67]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B19.low
end B21

namespace B22
def R : List Sig := vars 25
def T : Sig := 0xffaaaa00ffaaaa00
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50, swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B22

namespace B23
def R : List Sig := vars 26
def T : Sig := 0xffcccc00ffcccc00
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 50, swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B23

namespace B24
def R : List Sig := vars 27
def T : Sig := 0xffeeee88ffeeee88
theorem low : Lower true R T 6 := by
  exact lower_map (ms := [swapRows 66]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B17.low
end B24

namespace B25
def R : List Sig := vars 27
def T : Sig := 0xffeeee88ffeeee88
theorem low : Lower true R T 7 := by
  exact lower_map (ms := [swapRows 66]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B19.low
end B25

namespace B26
def R : List Sig := vars 28
def T : Sig := 0xfff0f000fff0f000
theorem low : Lower true R T 4 := by
  exact lower_map (ms := [swapRows 49, swapRows 64]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B0.low
end B26

namespace B27
def R : List Sig := vars 15
def T : Sig := 0xfeeafeeafeeafeea
theorem low : Lower true R T 5 := by
  have h := lift_ok (u := true) (ms := fixRows 1 0) (raw := R)
    (T := T) (xs := [(0xaaaaaaaaaaaaaaaa, 0, 1)]) (by decide +kernel) (proper_of _ (by decide))
    (proper_of _ (by decide)) B7.low
  have he : (([(0xaaaaaaaaaaaaaaaa, 0, 1)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide
  rw [he] at h
  exact h
end B27

namespace B28
def R : List Sig := vars 29
def T : Sig := 0xfffafaaafffafaaa
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 65]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B27.low
end B28

namespace B29
def R : List Sig := vars 30
def T : Sig := 0xfffcfcccfffcfccc
theorem low : Lower true R T 5 := by
  exact lower_map (ms := [swapRows 65, swapRows 16]) (by decide +kernel) (proper_of _ (by decide))
    (by decide) (by decide) (proper_of _ (by decide)) B27.low
end B29

namespace B30
def R : List Sig := vars 31
def T : Sig := 0xfee8e888fee8e888
def P : Nat → Bits
  | 0 => ((0x3e0f83e07e3e3f : BitVec 64) ++ (0xc7ff1fffffe071c7 : BitVec 64))
  | 1 => ((0x7c1f07c1f803fc7 : BitVec 64) ++ (0xf8ffe3ffffe38e38 : BitVec 64))
  | 2 => ((0xf801ffffffffc007 : BitVec 64) ++ (0xff1ffc70019c0fff : BitVec 64))
  | 3 => ((0xfffe007ffffffff8 : BitVec 64) ++ (0x1fff80061ff03f : BitVec 64))
  | 4 => ((0xffffff801fffffff : BitVec 64) ++ (0xffe00000181fffc0 : BitVec 64))
  | _ => 0
def N : Nat → Bits
  | 0 => ((0xaa82910c80160a09 : BitVec 64) ++ (0x41250492aaa030c3 : BitVec 64))
  | 1 => ((0x5054249065801442 : BitVec 64) ++ (0x884a212555418618 : BitVec 64))
  | 2 => ((0x1d6a52a52aaa4004 : BitVec 64) ++ (0xd2134840618c0b6d : BitVec 64))
  | 3 => ((0x618d6b4a534ca690 : BitVec 64) ++ (0x1c92018616d036 : BitVec 64))
  | 4 => ((0x86318c739c713927 : BitVec 64) ++ (0x24800006181b6d80 : BitVec 64))
  | _ => 0
theorem properPN : properPairs T (asRow P) (asRow N) := by unfold properPairs; decide +kernel
def w0 := inputObserved 31 P N 0
def w1 := inputObserved 31 P N 1
def w2 := inputObserved 31 P N 2
def w3 := inputObserved 31 P N 3
def w4 := inputObserved 31 P N 4
def w5 := combineObserved 1 w0 w1
def w6 := combineObserved 0 w3 w4
def w7 := combineObserved 2 w5 w6
def w8 := combineObserved 0 w2 w3
def w9 := combineObserved 0 w2 w4
def v0 : Closed T 4 := closeState (raw := R) properPN 4 [w7, w0, w1, w8, w9]
  (fun _ => ([], [])) (by decide +kernel)
theorem s0 : Slice true R T 0x5050505050505050 4 :=
  slice_correct (ms := fixRows 1 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B23.low
def p0 : Pool R T := prefixPool s0 [] (by decide +kernel)
def v1 : Closed T 5 := closeState (raw := R) properPN 5 [w7, w0, w1, w8, w2, w4]
  (fun _ => ([(usePool p0)], [v0])) (by decide +kernel)
theorem s1 : Slice true R T 0x5555555555555555 7 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B15.low
def p1 : Pool R T := prefixPool s1 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000), (0, 0xff00ff00ff00ff00, 0xffff0000ffff0000)] (by decide +kernel)
theorem s2 : Slice true R T 0xff000000ff0000 4 :=
  slice_correct (ms := fixRows 8 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B0.low
def p2 : Pool R T := prefixPool s2 [] (by decide +kernel)
theorem s3 : Slice true R T 0xf000f000f000f00 4 :=
  slice_correct (ms := fixRows 4 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B5.low
def p3 : Pool R T := prefixPool s3 [] (by decide +kernel)
theorem s4 : Slice true R T 0x5500550055005500 4 :=
  slice_correct (ms := fixRows 1 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B16.low
def p4 : Pool R T := prefixPool s4 [] (by decide +kernel)
def a0 : List Move := [swapRows 50]
theorem a0ok : autoOK T a0 = true := by decide +kernel
def r0 : Closed T 4 := rotateClosed v0 a0 a0ok
def a1 : List Move := [swapRows 66]
theorem a1ok : autoOK T a1 = true := by decide +kernel
def r1 : Closed T 4 := rotateClosed v0 a1 a1ok
def v2 : Closed T 5 := closeState (raw := R) properPN 5 [w0, w1, w5, w8, w9, w6]
  (fun h => chooseRoute #[(usePool p1), (usePool p2), (usePool p3), (usePool p4), (usePool p0)] #[v0, r0, r1] ((((0xa200001882e0e10 : Nat) >>> ((h % 20) * 3)) &&& 7))) (by decide +kernel)
def p5 : Pool R T := prefixPool s1 [(0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (0, 0xe0e0e0e0e0e0e0e0, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s5 : Slice true R T 0x3030303030303030 4 :=
  slice_correct (ms := fixRows 2 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B22.low
def p6 : Pool R T := prefixPool s5 [] (by decide +kernel)
theorem s6 : Slice true R T 0x4444444444444444 4 :=
  slice_correct (ms := fixRows 1 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B26.low
def p7 : Pool R T := prefixPool s6 [] (by decide +kernel)
theorem s7 : Slice true R T 0xff00ff00ff00ff 5 :=
  slice_correct (ms := fixRows 8 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B2.low
def p8 : Pool R T := prefixPool s7 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)] (by decide +kernel)
theorem s8 : Slice true R T 0xff00ff00ff00ff00 7 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B21.low
def p9 : Pool R T := prefixPool s8 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (3, 0xe000e000e000e000, 0xeeeeeeeeeeeeeeee)] (by decide +kernel)
theorem s9 : Slice true R T 0x5555000055550000 4 :=
  slice_correct (ms := fixRows 1 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B7.low
def p10 : Pool R T := prefixPool s9 [] (by decide +kernel)
def p11 : Pool R T := prefixPool s8 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (3, 0xe000e000e000e000, 0xffff0000ffff0000)] (by decide +kernel)
def w10 := combineObserved 0 w5 w2
def w11 := combineObserved 0 w10 w3
def v3 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w11, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p5), (usePool p6), (usePool p7), (joinPools p8 p9), (usePool p10), (joinPools p8 p11)] #[] ((((0xcd294 : Nat) >>> ((h % 10) * 3)) &&& 7))) (by decide +kernel)
def p12 : Pool R T := prefixPool s1 [(0, 0xeeeeeeeeeeeeeeee, 0xffff0000ffff0000), (3, 0xeeee0000eeee0000, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
theorem s10 : Slice true R T 0xf0f0f0f0f0f0f0f0 7 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B25.low
def p13 : Pool R T := prefixPool s10 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xeeeeeeeeeeeeeeee, 0xffff0000ffff0000)] (by decide +kernel)
def w12 := combineObserved 0 w5 w4
def w13 := combineObserved 3 w12 w2
def v4 : Closed T 6 := closeState (raw := R) properPN 6 [w13, w0, w1, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p7), (usePool p10), (usePool p12), (usePool p3), (usePool p13)] #[] ((((0x1108a03010000 : Nat) >>> ((h % 19) * 3)) &&& 7))) (by decide +kernel)
def p14 : Pool R T := prefixPool s1 [(0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s11 : Slice true R T 0xaaaaaaaaaaaaaaaa 5 :=
  slice_correct (ms := fixRows 0 1) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B29.low
def p15 : Pool R T := prefixPool s11 [] (by decide +kernel)
theorem s12 : Slice true R T 0x3333333333333333 7 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B12.low
def p16 : Pool R T := prefixPool s12 [(0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s13 : Slice true R T 0xcccccccccccccccc 5 :=
  slice_correct (ms := fixRows 0 2) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B28.low
def p17 : Pool R T := prefixPool s13 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
def v5 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w10, w5, w8, w3, w4]
  (fun h => chooseRoute #[(usePool p14), (usePool p15), (usePool p7), (usePool p0), (usePool p4), (joinPools p16 p17), (usePool p3)] #[] ((((0x845480018192 : Nat) >>> ((h % 23) * 3)) &&& 7))) (by decide +kernel)
def p18 : Pool R T := prefixPool s7 [(1, 0xcccccccccccccccc, 0xaaaaaaaaaaaaaaaa)] (by decide +kernel)
def p19 : Pool R T := prefixPool s8 [(1, 0xcccccccccccccccc, 0xaaaaaaaaaaaaaaaa), (1, 0xcccccccccccccccc, 0xf000f000f000f000), (1, 0xaaaaaaaaaaaaaaaa, 0xf000f000f000f000)] (by decide +kernel)
def p20 : Pool R T := prefixPool s10 [(1, 0xcccccccccccccccc, 0xaaaaaaaaaaaaaaaa), (1, 0xcccccccccccccccc, 0xf000f000f000f000)] (by decide +kernel)
def w14 := combineObserved 1 w1 w8
def v6 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w5, w8, w2, w14, w3, w4]
  (fun h => chooseRoute #[(joinPools p18 p19), (usePool p7), (usePool p0), (usePool p2), (usePool p3), (usePool p6), (usePool p20)] #[] ((((((0x300 : Nat) <<< 64) ||| 0x8600010620628c00) >>> ((h % 25) * 3)) &&& 7))) (by decide +kernel)
def p21 : Pool R T := prefixPool s10 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (1, 0xeeeeeeeeeeeeeeee, 0xf000f000f000f000)] (by decide +kernel)
def p22 : Pool R T := prefixPool s12 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (1, 0xeeeeeeeeeeeeeeee, 0xf000f000f000f000), (0, 0xfeeefeeefeeefeee, 0xffff0000ffff0000)] (by decide +kernel)
def w15 := combineObserved 1 w5 w8
def v7 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w8, w2, w15, w3, w4]
  (fun h => chooseRoute #[(joinPools p8 p9), (usePool p4), (usePool p0), (usePool p21), (usePool p2), (joinPools p22 p17)] #[] ((((0x26511a : Nat) >>> (((h / 3 + (((0x1d0 : Nat) >>> ((h % 3) * 3)) &&& 7)) % 9) * 3)) &&& 7))) (by decide +kernel)
def p23 : Pool R T := prefixPool s8 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xeeeeeeeeeeeeeeee, 0xff000000ff000000)] (by decide +kernel)
theorem s14 : Slice true R T 0xffff0000ffff0000 7 :=
  slice_correct (ms := fixRows 0 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B19.low
def p24 : Pool R T := prefixPool s14 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (2, 0xeeeeeeeeeeeeeeee, 0xff000000ff000000)] (by decide +kernel)
def a2 : List Move := [swapRows 67]
theorem a2ok : autoOK T a2 = true := by decide +kernel
def r2 : Closed T 5 := rotateClosed v1 a2 a2ok
def v8 : Closed T 6 := closeState (raw := R) properPN 6 [w7, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p6), (usePool p7), (usePool p3), (usePool p0), (usePool p4), (usePool p23), (usePool p24)] #[v1, r2] ((((((0x5002005413 : Nat) <<< 64) ||| 0x246891200702000) >>> (((h / 8 + (((0xc2a3012 : Nat) >>> ((h % 8) * 4)) &&& 15)) % 26) * 4)) &&& 15))) (by decide +kernel)
def p25 : Pool R T := prefixPool s1 [(0, 0xffff0000ffff0000, 0xff00ff00ff00ff00), (2, 0xeeeeeeeeeeeeeeee, 0xff000000ff000000)] (by decide +kernel)
def v9 : Closed T 6 := closeState (raw := R) properPN 6 [w7, w0, w1, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p6), (usePool p2), (usePool p25)] #[] ((((0x8c101 : Nat) >>> ((h % 11) * 2)) &&& 3))) (by decide +kernel)
def v10 : Closed T 6 := closeState (raw := R) properPN 6 [w7, w0, w1, w2, w6, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p2), (usePool p4), (usePool p24)] #[] ((((0x3086100 : Nat) >>> ((h % 13) * 2)) &&& 3))) (by decide +kernel)
def v11 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w10, w2, w6, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p3), (usePool p4), (usePool p0)] #[] ((((0x144000463 : Nat) >>> ((h % 19) * 2)) &&& 3))) (by decide +kernel)
def w16 := combineObserved 3 w5 w2
def v12 : Closed T 6 := closeState (raw := R) properPN 6 [w16, w0, w1, w2, w6, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p3), (usePool p7), (usePool p4), (usePool p0)] #[] ((((0x1400058220 : Nat) >>> (((h / 4 + (((0xc0 : Nat) >>> ((h % 4) * 2)) &&& 3)) % 17) * 3)) &&& 7))) (by decide +kernel)
def p26 : Pool R T := prefixPool s1 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xf000f000f000f000, 0xffff0000ffff0000)] (by decide +kernel)
def p27 : Pool R T := prefixPool s8 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xf000f000f000f000, 0xffff0000ffff0000), (2, 0xeeeeeeeeeeeeeeee, 0xf0000000f0000000)] (by decide +kernel)
theorem s15 : Slice true R T 0xf0f0f0f0f0f0f0f0 6 :=
  slice_correct (ms := fixRows 0 4) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B24.low
def p28 : Pool R T := prefixPool s15 [(0, 0xf000f000f000f000, 0xffff0000ffff0000)] (by decide +kernel)
theorem s16 : Slice true R T 0xffff0000ffff 5 :=
  slice_correct (ms := fixRows 16 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B1.low
def p29 : Pool R T := prefixPool s16 [] (by decide +kernel)
def w17 := combineObserved 0 w8 w4
def v13 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w5, w17, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p26), (usePool p15), (usePool p7), (usePool p6), (usePool p2), (joinPools p8 p27), (usePool p3), (usePool p28), (usePool p29)] #[] ((((((0x6 : Nat) <<< 64) ||| 0x6235817402040424) >>> (((h / 5 + (((0x1b73 : Nat) >>> ((h % 5) * 4)) &&& 15)) % 17) * 4)) &&& 15))) (by decide +kernel)
theorem s17 : Slice true R T 0xf0f0f0f0f0f0f0f 5 :=
  slice_correct (ms := fixRows 4 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B3.low
def p30 : Pool R T := prefixPool s17 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)] (by decide +kernel)
def p31 : Pool R T := prefixPool s10 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc), (0, 0xffff0000ffff0000, 0xff00ff00ff00ff00), (3, 0xf0f0f000f0f0f0, 0xeeeeeeeeeeeeeeee)] (by decide +kernel)
def p32 : Pool R T := prefixPool s1 [(0, 0xffff0000ffff0000, 0xff00ff00ff00ff00), (3, 0xff000000ff000000, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
def p33 : Pool R T := prefixPool s15 [(0, 0xffff0000ffff0000, 0xff00ff00ff00ff00)] (by decide +kernel)
def w18 := combineObserved 3 w6 w2
def v14 : Closed T 6 := closeState (raw := R) properPN 6 [w18, w0, w1, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p3), (usePool p7), (joinPools p30 p31), (usePool p32), (usePool p33), (usePool p2), (usePool p29)] #[] ((((0x80101741400c1 : Nat) >>> ((h % 21) * 3)) &&& 7))) (by decide +kernel)
def p34 : Pool R T := prefixPool s1 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000)] (by decide +kernel)
def p35 : Pool R T := prefixPool s16 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
def r3 : Closed T 5 := rotateClosed v1 a0 a0ok
def a3 : List Move := [swapRows 67, swapRows 66]
theorem a3ok : autoOK T a3 = true := by decide +kernel
def r4 : Closed T 5 := rotateClosed v1 a3 a3ok
def v15 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w5, w8, w9, w3, w4]
  (fun h => chooseRoute #[(usePool p34), (usePool p2), (usePool p3), (usePool p35), (usePool p4), (usePool p10)] #[r3, r4, v2] ((((0x48613572240110 : Nat) >>> (((h / 5 + (((0x5 : Nat) >>> ((h % 5) * 1)) &&& 1)) % 15) * 4)) &&& 15))) (by decide +kernel)
def w19 := combineObserved 3 w1 w2
def w20 := combineObserved 1 w19 w0
def v16 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w20, w1, w2, w6, w3, w4]
  (fun h => chooseRoute #[(usePool p15), (usePool p7), (usePool p2), (usePool p6), (usePool p0), (usePool p3)] #[] ((((((0x8 : Nat) <<< 64) ||| 0x4c000100d144) >>> ((h % 23) * 3)) &&& 7))) (by decide +kernel)
def w21 := combineObserved 3 w0 w4
def w22 := combineObserved 3 w21 w3
def v17 : Closed T 6 := closeState (raw := R) properPN 6 [w19, w22, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p6), (usePool p7)] #[] ((((0x81 : Nat) >>> ((h % 4) * 2)) &&& 3))) (by decide +kernel)
def w23 := combineObserved 0 w19 w3
def v18 : Closed T 6 := closeState (raw := R) properPN 6 [w23, w21, w0, w1, w2, w3, w4]
  (fun _ => ([(usePool p2)], [])) (by decide +kernel)
def w24 := combineObserved 3 w1 w4
def w25 := combineObserved 1 w24 w8
def v19 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w8, w2, w25, w3, w4]
  (fun _ => ([(usePool p2)], [])) (by decide +kernel)
def p36 : Pool R T := prefixPool s11 [(3, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
def w26 := combineObserved 1 w0 w6
def v20 : Closed T 6 := closeState (raw := R) properPN 6 [w19, w0, w1, w2, w3, w26, w4]
  (fun h => chooseRoute #[(usePool p15), (usePool p4), (usePool p7), (usePool p6), (usePool p36), (usePool p0), (usePool p3)] #[] ((((((0x8 : Nat) <<< 64) ||| 0x20460007630020c0) >>> ((h % 25) * 3)) &&& 7))) (by decide +kernel)
def p37 : Pool R T := prefixPool s12 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (1, 0xaaaaaaaaaaaaaaaa, 0xf000f000f000f000)] (by decide +kernel)
def p38 : Pool R T := prefixPool s10 [(1, 0xaaaaaaaaaaaaaaaa, 0xf000f000f000f000), (3, 0xcccccccccccccccc, 0xfaaafaaafaaafaaa)] (by decide +kernel)
def w27 := combineObserved 1 w0 w8
def w28 := combineObserved 3 w1 w27
def v21 : Closed T 6 := closeState (raw := R) properPN 6 [w28, w0, w1, w8, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p0), (usePool p7), (usePool p37), (usePool p38)] #[] ((((0x8810000c0010 : Nat) >>> ((h % 18) * 3)) &&& 7))) (by decide +kernel)
def p39 : Pool R T := prefixPool s12 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000), (0, 0xff00ff00ff00ff00, 0xffff0000ffff0000)] (by decide +kernel)
theorem s18 : Slice true R T 0xffff0000ffff0000 6 :=
  slice_correct (ms := fixRows 0 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B17.low
def p40 : Pool R T := prefixPool s18 [] (by decide +kernel)
def p41 : Pool R T := prefixPool s15 [] (by decide +kernel)
def v22 : Closed T 6 := closeState (raw := R) properPN 6 [w0, w1, w8, w9, w6]
  (fun h => chooseRoute #[(usePool p1), (usePool p39), (usePool p2), (usePool p3), (usePool p40), (usePool p41)] #[v2] ((((((((0x7124 : Nat) <<< 64) ||| 0x926984904b040305) <<< 64) ||| 0x250009d61b4c0082) >>> (((h / 16 + (((0xbe200c3019 : Nat) >>> ((h % 16) * 3)) &&& 7)) % 49) * 3)) &&& 7))) (by decide +kernel)
theorem s19 : Slice true R T 0xf0f00000f0f0000 4 :=
  slice_correct (ms := fixRows 4 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B4.low
def p42 : Pool R T := prefixPool s19 [] (by decide +kernel)
def v23 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w10, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p15), (usePool p3), (usePool p6), (usePool p0), (usePool p42), (usePool p2), (usePool p4)] #[] ((((((((((0x100135030e0 : Nat) <<< 64) ||| 0x40408401c0f01230) <<< 64) ||| 0x83180a13141c1749) <<< 64) ||| 0xa320a8400408080) >>> (((h / 27 + (((((0x19041031b8 : Nat) <<< 64) ||| 0x2300a1b223213000) >>> ((h % 27) * 4)) &&& 15)) % 80) * 3)) &&& 7))) (by decide +kernel)
def p43 : Pool R T := prefixPool s1 [(0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
def p44 : Pool R T := prefixPool s12 [(0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (0, 0xeeeeeeeeeeeeeeee, 0xff00ff00ff00ff00)] (by decide +kernel)
def p45 : Pool R T := prefixPool s13 [] (by decide +kernel)
def p46 : Pool R T := prefixPool s12 [(0, 0xeeeeeeeeeeeeeeee, 0xf0f0f0f0f0f0f0f0), (0, 0xeeeeeeeeeeeeeeee, 0xffff0000ffff0000)] (by decide +kernel)
def p47 : Pool R T := prefixPool s10 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)] (by decide +kernel)
def r5 : Closed T 6 := rotateClosed v4 a1 a1ok
def a4 : List Move := [swapRows 67, swapRows 50]
theorem a4ok : autoOK T a4 = true := by decide +kernel
def r6 : Closed T 6 := rotateClosed v4 a4 a4ok
def r7 : Closed T 6 := rotateClosed v3 a2 a2ok
def r8 : Closed T 6 := rotateClosed v5 a2 a2ok
def v24 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w10, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p43), (usePool p7), (usePool p0), (usePool p4), (usePool p10), (joinPools p44 p45), (usePool p3), (joinPools p46 p45), (usePool p42), (usePool p47)] #[r5, r6, v3, r7, v5, r8] ((((((((((0x111 : Nat) <<< 64) ||| 0x14011600103e5201) <<< 64) ||| 0x400110f1c1110b81) <<< 64) ||| 0x190190121d11a37) >>> (((h / 17 + (((0x401021100030c01 : Nat) >>> ((h % 17) * 4)) &&& 15)) % 51) * 4)) &&& 15))) (by decide +kernel)
def v25 : Closed T 7 := closeState (raw := R) properPN 7 [w16, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p3), (usePool p2), (usePool p4), (usePool p42), (usePool p0)] #[] ((((((((0x6022000200100 : Nat) <<< 64) ||| 0x24000000008114) <<< 64) ||| 0x20804506a200000) >>> (((h / 22 + (((((0x12008 : Nat) <<< 64) ||| 0x30000021010) >>> ((h % 22) * 4)) &&& 15)) % 65) * 3)) &&& 7))) (by decide +kernel)
def p48 : Pool R T := prefixPool s1 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
theorem s20 : Slice true R T 0x3333333333333333 6 :=
  slice_correct (ms := fixRows 2 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B9.low
def p49 : Pool R T := prefixPool s20 [] (by decide +kernel)
def p50 : Pool R T := prefixPool s12 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00)] (by decide +kernel)
def p51 : Pool R T := prefixPool s8 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)] (by decide +kernel)
def r9 : Closed T 6 := rotateClosed v9 a1 a1ok
def r10 : Closed T 6 := rotateClosed v10 a1 a1ok
def r11 : Closed T 6 := rotateClosed v8 a1 a1ok
def r12 : Closed T 6 := rotateClosed v14 a1 a1ok
def r13 : Closed T 6 := rotateClosed v12 a1 a1ok
def r14 : Closed T 6 := rotateClosed v5 a0 a0ok
def r15 : Closed T 6 := rotateClosed v11 a1 a1ok
def r16 : Closed T 6 := rotateClosed v15 a0 a0ok
def a5 : List Move := [swapRows 16]
theorem a5ok : autoOK T a5 = true := by decide +kernel
def r17 : Closed T 6 := rotateClosed v6 a5 a5ok
def v26 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w5, w8, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p48), (usePool p0), (usePool p6), (usePool p7), (usePool p15), (usePool p49), (usePool p50), (usePool p2), (usePool p3), (usePool p41), (usePool p47), (usePool p4), (usePool p51), (usePool p10)] #[r9, r10, r11, r12, r13, v3, v5, r14, r15, v13, v15, r16, v7, v6, r17] ((((((((((((((0x2084802d2300584 : Nat) <<< 64) ||| 0x200fb059410ae220) <<< 64) ||| 0x34675e2f2a884898) <<< 64) ||| 0x5d41b7203054038c) <<< 64) ||| 0xaa381eb01c603f06) <<< 64) ||| 0x8386080800766863) >>> (((h / 24 + (((((((0x30 : Nat) <<< 64) ||| 0xec600231814014) <<< 64) ||| 0x1401c2b0f144083) >>> ((h % 24) * 6)) &&& 63)) % 76) * 5)) &&& 31))) (by decide +kernel)
def v27 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w20, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p6), (usePool p0), (usePool p2), (usePool p4), (usePool p3), (usePool p42)] #[v16] ((((((((((0x130420c7 : Nat) <<< 64) ||| 0x80000400290) <<< 64) ||| 0x1a20000100100000) <<< 64) ||| 0x400018000a20c80) >>> (((h / 25 + (((((0x202500000 : Nat) <<< 64) ||| 0x291a021103001120) >>> ((h % 25) * 4)) &&& 15)) % 77) * 3)) &&& 7))) (by decide +kernel)
theorem s21 : Slice true R T 0x3300330033003300 4 :=
  slice_correct (ms := fixRows 2 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B13.low
def p52 : Pool R T := prefixPool s21 [] (by decide +kernel)
def v28 : Closed T 7 := closeState (raw := R) properPN 7 [w23, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p7), (usePool p52)] #[] ((((((0x10000010040440 : Nat) <<< 64) ||| 0x4051002044410) >>> (((h / 22 + (((0x48210404404 : Nat) >>> ((h % 22) * 2)) &&& 3)) % 65) * 2)) &&& 3))) (by decide +kernel)
def w29 := combineObserved 3 w21 w2
def v29 : Closed T 7 := closeState (raw := R) properPN 7 [w29, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p0), (usePool p10), (usePool p2), (usePool p6), (usePool p3), (usePool p4)] #[] ((((((((((0x6492b41245 : Nat) <<< 64) ||| 0x4544822da4080184) <<< 64) ||| 0x8002941108a61554) <<< 64) ||| 0x20480480304cd490) >>> (((h / 25 + (((((0x1000c000c410880 : Nat) <<< 64) ||| 0x319880c140001c00) >>> ((h % 25) * 5)) &&& 31)) % 77) * 3)) &&& 7))) (by decide +kernel)
theorem s22 : Slice true R T 0x5555555555555555 6 :=
  slice_correct (ms := fixRows 1 0) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B14.low
def p53 : Pool R T := prefixPool s22 [] (by decide +kernel)
def w30 := combineObserved 3 w0 w2
def v30 : Closed T 7 := closeState (raw := R) properPN 7 [w19, w30, w0, w1, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p53), (usePool p0), (usePool p6), (usePool p3)] #[] ((((((((((0x4 : Nat) <<< 64) ||| 0x28040000880) <<< 64) ||| 0x20c000200000000) <<< 64) ||| 0x14004000004) >>> (((h / 22 + (((0x3110000415e : Nat) >>> ((h % 22) * 2)) &&& 3)) % 69) * 3)) &&& 7))) (by decide +kernel)
theorem s23 : Slice true R T 0x3333000033330000 4 :=
  slice_correct (ms := fixRows 2 16) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B6.low
def p54 : Pool R T := prefixPool s23 [] (by decide +kernel)
def w31 := combineObserved 3 w0 w3
def a6 : List Move := [swapRows 66, swapRows 16]
theorem a6ok : autoOK T a6 = true := by decide +kernel
def r18 : Closed T 6 := rotateClosed v18 a6 a6ok
def r19 : Closed T 6 := rotateClosed v17 a2 a2ok
def a7 : List Move := [swapRows 67, swapRows 50, swapRows 16]
theorem a7ok : autoOK T a7 = true := by decide +kernel
def r20 : Closed T 6 := rotateClosed v17 a7 a7ok
def v31 : Closed T 7 := closeState (raw := R) properPN 7 [w19, w31, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p2), (usePool p7), (usePool p4), (usePool p52), (usePool p3), (usePool p0), (usePool p54)] #[r18, r19, r20] ((((((((((0x11164010100 : Nat) <<< 64) ||| 0x1010515140100101) <<< 64) ||| 0x9010027010381) <<< 64) ||| 0x1100060130100251) >>> (((h / 18 + (((0x500904020 : Nat) >>> ((h % 18) * 2)) &&& 3)) % 61) * 4)) &&& 15))) (by decide +kernel)
def p55 : Pool R T := prefixPool s15 [(0, 0xff00ff00ff00ff00, 0xffff0000ffff0000)] (by decide +kernel)
def p56 : Pool R T := prefixPool s10 [(0, 0xff00ff00ff00ff00, 0xffff0000ffff0000)] (by decide +kernel)
def r21 : Closed T 6 := rotateClosed v19 a1 a1ok
def v32 : Closed T 7 := closeState (raw := R) properPN 7 [w19, w0, w1, w2, w6, w3, w4]
  (fun h => chooseRoute #[(usePool p4), (usePool p3), (usePool p55), (usePool p52), (usePool p2), (usePool p7), (usePool p6), (usePool p42), (usePool p56), (usePool p0), (usePool p54)] #[v12, r18, v20, v16, r21] ((((((((((0x415611f0a016 : Nat) <<< 64) ||| 0x1850046e65895603) <<< 64) ||| 0x109c543002111135) <<< 64) ||| 0x1bd44031340700a4) >>> (((h / 20 + (((((0x1dc0088a : Nat) <<< 64) ||| 0x40008201023f1803) >>> ((h % 20) * 5)) &&& 31)) % 60) * 4)) &&& 15))) (by decide +kernel)
def r22 : Closed T 6 := rotateClosed v20 a1 a1ok
def v33 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w2, w27, w3, w4]
  (fun h => chooseRoute #[(usePool p0), (usePool p15), (usePool p48), (usePool p3), (usePool p2), (usePool p4), (usePool p6), (usePool p7), (usePool p37), (usePool p29)] #[r22] ((((((((((((0x5140061780141070 : Nat) <<< 64) ||| 0x9030510004644301) <<< 64) ||| 0x4004134010340000) <<< 64) ||| 0x71543244404a04) <<< 64) ||| 0x50500044440371) >>> (((h / 27 + (((((((0xd : Nat) <<< 64) ||| 0xfb61802304206134) <<< 64) ||| 0x504050042400824) >>> ((h % 27) * 5)) &&& 31)) % 80) * 4)) &&& 15))) (by decide +kernel)
def p57 : Pool R T := prefixPool s7 [] (by decide +kernel)
def p58 : Pool R T := prefixPool s8 [(1, 0xaaaaaaaaaaaaaaaa, 0xf000f000f000f000), (1, 0xcccccccccccccccc, 0xf000f000f000f000)] (by decide +kernel)
def p59 : Pool R T := prefixPool s10 [(1, 0xaaaaaaaaaaaaaaaa, 0xf000f000f000f000)] (by decide +kernel)
def v34 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w8, w2, w27, w3, w4]
  (fun h => chooseRoute #[(usePool p48), (usePool p2), (usePool p0), (usePool p3), (joinPools p57 p58), (usePool p37), (usePool p6), (usePool p4), (usePool p7), (usePool p59)] #[v21, v7, r17] ((((((((((0x123011 : Nat) <<< 64) ||| 0x210116711b010c12) <<< 64) ||| 0x1a13171100114621) <<< 64) ||| 0x1191011030800005) >>> (((h / 18 + (((((0x18000204000 : Nat) <<< 64) ||| 0x1000001121140003) >>> ((h % 18) * 6)) &&& 63)) % 54) * 4)) &&& 15))) (by decide +kernel)
def p60 : Pool R T := prefixPool s12 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xf000f000f000f000, 0xffff0000ffff0000)] (by decide +kernel)
def p61 : Pool R T := prefixPool s8 [(0, 0xf000f000f000f000, 0xffff0000ffff0000), (1, 0xaaaaaaaaaaaaaaaa, 0xf0000000f0000000)] (by decide +kernel)
def p62 : Pool R T := prefixPool s8 [(0, 0xf000f000f000f000, 0xffff0000ffff0000), (1, 0xcccccccccccccccc, 0xf0000000f0000000)] (by decide +kernel)
def v35 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w17, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p26), (usePool p60), (usePool p2), (joinPools p57 p61), (usePool p15), (usePool p53), (usePool p7), (usePool p3), (joinPools p57 p62), (usePool p49), (usePool p6)] #[v13] ((((((((((((0x22277202 : Nat) <<< 64) ||| 0x2082272222270222) <<< 64) ||| 0x9322022222022227) <<< 64) ||| 0x5000220200462722) <<< 64) ||| 0x2a0262272212272b) >>> (((h / 25 + (((((0x20346032a : Nat) <<< 64) ||| 0x1c01121003101201) >>> ((h % 25) * 4)) &&& 15)) % 73) * 4)) &&& 15))) (by decide +kernel)
def p63 : Pool R T := prefixPool s12 [(0, 0xffff0000ffff0000, 0xff00ff00ff00ff00), (3, 0xff000000ff000000, 0xf0f0f0f0f0f0f0f0)] (by decide +kernel)
def p64 : Pool R T := prefixPool s10 [(0, 0xffff0000ffff0000, 0xff00ff00ff00ff00)] (by decide +kernel)
def v36 : Closed T 7 := closeState (raw := R) properPN 7 [w18, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p7), (usePool p3), (usePool p15), (usePool p6), (usePool p2), (usePool p0), (usePool p4), (usePool p42), (usePool p32), (usePool p63), (usePool p64)] #[v14] ((((((((((((0x1710850444410141 : Nat) <<< 64) ||| 0x4b8111100111a403) <<< 64) ||| 0x4470a61400144409) <<< 64) ||| 0x1440047317170141) <<< 64) ||| 0x712106010141044) >>> (((h / 27 + (((((((0x22 : Nat) <<< 64) ||| 0xac03c61200200000) <<< 64) ||| 0x9004010300400000) >>> ((h % 27) * 5)) &&& 31)) % 80) * 4)) &&& 15))) (by decide +kernel)
def p65 : Pool R T := prefixPool s12 [(0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00), (0, 0xf0f0f0f0f0f0f0f0, 0xffff0000ffff0000)] (by decide +kernel)
theorem s24 : Slice true R T 0xff00ff00ff00ff00 6 :=
  slice_correct (ms := fixRows 0 8) (by decide +kernel)
    (by decide +kernel) (proper_of _ (by decide)) B20.low
def p66 : Pool R T := prefixPool s24 [] (by decide +kernel)
def v37 : Closed T 7 := closeState (raw := R) properPN 7 [w0, w1, w8, w9, w3, w4]
  (fun h => chooseRoute #[(usePool p34), (usePool p65), (usePool p2), (usePool p3), (usePool p40), (usePool p66)] #[v15, v22] ((((((((((0x70c0480 : Nat) <<< 64) ||| 0x4924d04820904132) <<< 64) ||| 0xe840080249349269) <<< 64) ||| 0x84c2584693083490) >>> (((h / 24 + (((((0x24 : Nat) <<< 64) ||| 0x2101001109440) >>> ((h % 24) * 3)) &&& 7)) % 73) * 3)) &&& 7))) (by decide +kernel)
def p67 : Pool R T := prefixPool s1 [] (by decide +kernel)
def p68 : Pool R T := prefixPool s14 [(1, 0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc)] (by decide +kernel)
def r23 : Closed T 7 := rotateClosed v25 a0 a0ok
def r24 : Closed T 7 := rotateClosed v25 a1 a1ok
def r25 : Closed T 7 := rotateClosed v24 a0 a0ok
def r26 : Closed T 7 := rotateClosed v24 a1 a1ok
def r27 : Closed T 7 := rotateClosed v23 a0 a0ok
def r28 : Closed T 7 := rotateClosed v23 a1 a1ok
def r29 : Closed T 7 := rotateClosed v26 a1 a1ok
def r30 : Closed T 7 := rotateClosed v26 a2 a2ok
def v38 : Closed T 8 := closeState (raw := R) properPN 8 [w0, w1, w5, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p67), (usePool p53), (usePool p49), (usePool p7), (usePool p15), (usePool p41), (usePool p47), (usePool p66), (usePool p51), (usePool p40), (usePool p68)] #[v25, r23, r24, v24, r25, r26, v23, r27, r28, v26, r29, r30] ((((((((((((((0xc20d08208076a815 : Nat) <<< 64) ||| 0x1248300c63298802) <<< 64) ||| 0x184e0286018c8358) <<< 64) ||| 0x92f88cc002a0010c) <<< 64) ||| 0xb250c33182d40004) <<< 64) ||| 0x140c030006000c02) >>> (((h / 24 + (((((0x3300013 : Nat) <<< 64) ||| 0x57110b1004815580) >>> ((h % 24) * 4)) &&& 15)) % 78) * 5)) &&& 31))) (by decide +kernel)
def p69 : Pool R T := prefixPool s10 [] (by decide +kernel)
def r31 : Closed T 7 := rotateClosed v28 a2 a2ok
def r32 : Closed T 7 := rotateClosed v31 a2 a2ok
def r33 : Closed T 7 := rotateClosed v29 a6 a6ok
def r34 : Closed T 7 := rotateClosed v29 a7 a7ok
def v39 : Closed T 8 := closeState (raw := R) properPN 8 [w19, w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p53), (usePool p7), (usePool p41), (usePool p49), (usePool p6), (usePool p66), (usePool p40), (usePool p69), (usePool p3), (usePool p42)] #[v25, v28, r31, v30, v31, r32, v32, r33, r34, v27] ((((((((((((((0x10840109180 : Nat) <<< 64) ||| 0x2040101421698739) <<< 64) ||| 0x8222048e010c80a) <<< 64) ||| 0xd2410c0100488410) <<< 64) ||| 0x450100080682840) <<< 64) ||| 0x386080bc910a029) >>> (((h / 24 + (((((0x610113f4 : Nat) <<< 64) ||| 0x62746000219a0e0) >>> ((h % 24) * 4)) &&& 15)) % 73) * 5)) &&& 31))) (by decide +kernel)
def p70 : Pool R T := prefixPool s8 [] (by decide +kernel)
def r35 : Closed T 7 := rotateClosed v36 a1 a1ok
def r36 : Closed T 7 := rotateClosed v28 a5 a5ok
def r37 : Closed T 7 := rotateClosed v32 a1 a1ok
def r38 : Closed T 7 := rotateClosed v32 a6 a6ok
def r39 : Closed T 7 := rotateClosed v37 a0 a0ok
def r40 : Closed T 7 := rotateClosed v34 a5 a5ok
def r41 : Closed T 7 := rotateClosed v33 a5 a5ok
def v40 : Closed T 8 := closeState (raw := R) properPN 8 [w0, w1, w8, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p48), (usePool p50), (usePool p53), (usePool p2), (usePool p3), (usePool p41), (usePool p49), (usePool p66), (usePool p40), (usePool p69), (usePool p42), (usePool p70)] #[r35, v28, r36, r37, r38, v26, v35, v37, r39, v34, r40, v33, r41] ((((((((((((((((0x2201810 : Nat) <<< 64) ||| 0x318ca0a80000486c) <<< 64) ||| 0x1ac170900508ce72) <<< 64) ||| 0xdc4a186418c0001) <<< 64) ||| 0x5006c3300631b4) <<< 64) ||| 0x841155321f09120a) <<< 64) ||| 0x381469014841806f) >>> (((h / 25 + (((((0xd379b00e1 : Nat) <<< 64) ||| 0x2d8c900020104022) >>> ((h % 25) * 4)) &&& 15)) % 82) * 5)) &&& 31))) (by decide +kernel)
def p71 : Pool R T := prefixPool s12 [] (by decide +kernel)
def p72 : Pool R T := prefixPool s14 [] (by decide +kernel)
def r42 : Closed T 8 := rotateClosed v39 a5 a5ok
def r43 : Closed T 8 := rotateClosed v39 a0 a0ok
def a8 : List Move := [swapRows 50, swapRows 16]
theorem a8ok : autoOK T a8 = true := by decide +kernel
def r44 : Closed T 8 := rotateClosed v39 a8 a8ok
def r45 : Closed T 8 := rotateClosed v39 a1 a1ok
def r46 : Closed T 8 := rotateClosed v39 a6 a6ok
def r47 : Closed T 8 := rotateClosed v40 a1 a1ok
def r48 : Closed T 8 := rotateClosed v40 a2 a2ok
def v41 : Closed T 9 := closeState (raw := R) properPN 9 [w0, w1, w2, w3, w4]
  (fun h => chooseRoute #[(usePool p67), (usePool p71), (usePool p69), (usePool p70), (usePool p72)] #[v39, r42, r43, r44, r45, r46, v38, v40, r47, r48] ((((((((0x4710d23a3 : Nat) <<< 64) ||| 0x4010e01500403000) <<< 64) ||| 0x600401824b92c300) >>> (((h / 14 + (((((0x6 : Nat) <<< 64) ||| 0x180c211ce12cc05) >>> ((h % 14) * 5)) &&& 31)) % 41) * 4)) &&& 15))) (by decide +kernel)
theorem low : Lower true R T 10 :=
  fromClosed v41 (by decide +kernel) [(0xaaaaaaaaaaaaaaaa, 2, 3), (0xcccccccccccccccc, 1, 3), (0xf0f0f0f0f0f0f0f0, 9, 13), (0xff00ff00ff00ff00, 5, 13), (0xffff0000ffff0000, 5, 21)]
    (proper_of _ (by decide)) (by decide +kernel) (by decide)
end B30
end PEqualNP.Outside.L_meta_49097.Atlas


namespace PEqualNP.Outside.L_meta_49097

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

def sixTarget : F := fun x : Fin 6 → Bool => Nat.testBit (4008241280 * 2 ^ 32 + 3900760064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
    have e : projectedWire points (PEqualNP.Outside.L_meta_49097.comb tag a b) = combine (!tag) left right := by
      cases tag <;> rfl
    have next := Reach.two (!tag) built (projectedAvailable all ha) (projectedAvailable all hb)
    obtain ⟨result, run, hit⟩ := ih next (by
      intro u hu
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · exact Or.inl (by rw [e]; exact List.mem_cons_self)
      · exact available_cons _ (all _ hu))
    exact ⟨result, by simpa only [Nat.add_assoc, Nat.add_comm 1 k] using run, hit⟩

end Projection
end PEqualNP.Outside.L_meta_49097

namespace PEqualNP.Outside.L_meta_49097.ReadFour
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



def ix (p : Fin 4) : Fin 6 := ⟨p.val,by omega⟩

def var (i : Fin 6) : Wire Row := observe (inputs.getD i.val Threshold.Core.zero)

def rawBase : List (Wire Row) := List.ofFn var

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem raw_included (i : Fin 6) : var i ∈ rawBase := List.mem_ofFn.mpr ⟨i,rfl⟩

def whole (r : Row) : Bool := (4008241280 * 2 ^ 32 + 3900760064 : Nat).testBit (r.val % 64)



def coValue (p : Fin 4) : Bool := p.val < 2

def coIndex (p : Fin 4) (i : Fin 6) : Nat :=
  let k := if i.val < p.val then i.val else i.val - 1
  if coValue p then ([2,0,1,3,4] : List Nat).getD k 0 else k

def coRow (p : Fin 4) (r : Row) : Row :=
  ⟨(List.range 6).foldl (fun n i =>
    let j : Fin 6 := Fin.ofNat 6 i
    let c := bit r (Threshold.TabKfive.root.getD (coIndex p j) Threshold.Core.zero)
    let value := if j = ix p then coValue p else if coValue p then c else !c
    if value then n + (1 <<< i) else n) 0 % 64,
    Nat.lt_trans (Nat.mod_lt _ (by decide : 0<64)) (by decide)⟩

def coBase (_ : Fin 4) : List (Wire Row) :=
  Threshold.TabKfive.root.map observe

def atlasWord (r : Row) : Bool :=
  (4276676744 : Nat).testBit (r.val % 32)

def coGoal (p : Fin 4) : Wire Row :=
  if coValue p then atlasWord else inv (observe Threshold.TabKfive.target)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem var_co_value : ∀ p : Fin 4, ∀ r : Row, var (ix p) (coRow p r) = coValue p := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coTarget : ∀ p : Fin 4, ∀ r : Row, whole (coRow p r) = coGoal p r := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem coRoot (p : Fin 4) {v : Wire Row} (member : v ∈ rawBase) :
    Available true (coBase p) (pull (coRow p) v) := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
  by_cases pin : i=ix p
  · subst i
    exact Or.inr (Or.inl ⟨coValue p, funext (var_co_value p)⟩)
  · let col := Threshold.TabKfive.root.getD (coIndex p i) Threshold.Core.zero
    have valid : ∀ (p : Fin 4) (i : Fin 6), i ≠ ix p →
        Threshold.TabKfive.root.getD (coIndex p i) Threshold.Core.zero ∈ Threshold.TabKfive.root := by
      decide +kernel
    have inRoot : observe col ∈ coBase p := List.mem_map_of_mem (valid p i pin)
    cases sign : coValue p
    · have eval : ∀ (p : Fin 4) (i : Fin 6), i ≠ ix p → coValue p = false → ∀ r : Row,
          (!(var i (coRow p r))) = bit r (Threshold.TabKfive.root.getD (coIndex p i) Threshold.Core.zero) := by
        decide +kernel
      have eq : inv (pull (coRow p) (var i)) = observe col := funext (eval p i pin sign)
      exact Or.inr (Or.inr ⟨rfl,eq.symm ▸ inRoot⟩)
    · have eval : ∀ (p : Fin 4) (i : Fin 6), i ≠ ix p → coValue p = true → ∀ r : Row,
          var i (coRow p r) = bit r (Threshold.TabKfive.root.getD (coIndex p i) Threshold.Core.zero) := by
        decide +kernel
      have eq : pull (coRow p) (var i) = observe col := funext (eval p i pin sign)
      exact Or.inl (eq.symm ▸ inRoot)

def embedAtlas (r : Atlas.Model.Row) : Row := ⟨r.val,by omega⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem atlasPoint : ∀ (p : Fin 5) (r : Atlas.Model.Row),
    observe (Threshold.TabKfive.root.getD p.val Threshold.Core.zero) (embedAtlas r) =
      Atlas.Model.observe (Atlas.B30.R.getD p.val 0) r := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem atlasRoots (p : Fin 4) : (coBase p).map (pull embedAtlas) =
    Atlas.B30.R.map Atlas.Model.observe := by
  have source : coBase p = List.ofFn (fun j : Fin 5 =>
      observe (Threshold.TabKfive.root.getD j.val Threshold.Core.zero)) := rfl
  have dest : Atlas.B30.R.map Atlas.Model.observe = List.ofFn (fun j : Fin 5 =>
      Atlas.Model.observe (Atlas.B30.R.getD j.val 0)) := rfl
  rw [source,dest,List.map_ofFn]
  apply congrArg List.ofFn
  funext j r
  exact atlasPoint j r

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem atlasBits : ∀ r : Atlas.Model.Row,
    atlasWord (embedAtlas r) = Atlas.Model.observe Atlas.B30.T r := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pull_to_atlas {base bank : List (Wire Row)} {n : Nat}
    (h : Reach true base n bank) :
    Atlas.Model.Reach true (base.map (pull embedAtlas)) n (bank.map (pull embedAtlas)) := by
  induction h using Reach.ind with
  | start => exact Atlas.Model.Reach.start
  | @two n bank a b op h ha hb ih =>
    have stock : ∀ v ∈ bank, Available true (bank.map (pull embedAtlas)) (pull embedAtlas v) :=
      fun _ h => Or.inl (List.mem_map_of_mem h)
    have next := Atlas.Model.Reach.two op ih (pull_available stock ha) (pull_available stock hb)
    have eq : pull embedAtlas (combine op a b) = combine op (pull embedAtlas a) (pull embedAtlas b) :=
      pull_result embedAtlas ⟨op,a,b⟩
    rw [List.map_cons,eq]
    exact next

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem co_floor (p : Fin 4) {n : Nat} {B : List (Wire Row)}
    (run : Reach true (coBase p) n B) (hit : Available true B (coGoal p)) : 10 ≤ n := by
  cases side : coValue p
  · have inverse : Available true B (inv (observe Threshold.TabKfive.target)) := by
      simpa only [coGoal,side,Bool.false_eq_true,ite_false] using hit
    have hitPos := avail_inv rfl inverse
    rw [inv_inv'] at hitPos
    exact Threshold.TabKfive.lower n B run hitPos
  · have pos : Available true B atlasWord := by simpa only [coGoal,side,ite_true] using hit
    have proof := pull_to_atlas run
    rw [atlasRoots p] at proof
    have filtered := pull_available (f:=embedAtlas) (fun _ k => Or.inl (List.mem_map_of_mem k)) pos
    rw [show pull embedAtlas atlasWord = Atlas.Model.observe Atlas.B30.T from funext atlasBits] at filtered
    exact Atlas.B30.low _ _ proof filtered

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pin_budget (h : Valid rawBase gs) (out : Available true (stock rawBase gs) whole)
    (p : Fin 4) : 10 + dropCount (coRow p) (coBase p) gs ≤ gs.length := by
  obtain ⟨n,B,e,reach,cover⟩ := project_steps h Reach.start (fun _ m => coRoot p m)
  have output := pull_available cover out
  have eq : pull (coRow p) whole = coGoal p := funext (coTarget p)
  rw [eq] at output
  have lb := co_floor p reach output
  omega

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem raw_free_one : ∀ p : Fin 4, (4 : Fin 6) ≠ ix p := by decide +kernel

def fullRows : List Nat := [12, 0, 12, 22, 26, 12, 22, 12, 12, 22, 12, 38, 12, 21, 12, 0, 25, 12, 21, 12, 12, 21, 12, 37, 10, 9, 9, 10, 9, 0, 19, 9, 9, 19, 9, 35, 6, 5, 5, 6, 19, 5, 5, 0, 5, 19, 5, 35]
theorem cheap_pivot {g : Binary Row} (p : Fin 4) (read : Reads [var (ix p)] g) :
    Cheap (coRow p) (coBase p) g := by
  have constant {v} (h : SignedIn [var (ix p)] v) : Constant (pull (coRow p) v) := by
    simp only [SignedIn,List.mem_singleton] at h
    rcases h with rfl | z
    · exact ⟨coValue p, funext (var_co_value p)⟩
    · have eq : v = inv (var (ix p)) := (inv_inv' v).symm.trans (congrArg inv z)
      rw [eq]
      exact inv_constant (⟨coValue p, funext (var_co_value p)⟩)
  exact read.elim (fun h => Or.inl (constant h)) (fun h => Or.inr (Or.inl (constant h)))


theorem pivot_once (h : Valid rawBase gs) (out : Available true (stock rawBase gs) whole)
    (cap : gs.length≤11) (p : Fin 4) : tally (Reads [var (ix p)]) gs ≤ 1 := by
  have subset := tally_disjoint_le (P:=Reads [var (ix p)]) (Q:=fun _ => False)
    (L:=Cheap (coRow p) (coBase p)) (fun _ h => cheap_pivot p h)
    (fun _ => False.elim) (by simp) gs
  have lem : tally (Reads [var (ix p)]) gs ≤ dropCount (coRow p) (coBase p) gs := by
    simpa [tally,dropCount] using subset
  have k := pin_budget h out p
  omega
def samplePair (rows : List Nat) (p : Fin 4) (q : Fin 6) (b : Bool) : Row × Row :=
  let n := rows.getD (p.val * 12 + q.val * 2 + b.toNat) 0
  (Fin.ofNat 512 n, Fin.ofNat 512 (n + (1 <<< (ix p).val)))

def Apart (p : Fin 4) (l r : Row) : Prop :=
  ∀ i : Fin 6, i ≠ ix p → var i l = var i r

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem full_pair : ∀ (p : Fin 4) (q : Fin 6) (b : Bool), q ≠ ix p →
    let w := samplePair fullRows p q b
    Apart p w.1 w.2 ∧ var q w.1 = b ∧ var q w.2 = b ∧ whole w.1 ≠ whole w.2 := by
  unfold Apart
  decide +kernel

theorem apart_agree {p : Fin 4} {l r : Row} (h : Apart p l r) :
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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem raw_other {gs : List (Binary Row)} (h : Valid rawBase gs)
    (done : Available true (stock rawBase gs) whole) (cap : gs.length≤11)
    {g : Binary Row} (gm : g ∈ gs) (p : Fin 4) (q : Fin 6) (ne : q≠ix p)
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
    have a : v w.1 = g.disj := by simp [negated,inv,w,left]
    have b : v w.2 = g.disj := by simp [negated,inv,w,right]
    exact hd (quiet_split h (apart_agree apart) noPre noSuf (saturated side a b) done (not_signed_root _))


def Phase (u a : Wire R) : Prop := u=a ∨ u=inv a

theorem phase_in {B : List (Wire R)} {w v : Wire R} (ha : w ∈ B) (h : Phase v w) :
    SignedIn B v := read_as_phase.mpr ⟨w,ha,h⟩

theorem raw_other_read {gs : List (Binary Row)} (h : Valid rawBase gs)
    (done : Available true (stock rawBase gs) whole) (cap : gs.length≤11)
    {g : Binary Row} (gm : g ∈ gs) (p : Fin 4) (q : Fin 6) (ne : q≠ix p)
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


theorem pivot_used (h : Valid rawBase gs) (done : Available true (stock rawBase gs) whole) (p : Fin 4) :
    ∃ g ∈ gs, Reads [var (ix p)] g := by
  classical
  by_contra no
  obtain ⟨hapart,_,_,dif⟩ := full_pair p 4 true (raw_free_one p)
  have eq := quiet h (apart_agree hapart) (fun g mem use => no ⟨g,mem,use⟩)
  exact dif (literal_agrees eq.2 done (not_signed_root _))


theorem trace_eleven (h : Valid rawBase gs) (done : Available true (stock rawBase gs) whole) :
    11 ≤ gs.length := by
  obtain ⟨g,m,use⟩ := pivot_used h done 0
  have k := tally_one (P:=Cheap (coRow 0) (coBase 0)) m (cheap_pivot 0 use)
  have lb := pin_budget h done 0
  change 1 ≤ dropCount (coRow 0) (coBase 0) gs at k
  omega
def signed (b : Bool) (f : Wire R) : Wire R := fun r => if b then !(f r) else f r

theorem signed_choice {a z : Wire R} (h : SignedIn [z] a) :
    ∃ b : Bool, a = signed b z := by
  obtain ⟨w,mem,phase⟩ := read_as_phase.mp h
  rw [List.mem_singleton.mp mem] at phase
  rcases phase with eq | eq
  · exact ⟨false,eq⟩
  · exact ⟨true,eq⟩

theorem sign_available {B : List (Wire R)} {z : Wire R} (b : Bool)
    (h : Available true B z) : Available true B (signed b z) := by
  cases b
  · exact h
  · exact avail_inv rfl h

theorem stock_contains {B : List (Wire R)} {xs : List (Binary R)} {v : Wire R}
    (m : v ∈ B) : v ∈ stock B xs := stock_mem.mpr (Or.inl m)

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

def controls : List (Wire Row) := List.ofFn fun p : Fin 4 => var (ix p)

theorem control_mem (p : Fin 4) : var (ix p) ∈ controls := List.mem_ofFn.mpr ⟨p,rfl⟩

theorem no_ctrl_signed {v : Wire Row}
    (no : ∀ p : Fin 4, ¬ SignedIn [var (ix p)] v) : ¬ SignedIn controls v := by
  intro h
  obtain ⟨r,m,sg⟩ := read_as_phase.mp h
  obtain ⟨p,rfl⟩ := List.mem_ofFn.mp m
  exact no _ (phase_in List.mem_cons_self sg)

theorem has_ctrl {g : Binary Row} (see : Reads controls g) :
    ∃ p : Fin 4, Reads [var (ix p)] g := by
  classical
  by_contra no
  push Not at no
  exact see.elim
    (no_ctrl_signed (fun p hs=>no p (Or.inl hs)))
    (no_ctrl_signed (fun p hs=>no p (Or.inr hs)))

theorem control_reads {g : Binary Row} {p : Fin 4} (single : Reads [var (ix p)] g) :
    Reads controls g :=
  reads_mono (fun _ m=>(List.mem_singleton.mp m).symm ▸ control_mem p) single

def testRows : List Nat := [12, 22, 38, 50, 12, 21, 37, 49, 9, 19, 35, 49, 5, 19, 35, 49]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem contr_ix : ∀ (p q : Fin 4), ix p = ix q → p=q := by decide +kernel

def testPair (p : Fin 4) (r : Row) : Row × Row :=
  let n := testRows.getD (p.val*4 + (r.val/16)%4) 0
  (Fin.ofNat 512 n, Fin.ofNat 512 (n + (1 <<< (ix p).val)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem row_tests : ∀ (p : Fin 4) (r : Row),
    let s := testPair p r
    Apart p s.1 s.2 ∧ (whole s.1 ≠ whole s.2) ∧
      (var 4 s.1 = var 4 r ∧ var 4 s.2 = var 4 r) ∧
      (var 5 s.1 = var 5 r ∧ var 5 s.2 = var 5 r) := by
  unfold Apart
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem only_free : ∀ i : Fin 6, (∀ p : Fin 4, i ≠ ix p) → i = 4 ∨ i = 5 := by
  decide +kernel

theorem same_free (p : Fin 4) (r : Row) :
    AgreesOutside (testPair p r).1 r controls rawBase ∧
    AgreesOutside (testPair p r).2 r controls rawBase := by
  obtain ⟨_,_,b,c⟩ := row_tests p r
  have only {i : Fin 6} (avoid : var i ∉ controls) : i=4 ∨ i=5 := by
    apply only_free
    intro q e
    exact avoid (e.symm ▸ control_mem q)
  constructor
  · intro w wm outside
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp wm
    rcases only outside with rfl|rfl
    · exact b.1
    · exact c.1
  · intro w wm outside
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp wm
    rcases only outside with rfl|rfl
    · exact b.2
    · exact c.2

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem trace_twelve (h : Valid rawBase gs) (done : Available true (stock rawBase gs) whole) :
    12 ≤ gs.length := by
  by_contra! tooSmall
  have cap : gs.length≤11 := by omega
  obtain ⟨reader,mem,seen⟩ := pivot_used h done 0
  obtain ⟨pre,g,suf,shape,rd,noPre⟩ := first_split ⟨reader,mem,control_reads seen⟩
  subst gs
  obtain ⟨p,hp⟩ := has_ctrl rd
  have gmem : g ∈ pre ++ g::suf := List.mem_append.mpr (Or.inr List.mem_cons_self)
  have ledger := (valid_append _ _ _).mp h
  obtain ⟨sig,w,operands⟩ := operand_choice hp
  have av := matched_available operands ledger.2.1 ledger.2.2.1
  have existsNew := result_fresh h done cap
  have wQuiet : ¬ SignedIn controls w := by
    apply no_ctrl_signed
    intro q asRaw
    by_cases eq : q=p
    · subst q
      obtain ⟨b,hw⟩ := signed_choice asRaw
      have inBase := combine_phases (stock_contains (xs:=pre) (raw_included (ix p))) sig b g.disj
      rw [← hw, ← matched_res operands] at inBase
      exact existsNew inBase
    · exact raw_other_read h done cap gmem p (ix q) (fun e=>eq (contr_ix q p e)) hp
        (matched_reads (matched_comm operands) asRaw)
  obtain ⟨avoidPre,avoidSuf⟩ := read_once (pivot_once h done cap p) hp
  have neverAbsorbs (r : Row) : w r ≠ g.disj := by
    intro equals
    have preserve := same_free p r
    have e₁ := literal_agrees (quiet ledger.1 preserve.1 noPre).2 av wQuiet
    have e₂ := literal_agrees (quiet ledger.1 preserve.2 noPre).2 av wQuiet
    obtain ⟨apart,dif,_,_⟩ := row_tests p r
    have sat := saturated (matched_side (matched_comm operands)) (e₁.trans equals) (e₂.trans equals)
    exact dif (quiet_split h (apart_agree apart) avoidPre avoidSuf sat done (not_signed_root _))
  have constant : Constant w := by
    refine ⟨!g.disj,funext (fun r=> ?_)⟩
    have hd := neverAbsorbs r
    cases ht : g.disj <;> cases hw : w r <;> simp_all
  apply existsNew
  rw [matched_res operands]
  exact from_constant _ (Or.inr constant)
    (sign_available _ (Or.inl (stock_contains (raw_included (ix p))))) av

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

end PEqualNP.Outside.L_meta_49097.ReadFour

namespace PEqualNP.Outside.L_meta_49097
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sixWitness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [11, 14]⟩, ⟨.and, [0, 15]⟩, ⟨.and, [1, 14]⟩, ⟨.or, [16, 17]⟩], 18⟩

theorem basis : Monotone2 sixWitness := by simp [Monotone2, sixWitness]

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
theorem correct : ∀ x : X, sixWitness.eval (List.ofFn x) = sixTarget x := by decide +kernel

end PEqualNP.Outside.L_meta_49097

open PEqualNP.Outside.L_meta_49097 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_49097 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241280 * 2 ^ 32 + 3900760064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241280 * 2 ^ 32 + 3900760064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  by_cases enough : 13 ≤ s
  · exact ⟨sixWitness, basis, enough, correct⟩
  obtain ⟨⟨gs,o⟩, fit, size, computes⟩ := h
  have hf : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    exact ⟨by simpa using (fit g hg).1, (fit g hg).2⟩
  change gs.length ≤ s at size
  exact ⟨⟨gs,o⟩, all_not_not ReadFour.highFloor gs o hf (by omega) computes, size, computes⟩
