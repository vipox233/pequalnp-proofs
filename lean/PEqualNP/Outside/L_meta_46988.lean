import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46988
-- The five-input lower bound is from V_meta_9980__k13, PR #20915 by alexandersato0830.
-- Its lower-bound method and data derive from #16362 by tungsten-wolf, Apache-2.0.
namespace RescueK5
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
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

abbrev Row := Fin 128
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

def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
theorem bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
theorem tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
theorem tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
theorem tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
theorem nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
theorem bin_four (u : Bool) (o : Nat) (h : (u || Nat.blt o 2) = true) : ∃ e, allowed u e ∧ ∀ a b, bin o a b = bin e a b := by
  cases u
  · refine ⟨o,Or.inl ?_,fun _ _ => rfl⟩
    simpa only [Bool.false_or,Nat.blt_eq] using h
  · by_cases h : o < 4
    · exact ⟨o,Or.inr ⟨rfl,h⟩,fun _ _ => rfl⟩
    · refine ⟨3,Or.inr ⟨rfl,by omega⟩,fun a b => ?_⟩
      have h0 : o ≠ 0 := by omega
      have h1 : o ≠ 1 := by omega
      have h2 : o ≠ 2 := by omega
      simp [bin,h0,h1,h2]
theorem W_zero : W 0 = zero := rfl
theorem W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
theorem W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (u : Bool) (R : List Nat) (T L : Nat) : Prop := Lower u (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (u : Bool) (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice u (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

abbrev BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^128 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧ (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
theorem BaseP.lt {T R} (h : BaseP T R) : T < 2^128 := h.1
theorem BaseP.plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
theorem BaseP.nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
theorem BaseP.plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
theorem BaseP.ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
theorem BaseP.prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2

theorem baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

theorem lowOf {u T R E K} (hB : baseOK T R E = true) (h : Impossible u (W T) K (rootsW R).toFinset) :
    LowN u R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {u T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN u R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

theorem mkSlice {u R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN u R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN u R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def opOK (u : Bool) (o : Nat) : Bool := u || Nat.blt o 2
def av (u : Bool) (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || (u && Nat.beq x (Nat.xor d m)))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (u : Bool) (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool u (bif opOK u c.1 then P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)] else P) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available u bank (RF f v)
theorem rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
theorem rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
theorem rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
theorem rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
theorem rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
theorem cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
theorem av_ok {u} {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS u f bank P)
    (h : av u d P v = true) : Available u bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | ⟨hu,h⟩⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv hu e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {u} {f : Row → Row} {roots bank p P} (o a b : Nat) (ho : opOK u o = true) (hr : Reach u roots p bank) (hP : PS u f bank P)
    (ha : Available u bank (RF f a)) (hb : Available u bank (RF f b)) :
    ∃ next, Reach u roots (p+1) next ∧ PS u f next P ∧ Available u next (RF f (nb o a b)) ∧
      ∀ v, Available u bank v → Available u next v := by
  obtain ⟨e,he,heq⟩ := bin_four u o ho
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) he ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {u} {f : Row → Row} {bank P} (hP : PS u f bank P) (i : Nat) : Available u bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {u} {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach u roots p bank)
    (hP : PS u f bank P) : ∃ next, Reach u roots (p+cs.length) next ∧ PS u f next (mkPool u P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    have big : ∃ next, Reach u roots (p+1) next ∧ PS u f next (bif opOK u c.1 then P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)] else P) := by
      cases ho : opOK u c.1
      · refine ⟨_,Reach.two false hr (Or.inr (Or.inl ⟨false,rfl⟩)) (Or.inr (Or.inl ⟨false,rfl⟩)),fun v hv => available_cons _ (hP v hv)⟩
      · obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ ho hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
        refine ⟨next,h1,?_⟩
        intro v hv
        rw [cond_true] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact h2 v hv
        · rw [List.mem_singleton.mp hv]
          exact h3
    obtain ⟨next,h1,this⟩ := big
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (u : Bool) (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av u d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (u : Bool) (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av u c.1 c.2.2.2) && keepB u c.1 c.2.2.2 ka a && keepB u c.1 c.2.2.2 kb b &&
  (bif av u c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av u c.1 c.2.2.2 a && av u c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def same (u : Bool) (p : Nat × Nat) (v : Nat) : Bool :=
  bif u then Nat.testBit v p.1 == Nat.testBit v p.2 else !(Nat.testBit v p.1) || Nat.testBit v p.2
def sepEval (u : Bool) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  same u p z && (!ka || same u p a) && (!kb || same u p b) && rest.all (same u p)
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && T.testBit p.1 && !(T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
theorem sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
theorem mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
theorem kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (u : Bool) (_R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach u (roots.map observe) c.2.2.1 bank ∧ PS u f bank c.2.2.2 ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {u R T c k rest a b o ka kb} (hc : CutP u R T c) (ho : opOK u o = true)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval u k rest a b (nb o a b) ka kb c = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach u (roots.map observe) q bank' ∧ PS u f bank' c.2.2.2 ∧ Available u bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av u c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b ho hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply u bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available u bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

theorem kid_mem {rest : List Nat} {a b z : Nat} {ka kb : Bool} {v : Sig} (hv : v ∈ kidW rest a b z ka kb) :
    ∃ x, v = W x ∧ (x = z ∨ (ka = true ∧ x = a) ∨ (kb = true ∧ x = b) ∨ x ∈ rest) := by
  rcases List.mem_cons.mp hv with rfl | hv
  · exact ⟨z,rfl,Or.inl rfl⟩
  have low : ∀ v ∈ kept kb (W b) (rest.map W), ∃ x, v = W x ∧ ((kb = true ∧ x = b) ∨ x ∈ rest) := by
    intro v hv
    cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
      exact ⟨x,e.symm,Or.inr hx⟩
    · rcases List.mem_cons.mp hv with e | hv
      · exact ⟨b,e,Or.inl ⟨rfl,rfl⟩⟩
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        exact ⟨x,e.symm,Or.inr hx⟩
  cases ka
  · obtain ⟨x,h1,h2⟩ := low v hv
    exact ⟨x,h1,Or.inr (Or.inr h2)⟩
  · rcases List.mem_cons.mp hv with e | hv
    · exact ⟨a,e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
    · obtain ⟨x,h1,h2⟩ := low v hv
      exact ⟨x,h1,Or.inr (Or.inr h2)⟩
theorem sep_sound {u T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval u rest a b (nb o a b) ka kb p = true) :
    Impossible u (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨p1,p2⟩,t1⟩,t2⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have all : ∀ v ∈ kidW rest a b (nb o a b) ka kb, ∃ x, v = W x ∧ same u p x = true := by
    intro v hv
    obtain ⟨x,rfl,hx⟩ := kid_mem hv
    refine ⟨x,rfl,?_⟩
    rcases hx with rfl | ⟨q,rfl⟩ | ⟨q,rfl⟩ | hx
    · exact h1
    · subst q; exact h2.resolve_left (by simp)
    · subst q; exact h3.resolve_left (by simp)
    · exact h4 x hx
  intro k' _ run
  cases u
  · obtain ⟨v,hv,hp,hn⟩ := mono_row_difference run rfl (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W]; exact t1) (by rw [bit_W]; exact t2)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    rw [bit_W] at hp hn
    simp only [same,cond_false,Bool.or_eq_true,Bool.not_eq_true'] at hx
    rcases hx with hx | hx
    · rw [hx] at hp; exact Bool.noConfusion hp
    · rw [hx] at hn; exact Bool.noConfusion hn
  · obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W,t1,t2]; simp)
    obtain ⟨x,rfl,hx⟩ := all v (List.mem_toFinset.mp hv)
    apply hne
    rw [bit_W,bit_W]
    simpa only [same,cond_true,beq_iff_eq] using hx

def KWOwn (S : Finset Sig) (T : Sig) (owns : Sig → Row → Row → Prop) : Prop :=
  (∀ p n, bit p T = true → bit n T = false → ∃ v, owns v p n) ∧
  (∀ v p n, owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false) ∧
  (∀ v w p n, owns v p n → owns w p n → v = w) ∧
  (∀ v p n p' n', owns v p n → owns v p' n' → owns v p n')
abbrev KWRooms (S : Finset Sig) (T : Sig) := {o : Sig → Row → Row → Prop // KWOwn S T o}
def KWRooms.owns {S T} (H : KWRooms S T) : Sig → Row → Row → Prop := H.1
theorem KWRooms.total {S T} (H : KWRooms S T) : ∀ p n, bit p T = true → bit n T = false → ∃ v, H.owns v p n := H.2.1
theorem KWRooms.valid {S T} (H : KWRooms S T) {v p n} : H.owns v p n → v ∈ S ∧ bit p v = true ∧ bit n v = false := H.2.2.1 v p n
theorem KWRooms.unique {S T} (H : KWRooms S T) {v w p n} : H.owns v p n → H.owns w p n → v = w := H.2.2.2.1 v w p n
theorem KWRooms.rect {S T} (H : KWRooms S T) {v p n p' n'} : H.owns v p n → H.owns v p' n' → H.owns v p n' := H.2.2.2.2 v p n p' n'
theorem kwLeaf (T : Sig) : Nonempty (KWRooms {T} T) := by
  refine ⟨⟨fun v p n => v = T ∧ bit p T = true ∧ bit n T = false,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    exact ⟨T,rfl,hp,hn⟩
  · rintro v p n ⟨rfl,hp,hn⟩
    exact ⟨by simp,hp,hn⟩
  · rintro v w p n ⟨rfl,_⟩ ⟨rfl,_⟩
    rfl
  · rintro v p n p' n' ⟨rfl,hp,_⟩ ⟨_,_,hn⟩
    exact ⟨rfl,hp,hn⟩
theorem kwFork {T : Sig} {U : Finset Sig} {a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1) (hab : a ≠ b) (ha : a ∉ U) (hb : b ∉ U)
    (hz : bin d a b ∉ U) (H : KWRooms (insert (bin d a b) U) T) : Nonempty (KWRooms (insert a (insert b U)) T) := by
  classical
  let z := bin d a b
  let own : Sig → Row → Row → Prop := fun v p n => (v ∈ U ∧ H.owns v p n) ∨
    (H.owns z p n ∧ v = (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)))
  have pickU : ∀ (p n : Row), (if d=0 then (if bit n a = false then a else b) else (if bit p a = true then a else b)) ∉ U := by
    intro p n
    split <;> split <;> assumption
  refine ⟨⟨own,?_,?_,?_,?_⟩⟩
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with e | hm
    · refine ⟨_,Or.inr ⟨?_,rfl⟩⟩
      rw [show v = z from e] at hv
      exact hv
    · exact ⟨v,Or.inl ⟨hm,hv⟩⟩
  · intro v p n h
    rcases h with ⟨hm,hv⟩ | ⟨hv,rfl⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm),(H.valid hv).2⟩
    · obtain ⟨_,hp,hn⟩ := H.valid hv
      change bit p (bin d a b) = true at hp
      change bit n (bin d a b) = false at hn
      rw [bit_bin] at hp hn
      rcases d01 with rfl | rfl
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
      · cases pa : bit p a <;> cases na : bit n a <;> cases pb : bit p b <;> cases nb' : bit n b <;> simp_all
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,rfl⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,rfl⟩
    · exact H.unique hv hw
    · exact absurd (show z ∈ U by rw [←H.unique hv hw]; exact vU) hz
    · exact absurd (show z ∈ U by rw [←H.unique hw hv]; exact wU) hz
    · rfl
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨hv,e1⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨hw,e2⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact absurd (e2 ▸ vU) (pickU p' n')
    · exact absurd (e1 ▸ wU) (pickU p n)
    · refine Or.inr ⟨H.rect hv hw,?_⟩
      by_cases h : d=0
      · rw [if_pos h] at e2 ⊢
        exact e2
      · rw [if_neg h] at e1 ⊢
        exact e1
theorem kwTight {T : Sig} {k : Nat} {S : Finset Sig} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact kwLeaf T
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b ∉ U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := live_size tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le a (insert b U)
    have le2 := Finset.card_insert_le b U
    have ha : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a ∈ insert b U)] at tight
      omega
    have hb : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by
      rcases hd with h | ⟨h,_⟩
      · omega
      · exact Bool.noConfusion h
    exact kwFork d01 hab ha hb fresh H
def only (l : List Nat) (p n a : Nat) : Bool :=
  Nat.blt p 128 && Nat.blt n 128 && l.all (fun x => !(Nat.testBit x p) || Nat.testBit x n || Nat.beq x a)
abbrev KwD := Nat × Nat × Nat × Nat × Nat × Nat
def findW (l : List Nat) (p n : Nat) : Nat := (l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n))).getD 0
def kwOK (T : Nat) (q : KwD) : Bool :=
  T.testBit q.1 && T.testBit q.2.2.2.1 && T.testBit q.2.2.2.2.2 && !(T.testBit q.2.1) && !(T.testBit q.2.2.1) && !(T.testBit q.2.2.2.2.1)
def kwList (l : List Nat) (q : KwD) : Bool :=
  let a := findW l q.1 q.2.2.1
  let b := findW l q.1 q.2.2.2.2.1
  only l q.1 q.2.2.1 a && only l q.2.2.2.1 q.2.1 a &&
  (bif Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1 then !(Nat.testBit a q.1 && !(Nat.testBit a q.2.1))
   else only l q.1 q.2.2.2.2.1 b && only l q.2.2.2.2.2 q.2.1 b && !(Nat.beq a b))
theorem only_own {l : List Nat} {T p n a : Nat} (H : KWRooms ((l.map W).toFinset) (W T))
    (h : only l p n a = true) (tp : T.testBit p = true) (tn : T.testBit n = false) :
    ∃ (hp : p < 128) (hn : n < 128), H.owns (W a) ⟨p,hp⟩ ⟨n,hn⟩ := by
  simp only [only,Bool.and_eq_true,Nat.blt_eq,List.all_eq_true,Bool.or_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨hp,hn⟩,hl⟩ := h
  refine ⟨hp,hn,?_⟩
  obtain ⟨v,hv⟩ := H.total ⟨p,hp⟩ ⟨n,hn⟩ (by rw [bit_W]; exact tp) (by rw [bit_W]; exact tn)
  obtain ⟨hm,h1,h2⟩ := H.valid hv
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  rw [bit_W] at h1 h2
  rcases hl x hx with (h | h) | h
  · rw [h] at h1; exact Bool.noConfusion h1
  · rw [h] at h2; exact Bool.noConfusion h2
  · rw [Nat.eq_of_beq_eq_true h] at hv
    exact hv
theorem kw_sound {T k : Nat} {l : List Nat} (nd : (l.map W).Nodup) (size : l.length = k+1) (lt : ∀ x ∈ l, x < 2^128) (q : KwD)
    (hT : kwOK T q = true) (h : kwList l q = true) : Impossible false (W T) k (l.map W).toFinset := by
  intro k' hk run
  have lb := live_size run
  rw [List.toFinset_card_of_nodup nd,List.length_map] at lb
  obtain ⟨H⟩ := kwTight run (by rw [List.toFinset_card_of_nodup nd,List.length_map]; omega)
  simp only [kwOK,Bool.and_eq_true,Bool.not_eq_true'] at hT
  obtain ⟨⟨⟨⟨⟨t1,t2⟩,t3⟩,t4⟩,t5⟩,t6⟩ := hT
  simp only [kwList,Bool.and_eq_true] at h
  obtain ⟨⟨h1,h2⟩,h3⟩ := h
  obtain ⟨hp,hna,o1⟩ := only_own H h1 t1 t5
  obtain ⟨hpa,hn,o2⟩ := only_own H h2 t2 t4
  have own := H.rect o1 o2
  cases hc : (Nat.beq q.1 q.2.2.2.2.2 && Nat.beq q.2.1 q.2.2.2.2.1)
  · rw [hc,cond_false] at h3
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at h3
    obtain ⟨⟨h4,h5⟩,h6⟩ := h3
    obtain ⟨_,hnb,o3⟩ := only_own H h4 t1 t6
    obtain ⟨hpb,_,o4⟩ := only_own H h5 t3 t4
    have own' := H.rect o3 o4
    have ee := H.unique own own'
    have mem : ∀ {a : Nat}, W a ∈ (l.map W).toFinset → ∃ x ∈ l, W x = W a := by
      intro a ha
      obtain ⟨x,hx,e⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact ⟨x,hx,e⟩
    have fw : ∀ p n, findW l p n < 2^128 := by
      intro p n
      unfold findW
      cases hf : l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n)) with
      | none => exact Nat.two_pow_pos 128
      | some x => exact lt x (List.mem_of_find?_eq_some hf)
    have := W_inj (fw _ _) (fw _ _) ee
    rw [this,Nat.beq_refl] at h6
    exact Bool.noConfusion h6
  · rw [hc,cond_true] at h3
    have v := (H.valid own).2
    rw [bit_W,bit_W] at v
    rw [v.1,v.2] at h3
    exact Bool.noConfusion h3

def hiM : Nat → Nat
  | 0 => 0x22222222222222222222222222222222
  | 1 => 0x0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
  | 2 => 0x00f000f000f000f000f000f000f000f0
  | 3 => 0x0000ff000000ff000000ff000000ff00
  | _ => 0x00000000ffff000000000000ffff0000
def loM : Nat → Nat
  | 0 => 0x44444444444444444444444444444444
  | 1 => 0x30303030303030303030303030303030
  | 2 => 0x0f000f000f000f000f000f000f000f00
  | 3 => 0x00ff000000ff000000ff000000ff0000
  | _ => 0x0000ffff000000000000ffff00000000
def keM : Nat → Nat
  | 0 => 0x99999999999999999999999999999999
  | 1 => 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
  | 2 => 0xf00ff00ff00ff00ff00ff00ff00ff00f
  | 3 => 0xff0000ffff0000ffff0000ffff0000ff
  | _ => 0xffff00000000ffffffff00000000ffff
def shM : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | _ => 16
def swapN (i v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (keM i)) (Nat.shiftLeft (Nat.land v (hiM i)) (shM i))) (Nat.shiftRight (Nat.land v (loM i)) (shM i))
def sig (i : Nat) (r : Row) : Row :=
  if (hiM i).testBit r.val then Fin.ofNat 128 (r.val + shM i) else
    if (loM i).testBit r.val then Fin.ofNat 128 (r.val - shM i) else r
def swapFacts (i : Nat) (r : Row) : Prop :=
  ((keM i).testBit r.val = true ∧ (sig i r).val = r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ shM i ≤ r.val ∧ (sig i r).val = r.val - shM i ∧ (hiM i).testBit (r.val - shM i) = true ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ (sig i r).val = shM i + r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = true)
theorem swap_facts : ∀ (i : Fin 5) (r : Row), swapFacts i.val r ∧ sig i.val (sig i.val r) = r := by
  unfold swapFacts
  decide +kernel
theorem swap_ok (i : Nat) (hi : i < 5) (v : Nat) : W (swapN i v) = rename (sig i) (W v) := by
  apply bit_ext
  intro r
  rw [bit_W,bit_rename,bit_W]
  have e : (swapN i v).testBit r.val = (((v.testBit r.val && (keM i).testBit r.val) ||
      (decide (shM i ≤ r.val) && (v.testBit (r.val - shM i) && (hiM i).testBit (r.val - shM i)))) ||
      (v.testBit (shM i + r.val) && (loM i).testBit (shM i + r.val))) := by
    have s1 : (Nat.shiftLeft (Nat.land v (hiM i)) (shM i)).testBit r.val = (decide (shM i ≤ r.val) && (Nat.land v (hiM i)).testBit (r.val - shM i)) := by
      exact Nat.testBit_shiftLeft ..
    have s2 : (Nat.shiftRight (Nat.land v (loM i)) (shM i)).testBit r.val = (Nat.land v (loM i)).testBit (shM i + r.val) := by
      exact Nat.testBit_shiftRight ..
    unfold swapN
    rw [tb_lor,tb_lor,s1,s2,tb_land,tb_land,tb_land]
  rw [e]
  rcases (swap_facts ⟨i,hi⟩ r).1 with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4,h5⟩ | ⟨h1,h2,h3,h4⟩
  · change (sig i r).val = r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
  · change (sig i r).val = r.val - shM i at h3
    rw [h3]
    simp only [] at h1 h2 h4 h5
    rw [h1,h4,h5,decide_eq_true h2]
    simp
  · change (sig i r).val = shM i + r.val at h2
    rw [h2]
    simp only [] at h1 h3 h4
    rw [h1,h4]
    cases hd : decide (shM i ≤ r.val)
    · simp
    · rw [hd,Bool.true_and] at h3
      rw [h3]; simp
def permN (l : List Nat) (v : Nat) : Nat := l.foldl (fun v i => swapN i v) v
def symOK (T : Nat) (l : List Nat) : Bool := l.all fun i => Nat.blt i 5 && Nat.beq (swapN i T) T
theorem perm_sound {u T k} (l : List Nat) (hT : symOK T l = true) (s : List Nat)
    (h : Impossible u (W T) k ((s.map (permN l)).map W).toFinset) : Impossible u (W T) k (s.map W).toFinset := by
  induction l generalizing s with
  | nil =>
    simpa [show (permN [] : Nat → Nat) = id from rfl] using h
  | cons i l ih =>
    simp only [symOK,List.all_cons,Bool.and_eq_true,Nat.blt_eq] at hT
    obtain ⟨⟨hi,hs⟩,hl⟩ := hT
    have h' : Impossible u (W T) k ((s.map (swapN i)).map W).toFinset := by
      apply ih hl
      have : (s.map (swapN i)).map (permN l) = s.map (permN (i::l)) := by
        rw [List.map_map]
        rfl
      rw [this]
      exact h
    intro k' hk run
    have onto : Function.Surjective (sig i) := fun r => ⟨sig i r,(swap_facts ⟨i,hi⟩ r).2⟩
    have r2 := live_rename run (sig i) onto
    rw [←swap_ok i hi T,Nat.eq_of_beq_eq_true hs] at r2
    apply h' k' hk
    have : ((s.map (swapN i)).map W).toFinset = (s.map W).toFinset.image (rename (sig i)) := by
      ext v
      simp only [List.mem_toFinset,List.mem_map,Finset.mem_image,exists_exists_and_eq_and,swap_ok i hi]
    rw [this]
    exact r2

abbrev StD := List Nat × List (List Nat)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
theorem picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
theorem pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
theorem beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
theorem mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
theorem kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (u : Bool) (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool u (initPool s.1 s.2.2) c.2)
abbrev Tabs := List CutV × List (Nat × Nat) × List KwD × List (List Nat)
def Tabs.cuts (t : Tabs) : List CutV := t.1
def Tabs.seps (t : Tabs) : List (Nat × Nat) := t.2.1
def Tabs.kws (t : Tabs) : List KwD := t.2.2.1
def Tabs.perms (t : Tabs) : List (List Nat) := t.2.2.2
def sortN (l : List Nat) : List Nat := l.foldr ins []
theorem mem_sortN {v : Nat} {l : List Nat} : v ∈ sortN l ↔ v ∈ l := by
  induction l with
  | nil => simp [sortN]
  | cons x xs ih =>
    change v ∈ ins x (sortN xs) ↔ _
    rw [mem_ins,ih]
    simp
def hintOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 10000 then (match t.cuts[i]? with
    | some c => cutEval u k rest a b z ka kb c
    | none => false)
  else bif Nat.blt i 20000 then (match t.seps[i-10000]? with
    | some q => sepEval u rest a b z ka kb q
    | none => false)
  else bif Nat.blt i 30000 then (match t.kws[i-20000]? with
    | some q => !u && Nat.beq (kidN rest a b z ka kb).length (k+1) && kwList (kidN rest a b z ka kb) q
    | none => false)
  else (match t.perms[i-30000]? with
    | some l => next.any (beqL (sortN ((kidN rest a b z ka kb).map (permN l))))
    | none => false)
def kidOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK u k next t rest a b z kk.1 kk.2)
def opsOf (u : Bool) : List Nat := bif u then [0,1,2,3] else [0,1]
def pairOK (u : Bool) (k : Nat) (next : List (List Nat)) (t : Tabs) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  (opsOf u).all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK u k next t p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
theorem allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
theorem asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK u k next t st.1) (pairs st.1) st.2
def levelOK (u : Bool) (T : Nat) (t : Tabs) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK u T t k next)
abbrev TabsP (u : Bool) (R : List Nat) (T : Nat) (t : Tabs) : Prop :=
  (∀ c ∈ t.cuts, CutP u R T c) ∧ t.seps.all (sepOK T) = true ∧ t.kws.all (kwOK T) = true ∧ t.perms.all (symOK T) = true
theorem TabsP.c {u R T t} (h : TabsP u R T t) : ∀ c ∈ t.cuts, CutP u R T c := h.1
theorem TabsP.s {u R T t} (h : TabsP u R T t) : t.seps.all (sepOK T) = true := h.2.1
theorem TabsP.k {u R T t} (h : TabsP u R T t) : t.kws.all (kwOK T) = true := h.2.2.1
theorem TabsP.p {u R T t} (h : TabsP u R T t) : t.perms.all (symOK T) = true := h.2.2.2
def LevelN (u : Bool) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible u (W T) k (st.1.map W).toFinset
theorem cutsGood {u R T} {Z : List SliceD} {C : List (Nat × List (Nat × Nat × Nat))} (hZ : ∀ s ∈ Z, SliceN u R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut u Z), CutP u R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS u f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=u) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

theorem stStep {u R T E t k next st} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hn : ∀ s ∈ next, Impossible u (W T) k (s.map W).toFinset)
    (h : stOK u T t k next st = true) : Impossible u (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true'] at h
  obtain ⟨⟨ha,hT⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have inOps : ∀ {o : Nat}, allowed u o → o ∈ opsOf u := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · have : o = 0 ∨ o = 1 := by omega
        simpa [opsOf] using this
      · exact Bool.noConfusion h
    · have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by rcases h with h | ⟨_,h⟩ <;> omega
      simpa [opsOf] using this
  have opk : ∀ {o : Nat}, allowed u o → opOK u o = true := by
    intro o h
    cases u
    · rcases h with h | ⟨h,_⟩
      · simpa only [opOK,Bool.false_or,Nat.blt_eq] using h
      · exact Bool.noConfusion h
    · rfl
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp

  have core : ∀ (o : Nat) (ja jb : Bool), allowed u o → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible u (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (inOps ho4)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with hk | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      have sub : ∀ x ∈ kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb, x < 2^128 := by
        intro x hx
        have hx' : x = nb o p.1 p.2.1 ∨ x ∈ st.1 := by
          unfold kidN at hx
          rw [mem_ins] at hx
          rcases hx with hx | hx
          · exact Or.inl hx
          · right
            rw [pm]
            cases ja <;> cases jb <;> simp only [cond_true,cond_false,mem_ins] at hx <;> tauto
        rcases hx' with rfl | hx'
        · have l1 : p.1 < 2^128 := lt _ ((pm _).mpr (Or.inl rfl))
          have l2 : p.2.1 < 2^128 := lt _ ((pm _).mpr (Or.inr (Or.inl rfl)))
          have la : Nat.land p.1 p.2.1 < 2^128 := Nat.lt_of_le_of_lt (Nat.and_le_left) l1
          unfold nb
          cases Nat.beq o 0 <;> cases Nat.beq o 1 <;> cases Nat.beq o 2 <;>
            first | exact la | exact Nat.or_lt_two_pow l1 l2 | exact Nat.xor_lt_two_pow l1 la | exact Nat.xor_lt_two_pow l2 la
        · exact lt x hx'
      cases h1 : Nat.blt i 10000
      · rw [h1,cond_false] at hi
        cases h2 : Nat.blt i 20000
        · rw [h2,cond_false] at hi
          cases h3 : Nat.blt i 30000
          · rw [h3,cond_false] at hi
            cases hg : t.perms[i-30000]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some l =>
              rw [hg] at hi
              obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hi
              rw [←kid_fin]
              apply perm_sound l (List.all_eq_true.mp ht.p l (List.mem_of_getElem? hg))
              have : (((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map (permN l)).map W).toFinset = (s.map W).toFinset := by
                rw [←beqL_ok e]
                ext v
                simp only [List.mem_toFinset,List.mem_map,mem_sortN]
              rw [this]
              exact hn s hs'
          · rw [h3,cond_true] at hi
            cases hg : t.kws[i-20000]? with
            | none => rw [hg] at hi; exact Bool.noConfusion hi
            | some q =>
              rw [hg] at hi
              simp only [Bool.and_eq_true,Bool.not_eq_true'] at hi
              obtain ⟨⟨hu,hlen⟩,hkw⟩ := hi
              rw [←kid_fin]
              have sz := Nat.eq_of_beq_eq_true hlen
              have nd' : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).Nodup := by
                apply List.dedup_eq_self.mp
                apply (List.dedup_sublist _).eq_of_length
                have c1 : ((kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).map W).toFinset.card = (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).length := by
                  rw [kid_fin,List.toFinset_card_of_nodup nk]
                rw [List.card_toFinset] at c1
                rw [c1,List.length_map]
                have il : ∀ (z : Nat) (l : List Nat), (ins z l).length = l.length + 1 := by
                  intro z l
                  induction l with
                  | nil => rfl
                  | cons x xs ih =>
                    unfold ins
                    cases Nat.ble z x
                    · rw [cond_false,List.length_cons,ih,List.length_cons]
                    · rfl
                unfold kidN kidW
                cases ja <;> cases jb <;> simp [kept,il]
              subst hu
              exact kw_sound nd' sz sub q (List.all_eq_true.mp ht.k q (List.mem_of_getElem? hg)) hkw
        · rw [h2,cond_true] at hi
          cases hg : t.seps[i-10000]? with
          | none => rw [hg] at hi; exact Bool.noConfusion hi
          | some q =>
            rw [hg] at hi
            exact sep_sound (List.all_eq_true.mp ht.s q (List.mem_of_getElem? hg)) hi
      · rw [h1,cond_true] at hi
        cases hg : t.cuts[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (ht.c q (List.mem_of_getElem? hg)) (opk ho4) nk hi
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have r := core (flipOp d) kb ka hfl.1 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {u R T E t k D' D} (hB : baseOK T R E = true) (ht : TabsP u R T t)
    (hI : LevelN u T k D') (h : levelOK u T t k (D'.map Prod.fst) D = true) : LevelN u T (k+1) D := by
  intro st hst
  refine stStep hB ht ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {u : Bool} {T : Nat} {t : Tabs} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK u T t k next ((D.drop (i*c)).take c) = true) : levelOK u T t k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
theorem lowSearch {u R T E K D} (hB : baseOK T R E = true) (hI : LevelN u T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN u R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this

def sw0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def sw1 : Nat := 0xcccccccccccccccccccccccccccccccc
def sw2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def sw3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
def sw4 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def sw5 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
def sw6 : Nat := 0xffccffccffccffccffccffccffccffcc
def sw7 : Nat := 0xfefefefefefefefefefefefefefefefe
def sw8 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee
def sw9 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def sw10 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
def sw11 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe
def sw12 : Nat := 0xffff0000ffff0000ffff0000ffff0000
def sw13 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaa
def sw14 : Nat := 0xffffccccffffccccffffccccffffcccc
def sw15 : Nat := 0xeeee0000eeee0000eeee0000eeee
def sw16 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0
def sw17 : Nat := 0xffffff00ffffff00ffffff00ffffff00
def sw18 : Nat := 0xfffffafafffffafafffffafafffffafa
def sw19 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfc
def sw20 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffee
def sw21 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeee
def sw22 : Nat := 0xfffefffefffefffefffefffefffefffe
def sw23 : Nat := 0xfefe0000fefe0000fefe0000fefe
def sw24 : Nat := 0xaaa8aaa8aaa8aaa8aaa8aaa8aaa8aaa8
def sw25 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffc
def sw26 : Nat := 0xa0000000a0000000a0000000a
def sw27 : Nat := 0xfffffff0fffffff0fffffff0fffffff0
def sw28 : Nat := 0x88888888888888888888888888888888
def sw29 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
def sw30 : Nat := 0xaaaafefeaaaafefeaaaafefeaaaafefe
def sw31 : Nat := 0xf000f000f000f000f000f000f000f000
def sw32 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc
def sw33 : Nat := 0xee000000ee000000ee000000ee
def sw34 : Nat := 0xfffafffafffafffafffafffafffafffa
def sw35 : Nat := 0xffffffaaffffffaaffffffaaffffffaa
def sw36 : Nat := 0xfafafafafafafafafafafafafafafafa
def sw37 : Nat := 0xfffffffcfffffffcfffffffcfffffffc
def sw38 : Nat := 0xffffffccffffffccffffffccffffffcc
def sw39 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa
def sw40 : Nat := 0xfffe0000fffe0000fffe0000fffe
def sw41 : Nat := 0xfffffe00fffffe00fffffe00fffffe00
def sw42 : Nat := 0x2aaaa0002aaaa0002aaaa0002aaaa
def sw43 : Nat := 0xfffffefefffffefefffffefefffffefe
def sw44 : Nat := 0xaaaaaaa8aaaaaaa8aaaaaaa8aaaaaaa8
def sw45 : Nat := 0xfffffffefffffffefffffffefffffffe
def sw46 : Nat := 0xaaaafffeaaaafffeaaaafffeaaaafffe
def sw47 : Nat := 0xfe000000fe000000fe000000fe
def sw48 : Nat := 0xfffc0000fffc0000fffc0000fffc
def sw49 : Nat := 0xffff000affff000affff000affff000a
def sw50 : Nat := 0x55555550555555505555555055555550
def sw51 : Nat := 0xffff8888ffff8888ffff8888ffff8888
def sw52 : Nat := 0xfffefefefffefefefffefefefffefefe
def sw53 : Nat := 0xfefefe00fefefe00fefefe00fefefe
def sw54 : Nat := 0xff000000ff000000ff000000ff000000
def sw55 : Nat := 0xffff00aaffff00aaffff00aaffff00aa
def sw56 : Nat := 0xfefefffefefefffefefefffefefefffe
def sw57 : Nat := 0xaaa8fffcaaa8fffcaaa8fffcaaa8fffc
def sw58 : Nat := 0xffff00eeffff00eeffff00eeffff00ee
def sw59 : Nat := 0xaafeaafeaafeaafeaafeaafeaafeaafe
def sw60 : Nat := 0xeeeefffeeeeefffeeeeefffeeeeefffe
def sw61 : Nat := 0xaafe0000aafe0000aafe0000aafe
def sw62 : Nat := 0x8888fff88888fff88888fff88888fff8
def sw63 : Nat := 0xfcccfcccfcccfcccfcccfcccfcccfccc
def sw64 : Nat := 0xfffff000fffff000fffff000fffff000
def sw65 : Nat := 0xfff00000fff00000fff00000fff0
def sw66 : Nat := 0xaafcfe00aafcfe00aafcfe00aafcfe
def sw67 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfc
def sw68 : Nat := 0xffffffeeffffffeeffffffeeffffffee
def sw69 : Nat := 0xf3f2f3f2f3f2f3f2f3f2f3f2f3f2f3f2
def sw70 : Nat := 0xf3f0f3f0f3f0f3f0f3f0f3f0f3f0f3f0
def sw71 : Nat := 0xaafaaafaaafaaafaaafaaafaaafaaafa
def sw72 : Nat := 0xfff0f0f0fff0f0f0fff0f0f0fff0f0f0
def sw73 : Nat := 0xfffffffafffffffafffffffafffffffa
def sw74 : Nat := 0xffffee00ffffee00ffffee00ffffee
def sw75 : Nat := 0xffa00000ffa00000ffa00000ffa
def sw76 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def sw77 : Nat := 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0
def sw78 : Nat := 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0
def sw79 : Nat := 0x3fffc0003fffc0003fffc0003fffc
def sw80 : Nat := 0xfffeff00fffeff00fffeff00fffeff00
def sw81 : Nat := 0xff00fe00ff00fe00ff00fe00ff00fe00
def sw82 : Nat := 0xaaaafffcaaaafffcaaaafffcaaaafffc
def sw83 : Nat := 0x99989998999899989998999899989998
def sw84 : Nat := 0xffccccccffccccccffccccccffcccccc
def sw85 : Nat := 0xffe00000ffe00000ffe00000ffe
def sw86 : Nat := 0xffffffff00000000ffffffff00000000
def s1_T : Nat := 0x88888888888888888888888888888888
def s1_R : List Nat := [0, 1]
def s1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem s1_B : baseOK s1_T s1_R s1_E = true := by decide +kernel
theorem s1_L : LowN true s1_R s1_T 1 := lowCount s1_B (by decide +kernel)
def s2_T : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def s2_R : List Nat := [0, 1]
def s2_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem s2_B : baseOK s2_T s2_R s2_E = true := by decide +kernel
theorem s2_L : LowN true s2_R s2_T 1 := lowCount s2_B (by decide +kernel)
def s3_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def s3_R : List Nat := [0, 1, 2]
def s3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem s3_B : baseOK s3_T s3_R s3_E = true := by decide +kernel
theorem s3_S0 : SliceN true s3_R s3_T (0x33333333333333333333333333333333,1,[0, 2]) := mkSlice (w:=0) s3_B s1_B s1_L (by decide +kernel)
theorem s3_S1 : SliceN true s3_R s3_T (0x55555555555555555555555555555555,1,[1, 2]) := mkSlice (w:=0) s3_B s1_B s1_L (by decide +kernel)
theorem s3_S2 : SliceN true s3_R s3_T (0xcccccccccccccccccccccccccccccccc,1,[0, 2]) := mkSlice (w:=2) s3_B s2_B s2_L (by decide +kernel)
theorem s3_S3 : SliceN true s3_R s3_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]) := mkSlice (w:=1) s3_B s2_B s2_L (by decide +kernel)
theorem s3_S4 : SliceN true s3_R s3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]) := mkSlice (w:=0) s3_B s1_B s1_L (by decide +kernel)
theorem s3_S5 : SliceN true s3_R s3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1]) := mkSlice (w:=4) s3_B s2_B s2_L (by decide +kernel)
def s3_Z : List SliceD := [(0x33333333333333333333333333333333,1,[0, 2]),(0x55555555555555555555555555555555,1,[1, 2]),(0xcccccccccccccccccccccccccccccccc,1,[0, 2]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,1,[1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,1,[0, 1]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,1,[0, 1])]
theorem s3_Y : ∀ s ∈ s3_Z, SliceN true s3_R s3_T s := by
  unfold s3_Z
  simp only [List.forall_mem_cons]
  exact ⟨s3_S0,s3_S1,s3_S2,s3_S3,s3_S4,s3_S5,by simp⟩
def s3_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def s3_t : Tabs := (s3_C.map (mkCut true s3_Z),[(5,4),(3,1),(3,0),(3,2),(6,2),(5,1)],[],[])
theorem s3_W : TabsP true s3_R s3_T s3_t := ⟨cutsGood s3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def s3_D3 : List StD := [
([sw0,sw1,sw2],[[0,1,10000,2,3,10001,10002],[4,1,10003,10000,3],[10001,0,5,2,10004,10005]])]
def s3_D2 : List StD := []
theorem s3_I2 : LevelN true s3_T 2 s3_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s3_C3x0 : levelOK true s3_T s3_t 2 (s3_D2.map Prod.fst) ((s3_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem s3_I3 : LevelN true s3_T 3 s3_D3 := levelStep s3_B s3_W s3_I2 (chunks 16 s3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s3_C3x0
  ))
theorem s3_L : LowN true s3_R s3_T 4 := lowSearch s3_B s3_I3 (by decide +kernel)
def s4_T : Nat := 0xfefefefefefefefefefefefefefefefe
def s4_R : List Nat := [0, 1, 2]
def s4_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem s4_B : baseOK s4_T s4_R s4_E = true := by decide +kernel
theorem s4_L : LowN true s4_R s4_T 2 := lowCount s4_B (by decide +kernel)
def s5_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def s5_R : List Nat := [0, 1, 2, 3]
def s5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem s5_B : baseOK s5_T s5_R s5_E = true := by decide +kernel
theorem s5_S0 : SliceN true s5_R s5_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S1 : SliceN true s5_R s5_T (0x33333333333333333333333333333333,4,[0, 2, 3]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S2 : SliceN true s5_R s5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S3 : SliceN true s5_R s5_T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]) := mkSlice (w:=0) s5_B s3_B s3_L (by decide +kernel)
theorem s5_S4 : SliceN true s5_R s5_T (0x11111111111111111111111111111111,1,[2, 3]) := mkSlice (w:=0) s5_B s1_B s1_L (by decide +kernel)
theorem s5_S5 : SliceN true s5_R s5_T (0x22222222222222222222222222222222,1,[2, 3]) := mkSlice (w:=1) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S6 : SliceN true s5_R s5_T (0x44444444444444444444444444444444,1,[2, 3]) := mkSlice (w:=2) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S7 : SliceN true s5_R s5_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]) := mkSlice (w:=1) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S8 : SliceN true s5_R s5_T (0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]) := mkSlice (w:=2) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S9 : SliceN true s5_R s5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]) := mkSlice (w:=4) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S10 : SliceN true s5_R s5_T (0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]) := mkSlice (w:=1) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S11 : SliceN true s5_R s5_T (0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]) := mkSlice (w:=8) s5_B s4_B s4_L (by decide +kernel)
theorem s5_S12 : SliceN true s5_R s5_T (0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]) := mkSlice (w:=2) s5_B s2_B s2_L (by decide +kernel)
theorem s5_S13 : SliceN true s5_R s5_T (0x50505050505050505050505050505050,1,[1, 3]) := mkSlice (w:=4) s5_B s2_B s2_L (by decide +kernel)
def s5_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3]),(0x33333333333333333333333333333333,4,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]),(0x11111111111111111111111111111111,1,[2, 3]),(0x22222222222222222222222222222222,1,[2, 3]),(0x44444444444444444444444444444444,1,[2, 3]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,2,[1, 2, 3]),(0xcccccccccccccccccccccccccccccccc,2,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,2,[0, 1, 3]),(0xaa00aa00aa00aa00aa00aa00aa00aa,1,[1, 2]),(0xff00ff00ff00ff00ff00ff00ff00ff00,2,[0, 1, 2]),(0xcc00cc00cc00cc00cc00cc00cc00cc,1,[0, 2]),(0x50505050505050505050505050505050,1,[1, 3])]
theorem s5_Y : ∀ s ∈ s5_Z, SliceN true s5_R s5_T s := by
  unfold s5_Z
  simp only [List.forall_mem_cons]
  exact ⟨s5_S0,s5_S1,s5_S2,s5_S3,s5_S4,s5_S5,s5_S6,s5_S7,s5_S8,s5_S9,s5_S10,s5_S11,s5_S12,s5_S13,by simp⟩
def s5_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(4,[]),(0,[(1,0,2)]),(1,[(1,0,2)]),(5,[]),(1,[(3,0,2)]),(6,[]),(0,[(3,0,2)]),(2,[(1,1,2)]),(2,[(1,0,2)]),(0,[(1,0,1)]),(1,[(1,0,1)]),(1,[(3,0,1)]),(7,[]),(0,[(3,0,1)]),(8,[]),(0,[(2,0,1)]),(9,[]),(10,[]),(0,[(2,0,2)]),(11,[]),(12,[]),(0,[(1,0,2),(1,1,2)]),(8,[(1,1,2)]),(0,[(1,0,1),(1,1,2)]),(0,[(1,0,1),(1,0,2)]),(0,[(1,1,2),(1,0,3)]),(3,[(3,1,2)]),(0,[(0,0,2)]),(0,[(2,1,2)]),(0,[(0,1,2)]),(13,[])]
def s5_t : Tabs := (s5_C.map (mkCut true s5_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(6,4),(6,2),(10,8),(10,2),(12,8),(12,4),(7,8)],[],[[],[1],[2,1],[0,1],[0,2,1],[1,0,2,1],[0,1,2],[0,1,2,1],[1,2],[1,2,1],[2],[1,0]])
theorem s5_W : TabsP true s5_R s5_T s5_t := ⟨cutsGood s5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def s5_D6 : List StD := [
([sw0,sw1,sw2,sw3],[[0,1,10000,30000,10001,10002],[0,10001,30001,10000,10003,2],[0,10000,30002,10004,10005,3],[1,10002,30003,10006,10007,2],[1,10002,30004,10008,10009,3],[2,10003,30005,10010,10011,3]])]
noncomputable def s5_D5 : List StD := [
([sw0,sw1,sw4,sw2,sw3],[[0,1],[1],[0,30006,10003,4],[0,30007,10005,5],[0],[1,30008,10007,4],[1,30009,10009,5],[4,6,2,30000,10003,30010,10010],[5,6,3,30010,10005,30000,10011],[10003,4,10010,10011]])]
noncomputable def s5_D4 : List StD := [
([sw0,sw1,sw2,sw5,sw6],[[7,30011,8],[7,9],[10],[7,8,9],[8,11],[8,7,11],[12],[13,9,10007],[14,11,10003],[7,8]]),
([sw0,sw1,sw2,sw7,sw3],[[15,4,16],[15,16,4],[17],[15,18],[4,15,16],[19],[16,20],[21],[4,22],[3,18,30000]]),
([sw8,sw0,sw1,sw2,sw3],[[0,1],[1,0],[2,23,6],[7],[24,23],[6,23],[6,25,5],[6,26],[23,25],[23,25]])]
noncomputable def s5_D3 : List StD := [
([sw0,sw9,sw6,sw10],[[27,28,10012],[29,28,10000],[30,10000,10001],[3,31,32],[3,28,1],[1,28]]),
([sw11,sw0,sw1,sw2],[[0,18],[24,20,33],[34,6,35],[36,18],[11,18],[9,20]])]
def s5_D2 : List StD := []
theorem s5_I2 : LevelN true s5_T 2 s5_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C3x0 : levelOK true s5_T s5_t 2 (s5_D2.map Prod.fst) ((s5_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I3 : LevelN true s5_T 3 s5_D3 := levelStep s5_B s5_W s5_I2 (chunks 16 s5_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C4x0 : levelOK true s5_T s5_t 3 (s5_D3.map Prod.fst) ((s5_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I4 : LevelN true s5_T 4 s5_D4 := levelStep s5_B s5_W s5_I3 (chunks 16 s5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C4x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C5x0 : levelOK true s5_T s5_t 4 (s5_D4.map Prod.fst) ((s5_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I5 : LevelN true s5_T 5 s5_D5 := levelStep s5_B s5_W s5_I4 (chunks 16 s5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s5_C6x0 : levelOK true s5_T s5_t 5 (s5_D5.map Prod.fst) ((s5_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem s5_I6 : LevelN true s5_T 6 s5_D6 := levelStep s5_B s5_W s5_I5 (chunks 16 s5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s5_C6x0
  ))
theorem s5_L : LowN true s5_R s5_T 7 := lowSearch s5_B s5_I6 (by decide +kernel)
def s6_T : Nat := 0xfffefffefffefffefffefffefffefffe
def s6_R : List Nat := [0, 1, 2, 3]
def s6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8)]
theorem s6_B : baseOK s6_T s6_R s6_E = true := by decide +kernel
theorem s6_L : LowN true s6_R s6_T 3 := lowCount s6_B (by decide +kernel)
def s7_T : Nat := 0xfffefee8fffefee8fffefee8fffefee8
def s7_R : List Nat := [0, 1, 2, 3, 4]
def s7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem s7_B : baseOK s7_T s7_R s7_E = true := by decide +kernel
theorem s7_S0 : SliceN true s7_R s7_T (0x55555555555555555555555555555555,7,[1, 2, 3, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S1 : SliceN true s7_R s7_T (0x33333333333333333333333333333333,7,[0, 2, 3, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S2 : SliceN true s7_R s7_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S3 : SliceN true s7_R s7_T (0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S4 : SliceN true s7_R s7_T (0xffff0000ffff0000ffff0000ffff,7,[0, 1, 2, 3]) := mkSlice (w:=0) s7_B s5_B s5_L (by decide +kernel)
theorem s7_S5 : SliceN true s7_R s7_T (0x11111111111111111111111111111111,4,[2, 3, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S6 : SliceN true s7_R s7_T (0x3333000033330000333300003333,4,[0, 2, 3]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S7 : SliceN true s7_R s7_T (0x5555000055550000555500005555,4,[1, 2, 3]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S8 : SliceN true s7_R s7_T (0x3030303030303030303030303030303,4,[0, 3, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S9 : SliceN true s7_R s7_T (0x5050505050505050505050505050505,4,[1, 3, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S10 : SliceN true s7_R s7_T (0x1010101010101010101010101010101,1,[3, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S11 : SliceN true s7_R s7_T (0xf000f000f000f000f000f000f000f,4,[0, 1, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S12 : SliceN true s7_R s7_T (0xf0f00000f0f00000f0f00000f0f,4,[0, 1, 3]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S13 : SliceN true s7_R s7_T (0xff000000ff000000ff000000ff,4,[0, 1, 2]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S14 : SliceN true s7_R s7_T (0x550055005500550055005500550055,4,[1, 2, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S15 : SliceN true s7_R s7_T (0x33003300330033003300330033003300,2,[0, 2, 4]) := mkSlice (w:=8) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S16 : SliceN true s7_R s7_T (0xffff0000ffff0000ffff0000ffff0000,3,[0, 1, 2, 3]) := mkSlice (w:=16) s7_B s6_B s6_L (by decide +kernel)
theorem s7_S17 : SliceN true s7_R s7_T (0x11110000111100001111000011110000,1,[2, 3]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S18 : SliceN true s7_R s7_T (0x10101010101010101010101010101010,1,[3, 4]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S19 : SliceN true s7_R s7_T (0x11001100110011001100110011001100,1,[2, 4]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S20 : SliceN true s7_R s7_T (0x22222222222222222222222222222222,2,[2, 3, 4]) := mkSlice (w:=1) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S21 : SliceN true s7_R s7_T (0x2222000022220000222200002222,1,[2, 3]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S22 : SliceN true s7_R s7_T (0xff000000ff000000ff000000ff0000,2,[0, 1, 2]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S23 : SliceN true s7_R s7_T (0x2020202020202020202020202020202,1,[3, 4]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S24 : SliceN true s7_R s7_T (0xcc000000cc000000cc000000cc,1,[0, 2]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S25 : SliceN true s7_R s7_T (0xcccccccccccccccccccccccccccccccc,3,[0, 2, 3, 4]) := mkSlice (w:=2) s7_B s6_B s6_L (by decide +kernel)
theorem s7_S26 : SliceN true s7_R s7_T (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]) := mkSlice (w:=1) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S27 : SliceN true s7_R s7_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]) := mkSlice (w:=2) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S28 : SliceN true s7_R s7_T (0xa0a00000a0a00000a0a00000a0a,1,[1, 3]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S29 : SliceN true s7_R s7_T (0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]) := mkSlice (w:=2) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S30 : SliceN true s7_R s7_T (0x330033003300330033003300330033,4,[0, 2, 4]) := mkSlice (w:=0) s7_B s3_B s3_L (by decide +kernel)
theorem s7_S31 : SliceN true s7_R s7_T (0x30003000300030003000300030003,1,[0, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S32 : SliceN true s7_R s7_T (0x44444444444444444444444444444444,2,[2, 3, 4]) := mkSlice (w:=2) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S33 : SliceN true s7_R s7_T (0xaa00aa00aa00aa00aa00aa00aa00aa,2,[1, 2, 4]) := mkSlice (w:=1) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S34 : SliceN true s7_R s7_T (0xf0f00000f0f00000f0f00000f0f0,2,[0, 1, 3]) := mkSlice (w:=4) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S35 : SliceN true s7_R s7_T (0xff00ff00ff00ff00ff00ff00ff00ff00,3,[0, 1, 2, 4]) := mkSlice (w:=8) s7_B s6_B s6_L (by decide +kernel)
theorem s7_S36 : SliceN true s7_R s7_T (0x30303030303030303030303030303030,2,[0, 3, 4]) := mkSlice (w:=4) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S37 : SliceN true s7_R s7_T (0x33330000333300003333000033330000,2,[0, 2, 3]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S38 : SliceN true s7_R s7_T (0x50505050505050505050505050505050,2,[1, 3, 4]) := mkSlice (w:=4) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S39 : SliceN true s7_R s7_T (0x55005500550055005500550055005500,2,[1, 2, 4]) := mkSlice (w:=8) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S40 : SliceN true s7_R s7_T (0x55550000555500005555000055550000,2,[1, 2, 3]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S41 : SliceN true s7_R s7_T (0xaa000000aa000000aa000000aa,1,[1, 2]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S42 : SliceN true s7_R s7_T (0xc0c00000c0c00000c0c00000c0c,1,[0, 3]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S43 : SliceN true s7_R s7_T (0xf0f00000f0f00000f0f00000f0f0000,2,[0, 1, 3]) := mkSlice (w:=16) s7_B s4_B s4_L (by decide +kernel)
theorem s7_S44 : SliceN true s7_R s7_T (0xf0000000f0000000f0000000f0000,1,[0, 1]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S45 : SliceN true s7_R s7_T (0x440044004400440044004400440044,1,[2, 4]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S46 : SliceN true s7_R s7_T (0x3030000030300000303000003030000,1,[0, 3]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S47 : SliceN true s7_R s7_T (0x500050005000500050005000500050,1,[1, 4]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S48 : SliceN true s7_R s7_T (0xf0000000f0000000f0000000f00,1,[0, 1]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S49 : SliceN true s7_R s7_T (0xf0000000f0000000f0000000f0,1,[0, 1]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S50 : SliceN true s7_R s7_T (0x300030003000300030003000300030,1,[0, 4]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S51 : SliceN true s7_R s7_T (0x220022002200220022002200220022,1,[2, 4]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S52 : SliceN true s7_R s7_T (0x5000500050005000500050005000500,1,[1, 4]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S53 : SliceN true s7_R s7_T (0x4040404040404040404040404040404,1,[3, 4]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S54 : SliceN true s7_R s7_T (0xa000a000a000a000a000a000a000a,1,[1, 4]) := mkSlice (w:=1) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S55 : SliceN true s7_R s7_T (0x3300000033000000330000003300,1,[0, 2]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S56 : SliceN true s7_R s7_T (0x550000005500000055000000550000,1,[1, 2]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S57 : SliceN true s7_R s7_T (0x5050000050500000505000005050,1,[1, 3]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S58 : SliceN true s7_R s7_T (0x3030000030300000303000003030,1,[0, 3]) := mkSlice (w:=4) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S59 : SliceN true s7_R s7_T (0x5050000050500000505000005050000,1,[1, 3]) := mkSlice (w:=16) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S60 : SliceN true s7_R s7_T (0x50005000500050005000500050005,1,[1, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S61 : SliceN true s7_R s7_T (0x110011001100110011001100110011,1,[2, 4]) := mkSlice (w:=0) s7_B s1_B s1_L (by decide +kernel)
theorem s7_S62 : SliceN true s7_R s7_T (0x3000300030003000300030003000300,1,[0, 4]) := mkSlice (w:=8) s7_B s2_B s2_L (by decide +kernel)
theorem s7_S63 : SliceN true s7_R s7_T (0xc000c000c000c000c000c000c000c,1,[0, 4]) := mkSlice (w:=2) s7_B s2_B s2_L (by decide +kernel)
def s7_Z : List SliceD := [(0x55555555555555555555555555555555,7,[1, 2, 3, 4]),(0x33333333333333333333333333333333,7,[0, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,7,[0, 1, 2, 3]),(0x11111111111111111111111111111111,4,[2, 3, 4]),(0x3333000033330000333300003333,4,[0, 2, 3]),(0x5555000055550000555500005555,4,[1, 2, 3]),(0x3030303030303030303030303030303,4,[0, 3, 4]),(0x5050505050505050505050505050505,4,[1, 3, 4]),(0x1010101010101010101010101010101,1,[3, 4]),(0xf000f000f000f000f000f000f000f,4,[0, 1, 4]),(0xf0f00000f0f00000f0f00000f0f,4,[0, 1, 3]),(0xff000000ff000000ff000000ff,4,[0, 1, 2]),(0x550055005500550055005500550055,4,[1, 2, 4]),(0x33003300330033003300330033003300,2,[0, 2, 4]),(0xffff0000ffff0000ffff0000ffff0000,3,[0, 1, 2, 3]),(0x11110000111100001111000011110000,1,[2, 3]),(0x10101010101010101010101010101010,1,[3, 4]),(0x11001100110011001100110011001100,1,[2, 4]),(0x22222222222222222222222222222222,2,[2, 3, 4]),(0x2222000022220000222200002222,1,[2, 3]),(0xff000000ff000000ff000000ff0000,2,[0, 1, 2]),(0x2020202020202020202020202020202,1,[3, 4]),(0xcc000000cc000000cc000000cc,1,[0, 2]),(0xcccccccccccccccccccccccccccccccc,3,[0, 2, 3, 4]),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,2,[1, 3, 4]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2,[0, 3, 4]),(0xa0a00000a0a00000a0a00000a0a,1,[1, 3]),(0xcccc0000cccc0000cccc0000cccc,2,[0, 2, 3]),(0x330033003300330033003300330033,4,[0, 2, 4]),(0x30003000300030003000300030003,1,[0, 4]),(0x44444444444444444444444444444444,2,[2, 3, 4]),(0xaa00aa00aa00aa00aa00aa00aa00aa,2,[1, 2, 4]),(0xf0f00000f0f00000f0f00000f0f0,2,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff00,3,[0, 1, 2, 4]),(0x30303030303030303030303030303030,2,[0, 3, 4]),(0x33330000333300003333000033330000,2,[0, 2, 3]),(0x50505050505050505050505050505050,2,[1, 3, 4]),(0x55005500550055005500550055005500,2,[1, 2, 4]),(0x55550000555500005555000055550000,2,[1, 2, 3]),(0xaa000000aa000000aa000000aa,1,[1, 2]),(0xc0c00000c0c00000c0c00000c0c,1,[0, 3]),(0xf0f00000f0f00000f0f00000f0f0000,2,[0, 1, 3]),(0xf0000000f0000000f0000000f0000,1,[0, 1]),(0x440044004400440044004400440044,1,[2, 4]),(0x3030000030300000303000003030000,1,[0, 3]),(0x500050005000500050005000500050,1,[1, 4]),(0xf0000000f0000000f0000000f00,1,[0, 1]),(0xf0000000f0000000f0000000f0,1,[0, 1]),(0x300030003000300030003000300030,1,[0, 4]),(0x220022002200220022002200220022,1,[2, 4]),(0x5000500050005000500050005000500,1,[1, 4]),(0x4040404040404040404040404040404,1,[3, 4]),(0xa000a000a000a000a000a000a000a,1,[1, 4]),(0x3300000033000000330000003300,1,[0, 2]),(0x550000005500000055000000550000,1,[1, 2]),(0x5050000050500000505000005050,1,[1, 3]),(0x3030000030300000303000003030,1,[0, 3]),(0x5050000050500000505000005050000,1,[1, 3]),(0x50005000500050005000500050005,1,[1, 4]),(0x110011001100110011001100110011,1,[2, 4]),(0x3000300030003000300030003000300,1,[0, 4]),(0xc000c000c000c000c000c000c000c,1,[0, 4])]
theorem s7_Y : ∀ s ∈ s7_Z, SliceN true s7_R s7_T s := by
  unfold s7_Z
  simp only [List.forall_mem_cons]
  exact ⟨s7_S0,s7_S1,s7_S2,s7_S3,s7_S4,s7_S5,s7_S6,s7_S7,s7_S8,s7_S9,s7_S10,s7_S11,s7_S12,s7_S13,s7_S14,s7_S15,s7_S16,s7_S17,s7_S18,s7_S19,s7_S20,s7_S21,s7_S22,s7_S23,s7_S24,s7_S25,s7_S26,s7_S27,s7_S28,s7_S29,s7_S30,s7_S31,s7_S32,s7_S33,s7_S34,s7_S35,s7_S36,s7_S37,s7_S38,s7_S39,s7_S40,s7_S41,s7_S42,s7_S43,s7_S44,s7_S45,s7_S46,s7_S47,s7_S48,s7_S49,s7_S50,s7_S51,s7_S52,s7_S53,s7_S54,s7_S55,s7_S56,s7_S57,s7_S58,s7_S59,s7_S60,s7_S61,s7_S62,s7_S63,by simp⟩
def s7_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(4,[(1,0,1)]),(5,[]),(0,[(1,0,3)]),(1,[(1,0,3)]),(2,[(1,0,3),(1,1,3)]),(3,[(1,0,3),(1,1,3)]),(6,[]),(7,[]),(0,[(1,0,1)]),(1,[(1,0,1)]),(8,[]),(3,[(1,0,1),(1,2,4)]),(4,[(1,0,1),(1,2,4)]),(9,[]),(10,[]),(0,[(2,0,3)]),(4,[(3,0,1)]),(1,[(2,0,3)]),(0,[(1,1,2)]),(1,[(1,1,2)]),(11,[(1,0,1)]),(5,[(1,0,1)]),(11,[]),(4,[(1,2,3)]),(0,[(1,1,2),(1,1,3),(1,2,3)]),(1,[(1,1,2),(1,1,3),(1,2,3)]),(12,[]),(13,[]),(0,[(1,0,3),(1,2,3)]),(1,[(1,0,2),(1,2,3)]),(2,[(1,0,2),(1,1,3),(1,2,3)]),(3,[(1,1,3)]),(6,[(1,0,2)]),(14,[(1,0,2)]),(15,[]),(14,[]),(1,[(1,2,3),(1,0,4)]),(16,[]),(0,[(1,1,3),(1,2,3)]),(1,[(1,1,3),(1,2,3)]),(2,[(1,0,1),(1,2,3)]),(3,[(1,0,1),(1,2,3)]),(17,[]),(5,[(1,1,2)]),(5,[(1,0,2)]),(0,[(1,2,3),(3,1,3)]),(18,[]),(19,[]),(0,[(1,1,3),(3,2,3)]),(0,[(1,0,3),(1,1,3)]),(1,[(1,0,3),(1,1,4)]),(4,[(1,0,2)]),(20,[]),(4,[(3,0,2)]),(0,[(1,0,3),(1,1,4)]),(0,[(1,1,3),(1,0,4)]),(21,[]),(1,[(1,0,3),(1,1,3)]),(9,[(1,0,2)]),(22,[]),(23,[]),(4,[(1,1,2)]),(11,[(1,1,2)]),(0,[(1,0,1),(2,0,3)]),(4,[(1,1,2),(1,0,4)]),(2,[(0,1,3)]),(0,[(1,0,1),(1,0,3)]),(12,[(1,0,1)]),(8,[(2,0,2)]),(4,[(1,0,1),(1,1,2)]),(24,[]),(0,[(1,0,1),(1,0,2)]),(2,[(1,0,1),(1,2,4)]),(1,[(1,0,1),(1,0,2)]),(1,[(1,0,2),(3,0,1)]),(1,[(1,0,1),(3,0,2)]),(0,[(1,0,2),(3,0,1)]),(0,[(1,0,1),(3,0,2)]),(25,[]),(0,[(1,0,2),(2,0,1)]),(0,[(1,0,1),(2,0,2)]),(2,[(1,0,1),(1,3,4)]),(26,[]),(1,[(1,1,3),(3,0,3)]),(27,[]),(0,[(1,1,3),(3,0,3)]),(0,[(1,0,3),(3,1,3)]),(3,[(1,0,1),(1,3,4)]),(28,[]),(8,[(1,0,1)]),(1,[(1,0,1),(1,2,4)]),(9,[(1,0,1)]),(3,[(1,0,1),(3,2,4)]),(5,[(2,0,1)]),(5,[(2,0,2)]),(1,[(1,0,1),(3,3,4)]),(2,[(1,0,1),(3,3,4)]),(9,[(2,0,2)]),(29,[]),(2,[(1,1,2),(2,0,4)]),(2,[(1,1,2),(0,0,1)]),(2,[(1,1,2),(3,0,1)]),(30,[]),(1,[(1,1,2),(0,0,4)]),(2,[(1,1,2),(0,0,4)]),(3,[(1,1,2),(0,0,4)]),(31,[]),(9,[(3,0,1)]),(32,[]),(5,[(3,0,1)]),(9,[(2,0,1)]),(0,[(1,0,1),(1,2,4)]),(0,[(1,0,1),(3,2,4)]),(33,[]),(3,[(1,0,2),(1,1,4)]),(2,[(1,0,2),(1,1,4)]),(0,[(1,0,2),(1,1,4)]),(0,[(1,1,2),(1,0,4)]),(0,[(1,0,1),(1,3,4)]),(0,[(1,0,1),(3,3,4)]),(4,[(1,0,2),(1,1,4)]),(34,[]),(4,[(1,2,3),(0,0,4)]),(9,[(1,1,2)]),(2,[(1,2,3),(2,0,4)]),(3,[(1,2,3),(2,0,4)]),(35,[]),(4,[(1,2,3),(2,0,4)]),(13,[(2,0,2)]),(9,[(3,1,2)]),(9,[(2,1,2)]),(4,[(1,2,3),(2,0,1)]),(4,[(1,2,3),(3,0,1)]),(2,[(1,2,3)]),(3,[(1,2,3)]),(2,[(0,0,1),(1,2,3)]),(36,[]),(3,[(0,0,1),(1,2,3)]),(37,[]),(4,[(0,0,1),(1,2,3)]),(38,[]),(39,[]),(40,[]),(3,[(0,0,1),(3,2,3)]),(4,[(0,0,1),(2,2,3)]),(3,[(0,0,1),(2,2,3)]),(3,[(1,0,1),(3,2,3)]),(2,[(1,0,1),(3,2,3)]),(3,[(1,0,1),(2,2,3)]),(3,[(1,1,2),(0,0,3)]),(3,[(1,1,2),(1,0,3)]),(1,[(2,0,3),(1,1,2)]),(2,[(2,0,3),(1,1,2)]),(3,[(2,0,3),(1,1,2)]),(3,[(2,0,3),(3,1,2)]),(3,[(2,0,3),(2,1,2)]),(2,[(2,0,3),(2,1,2)]),(0,[(0,1,2)]),(4,[(0,2,3),(1,0,1)]),(4,[(0,2,3),(3,0,1)]),(5,[(0,0,1)]),(0,[(0,1,2),(1,0,3)]),(0,[(2,0,3),(0,1,2)]),(41,[]),(42,[]),(0,[(2,0,3),(2,1,2)]),(0,[(2,0,3),(3,1,2)]),(43,[]),(4,[(1,2,3),(1,0,1)]),(0,[(1,1,2),(1,0,3)]),(0,[(2,0,3),(1,1,2)]),(44,[]),(45,[]),(46,[]),(47,[]),(0,[(1,2,3)]),(1,[(1,2,3)]),(0,[(1,2,3),(2,0,4)]),(1,[(1,2,3),(2,0,4)]),(5,[(3,1,2)]),(5,[(2,1,2)]),(5,[(1,0,2),(1,1,2)]),(5,[(1,0,1),(1,1,2)]),(5,[(1,0,1),(1,0,2)]),(0,[(1,2,3),(1,1,4)]),(0,[(1,1,3),(1,2,4)]),(0,[(1,1,2),(1,3,4)]),(3,[(1,0,2),(1,3,4)]),(48,[]),(49,[]),(0,[(1,1,2),(1,2,3),(1,1,5)]),(0,[(1,1,2),(1,2,3),(2,3,4)]),(0,[(1,1,2),(1,1,3),(1,2,5)]),(0,[(1,1,2),(1,1,3),(2,3,4)]),(15,[(1,1,2)]),(4,[(1,0,3),(1,2,4)]),(11,[(1,0,2)]),(16,[(1,2,3)]),(3,[(1,0,3),(1,2,4)]),(12,[(1,0,2)]),(39,[(1,1,2)]),(0,[(1,1,3),(1,1,2),(1,2,4)]),(0,[(1,1,3),(1,1,2),(2,3,5)]),(0,[(1,1,2),(1,1,3),(2,2,5)]),(4,[(1,1,3),(1,0,3),(1,0,4)]),(3,[(0,0,3)]),(3,[(0,1,3)]),(0,[(1,0,2),(1,0,3)]),(14,[(2,0,2)]),(4,[(1,0,1),(1,0,3),(1,1,3)]),(8,[(1,1,2)]),(0,[(1,0,2),(1,1,3),(1,2,3)]),(30,[(1,1,2)]),(0,[(1,0,1),(1,1,3),(1,2,3)]),(0,[(1,0,1),(1,0,2),(1,2,3)]),(0,[(1,0,1),(1,0,2),(1,1,3)]),(4,[(1,1,3),(1,2,4)]),(4,[(1,1,2),(1,3,4)]),(4,[(1,1,3),(2,2,4)]),(4,[(1,1,2),(2,3,4)]),(4,[(1,1,3),(1,1,2)]),(1,[(1,1,3),(1,2,4)]),(16,[(1,1,2)]),(3,[(1,1,2),(1,2,3)]),(1,[(1,0,1),(1,1,3),(1,2,3)]),(3,[(1,2,3),(3,0,2)]),(50,[]),(51,[]),(52,[]),(0,[(1,1,3),(1,2,3),(3,0,2)]),(53,[]),(2,[(1,0,3),(1,2,4)]),(1,[(1,0,1),(1,3,4),(1,2,3)]),(54,[]),(1,[(1,0,1),(1,1,2),(1,2,3)]),(3,[(1,0,2)]),(1,[(1,0,2),(1,1,3),(1,2,3)]),(1,[(1,1,3),(1,2,3),(3,0,2)]),(0,[(1,2,3),(1,0,1),(1,3,5)]),(2,[(1,0,2),(1,2,3),(3,1,3)]),(1,[(1,0,2),(1,2,3),(3,1,3)]),(0,[(1,0,2),(1,1,2)]),(0,[(1,0,2),(1,1,2),(1,0,3)]),(0,[(2,0,3),(1,0,2),(3,1,2)]),(4,[(1,0,1),(1,1,3),(1,2,3)]),(2,[(1,1,3),(1,2,3),(3,0,2)]),(55,[]),(56,[]),(4,[(1,0,3),(3,2,3)]),(14,[(1,1,2)]),(2,[(1,1,2)]),(4,[(1,0,2),(1,1,3),(1,1,4)]),(2,[(1,1,2),(0,0,3)]),(4,[(1,0,2),(1,1,3),(1,0,5)]),(3,[(1,0,2),(0,1,3)]),(30,[(2,0,2)]),(3,[(1,0,3),(1,1,2),(1,3,5)]),(0,[(1,1,3)]),(3,[(1,0,2),(1,2,3)]),(1,[(1,0,2),(1,0,3),(1,2,3)]),(20,[(1,1,2)]),(4,[(1,1,3),(3,0,3)]),(4,[(1,0,3),(1,1,3)]),(4,[(1,0,3),(3,1,3)]),(7,[(1,0,2)]),(3,[(1,1,2),(3,0,1)]),(3,[(1,1,2),(2,0,4)]),(0,[(1,0,1),(1,1,3)]),(4,[(1,0,1),(1,2,3)]),(4,[(1,0,1),(3,2,3)]),(4,[(1,0,1),(2,2,3)]),(3,[(1,1,2),(2,0,3)]),(3,[(2,2,3)]),(3,[(0,2,3)]),(4,[(1,2,3),(1,0,1),(1,2,5)]),(57,[]),(58,[]),(4,[(1,0,2),(1,1,2),(1,0,5)]),(8,[(0,0,2)]),(0,[(2,0,3),(1,0,1)]),(0,[(2,0,3),(2,0,1)]),(8,[(1,0,2)]),(0,[(2,1,2),(0,0,3)]),(0,[(2,1,2),(1,0,3)]),(59,[]),(0,[(1,0,2),(1,0,3),(1,2,3)]),(30,[(1,0,2)]),(0,[(1,0,3),(1,2,3),(3,0,2)]),(0,[(1,0,2),(1,2,3),(3,0,3)]),(0,[(1,0,2),(1,0,3),(1,2,5)]),(0,[(1,0,3),(2,1,4)]),(4,[(1,0,1),(3,2,4)]),(0,[(1,0,3),(1,0,1),(3,3,5)]),(8,[(3,0,1)]),(3,[(0,0,1),(1,0,1),(3,2,5)]),(8,[(2,0,1)]),(3,[(0,0,1),(1,0,1),(1,2,5)]),(4,[(0,0,1),(1,0,1)]),(3,[(1,0,3)]),(0,[(0,0,3)]),(0,[(2,2,3)]),(30,[(1,0,1)]),(30,[(2,0,1)]),(14,[(2,0,1)]),(0,[(1,0,1),(0,0,3)]),(0,[(1,0,1),(2,1,3)]),(9,[(0,0,2)]),(0,[(1,0,1),(2,2,3)]),(14,[(1,0,1)]),(0,[(2,1,3)]),(60,[]),(61,[]),(14,[(0,0,2)]),(14,[(3,0,1)]),(14,[(3,1,2)]),(14,[(2,1,2)]),(0,[(0,2,3)]),(0,[(0,2,3),(2,0,3)]),(9,[(0,1,2)]),(0,[(0,2,3),(0,0,3)]),(7,[(1,0,1)]),(9,[(3,0,2)]),(0,[(1,1,3),(0,2,3)]),(0,[(0,1,3)]),(0,[(0,1,2),(1,1,2)]),(0,[(0,1,2),(1,1,2),(2,0,3)]),(0,[(0,1,2),(1,1,2),(0,0,3)]),(0,[(0,1,2),(1,1,2),(1,0,3)]),(7,[(1,1,2)]),(0,[(2,0,3),(0,1,3)]),(0,[(2,0,3),(1,1,2),(3,3,5)]),(62,[]),(0,[(1,2,3),(0,2,3)]),(0,[(0,2,3),(1,2,3)]),(0,[(0,2,3),(1,2,3),(2,0,5)]),(0,[(0,2,3),(1,2,3),(0,0,5)]),(5,[(0,1,2),(1,1,2)]),(63,[]),(0,[(1,1,2),(1,1,3)]),(5,[(1,1,2),(1,0,3)]),(40,[(1,1,2)]),(32,[(1,0,1)]),(40,[(1,0,2)]),(0,[(2,1,2),(2,0,3)]),(0,[(2,1,2),(1,0,1)]),(0,[(2,1,2),(1,0,1),(1,0,3)]),(0,[(2,0,3),(1,0,1),(1,1,2)]),(0,[(1,1,2),(1,0,2)]),(0,[(1,0,2),(1,1,3),(1,2,5)]),(0,[(1,1,3),(1,2,3),(0,0,1)]),(0,[(1,1,3),(1,2,3),(2,0,1)]),(9,[(2,1,2),(1,0,1)]),(9,[(2,1,2),(2,0,2)]),(5,[(0,1,2)]),(0,[(1,0,1),(1,0,2),(1,0,3)]),(9,[(1,0,1),(1,1,2)]),(30,[(2,1,2)]),(0,[(2,0,3),(1,0,1),(2,1,2)]),(11,[(3,0,2)]),(30,[(3,0,2)]),(14,[(3,0,2)]),(11,[(0,0,1),(1,0,1)]),(11,[(2,0,2)]),(11,[(2,1,2)]),(0,[(0,0,1),(1,0,1)]),(11,[(0,1,2)]),(0,[(0,0,1),(1,0,1),(1,3,5)]),(14,[(0,0,1)]),(11,[(3,1,2)]),(30,[(3,1,2)]),(12,[(3,0,1)]),(12,[(2,0,1)]),(7,[(2,0,1)]),(11,[(2,0,1)]),(11,[(3,0,1)]),(11,[(0,0,1)]),(7,[(3,1,2)]),(7,[(2,1,2)]),(0,[(1,1,2),(2,0,3)]),(11,[(0,0,2)]),(7,[(2,0,2)]),(11,[(1,0,2),(1,1,2)]),(9,[(1,0,1),(3,2,3)]),(0,[(2,0,3),(1,0,2),(2,1,3)]),(30,[(2,0,2),(1,0,1)]),(0,[(2,0,3),(1,0,2),(0,1,3)])]
def s7_t : Tabs := (s7_C.map (mkCut true s7_Z),[(5,4),(3,2),(3,1),(5,1),(9,8),(9,1),(17,16),(17,1),(6,4),(6,2),(10,8),(10,2),(18,16),(18,2),(12,8),(12,4),(20,16),(20,4),(24,16),(24,8),(10,16),(18,4),(24,0),(17,0),(19,2),(5,8),(19,8),(22,8),(17,4),(9,2),(20,8),(20,0),(7,4),(18,0),(19,1),(21,1),(25,1),(3,0),(12,0),(21,4),(22,4),(14,16),(7,1),(14,8)],[],[[],[1],[2,1],[3,2,1],[0,1],[0,2,1],[0,3,2,1],[1,0,2,1],[1,0,3,2,1],[2,1,0,3,2,1],[0,1,2,3],[0,1,2,1,3],[0,1,2,3,2,1],[1,2,3],[1,2,1,3],[1,2,3,2,1],[2,3],[2],[3],[3,2],[0,1,0,2],[0,1,2,1,0],[1,0,2],[1,2,1,0],[0],[2,3,2,1],[0,2,3,2,1],[0,2],[2,3,2],[0,1,2,1,0,3],[0,1,2,3,2,1,0],[1,2,1,0,3],[1,2,3,2,1,0],[2,1,0,3],[2,3,2,1,0],[2,1,0],[3,2,1,0],[2,1,0,3,2,1,0],[1,0],[1,0,3],[0,2,1,3,2],[0,1,3,2],[0,1,0,2,1,3],[2,1,3,2],[1,3,2],[1,0,2,1,3],[1,0,2,1,3,2],[0,1,0,2,3,2,1],[0,1,2,1,0,3,2,1],[0,3,2],[0,3],[1,0,2,3,2,1],[0,2,3],[1,2,1,0,3,2,1],[0,1,0,3],[0,1,2,3,2],[0,1,2],[2,1,3],[0,2,1,3],[0,1,3],[0,1,2,1],[1,3],[1,2,1],[1,2],[1,2,3,2],[0,1,0,2,1,3,2],[1,2,1,3,2],[1,3,2,1],[0,1,0,3,2,1],[0,1,3,2,1],[1,0,2,1,0,3,2,1],[1,0,2,1,3,2,1],[1,0,2,1,0]])
theorem s7_W : TabsP true s7_R s7_T s7_t := ⟨cutsGood s7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
noncomputable def s7_D9 : List StD := [
([sw0,sw1,sw2,sw3,sw12],[[0,1,10000,30000,10001,10002],[0,10001,30001,10000,10003,2],[0,10000,30002,10004,10005,3],[0,10000,30003,10006,10007,4],[1,10002,30004,10008,10009,2],[1,10002,30005,10010,10011,3],[1,10002,30006,10012,10013,4],[2,10003,30007,10014,10015,3],[2,10003,30008,10016,10017,4],[3,10005,30009,10018,10019,4]])]
noncomputable def s7_D8 : List StD := [
([sw0,sw1,sw4,sw2,sw3,sw12],[[0,1],[0,1],[0,30010,10003,5],[0,30011,10005,6],[0,30012,10007,7],[0],[1,30013,10009,5],[1,30014,10011,6],[1,30015,10013,7],[5,8,2,30000,10003,30016,10014],[6,8,3,30017,10005,30018,10015],[7,8,4,30019,10007,30000,10017],[5,10003,30000,10014,10015,6],[5,10003,30018,10016,10017,7],[6,10005,30016,10018,10019,7]])]
noncomputable def s7_D7 : List StD := [
([sw0,sw1,sw2,sw3,sw13,sw14],[[9,10,30007],[9,30020,10003,11],[9,30021,10005,12],[9,4],[9,10,13,10007],[10,30022,10009,11],[10,30023,10011,12],[10,9,14,10013],[10,4],[11,10003,30007,10014,10015,12],[11,10009,30000,10003,30024,14,30025],[11,10003,30024,10009,30000,13,30026],[12,10011,30017,10005,30027,14,30003],[12,10005,30027,10011,30017,13,30006],[9,10]]),
([sw0,sw1,sw4,sw2,sw7,sw3,sw12],[[15,16],[16],[15,16,5],[17],[15,30011,10005,18],[15,30012,10007,19],[15],[16,15,5],[20],[16,30014,10011,18],[16,30015,10013,19],[5,8],[5],[18,8,30000,10005],[19,8,30018,10007],[8],[5,30016,10015,18],[5,30028,10017,19],[18,21,6,30000,10005,30018,10018],[19,21,7,30018,10007,30000,10019],[10005,18,10018,10019]]),
([sw0,sw1,sw2,sw7,sw3,sw12],[[15,5,16],[15,5,16],[15,17],[15,30029,10005,10001],[15,30030,10007,10001],[5,15,16],[16,20],[16,30031,10011,10002],[16,30032,10013,10002],[5,8],[5,30033,10015,10003],[5,30034,10017,10003],[30035,3,10018,30000,10005,30018,30009],[30036,4,10019,30018,10007,30000,30037],[30009,10005,10007,10018,10019,30035,30036]]),
([sw15,sw0,sw1,sw2,sw3,sw12],[[22,7,8,23],[22,7],[8,30038,10003,2],[8,30035,10005,3],[7,8,9],[22,7,8,24],[22,30024,10003,10001],[22,30027,10005,10001],[22,7,10006],[8,30000,10009,10002],[8,30017,10011,10002],[7,8,10012],[30000,10003,10005,10014,10015,30039,30033],[7,10017,10019],[7,10019,10017]]),
([sw0,sw1,sw4,sw2,sw3,sw10,sw12],[[25,26],[26],[25,5,30040],[25,6,30041],[25,30042,30010,27,10001],[25,30042,10007,10001],[25],[26,5,30043],[26,6,30044],[26,30045,30013,27,10002],[26,30045,10013,10002],[5,30016,30033,28,10014],[6,30018,30039,28,10015],[27,28,8,30007,30000,30019,30046,29],[30,28,30007,10007,30000,10017],[5,6],[6],[5,30016,10017,10014],[5],[6,30018,10019,10015],[7,27,30000,10017,30007,10007]])]
noncomputable def s7_D6 : List StD := [
([sw0,sw1,sw10,sw16,sw17],[[31,32,10000,30000,10001,10002],[31,10001,30000,10000,30019,29,30042],[31,10001,30018,10000,30017,33,30047],[31,10000,30016,10004,30000,34,30048],[32,10002,30024,10008,30049,29,30045],[32,10002,30050,10008,30027,33,30051],[32,10002,30052,10010,30024,34,30053],[29,33,4,30,34],[29,34,4,30,33],[33,34,3,30,29]]),
([sw0,sw1,sw2,sw5,sw14,sw17],[[35,36,30038],[35,30054,10003,37],[38],[35,30055,30056,39,10004],[35,10004,34,10005],[36,30038,10009,37],[36,30013,30044,40,10020],[34],[36,38,34,10013],[10009,37,10003,30050,30057],[10003,37,10009,30000,30026],[10003,37,41,30000,10014,30009],[39,40,42,43,41,44,13],[35,39],[36,38]]),
([sw0,sw1,sw4,sw2,sw3,sw16,sw17],[[45,46],[46],[45,30058,47],[45,30059,48],[45,30060,10001],[45,30056,10001],[45],[46,30057,47],[46,30061,48],[46,30062,10002],[46,30063,10002],[47,30033,49],[48,30039,49],[50,30035,33],[51,30038,34],[47,30000,48],[52],[47,48,53],[48,47,54],[55],[47,48]]),
([sw0,sw1,sw2,sw3,sw13,sw14,sw18],[[56,30045,57],[56,58,11],[56,59],[58],[56,57,59],[60],[57,30043,11],[57,10011],[57,56,14],[58],[57,61,30064],[11,10015],[11,14],[11,62,63],[14],[10011,59],[10015,10011],[10011,59],[56,57],[11],[57,20]]),
([sw0,sw1,sw2,sw3,sw13,sw19],[[64,30063,30007,65,10008],[11,30017,30005,51,10009],[66,65,10011,30021,67,10005,30018],[68],[30018,65,0,66,67,57,30055,10007],[64,10008,65,11],[64,30023,10011,10008],[64,66,61,10008],[33],[11,30035,10015,10009],[11,66,62,10009],[13],[10011,69,67,30004,10005,30003],[10005,10007,10011,30000,30041],[61,17,67]]),
([sw15,sw0,sw2,sw9,sw3,sw12],[[15,70,24],[2,8,71],[70,72,8],[8,30035,10005,29],[73,8],[70,30000,30017,74,10001],[70,10001,75,10002],[70,30024,10005,10001],[70,76,10006],[24],[77,10005,30017,53,10015,30039],[76,53,10021,75,10019],[10002,10005,30000,53,10015,30024],[74,75,10002,76,53,10012],[10005,76,10019,10017]]),
([sw0,sw1,sw2,sw7,sw3,sw20,sw12],[[78,79,80],[78,80,79],[81],[78,80,18],[82],[78,59],[79,78,80],[83],[80,78,18],[84],[80,85],[86],[79,30019,18],[79,18,30016],[79,10017],[18,79,30018],[79,18],[10019,59],[87],[18,10019],[10017,59]]),
([sw0,sw1,sw4,sw2,sw3,sw21,sw16],[[56,64],[64],[56,30005,88],[56,89],[90],[56,89],[56],[64,30002,88],[64,91],[92],[64,91],[88,30017,51],[51,89],[90],[51,88,89],[88,53],[88,51,53],[93],[48,89,10015],[94,53,95],[88,51]]),
([sw0,sw1,sw4,sw2,sw3,sw22,sw12],[[30000,85,89],[96],[79,97,28],[28,89],[30010],[28,89],[98],[89,85,97],[97,85],[30013],[97,85],[79,85,28],[28,85],[29],[28,85],[89,28,18],[99],[89,53],[100],[18,54],[7,85,30000]]),
([sw23,sw0,sw1,sw4,sw2,sw3,sw12],[[0,19,17],[19,20],[19,17],[19,8],[6,95,21],[51],[30000,77,95],[75],[101,102,103],[21,95],[19,30004,21],[104],[95,77,101],[21,105],[19,30001,21],[101,19,77],[21,95],[19,30000,21],[95,10015],[19,49],[19,49]]),
([sw24,sw0,sw1,sw2,sw3,sw25,sw12],[[106],[107,29,108],[106,109],[29,17],[30010],[28,30056,30030],[98,30063,110],[28,30017,111],[28,30000,112],[30000,28,113],[28,10007],[28,112,98],[28,98,112],[114],[28,115],[98,28,112],[116],[98,53],[117],[112,54],[113,115]]),
([sw0,sw1,sw2,sw7,sw3,sw22,sw12],[[118,79,97],[118,97,79],[96],[118,89],[30010],[118,89],[79,118,97],[98],[97,85],[30013],[97,85],[28],[79,53],[30016],[79,53],[30035,30018,89],[3],[10019,89],[119],[95,10019,120],[30036,89,30000]]),
([sw0,sw1,sw2,sw3,sw22,sw12],[[96,98,10000,18,85,10001,89],[96,28,10001,10000,121,59],[10000,98,18,89,122,10004],[30010,10006],[10000,98,30030,89,10007,30000,10013],[98,28,122,85,118,10003],[18,85,123,96,10005],[30013,10012],[95,96,10007,30032,85,10013,30024],[18,122,124],[30016,122,10016],[122,30034,10017,10003],[30018,18,10018],[18,30036,10019,10005],[4,30036,30000,85,10007]]),
([sw23,sw0,sw1,sw2,sw7,sw3,sw12],[[15,17],[17,95,20],[17,8],[4],[21,95],[125],[126,95],[126,127,103],[75],[21,95],[21,30004,127],[95,126,102],[104],[21,105],[95,30001,21],[101],[95,128],[21,30000,127],[21,95],[21,30000,127],[95,10019,10022]]),
([sw23,sw0,sw1,sw2,sw3,sw12],[[0,44,17,105],[17,44,20,95],[17,44,8,105],[3,44,30035,105,10005,30000,10018],[30018,30000,10007],[75,104,10000,105,95,19,10001],[75,101,10001,10000,127,63],[10000,10018,30004,95,10005,30018],[105,104,10000,44,30000,10006,19],[95,101,10002,126,128,10003,105],[10002,10005,30001,105,10011,30050],[95,75,19,30024,10012],[10003,95,30000,128,10015,30039,10005],[105,75,19,30038,10016],[105,19,10019,30035,10018]]),
([sw26,sw0,sw1,sw2,sw3,sw12,sw27],[[129],[130,10002],[30016],[30018],[30000],[30013],[130,10002],[131,128],[130,41,132],[130,44,128],[130,128,30000],[130,128],[10002,133],[10002,44],[10002,128],[130,128],[130,132,134],[135],[128,130,132],[136],[137]]),
([sw28,sw0,sw1,sw2,sw3,sw12,sw27],[[138],[139],[140,30016,41],[130,30018,141],[138,30000,41],[130,30046],[30000,130,41],[142,143],[130,41,144],[130,145,146],[130,41,30065],[41,147,130],[143,148,144],[41,149,146],[8,147,30046],[130,41,143],[130,143],[150],[144,41],[151],[152]]),
([sw0,sw1,sw4,sw2,sw3,sw12,sw27],[[30000,10001,10002],[139],[10001,30040,54],[10001,30041,53],[10001,30056,54],[10001,30010,0],[138],[10002,30043,54],[10002,30044,53],[10002,30063,54],[10002,30013,8],[54,30016,140],[53,30018,141],[139,30000,54],[8,30000,30046],[48,54],[47,53],[153],[48,54],[154],[155]]),
([sw29,sw0,sw1,sw2,sw3,sw25,sw12],[[156],[98,30013,17],[17,30016,28],[156,30018,98],[98,30056,30030],[157],[98,30063,158],[28,30017,159],[98,30000,160],[98,30000,10006],[98,10006,10023],[98,160,28],[28,98,160],[161],[28,115],[98,28,160],[162],[98,53],[163],[160,54],[4,115,30000]]),
([sw0,sw30,sw1,sw2,sw3,sw12],[[17],[17,19,104,10001],[17,127,101,10000],[10001,104,30010,95,10005,30018,10011],[19,89,10007,104,10024],[17,19,104],[17,19,101],[3,21,30002,95,10005,30018,10018],[19,89,10007,21,10019],[17,10002,126,10003],[17,30001,10011,10002],[17,19,10012],[17,30000,10015,10003],[17,19,10016],[19,10019,10007]]),
([sw15,sw0,sw1,sw31,sw2,sw3,sw12],[[164,165,166],[165,164],[3,30007,8],[167,77],[3,95,167],[168],[169,165,95],[8,30024,77],[167,170],[167,95],[165,66],[8,30000,95],[167,77],[167,171],[165,66],[172],[173],[165,30000,104],[30000,95,77],[165,66],[165,174]]),
([sw15,sw0,sw1,sw2,sw3,sw10,sw12],[[25,175,139],[175,25],[28,30016,20],[28,30018,3],[28,30007,29],[176],[177,175,158],[28,30027,178],[28,30024,178],[28,30024,178],[175,178],[28,30017,178],[28,30000,178],[28,30000,178],[175,178],[30000,54,53],[173],[175,53,10019],[172],[175,54,10017],[175,54,30000]]),
([sw29,sw32,sw0,sw1,sw2,sw3,sw12],[[0,30018,17],[156],[17,30054,117],[17,30059,100],[156,10005,117],[157],[0,30000,75],[117,100],[117,100],[28],[75,179],[117,30001,75],[100,30000,75],[117,10005],[117,180,10023],[117,179,100],[100,148,160],[100,179],[117,148,179],[117,181],[10005,180]]),
([sw33,sw0,sw1,sw2,sw3,sw12,sw17],[[182,183],[183,182],[50,77],[30018],[30000],[30016],[184,77,185],[50,170],[50,41,77],[50,44,77],[50,41,77],[50,77],[50,148,170],[50,44,170],[50,44,170],[77,41],[77,44],[77,41],[30000,44,41],[186],[187]])]
noncomputable def s7_D5 : List StD := [
([sw0,sw1,sw4,sw10,sw16,sw17],[[31,32],[32],[31,30049,10001],[31,30027,10001],[31,30024,10001],[31],[32,30019,10002],[32,30017,10002],[32,30000,10002],[188,30019,29],[189,30017,33],[190,30000,34],[6,191,153],[17,192,7],[6,193,17]]),
([sw0,sw1,sw10,sw34,sw16,sw17],[[31,10002],[31,29],[29],[31,194,195],[31,195,196],[10002,195],[32,10002,10012],[10002,196],[10002,195],[31],[29,197,198],[29,199,200],[30,194,42],[30,199,20],[29]]),
([sw0,sw1,sw10,sw16,sw35],[[31,30024,10002,201],[31,201,202,203,10005],[31,204,205,206,10025],[34],[10002,10005,207,30050,10008,30045],[10002,201,204,30024,10008,30051],[10008,17,10002,30000,30066],[202,203,204,201,191,205],[14,203,202,208,10005,209],[42,206,201,208,203,210]]),
([sw15,sw2,sw5,sw6,sw12],[[96,8,30038,10003],[8,211,212],[8,211,213],[214,8],[215,75,171,10003,30024,30017,10009],[10003,104,10009,30000,30027],[10003,216,10017,10026],[8],[171,215,216,10026,10017],[216,10026,10017]]),
([sw0,sw9,sw6,sw16,sw17],[[217,218,77,30043,10001,30010,10004],[219,220,77,30044,10001,30011,10000],[10001,221,10000,30017,30047],[77,222,10004,30000,30048,10001],[219,217,141,223,224,225,226],[223,217,227,219],[34,217,223,228,207,17,53],[33,219,224,77,229,109],[224,219,227,217],[77,17,230,217]]),
([sw0,sw1,sw36,sw6,sw16,sw17],[[218,30000,231],[232],[218,30041,233],[218,233,234],[218,30060,10000],[231,30043,235],[236],[231,30063,10010],[231,235,237],[130,30019,219],[218,234],[237,233],[234,235],[231,237],[234,233,235]]),
([sw0,sw1,sw36,sw10,sw18,sw17],[[31,170],[33],[31,170],[33],[31,238,89],[130,170],[239,128,240],[241,170,10010],[170,10010],[31,170],[33],[130,238,89],[242,170,148],[170,130],[130,89]]),
([sw0,sw1,sw2,sw5,sw19,sw17],[[243,30022,149],[149,30027,37],[244],[182,30056,10004],[65,10004,67],[243,245,37],[243,30013,181],[246],[243,149,115],[37,30016,179],[247],[37,149,181],[42,149,148],[65,149,67],[67,181]]),
([sw15,sw0,sw2,sw6,sw10,sw12],[[248,26],[98,30067,28],[28,248,213],[28,148,29],[249],[28,30000,171],[28,171,95],[28,30024,178],[28,178,171],[95,28,53],[250],[251,53,10027],[28,171],[95,178],[171,53,30000]]),
([sw0,sw1,sw2,sw5,sw14,sw27],[[149,30038,41],[149,30006,37],[252],[130,30004,253],[9,41,67],[41,30002,37],[217,30061,254],[246],[67,149,115],[37,41,254],[37,149,253],[255],[256,149,41],[9,149,67],[67,41,115]]),
([sw15,sw2,sw36,sw3,sw6,sw12],[[257,258,8],[8,258,259],[8,260,242],[8,260,261],[214],[8],[171,30000,170],[104,30017,10003],[170,10028,10019],[262,30024,10029],[104,171,170],[171,178],[8],[171,10019,10017],[170,10019,178]]),
([sw0,sw1,sw2,sw3,sw13,sw37],[[148,30007,145],[148,30005,178],[178,30004,53],[171],[0,145,67],[145,263,178],[145,148,178],[53,178,115],[10002],[263,148],[217,145,53],[10003],[263,148],[10005],[0,148,67]]),
([sw23,sw0,sw1,sw36,sw3,sw16],[[264,17],[17,20],[20,17],[265,95,149],[17,65,104],[149,95],[75],[149,95],[104,127,170],[104,95],[170,10011,53],[95,149],[104,95],[104,149,127],[95,149]]),
([sw0,sw1,sw2,sw5,sw13,sw38],[[148,30038,266],[148,267],[268],[269],[0,267],[266,115],[266,148,115],[266,115],[270],[40,148],[271,267],[20,148,10003],[268,148],[0,267],[0,148,267]]),
([sw29,sw1,sw2,sw5,sw25,sw12],[[98,30068,96],[96,30069,148],[156],[98,95],[157],[98,118],[118],[118],[118],[98,148,118],[118],[98,118],[98,95],[118],[95,148,118]]),
([sw24,sw1,sw2,sw5,sw25,sw12],[[98,29,272],[29,109],[273],[95],[98,30056,253],[98,118],[118],[118],[118],[98,253,118],[118],[98,118],[98,118],[118],[118]]),
([sw23,sw0,sw1,sw7,sw3,sw16],[[274,17],[17,20],[4],[181,95,21],[17,181],[181,95],[75],[21,95],[21,127,171],[104],[181,171,21],[95,181],[21,95],[21,127],[95,53]]),
([sw0,sw1,sw2,sw3,sw21,sw27],[[149,275,145],[149,30005,178],[149,30004,178],[139],[9,145,67],[145,30002,178],[145,30001,178],[138],[67,149,115],[66,275,54],[130,149,53],[276],[141,149,54],[277],[29,67,54]]),
([sw15,sw0,sw2,sw3,sw25,sw12],[[278,17,156],[17,181],[278,171,53],[22,181,95],[115],[171,30017,54],[53,30000,178],[22,171,95],[171,178],[171,53],[262],[77,53,10019],[75],[171,54,10017],[95,53,178]]),
([sw23,sw0,sw1,sw3,sw10,sw12],[[25,17],[17,20],[3,54],[279,54,280],[53],[254,281,170],[178,30024,282],[254,170],[281,178],[254,30000,283],[178,282],[281,254],[75],[281,10030,30035],[281,254]]),
([sw0,sw30,sw1,sw3,sw10,sw12],[[17],[17,281,77],[77,30006,282],[149,170],[281,234,10024],[17,281,20],[3,282,54],[149,77],[281,234,10019],[17,30000,170],[17,77],[17,254,281],[17],[281,10019,234],[281,149]]),
([sw15,sw2,sw36,sw9,sw3,sw12],[[17,284,181],[75,285],[17,284,181],[181,95,53],[73],[286],[287],[75,53],[75,53],[75,95,286],[104,95],[104,53],[75,53],[75,53],[95,174]]),
([sw29,sw32,sw1,sw36,sw3,sw12],[[0,170],[17,30059,117],[285],[117,10005],[288],[170,117],[117,170],[98],[170,181,75],[117,181],[10005,148,181],[75,179],[117,10005],[117,181],[10005,148,181]]),
([sw15,sw39,sw1,sw2,sw3,sw12],[[20,77,178],[178,20,289],[20,170,54],[242,253],[290],[75,77],[77,170,54],[177],[77,178],[178,30000,54],[178,10029,21],[170,178],[170,54],[170,10028,21],[10011,54,291]]),
([sw0,sw1,sw2,sw20,sw21,sw17],[[292,170],[292,170],[293],[253],[292,95],[95,77,54],[294],[295],[170,296,67],[174,170,10016],[235,170,10014],[170,54],[7,54,293],[7,95,174],[6,95,54]]),
([sw23,sw0,sw1,sw2,sw3,sw21],[[9,19,288],[19,297],[19,298],[174,95],[19,288],[149,19,95],[174,170,149],[149,95],[283],[174,299,234],[170,115,67],[282],[174,10015],[75,19,10031],[10015,174]]),
([sw28,sw4,sw2,sw3,sw22,sw12],[[10032],[95,30070,54],[96,30071,170],[30046],[95,30046,54],[54,170],[53,95],[300],[54,67],[95,54,170],[301],[96,53],[302],[95,54,303],[304,54,30000]]),
([sw23,sw0,sw1,sw2,sw3,sw13],[[0,288],[288,170,20],[288,170,54],[305,95,174],[0,288],[104,170],[174,170,149],[104,95],[77],[95,126],[170,126],[126],[170,126],[104,170,126],[126]]),
([sw40,sw0,sw1,sw4,sw2,sw3],[[0,77,67],[67,170,115],[22,67,306],[67,77,53],[307,95,54],[30000,77,170],[253],[115,170],[77,67,115],[149],[95,77,54],[67,115],[54,77],[53,67],[77,53,67]]),
([sw23,sw28,sw4,sw2,sw3,sw12],[[0,170,30007],[22,20,306],[20,170,149],[149,95],[65],[10032],[149,30038,95],[170,30038,149],[170,30038,104],[104,170,282],[254,95,21],[282,149],[170,282,95],[170,149],[95,149]]),
([sw23,sw0,sw1,sw2,sw3,sw12],[[0,77,17],[17,20],[17,77,149],[149,95],[65],[149,77,95],[149,170],[77,95,149],[77,174],[95,77,282],[170,171,75],[95,149],[77,282,95],[77,149],[95,149]]),
([sw0,sw1,sw2,sw7,sw3,sw41],[[181,18],[18],[18],[18],[181,18],[18],[18],[181,18],[18],[18],[18],[18],[18],[18],[181,18]]),
([sw42,sw1,sw2,sw3,sw25,sw12],[[98,77,17],[17,308,309],[98,96,77],[98,77,113],[98,157,77],[98,77,282],[181,98,53],[114],[113,115],[98,282],[310],[98,181],[117],[113,54],[113,181]]),
([sw24,sw1,sw2,sw3,sw22,sw12],[[98,77,96],[96,308],[98,96,77],[30030],[98,30010,77],[98,77,282],[181,98,53],[114],[282,115,53],[98,282],[310],[98,181],[117],[282,54,181],[14,181,10023]]),
([sw23,sw0,sw1,sw2,sw3,sw43],[[65,288],[288,65],[65,181],[181,282,149],[65],[181,77,170],[149,170],[282,95],[10023],[95,181],[181,115,53],[10033],[77,282,95],[10031],[30000,282,10022]]),
([sw44,sw1,sw2,sw3,sw25,sw12],[[98,77,17],[17,283],[98,253,77],[98,77,300],[98,113,77],[98,77,253],[283,98,181],[114],[282,115,53],[98,283],[310],[98,181],[117],[283,54,181],[14,181,30056]]),
([sw40,sw0,sw1,sw2,sw7,sw3],[[15,77,113],[70,115,311],[312,77,53],[104,115,313],[314,282,21],[282,77,170],[115,170],[180],[77,95,115],[95,77,282],[235],[53,115],[54],[77,53,95],[10022,115]]),
([sw29,sw1,sw2,sw3,sw22,sw12],[[282,77,170],[115,170],[282,95],[30030],[67],[95,282],[170,115,53],[114],[282,115,53],[77,282,95],[310],[77,53,98],[117],[282,54,315],[14,115,174]]),
([sw44,sw1,sw2,sw3,sw12,sw37],[[282,77,217],[217,283],[282,253,77],[77,174],[30010],[253,282,77],[283,115],[282,174],[30046],[77,282,253],[77,53,235],[30040],[282,174],[30041],[30056]]),
([sw0,sw1,sw2,sw3,sw12,sw45],[[282,77,253],[115,283,174],[282,253,77],[77,174],[30010],[253,282,77],[283,115],[282,115,174],[30013],[77,282,253],[77,53,235],[30016],[282,174],[30018],[30000]]),
([sw40,sw0,sw1,sw2,sw3,sw12],[[0,77,174],[174,282],[316,77,149],[174,282],[53],[282,77,283],[174,283],[77,253],[77,174],[174,77,282],[283,171],[282,174],[77,282,174],[77,149],[282,174]]),
([sw40,sw0,sw1,sw2,sw3,sw22],[[53,77,113],[53,282,115],[235,53],[315,282,235],[14],[282,77,253],[115,283,171],[53,253,77],[10023],[235,77,282],[53,115],[10033],[77,53,253],[10031],[10022]]),
([sw40,sw0,sw1,sw2,sw3],[[0,174,67,77,10001,113],[67,174,22,115,282,10002,317],[67,149,316,53,77,10003,318],[113,174,307,235,282,10005,21],[253,282,10000,77,10002,10001],[174,115,10001,10000,10003],[77,115,10001,253,67,10005,10004],[174,10003,282,77,10009],[10002,67,235,115,10011,10005],[77,174,10003,253,282,10015,10005]]),
([sw0,sw46,sw1,sw2,sw3,sw12],[[174],[282,77,253],[149,283,171],[282,253,77],[77,67,10024],[149,282],[149,77],[149,282],[0,67,30000],[253,282,77],[283,171],[282,149],[77,282,253],[77,149],[282,149]]),
([sw47,sw0,sw1,sw2,sw3,sw12],[[0,77,253],[149,20,319],[253,77],[282],[181],[253,77],[149,170],[77,253],[77,174],[253,77],[170,235],[170,149],[77,253],[77,149],[30000,149,235]]),
([sw0,sw1,sw2,sw3,sw22,sw12],[[253,77],[315,283,171],[77,253],[113],[253,67,315],[253,77],[315,171,283],[320],[67,115],[77,253],[310],[253,181,67],[117],[315,235],[14,67,30000]]),
([sw29,sw11,sw1,sw2,sw3,sw12],[[0,77,253],[253,77],[315,170],[77,253],[234],[315,320],[253,77],[283],[235,181],[253,77],[315,235],[170,179,21],[77,253],[77,181,235],[315,235]]),
([sw29,sw48,sw0,sw1,sw2,sw3],[[0,30000,67],[283],[235,10034,113],[113,10035,115],[113,10036,115],[0,10024,174],[174,115,306],[235,181],[174,235,181],[235,30063,180],[115,30017,174],[115,30000,178],[235,115,181],[181,235],[174,282]]),
([sw0,sw1,sw2,sw3,sw49,sw27],[[235,240],[256,283,174],[282,253,178],[235,174,283],[256,240],[235,282],[240,235],[282,240],[8,235,10002],[256,283,174],[235,256,253],[321],[256,235],[136],[256,240]]),
([sw26,sw50,sw1,sw2,sw3,sw12],[[30010],[235,10002],[170],[95],[240],[10002,235],[0,256,321],[0,282,253],[0,235,322],[235,282],[10002,235],[10002,178],[256,282,253],[235,256,253],[256,235]]),
([sw0,sw1,sw2,sw3,sw51,sw27],[[235,30046,253],[256,283,178],[178,253],[235,178,253],[256,253,30065],[235,282],[256,235],[282,178],[8,235,30046],[256,253],[235,256,253],[321],[256,235],[136],[256,322]]),
([sw0,sw1,sw2,sw3,sw52,sw12],[[315,170],[315,170],[282,67],[113],[315,67],[240,315,282],[315,115,67],[320],[170,115,67],[315,282,67],[310],[170,181,67],[315,282,117],[315,30000,282],[14,67,104]]),
([sw53,sw0,sw1,sw2,sw3,sw12],[[0,283,113],[42,315,320],[42,315,310],[42,283,117],[14,65,104],[283,170,315],[315,283,170],[282,95],[283,240,315],[95,315,282],[283,171],[170,179,21],[315,283,95],[170,181,240],[283,10019,315]]),
([sw28,sw4,sw2,sw3,sw12,sw27],[[10037],[256,30070,27],[27,30071,130],[256,30046,275],[256,30046,10002],[130,282],[256,253],[282,180],[8,282,30046],[256,282,130],[130,256,253],[321],[256,130,282],[136],[137]]),
([sw23,sw0,sw1,sw2,sw54,sw3],[[323,240],[324,325,326],[240,170,181],[30035],[240,282,30000],[181,240],[178,170,327],[178,30004,104],[282,95],[240,181],[240,30001,101],[240,171,283],[170,30000,104],[170,282,95],[180]]),
([sw0,sw1,sw2,sw3,sw55,sw19],[[65,30046,180],[180,30040,327],[65,10004,178],[65,180,10004],[65,180,10004],[65,327,282],[180,115],[327,65,178],[328],[65,282],[65,62],[62],[327,180],[62],[65,62]]),
([sw0,sw1,sw2,sw56,sw3,sw12],[[282,170],[115,170],[180],[282,95],[115,240],[95,282],[320],[170,115,283],[282,115,67],[310],[170,282,95],[170,181,240],[320,282,117],[313,115,30000],[282,10018]]),
([sw57,sw0,sw1,sw2,sw3,sw12],[[0,283,180],[22,282,178],[316,253,234],[307,283,180],[0,181,113],[283,171],[113,283],[282,253,113],[283,10007,10023],[253,282,77],[283,171],[282,149],[171,283],[253,149],[283,149]]),
([sw0,sw1,sw2,sw3,sw58,sw16],[[180,240,149],[180,30040,149],[149,195,178],[195,180],[195,180],[240,30043,51],[180,195,240],[195,240],[195,149],[180,53],[20,149,53],[170],[329,180,10015],[240,180,10036],[51,240]]),
([sw29,sw59,sw1,sw2,sw3,sw12],[[253],[117,170],[100,170],[117,95],[240],[117,170],[117,170,100],[117,95],[14,180],[117,119],[170,119],[170,119],[117,119],[117,119],[95,180]]),
([sw0,sw1,sw60,sw2,sw3,sw12],[[282,170],[180],[171,170,283],[282,95],[171,240,115],[149],[95,282],[170,171,283],[282,115,67],[20,170,310],[310,282,117],[306,240,30000],[170,282,171],[170,49],[282,49]]),
([sw61,sw0,sw1,sw2,sw3,sw12],[[0,77,180],[149,170],[149,77],[0,282,180],[240],[180,77],[180,170,149],[77,95,149],[77,180],[95,77,49],[180,235,170],[170,149],[77,54],[77,149],[95,180]]),
([sw62,sw0,sw1,sw2,sw3,sw12],[[0,283,180],[149,282],[149,42,330],[180,283],[0,256,322],[283,30000,149],[180,283],[149,253,113],[283,180],[253,282,137],[283,195,322],[282,149],[180,283],[253,149],[283,180]]),
([sw15,sw0,sw2,sw63,sw3,sw12],[[180,77],[20,77,167],[167,20,313],[180,95],[65],[180,170,167],[180,77],[77,95,167],[77,180],[167,77],[180,30000,77],[77,254],[180,167,170],[95,254],[95,180]]),
([sw15,sw0,sw1,sw2,sw3,sw64],[[180,77],[104,313],[104,77,149],[180,95],[104,65],[180,77],[180,170,149],[77,95,104],[77,180],[104,77,49],[180,171],[95,149],[180,30000,77],[77,149],[95,180]]),
([sw15,sw0,sw1,sw31,sw10,sw12],[[331,77,180],[332,333],[20,30007,28],[180,77],[334],[180,77],[77,30024,332],[332,170],[77,180],[28,30000,170],[180,77],[170,178],[10038],[104,30000,335],[77,180]]),
([sw15,sw65,sw0,sw1,sw2,sw3],[[8,30000,240],[137,240],[178,137,282],[240,10035,149],[240,10036,149],[8,10039,178],[8,10040,240],[149,215,336],[149,104,215],[149,240],[178,30027,149],[178,30024,149],[240,30017,49],[240,30000,49],[180,337,254]]),
([sw66,sw0,sw1,sw2,sw3,sw12],[[0,77,180],[22,20,306],[20,77,8],[180,282,49],[0,51,101],[282,77,170],[49,170],[77,338],[77,240,101],[49,77],[49,171],[282,149],[77,282,171],[77,49],[282,49]]),
([sw15,sw0,sw67,sw2,sw3,sw12],[[180,171],[22,20,313],[20,77,100],[180,171],[65],[180,171],[180,30024,100],[77,95,100],[171,180],[100,77],[180,171],[95,149],[180,54,77],[77,10021,104],[171,180]]),
([sw0,sw1,sw2,sw3,sw58,sw17],[[180,77],[180,170,50],[77,253],[50,180,253],[77,180],[50,77],[180,195,170],[50,170,195],[170,195],[180,253,77],[253,77],[77,253],[339,180,54],[186],[50,307]]),
([sw33,sw0,sw1,sw2,sw54,sw17],[[340,77,180],[341,342],[343,77],[30009],[171],[180,77],[180,170,341],[77,30024,341],[77,180],[343,77],[180,30000,170],[343,149,170],[77,30000,180],[77,149],[10022]])]
noncomputable def s7_D4 : List StD := [
([sw0,sw4,sw10,sw16,sw38],[[180],[188,30018,344],[189,30000,171],[345,344,95],[188,171],[189,344],[345,95],[344,346,171],[95,171,282],[95,344,282]]),
([sw0,sw1,sw10,sw16,sw68],[[180,171],[188,95],[171,180],[10000],[180,171],[95,347],[10008],[171,180],[20,180,282],[20,282]]),
([sw0,sw1,sw10,sw18,sw38],[[347,30000,180],[347,283,178],[171],[345,180,240],[180,235,178],[189,347,348],[170],[40,347,235],[240,347,283],[20,283]]),
([sw15,sw2,sw5,sw25,sw12],[[28,282,98],[28,171],[28,282,170],[240],[171,28,282],[116],[77,53,10026],[28,170],[282,10026,180],[170,53,149]]),
([sw23,sw0,sw6,sw10,sw12],[[248,171,178],[178,170],[349,171],[240],[347,171,170],[178,170,349],[171,178],[178,171,101],[170,178],[171,349]]),
([sw0,sw30,sw6,sw10,sw12],[[178],[347,170],[349,170],[171,240,10024],[347,170],[349,170],[248,240,10027],[240,171,101],[170,347],[170,349]]),
([sw15,sw39,sw9,sw3,sw12],[[8,171],[350,351,170],[100,253,315],[352],[350,8,170],[353],[171,178],[170,253],[170,178],[10011,54,291]]),
([sw0,sw9,sw6,sw16,sw35],[[218,30011,180],[220,95],[221,180,195],[77],[180,195,178],[195,349],[17,195,171],[95,180],[17,180,171],[17,54,315]]),
([sw15,sw36,sw6,sw10,sw12],[[178,171],[178,354,170],[8,171],[249],[104,171,170],[178,170,8],[171,178],[178,171,8],[170,178],[171,54,30000]]),
([sw4,sw36,sw6,sw16,sw17],[[195,171,180],[45,195,236],[195,170,50],[51,195,171],[130,171,170],[171,170,50],[98,355,77],[95,54,149],[170,171,51],[171,355,170]]),
([sw0,sw1,sw69,sw16,sw17],[[256,171,253],[256,253,171],[256,283,171],[256,253,67],[356,95,357,10041],[253,282,10042],[283,171],[256,253],[171,256,283],[256,171]]),
([sw15,sw65,sw0,sw2,sw6],[[8,171],[358,171,253],[358,10035,54],[359,358,95],[8,10026,178],[171,215],[359,171,360],[171,30000,54],[359,171,95],[359,54,282]]),
([sw0,sw9,sw6,sw14,sw27],[[54,171,180],[282,171,219],[54,171,253],[361,180,10001],[180,54,282],[253,219,362],[219,171],[282,54,180],[219,171],[219,171]]),
([sw0,sw1,sw70,sw18,sw17],[[282,170],[45,170],[171],[282,180,67],[180,282,178],[54,282,10043],[170,178],[42,170,54],[170,282,180],[42,282,54]]),
([sw0,sw1,sw7,sw10,sw41],[[282,170],[180],[315,170],[282,67],[320],[308,282,77],[170,65,67],[315,310],[54,282],[170,282,67]]),
([sw29,sw48,sw1,sw2,sw5],[[0,67],[282,10034,363],[54,10035,195],[77],[67,282,178],[67,262],[178,67,282],[54,282,195],[180,195,171],[178,282]]),
([sw15,sw71,sw9,sw3,sw12],[[262,308,171],[350,351,313],[308,171,180],[352],[262,171],[262,353,364],[171,180],[180,171],[170,178],[171,180]]),
([sw0,sw1,sw72,sw17,sw73],[[180,170,282],[191,170],[282,180,95],[365],[180,282,95],[170,178],[109,170,30013],[170,180],[321],[322]]),
([sw74,sw0,sw1,sw2,sw17],[[182,293,366],[293,40,367],[180,170,30016],[293,180],[293,170,40],[40,170],[40,293,95],[293,77],[293,40,170],[170,54]]),
([sw0,sw1,sw72,sw17,sw68],[[40,170],[40,170],[40,180,95],[366],[180,77],[170,40,293],[367],[170,180],[29,170,30016],[215]]),
([sw40,sw28,sw4,sw2,sw3],[[0,95,30007],[22,368,306],[368,77,149],[368,95,149],[10032],[95,30072,149],[77,30007,149],[180,77,54],[53,95],[95,54,77]]),
([sw75,sw0,sw1,sw10,sw12],[[25,29],[54,95,347],[29,25],[203],[347,95],[347,95],[322,180,195],[180,195,369],[95,347],[95,347]]),
([sw23,sw76,sw9,sw3,sw12],[[369,77,180],[370,371,372],[369,95,180],[373],[180,77],[77,95,104],[77,180],[180,282],[95,178],[95,180]]),
([sw23,sw0,sw9,sw77,sw12],[[369,77,180],[370,95,374],[369,77,180],[65],[180,77],[126,95],[77,180],[180,77],[95,178],[77,180]]),
([sw23,sw0,sw9,sw3,sw78],[[369,77,178],[178,95],[369,95,180],[369,77,104],[180,77],[77,95,104],[104,178,171],[178,171,180],[95,77,178],[77,180,95]]),
([sw79,sw0,sw1,sw2,sw3],[[0,77,67],[67,69,375],[67,77,376],[69,180,54],[282,77,253],[54,283,171],[77,253],[54,77],[283,171],[77,54]]),
([sw0,sw1,sw2,sw80,sw43],[[282,95],[171,283],[282,95],[377],[95,282],[283,171],[378],[95,282],[379],[34,282,54]]),
([sw23,sw0,sw1,sw2,sw81],[[180,171],[370,95,178],[370,77,149],[180,171],[180,171],[180,283],[178,95,149],[95,77,282],[180,171],[180,283]]),
([sw0,sw82,sw1,sw2,sw3],[[0,171,180],[282,171,283],[171,283],[282,253,77],[22,282,149],[149,253],[149,171],[253,282,77],[283,171],[171,282]]),
([sw40,sw0,sw1,sw2,sw3],[[0,171,180],[22,95,149],[149,77],[180,171],[180,171],[171,283],[149,95],[95,77,282],[180,171],[171,283]]),
([sw47,sw0,sw1,sw2,sw54],[[323,95],[283,171],[95,283],[10036],[283,95,171],[171,283],[283,30004,149],[95,282],[95,30001,180],[180,30000,77]]),
([sw0,sw1,sw7,sw72,sw17],[[282,171,283],[180],[171,283],[282,95],[380],[95,282],[283,171],[380,77,54],[34,282,30000],[171,282]]),
([sw23,sw0,sw1,sw3,sw72],[[369,171,178],[178,95],[369,171,30000],[369,77,54],[283,171],[178,95,282],[171,283],[178,171,283],[178,77,282],[171,283]]),
([sw0,sw1,sw2,sw52,sw17],[[282,171,283],[171,283],[381],[282,95],[95,282],[380],[283,171],[379],[171,282],[34,282,54]]),
([sw62,sw4,sw2,sw3,sw12],[[382,171,283],[171,335,383],[171,283,384],[171,54,137],[382,283],[382,253],[283,180],[137,283],[335,149],[283,180]]),
([sw15,sw0,sw63,sw10,sw12],[[369,171,283],[385,20,372],[369,171,180],[65],[385,171,180],[104,95],[171,180],[180,171],[95,347],[171,180]]),
([sw15,sw0,sw1,sw10,sw64],[[20,171,283],[104,313],[29,171,149],[20,65,104],[104,171,180],[104,95],[171,180],[180,171],[95,347],[171,149]]),
([sw83,sw4,sw2,sw3,sw12],[[0,98,114],[98,54,109],[114,109],[95,54,67],[114,77,54],[382,95,53],[54,67],[114,54,77],[114,53],[95,54,368]]),
([sw33,sw0,sw2,sw84,sw17],[[369,77,180],[369,77,349],[180,14,372],[271],[180,170,349],[349,77,170],[77,180],[180,77,262],[77,349],[170,180]]),
([sw33,sw0,sw1,sw72,sw17],[[369,109,386],[109,14],[369,77,149],[271],[387,77,262],[149,170],[77,180],[262,77],[262,347,170],[77,149]])]
noncomputable def s7_D3 : List StD := [
([sw4,sw10,sw18,sw38],[[388,170,283],[109,283,77],[345,170],[109,170,271],[20,283],[109,170,77]]),
([sw15,sw65,sw36,sw6],[[29,389,283],[358,283],[359,358,372],[390,391,392],[359,283],[359,283]]),
([sw40,sw0,sw63,sw10],[[20,283,180],[104,283,347],[180,77],[180,77],[178,283],[180,283,77]]),
([sw85,sw0,sw1,sw10],[[25,77,180],[104,170,347],[180,77],[180,77],[347,170],[180,77]]),
([sw47,sw0,sw1,sw72],[[325,77,180],[347,325,372],[325,77,180],[180,77],[347,170],[180,77]])]
def s7_D2 : List StD := []
theorem s7_I2 : LevelN true s7_T 2 s7_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C3x0 : levelOK true s7_T s7_t 2 (s7_D2.map Prod.fst) ((s7_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I3 : LevelN true s7_T 3 s7_D3 := levelStep s7_B s7_W s7_I2 (chunks 16 s7_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C4x0 : levelOK true s7_T s7_t 3 (s7_D3.map Prod.fst) ((s7_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C4x1 : levelOK true s7_T s7_t 3 (s7_D3.map Prod.fst) ((s7_D4.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C4x2 : levelOK true s7_T s7_t 3 (s7_D3.map Prod.fst) ((s7_D4.drop (2*16)).take 16) = true := by decide +kernel
theorem s7_I4 : LevelN true s7_T 4 s7_D4 := levelStep s7_B s7_W s7_I3 (chunks 16 s7_D4 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C4x0
  · exact s7_C4x1
  · exact s7_C4x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x0 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x1 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x2 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (2*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x3 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (3*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C5x4 : levelOK true s7_T s7_t 4 (s7_D4.map Prod.fst) ((s7_D5.drop (4*16)).take 16) = true := by decide +kernel
theorem s7_I5 : LevelN true s7_T 5 s7_D5 := levelStep s7_B s7_W s7_I4 (chunks 16 s7_D5 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C5x0
  · exact s7_C5x1
  · exact s7_C5x2
  · exact s7_C5x3
  · exact s7_C5x4
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C6x0 : levelOK true s7_T s7_t 5 (s7_D5.map Prod.fst) ((s7_D6.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C6x1 : levelOK true s7_T s7_t 5 (s7_D5.map Prod.fst) ((s7_D6.drop (1*16)).take 16) = true := by decide +kernel
theorem s7_I6 : LevelN true s7_T 6 s7_D6 := levelStep s7_B s7_W s7_I5 (chunks 16 s7_D6 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C6x0
  · exact s7_C6x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C7x0 : levelOK true s7_T s7_t 6 (s7_D6.map Prod.fst) ((s7_D7.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I7 : LevelN true s7_T 7 s7_D7 := levelStep s7_B s7_W s7_I6 (chunks 16 s7_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C8x0 : levelOK true s7_T s7_t 7 (s7_D7.map Prod.fst) ((s7_D8.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I8 : LevelN true s7_T 8 s7_D8 := levelStep s7_B s7_W s7_I7 (chunks 16 s7_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C8x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s7_C9x0 : levelOK true s7_T s7_t 8 (s7_D8.map Prod.fst) ((s7_D9.drop (0*16)).take 16) = true := by decide +kernel
theorem s7_I9 : LevelN true s7_T 9 s7_D9 := levelStep s7_B s7_W s7_I8 (chunks 16 s7_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact s7_C9x0
  ))
theorem s7_L : LowN true s7_R s7_T 10 := lowSearch s7_B s7_I9 (by decide +kernel)
end RescueK5

open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 128
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
lemma bin_comm_flip (d : Nat) (hd : d < 4) (a b : Nat) : bin d a b = bin (flipOp d) b a := by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
lemma flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  interval_cases d <;> decide
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^128) (hb : b < 2^128) : bin d a b < 2^128 := by
  have h1 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x &&& y) < 2^128 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ||| y) < 2^128 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ^^^ y) < 2^128 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
lemma bin_bit0 (d a b : Nat) (ha : a.testBit 0 = false) (hb : b.testBit 0 = false) :
    (bin d a b).testBit 0 = false := by
  rw [testBit_bin]
  rcases d with _ | _ | _ | d <;> simp [ha, hb]
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_size {T k S} (h : Live T k S) : S.card ≤ k + 1 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; simp
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, hf, tail⟩ := h
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have ht := ih tail
    rw [Finset.card_insert_of_notMem hu] at ht
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def swZero : SWire := (false, 0)
def swFlip (a : SWire) : SWire := (!a.1, a.2)
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def swMeet (a b : SWire) : SWire := (a.1 && b.1, bin (opIdx a.1 b.1) a.2 b.2)
def swJoin (a b : SWire) : SWire := swFlip (swMeet (swFlip a) (swFlip b))
def swRead (j : Nat) (a : SWire) : Bool := a.1 != a.2.testBit j
lemma swRead_zero (j : Nat) : swRead j swZero = false := by simp [swRead, swZero]
lemma swRead_flip (j : Nat) (a : SWire) : swRead j (swFlip a) = !(swRead j a) := by
  cases a with | mk s v => cases s <;> cases h : v.testBit j <;> simp [swRead, swFlip, h]
lemma swRead_meet (j : Nat) (a b : SWire) : swRead j (swMeet a b) = (swRead j a && swRead j b) := by
  obtain ⟨s, u⟩ := a; obtain ⟨t, v⟩ := b
  cases s <;> cases t <;> cases hu : u.testBit j <;> cases hv : v.testBit j <;>
    simp [swRead, swMeet, opIdx, testBit_bin, hu, hv]
lemma swRead_join (j : Nat) (a b : SWire) : swRead j (swJoin a b) = (swRead j a || swRead j b) := by
  simp only [swJoin, swRead_flip, swRead_meet]
  cases swRead j a <;> cases swRead j b <;> rfl
def swGate (w : List SWire) (g : Gate) : SWire :=
  let arg := fun i => w.getD i swZero
  match g.op, g.inputs with
  | .not, xs => swFlip (arg (xs.headD w.length))
  | .and, [] => swFlip swZero
  | .or, [] => swZero
  | .and, [i] | .or, [i] => arg i
  | .and, i :: j :: _ => swMeet (arg i) (arg j)
  | .or, i :: j :: _ => swJoin (arg i) (arg j)
  | _, _ => swZero
def swExec (gs : List Gate) (w : List SWire) : List SWire :=
  gs.foldl (fun w g => w ++ [swGate w g]) w
def isBin (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma get_simple (w : List SWire) (i : Nat) : simple w (w.getD i swZero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
lemma swGate_priced (w : List SWire) (g : Gate) : priced w (isBin g) (swGate w g).2 := by
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | not => exact Or.inl (get_simple w _)
  | _ => exact Or.inl (Or.inl rfl)
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^128 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^128 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^128 ∧ (w.getD i swZero).2.testBit 0 = false := by
    simp only [List.getD_eq_getElem?_getD]
    cases eq : w[i]? with
    | none => exact hz
    | some a => exact hw a (List.mem_of_getElem? eq)
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | not => exact hg (xs.headD w.length)
  | _ => exact hz
lemma swExec_lt (gs : List Gate) (w : List SWire)
    (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hw u hu
    · rw [List.mem_singleton.mp hu]; exact swGate_lt w hw g
lemma swRead_get (j : Nat) (w : List SWire) (i : Nat) :
    (w.map (swRead j)).getD i false = swRead j (w.getD i swZero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [swRead_zero]
lemma swGate_read (w : List SWire) (g : Gate)
    (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (j : Nat) :
    swRead j (swGate w g) = g.op.eval (g.inputs.map fun i => (w.map (swRead j)).getD i false) := by
  simp_rw [swRead_get]
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := legal
  rcases hop with rfl | rfl | rfl <;>
    rcases xs with _ | ⟨i, _ | ⟨k, _ | ⟨h, rest⟩⟩⟩ <;>
    simp_all [swGate, GateOp.eval, swRead_flip, swRead_meet, swRead_join, swRead_zero]
lemma swExec_read (j : Nat) (gs : List Gate) (w : List SWire)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (swExec gs w).map (swRead j) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (swRead j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (swExec gs (w ++ [swGate w g])).map (swRead j) = _
    rw [ih _ (fun v hv => legal v (List.mem_cons_of_mem _ hv))]
    simp [swGate_read w g (legal g List.mem_cons_self) j]
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
lemma extract_live {T} (hT : T ≠ 0) (gs : List Gate) (w : List SWire)
    (found : T ∈ reps (swExec gs w)) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {T}, by simp, ⟨rfl, hT⟩, by simpa [swExec] using found⟩
  | cons g gs ih =>
    obtain ⟨k, S, lim, h, sub⟩ := ih (w ++ [swGate w g]) found
    have sub' : ∀ a ∈ S, a ∈ reps w ++ [(swGate w g).2] := by simpa [reps] using sub
    obtain ⟨l, V, cost, hl, raw⟩ := pull_live h (swGate_priced w g) sub'
    refine ⟨l, V, ?_, hl, raw⟩
    rw [List.countP_cons]
    cases e : isBin g <;> simp [e] at cost ⊢ <;> omega
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 128 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 128 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^128) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Impossible (T : Nat) (cap : Nat) (S : Finset Nat) : Prop :=
  ∀ k ≤ cap, ¬Live T k S
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma lower_of_impossible {roots : List Nat} {T L : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (ess : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hnz : normPack (obs T) ≠ 0 := by rwa [hnormT]
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left hnz
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha'
    exact normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have heq : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    exact ⟨fun ha' => raw_required run roots a sub (ess a ha'), sub a⟩
  by_contra! small
  exact noRun k (by omega) (heq.symm ▸ run)
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def Slice (raw : List Nat) (T d : Nat) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Nat),
    (∀ r : Row, d.testBit (f r).val = true) ∧
    (∀ a ∈ raw, Avail (roots.map obs) (restrictW f (obs a))) ∧
    ¬Constant (restrictW f (obs T)) ∧
    ∀ p bank, Reach (roots.map obs) p bank → Avail bank (restrictW f (obs T)) → L ≤ p
def isConstM (d a : Nat) : Bool := (a &&& d == 0) || (a &&& d == d)
def availM (d : Nat) (pm : List Nat) (a : Nat) : Bool :=
  let m := a &&& d
  m == 0 || m == d || pm.contains m || pm.contains (d ^^^ m)
lemma masked_eq_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (b &&& d)) : restrictW f (obs a) = restrictW f (obs b) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_zero_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = 0) : restrictW f (obs a) = fun _ => false := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_one_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = d) : restrictW f (obs a) = fun _ => true := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_comp_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (d ^^^ (b &&& d))) : restrictW f (obs a) = invW (restrictW f (obs b)) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simp only [Nat.testBit_and, Nat.testBit_xor, dom r, Bool.and_true] at h
  simp only [restrictW, obs, invW, h]
  cases b.testBit (f r).val <;> rfl
def poolSupply (f : Row → Row) (bank : List Wire) (pool : List Nat) : Prop :=
  ∀ a ∈ pool, Avail bank (restrictW f (obs a))
lemma availM_sound {f : Row → Row} {d a : Nat} {bank : List Wire} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hs : poolSupply f bank pool)
    (ok : availM d (pool.map (· &&& d)) a = true) :
    Avail bank (restrictW f (obs a)) := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at ok
  rcases ok with ((h0 | h1) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero_obs dom h0⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one_obs dom h1⟩)
  · exact (masked_eq_obs dom he.symm) ▸ hs v hv
  · have hinv := avail_inv (hs v hv)
    have hcomp : restrictW f (obs a) = invW (restrictW f (obs v)) := by
      have hx : (a &&& d) = d ^^^ (v &&& d) := by
        have := congrArg (d ^^^ ·) he
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_self] using this.symm
      exact masked_comp_obs dom hx
    exact hcomp ▸ hinv
abbrev Choice := Nat × Nat × Nat
def choiceVal (c : Choice) : Nat := bin c.1 c.2.1 c.2.2
def choiceOK (d : Nat) (pm : List Nat) (c : Choice) : Bool :=
  decide (c.1 < 4) && availM d pm c.2.1 && availM d pm c.2.2
def makePool (d : Nat) (pool : List Nat) : List Choice → Option (List Nat)
  | [] => some pool
  | c :: cs => if choiceOK d (pool.map (· &&& d)) c then makePool d (choiceVal c :: pool) cs else none
lemma pay_choice {f : Row → Row} {d : Nat} {roots bank q} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d (pool.map (· &&& d)) c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  have ha := availM_sound dom hs valid.1.2
  have hb := availM_sound dom hs valid.2
  have hprep : ∃ op x y, comb4 c.1 (restrictW f (obs c.2.1)) (restrictW f (obs c.2.2)) = comb2 op x y ∧
      Avail bank x ∧ Avail bank y := by
    have hd := valid.1.1
    interval_cases c.1
    · exact ⟨false, _, _, rfl, ha, hb⟩
    · exact ⟨true, _, _, rfl, ha, hb⟩
    · exact ⟨false, _, _, rfl, ha, avail_inv hb⟩
    · exact ⟨false, _, _, rfl, avail_inv ha, hb⟩
  obtain ⟨op, x, y, eq, hx, hy⟩ := hprep
  refine ⟨comb2 op x y :: bank, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · have hcv : restrictW f (obs (choiceVal c)) = comb2 op x y := by
      rw [← eq]; funext r; simp only [choiceVal, restrictW, obs, testBit_bin, comb4, comb2, invW]
      rcases c.1 with _ | _ | _ | d' <;> rfl
    exact hcv ▸ Or.inl (by simp)
  · exact avail_cons _ (hs v hv)
lemma makePool_sound {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {res} (ok : makePool d pool cs = some res) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next res := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction
lemma count_constM {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (ws : List Nat) : ws.countP (isConstM d) ≤ wmass ((ws.map obs).map (restrictW f)) := by
  classical
  induction ws with
  | nil => simp [wmass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, wmass, List.sum_cons] at ih ⊢
    cases h : isConstM d a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih.trans (Nat.le_add_left _ _)
    · have hc : Constant (restrictW f (obs a)) := by
        simp only [isConstM, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h0 | h1
        · exact ⟨false, masked_zero_obs dom h0⟩
        · exact ⟨true, masked_one_obs dom h1⟩
      simp only [ite_true, wcost, hc]
      omega
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  c.pm = c.wires.map (· &&& c.dom) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map fun pool => ⟨d, lb, cs.length, pool, pool.map (· &&& d)⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨rfl, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let z := choiceVal op
  let extra := !(availM c.dom c.pm z)
  decide (k + c.paid + extra.toNat < c.lb + (z :: rest).countP (isConstM c.dom)) &&
    rest.all (availM c.dom c.pm) && (!extra || choiceOK c.dom c.pm op)
lemma scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  obtain ⟨hpm, f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  intro t ht run
  have finish (n : Nat) (out : List Wire) (hr : Reach (roots.map obs) n out)
      (hsup : poolSupply f out (choiceVal op :: rest))
      (hle : n = c.paid + (!(availM c.dom c.pm (choiceVal op))).toNat) : False := by
    have hcov : Supply out (((choiceVal op :: rest).map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact hsup a ha
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction nc (restrict_run f (live_to_run run (choiceVal op :: rest) nd rfl)) (roots.map obs) hr hcov
    have hlo := lo q next hq hav
    have hcm := count_constM dom (choiceVal op :: rest)
    have hineq := cut.1.1
    omega
  cases hav : availM c.dom c.pm (choiceVal op) with
  | true =>
    apply finish c.paid bank hp _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact availM_sound dom hs (hpm ▸ hav)
    · exact availM_sound dom hs (hpm ▸ cut.1.2 a ha)
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      exact hpm ▸ h2
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (hpm ▸ cut.1.2 a ha)
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (127 ^^^ z)) ||| o) % 128, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 128
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 128 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^128) (hb : b < 2^128) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 128 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^128) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^128 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^128 := hS a (by simp)
    have hblt : b < 2^128 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^128 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^128 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^128 := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact hzlt; exact hUlt x hx
    have nr := ih tail htail_lt
    simp only [Finset.image_insert, renameW_bin] at nr ⊢
    refine ⟨U.image (renameW f), renameW f a, renameW f b, d, hd, rfl,
      fun hz => ha (renameW_inj f onto halt (by decide) (hz.trans (renameW_zero f).symm)),
      fun hz => hb (renameW_inj f onto hblt (by decide) (hz.trans (renameW_zero f).symm)),
      fun heq => hab (renameW_inj f onto halt hblt heq), ?_, nr⟩
    intro hm
    rw [← renameW_bin] at hm
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt halt heq]; simp)
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt hblt heq]; simp)
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
    exact fresh (by rw [renameW_inj f onto hzlt (hUlt x hx) heq.symm]; simp [hx])
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^128) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0
def ALL128 : Nat := 0xffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 128, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL128 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 7) (hj : j < 7) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 7 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL128 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
  | true =>
    obtain ⟨heq, h10, h01⟩ := hr.1 hms
    rw [heq]
    by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
    · simp [hd, h10 hd, h01]
    · simp [hd, h01]
  | false =>
    rcases hr.2 hms with ⟨hd, h10, heq, h01⟩ | ⟨h10, h01, heq⟩
    · simp [hd, h10, heq, h01]
    · by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
      · simp [hd, h10 hd, h01, heq]
      · simp [hd, h01, heq]
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) : swapWord i j w < 2^128 := by
  have hi : i < 7 := by omega
  have h1 : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^128 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^128 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^128 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 7)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^128) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^128 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hr⟩, testBit_renameW _ _ (swapRow p.1 p.2 ⟨r, hr⟩), testBit_renameW _ _ ⟨r, hr⟩]
      rfl
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega)))]
lemma permRow_surj (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) :
    Function.Surjective (permRow swaps) := by
  induction swaps with
  | nil => intro r; exact ⟨r, rfl⟩
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro r
    obtain ⟨q, hq⟩ := ih hv.2 r
    refine ⟨swapRow p.1 p.2 q, ?_⟩
    change permRow ps (swapRow p.1 p.2 (swapRow p.1 p.2 q)) = r
    rw [swapRow_invol p.1 p.2 (by omega) hv.1.2, hq]
lemma permRow_rev_cancel (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) (r : Row) :
    permRow swaps.reverse (permRow swaps r) = r := by
  induction swaps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
        swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
      simp [permRow, List.reverse_cons, List.foldl_append]
    rw [h1, ih hv.2, swapRow_invol p.1 p.2 (by omega) hv.1.2]
lemma rotate_impossible {T n : Nat} {ws : List Nat} (hi : Impossible T n ws.toFinset)
    (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (hT : T < 2^128) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^128) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^128 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^128 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
  have run' := live_renameW run hr (permRow swaps.reverse) (permRow_surj swaps.reverse hvr)
  have hT' : renameW (permRow swaps.reverse) T = T := by
    conv_lhs => rw [← hfix]
    exact hinv_word T hT
  have hS' : (ws.map (permWord swaps)).toFinset.image (renameW (permRow swaps.reverse)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hinv_word x (hw x hx)]
    · intro ha
      exact ⟨permWord swaps a, ⟨a, ha, rfl⟩, hinv_word a (hw a ha)⟩
  rw [hT', hS'] at run'
  exact hi k hk run'
abbrev Decor := Nat × Nat × Nat
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1, bin d x.2.1 y.2.1, bin d x.2.2 y.2.2)
def dsep (x : Decor) : Nat := x.2.1 ^^^ x.2.2
def projBits (rows : List Nat) (w : Nat) : Nat :=
  rows.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0
lemma testBit_projBits (rows : List Nat) (w i : Nat) :
    (projBits rows w).testBit i = match rows[i]? with | none => false | some r => w.testBit r := by
  induction rows generalizing i with
  | nil => simp [projBits]
  | cons r rs ih =>
    simp only [projBits, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.not_le.mpr (by decide : 0 < 1)]
      cases w.testBit r <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      have h0 : (if w.testBit r then (1 : Nat) else 0).testBit (i + 1) = false := by
        cases w.testBit r
        · simp
        · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
      rw [h0, Bool.or_false]
      exact ih i
lemma projBits_bin (rows : List Nat) (d a b : Nat) :
    projBits rows (bin d a b) = bin d (projBits rows a) (projBits rows b) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_projBits, testBit_bin, testBit_projBits, testBit_projBits]
  cases rows[i]? with
  | none => rcases d with _ | _ | _ | d <;> rfl
  | some r => exact testBit_bin d a b r
def faithful (pos neg : List Nat) (x : Decor) : Prop :=
  x.2.1 = projBits pos x.1 ∧ x.2.2 = projBits neg x.1
lemma faithful_bin {pos neg x y} (d : Nat) (hx : faithful pos neg x) (hy : faithful pos neg y) :
    faithful pos neg (dbin d x y) :=
  ⟨by rw [dbin, hx.1, hy.1, projBits_bin], by rw [dbin, hx.2, hy.2, projBits_bin]⟩
def goodPairs (T : Nat) (pos neg : List Nat) : Prop :=
  pos.length = neg.length ∧ ∀ i < pos.length,
    T.testBit (pos.getD i 0) = true ∧ T.testBit (neg.getD i 0) = false
def fullMask (n : Nat) : Nat := (1 <<< n) - 1
abbrev Cov := Nat × Nat × Nat
def addCov (z : Nat) (c : Cov) : Cov :=
  (z ||| c.1, (z ^^^ (z &&& c.1)) ||| (c.2.1 ^^^ (c.2.1 &&& z)),
   (z &&& c.2.1) ||| (c.2.2 ^^^ (c.2.2 &&& z)))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (dsep a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := c.1 ^^^ (c.1 &&& (c.2.1 &&& a))
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
lemma cov_one (c : Cov) (a : Nat) : takeOne (addCov a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOne, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
lemma cov_two (c : Cov) (a b : Nat) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwo, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma addCov_swap (c : Cov) (a b : Nat) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [addCov, Nat.testBit_or]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
      simp only [addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma cov_perm {l r : List Decor} (h : l.Perm r) : coverage l = coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (dsep a)) ih
  | swap _ _ _ => exact addCov_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
def delOne (ws : List Decor) (a : Decor) (k : Bool) : List Decor := if k then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
def restCov (c : Cov) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOne c b) else if kb then takeOne c a else takeTwo c a b
lemma cov_delOne {ws : List Decor} (a : Decor) (ha : a ∈ ws) (k : Bool) :
    (coverage (delOne ws a k)).1 = if k then (coverage ws).1 else takeOne (coverage ws) (dsep a) := by
  cases k
  · change (coverage (ws.erase a)).1 = _
    rw [cov_perm (List.perm_cons_erase ha)]
    exact (cov_one _ _).symm
  · rfl
lemma cov_delTwo {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb := by
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
    have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hbm))
    change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm hp]
    exact (cov_two _ _ _).symm
  · exact cov_delOne a ha false
  · exact cov_delOne b hb false
  · rfl
lemma cov_testBit (ws : List Decor) (i : Nat) :
    (coverage ws).1.testBit i = true ↔ ∃ x ∈ ws, (dsep x).testBit i = true := by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change (dsep a ||| (coverage ws).1).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp
lemma cov_required {T k pos neg} {ws : List Decor}
    (gp : goodPairs T pos neg) (hf : ∀ x ∈ ws, faithful pos neg x)
    (h : Live T k (ws.map Prod.fst).toFinset) :
    ((coverage ws).1 &&& fullMask pos.length) = fullMask pos.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have hfm : (fullMask pos.length).testBit i = decide (i < pos.length) := by
    simp [fullMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · have ⟨hp, hn⟩ := gp.2 i hi
    have hsep : T.testBit (pos.getD i 0) ≠ T.testBit (neg.getD i 0) := by rw [hp, hn]; decide
    obtain ⟨v, hv, hvd⟩ := live_sep h hsep
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hfx := hf x hx
    have hpi : pos[i]? = some (pos.getD i 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hni : neg[i]? = some (neg.getD i 0) := by
      have hi' : i < neg.length := gp.1 ▸ hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    have hbit : (dsep x).testBit i = true := by
      simp only [dsep, Nat.testBit_xor, hfx.1, hfx.2, testBit_projBits, hpi, hni]
      have h12 : x.1.testBit (pos.getD i 0) ≠ x.1.testBit (neg.getD i 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        exact hvd
      cases h1 : x.1.testBit (pos.getD i 0) <;> cases h2 : x.1.testBit (neg.getD i 0)
      · exact absurd (h1.trans h2.symm) h12
      · rfl
      · rfl
      · exact absurd (h1.trans h2.symm) h12
    have hc := (cov_testBit ws i).mpr ⟨x, hx, hbit⟩
    simp [hfm, hi, hc]
  · simp [hfm, hi]
def insertNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs
def sortNats : List Nat → List Nat
  | [] => []
  | a :: bs => insertNat a (sortNats bs)
lemma insertNat_perm (a : Nat) (l : List Nat) : (insertNat a l).Perm (a :: l) := by
  induction l with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp [insertNat, h]
    · exact by simpa [insertNat, h] using (List.Perm.cons b ih).trans (.swap a b bs)
lemma sortNats_perm (l : List Nat) : (sortNats l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertNat_perm a (sortNats bs)).trans (.cons a ih)
lemma sortNats_toFinset (l : List Nat) : (sortNats l).toFinset = l.toFinset := by
  ext x; simpa only [List.mem_toFinset] using (sortNats_perm l).mem_iff
def childTwo (ws : List Nat) (a b d : Nat) (ka kb : Bool) : List Nat :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma erase_toFinset {l : List Nat} (nd : l.Nodup) (a : Nat) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [nd.mem_erase_iff]
lemma enum_step {T cap : Nat} {ws : List Nat} (nd : ws.Nodup) (out : T ∉ ws)
    (stepOK : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb : Bool,
      a ≠ b → bin d a b ≠ 0 → bin d a b ∉ ws → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  cases k with
  | zero =>
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  | succ k =>
    obtain ⟨U, a, b, d, hd, he, _, _, hab, hf, tail⟩ := h
    have am : a ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_self a _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    have fresh : bin d a b ∉ ws := fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hnz : bin d a b ≠ 0 := live_nonzero tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b from rfl, erase_toFinset (nd.erase _) b, erase_toFinset nd a]
    have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
      cases c <;> simp [kept]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kf, kf, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (nd.erase _).erase _
    have ar : a ∉ rest := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (nd.erase a).not_mem_erase
    have nk := kept_nodup kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have ndc : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr hm))),
        kept_nodup ka a _ nk ax⟩
    have eqc : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := live_size tail
    have hlen : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup ndc, eqc]; omega
    exact stepOK a am b bm d hd ka kb hab hnz fresh hlen k (by omega) (eqc.symm ▸ tail)
lemma delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k; exact List.erase_sublist; exact List.Sublist.refl _
lemma delTwo_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) : (delTwo ws a b ka kb).Sublist ws :=
  (delOne_sub _ _ _).trans (delOne_sub _ _ _)
lemma delTwo_len (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
  cases ka <;> cases kb <;> simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
lemma unique_fst {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hn (eq ▸ List.mem_map_of_mem hb')).elim
    · exact (hn (eq.symm ▸ List.mem_map_of_mem ha')).elim
    · exact ih ht ha' hb'
lemma delTwo_map_toFinset {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  have wn : ws.Nodup := nd.of_map
  have dn : (delOne ws a ka).Nodup := wn.sublist (delOne_sub ws a ka)
  have m1 (l : List Decor) (hl : l.Nodup) (x y : Decor) (c : Bool) :
      y ∈ delOne l x c ↔ y ∈ l ∧ (y ≠ x ∨ c = true) := by
    cases c <;> simp [delOne, hl.mem_erase_iff, and_comm]
  have km (v : Nat) : v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
    simp only [delTwo, List.mem_map, m1 _ wn, m1 _ dn]
    constructor
    · rintro ⟨w, ⟨⟨hw, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, h1.imp (fun h e => h (unique_fst nd hw ha e)) id,
        h2.imp (fun h e => h (unique_fst nd hw hb e)) id⟩
    · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hw, h1.imp (fun h e => h (congrArg Prod.fst e)) id⟩,
        h2.imp (fun h e => h (congrArg Prod.fst e)) id⟩, rfl⟩
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (v : Nat) : v ∈ kept c x l ↔ (v = x ∧ c = true) ∨ v ∈ l := by
    cases c <;> simp [kept]
  ext v
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, km, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all
lemma childTwo_swap (v : List Nat) (nd : v.Nodup) (a b : Nat) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (y : Nat) : y ∈ kept c x l ↔ (y = x ∧ c = true) ∨ y ∈ l := by
    cases c <;> simp [kept]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm_flip d hd a b]
  tauto
def varsOf (m : Nat) : List Nat :=
  (List.range 7).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    let fr := ((r &&& (127 ^^^ z)) ||| o) % 128
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 128
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 128 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127 : ((r.val &&& (127 ^^^ z)) ||| o) < 128 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (127 ^^^ z)) < 128 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 7) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (127 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 7
    · have h7 : (127 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 128) && decide (s < 128) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL128 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL128]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 128 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^128) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^128 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^128) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^128 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def carryOK (swaps : List (Nat × Nat)) (roots1 : List Nat) (T1 : Nat) (roots2 : List Nat) (T2 : Nat) : Bool :=
  swapsValid swaps && checkProper T1 && checkRoots roots1 && checkProper T2 &&
    (permWord swaps T1 == T2) && roots1.all (fun a => freeIn roots2 (permWord swaps a))
lemma carry_of {swaps roots1 T1 roots2 T2 L} (ok : carryOK swaps roots1 T1 roots2 T2 = true)
    (hL : Lower roots2 T2 L) : Lower roots1 T1 L := by
  simp only [carryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hsv, hT1⟩, hR1⟩, hT2⟩, heq⟩, hcov⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT1
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hT2
  have hR1' := checkRoots_sound hR1
  have heq' : renameW (permRow swaps) T1 = T2 := (permWord_eq_renameW swaps hsv T1 p1b).symm.trans heq
  have hcov' : ∀ a ∈ roots1, Avail (roots2.map obs) (restrictW (permRow swaps) (obs a)) := fun a ha =>
    freeIn_sound (permWord_eq_renameW swaps hsv a (hR1' a ha).1 ▸ hcov a ha)
  simpa using lower_slice p1a p1b p1c hR1' p2a p2b p2c (permRow swaps) heq' hcov' ∅ (by simp) (by simp) L hL
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL128))
lemma lift_of {z o roots T other G essPairs L} (ok : liftCheck z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G := (fixWord_eq_renameW z o T).symm.trans heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL128]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 128 r'.val |> fun e => by simpa [this] using e⟩
def goodPairsCheck (T : Nat) (pos neg : List Nat) : Bool :=
  (pos.length == neg.length) &&
    (List.range pos.length).all fun i => T.testBit (pos.getD i 0) && !(T.testBit (neg.getD i 0))
lemma goodPairs_of {T pos neg} (ok : goodPairsCheck T pos neg = true) : goodPairs T pos neg := by
  simp only [goodPairsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at ok
  exact ok
def autosCheck (T : Nat) (autos : List (List (Nat × Nat))) : Bool :=
  autos.all fun sw => swapsValid sw && (permWord sw T == T)
lemma autos_of {T autos} (ok : autosCheck T autos = true) :
    ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T := by
  simp only [autosCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok
def baseCheck (pos neg : List Nat) (base : List Decor) : Bool :=
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^128)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := by
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  intro x hx
  have h := ok x hx
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
def forestRootCheck (roots : List Nat) (T : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    roots.all fun a => essPairs.any fun e => (e.1 == a) && checkEss1 T roots e.1 e.2.1 e.2.2
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat

def nodesWithIdentity (entries : List (List Nat × List Nat)) : List NodeSpec :=
  entries.map (fun entry => (entry.1, entry.2, [0]))

lemma var_testBit (i : Fin 7) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
def sliceDirectCheck (z o zDead : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    decide (zDead < 128) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead : Nat) (hz : z < 128) (hd : zDead < 128) (ho : o < 128)
    (hzo : ((z ||| zDead) &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true := by
  have hsub := subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n := 7) hz hd) ho hzo r
  unfold subcube at hsub ⊢
  rw [testBit_foldr_bits] at hsub ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsub ⊢
  refine ⟨hsub.1, ?_, hsub.2.2⟩
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun x => x.testBit i) hsub.2.1
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  cases hfa : (fixRow (z ||| zDead) o r).val.testBit i <;> cases hzb : z.testBit i <;> simp_all
lemma slice_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) qL := by
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, ho⟩, _hzo0⟩, hd⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  refine ⟨fixRow (z ||| zDead) o, qRoots, subcube_fixRow_sup z o zDead hz hd ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW (z ||| zDead) o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW, heq]
  exact hPrior
def evalInput6 (r : Row) : Fin 6 → Bool := fun i => r.val.testBit i.val
def packInput6 (x : Fin 6 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    omega⟩
lemma evalInput6_packInput6 (x : Fin 6 → Bool) : evalInput6 (packInput6 x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (j : Fin 6),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
  fin_cases i <;> simpa [evalInput6, packInput6] using hi
lemma sum_eq_packInput6 (x : Fin 6 → Bool) :
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = (packInput6 x).val := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two, packInput6]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide
lemma testBit_rep64 (T6 : Nat) (hT6 : T6 < 2^64) (r : Row) :
    (T6 ||| (T6 <<< 64)).testBit r.val = T6.testBit (r.val % 64) := by
  have hr := r.isLt
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h64 : r.val < 64
  · have hn : ¬(64 ≤ r.val) := by omega
    rw [Nat.mod_eq_of_lt h64]
    simp [hn]
  · have hge : 64 ≤ r.val := by omega
    have hmod : r.val % 64 = r.val - 64 := by omega
    rw [hmod]
    have hhi : T6.testBit r.val = false → (T6.testBit r.val || (decide (64 ≤ r.val) && T6.testBit (r.val - 64))) = T6.testBit (r.val - 64) := by
      intro hf; simp [hf, hge]
    have hf : T6.testBit r.val = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hT6 (Nat.pow_le_pow_right (by decide : 0 < 2) hge))
    exact hhi hf
lemma sw_extract_full_6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^128 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput6 r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi6 : i < 6 := by simpa using hi2
      have hv : (varsOf 63)[i]? = some (VAR i) := by interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput6, swRead, Bool.false_bne]
      have hget : (varsOf 63)[i]'(by simpa [seeds] using hi1) = VAR i := (List.getElem?_eq_some_iff.mp hv).2
      rw [hget]
      exact var_testBit ⟨i, by omega⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · have h := hev ⟨r, hr⟩; simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]; exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma table2_of_lower (T6 : Nat) (hT6lt : T6 < 2^64)
    (hT0 : (T6 ||| (T6 <<< 64)) ≠ 0) (hTlt : (T6 ||| (T6 <<< 64)) < 2^128) (hTb0 : (T6 ||| (T6 <<< 64)).testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 63) (T6 ||| (T6 <<< 64)) L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = (T6 ||| (T6 <<< 64)).testBit r.val)
    (s : ℕ)
    (hcs : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  let T := T6 ||| (T6 <<< 64)
  obtain ⟨C, hfan, hsize, heval⟩ := hcs
  have hlegal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have ⟨hm, hl⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    exact ⟨hm, hl⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · have hlt : C.gates.countP isBin < C.gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    have heR : ∀ r : Row, Circuit.eval ⟨C.gates, C.output⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val := by
      intro r
      have h1 := heval (evalInput6 r)
      have hsum : (∑ i : Fin 6, if evalInput6 r i then 2 ^ (i : ℕ) else 0) = r.val % 64 := by
        rw [sum_eq_packInput6]
        have h : ∀ j : Row, (packInput6 (evalInput6 j)).val = j.val % 64 := by decide +kernel
        exact h r
      dsimp only at h1
      rw [hsum] at h1
      exact h1.trans (testBit_rep64 T6 hT6lt r).symm
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full_6 T hT0 hTlt hTb0 C.gates C.output hlegal heR
    have hrun := live_to_run hlive S.toList (Finset.nodup_toList S) (by simp)
    have hsup : Supply ((varsOf 63).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 63).map obs)
        (show Reach ((varsOf 63).map obs) 0 ((varsOf 63).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    have hwEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
      intro x
      rw [← evalInput6_packInput6 x, hwEvalR (packInput6 x), testBit_rep64 T6 hT6lt (packInput6 x)]
      rw [evalInput6_packInput6 x, sum_eq_packInput6 x]
      have hlt64 : (packInput6 x).val < 64 := by
        have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
        have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
        simp only [packInput6]; omega
      rw [Nat.mod_eq_of_lt hlt64]
    have hcsz : C.size = C.gates.length := rfl
    refine ⟨⟨wit, wo⟩, hwMono, ?_, hwEval⟩
    change wit.length ≤ s
    omega
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    have ⟨hm, hl⟩ := hlegal g hg
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
inductive BT (α : Type) where
  | empty : BT α
  | leaf : α → BT α
  | node : BT α → BT α → BT α
def btGet {α : Type} (d : α) : BT α → Nat → α
  | .empty, _ => d
  | .leaf x, _ => x
  | .node l r, i => if i &&& 1 == 0 then btGet d l (i >>> 1) else btGet d r (i >>> 1)
def btSet {α : Type} : Nat → BT α → Nat → α → BT α
  | 0, _, _, v => .leaf v
  | d + 1, .empty, i, v =>
    if i &&& 1 == 0 then .node (btSet d .empty (i >>> 1) v) .empty
    else .node .empty (btSet d .empty (i >>> 1) v)
  | d + 1, .leaf x, i, v =>
    if i &&& 1 == 0 then .node (btSet d (.leaf x) (i >>> 1) v) .empty
    else .node .empty (btSet d (.leaf x) (i >>> 1) v)
  | d + 1, .node l r, i, v =>
    if i &&& 1 == 0 then .node (btSet d l (i >>> 1) v) r
    else .node l (btSet d r (i >>> 1) v)
def btUpdate {α : Type} (d0 : α) : Nat → BT α → Nat → (α → α) → BT α
  | 0, .leaf x, _, f => .leaf (f x)
  | 0, _, _, f => .leaf (f d0)
  | d + 1, .empty, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d .empty (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d .empty (i >>> 1) f)
  | d + 1, .leaf x, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d (.leaf x) (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d (.leaf x) (i >>> 1) f)
  | d + 1, .node l r, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d l (i >>> 1) f) r
    else .node l (btUpdate d0 d r (i >>> 1) f)
def btAll {α : Type} (P : α → Prop) : BT α → Prop
  | .empty => True
  | .leaf x => P x
  | .node l r => btAll P l ∧ btAll P r
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction t generalizing i with
  | empty => exact hd
  | leaf x => exact ht
  | node l r ihl ihr =>
    unfold btGet
    split
    · exact ihl ht.1 _
    · exact ihr ht.2 _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact hv
  | succ d ih =>
    cases t with
    | empty =>
      unfold btSet; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btSet; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btSet; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases t with
    | leaf x => exact hf x ht
    | empty => exact hf d0 hd0
    | node _ _ => exact hf d0 hd0
  | succ d ih =>
    cases t with
    | empty =>
      unfold btUpdate; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btUpdate; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btUpdate; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
def btOfList {α : Type} (depth : Nat) (l : List α) : BT α :=
  (l.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) (0, BT.empty)).2
lemma btAll_ofList {α : Type} {P : α → Prop} {depth : Nat} {l : List α}
    (h : ∀ x ∈ l, P x) : btAll P (btOfList depth l) := by
  unfold btOfList
  have hgo : ∀ (xs : List α) (acc : Nat × BT α),
      (∀ x ∈ xs, P x) → btAll P acc.2 →
      btAll P (xs.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) acc).2 := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; exact hacc
    | cons x xs ih =>
      intro acc hx hacc
      exact ih (acc.1 + 1, btSet depth acc.2 acc.1 x)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (btAll_set hacc (hx x (List.mem_cons_self ..)))
  exact hgo l (0, BT.empty) h trivial
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL128 ^^^ VAR i else if o.testBit i then VAR i else ALL128
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 7) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL128.testBit r.val = true := by
    simp only [ALL128]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 128 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · have hsub : (subcube z o).testBit r = ((r &&& z == 0) && (r &&& o == o)) := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and,
      fastBitMask_testBit z o 0 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 1 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 2 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 3 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 4 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 7) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 7, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 7
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 7
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 128 ≤ r := by omega
      have ha : ALL128 < 2^128 := by decide
      have hv : VAR i < 2^128 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^128; decide
      have hlt_m : fastBitMask z o i < 2^128 := by
        unfold fastBitMask; split
        · exact Nat.xor_lt_two_pow ha hv
        · split; exact hv; exact ha
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by decide : 0 < 2) hle))
    have hsub : (subcube z o).testBit r = false := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and, hlt_f]
    rfl
lemma slice_fast_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  have ok2 := ok
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1.1.1 ok2.1.1.1.1.1.1.1.2 ok2.1.1.1.1.1.1.2]
  exact slice_direct ok hPrior
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) &&& 63
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (ws.map (permWord sw)))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContainsBT at hhit
    have hmem := List.contains_iff_mem.mp hhit
    have hb : ∀ xs ∈ btGet [] prevBks (hashWs64 (sortNats ((choiceVal op :: rest).map (permWord sw)))),
        Impossible T k xs.toFinset :=
      btAll_get hPrev (fun _ hx => (List.not_mem_nil hx).elim) _
    have himp := hb _ hmem
    rw [sortNats_toFinset] at himp
    have ⟨hsv, hfix⟩ := hAutos sw hsw
    have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
    have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
        ∀ r : Row, permRow l.reverse (permRow l r) = r := by
      intro l hl
      induction l with
      | nil => intro r; rfl
      | cons p ps ih =>
        simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
        intro r
        have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
            swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
          simp [permRow, List.reverse_cons, List.foldl_append]
        rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
    have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
      simpa using hinv_row_gen sw.reverse hvr
    have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 128
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rw [permWord_eq_renameW sw hsv x (hlt x hx)]
      exact renameW_lt _ x
    have hrot := rotate_impossible himp sw.reverse hvr hT hfixr hmap_lt
    have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
      exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
    rwa [hback] at hrot
abbrev FastPool := BoundPool × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else some (c, miss, vals.countP (isConstM c.dom))
def fastPoolCut (fp : FastPool) (k : Nat) (a b d : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let totC := fp.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && isConstM c.dom a then 1 else 0
    let dropB := if !kb && isConstM c.dom b then 1 else 0
    let z := bin d a b
    let cRest := totC - dropA - dropB + (if isConstM c.dom z then 1 else 0)
    let zIn := availM c.dom c.pm z
    let extra := if zIn then 0 else 1
    decide (k + c.paid + extra < c.lb + cRest) && (zIn || choiceOK c.dom c.pm (d, a, b))
lemma countP_erase {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {x : α} (hx : x ∈ l) :
    (l.erase x).countP p + (if p x then 1 else 0) = l.countP p := by
  have hp := List.perm_cons_erase hx
  have h1 := List.Perm.countP_eq p hp
  simp only [List.countP_cons] at h1
  omega
lemma countP_delTwo_fst (p : Nat → Bool) {ws : List Decor} {a b : Decor}
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map Prod.fst).countP p =
      (ws.map Prod.fst).countP p - (if !ka && p a.1 then 1 else 0) - (if !kb && p b.1 then 1 else 0) := by
  have hne : a ≠ b := fun e => hab (congrArg Prod.fst e)
  have hmap_erase : ∀ (l : List Decor) (x : Decor), (l.map Prod.fst).Nodup → x ∈ l →
      (l.erase x).map Prod.fst = (l.map Prod.fst).erase x.1 := by
    intro l x hnd hx
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne1 : y.1 ≠ x.1 := by
          intro eq; apply hnd.1; rw [eq]
          exact List.mem_map_of_mem ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))
        have h1 : (y == x) = false := beq_false_of_ne hyx
        have h2 : (y.1 == x.1) = false := beq_false_of_ne hne1
        simp only [List.erase_cons, h1, h2, List.map_cons]
        exact congrArg (y.1 :: ·) (ih hnd.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx)))
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne hne.symm).mpr hb
    have hnd1 : ((ws.erase a).map Prod.fst).Nodup := ((List.erase_sublist).map Prod.fst).nodup nd
    change (((ws.erase a).erase b).map Prod.fst).countP p = _
    rw [hmap_erase _ b hnd1 hbm, hmap_erase ws a nd ha]
    have ha1 : a.1 ∈ ws.map Prod.fst := List.mem_map_of_mem ha
    have hb1 : b.1 ∈ (ws.map Prod.fst).erase a.1 := (List.mem_erase_of_ne hab.symm).mpr (List.mem_map_of_mem hb)
    have c1 := countP_erase p ha1
    have c2 := countP_erase p hb1
    cases hpa : p a.1 <;> cases hpb : p b.1 <;> simp [hpa, hpb] at c1 c2 ⊢ <;> omega
  · change ((ws.erase a).map Prod.fst).countP p = _
    rw [hmap_erase ws a nd ha]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) ha)
    cases hpa : p a.1 <;> simp [hpa] at c1 ⊢ <;> omega
  · change ((ws.erase b).map Prod.fst).countP p = _
    rw [hmap_erase ws b nd hb]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) hb)
    cases hpb : p b.1 <;> simp [hpb] at c1 ⊢ <;> omega
  · simp [delTwo, delOne]
lemma fastPoolCut_sound {raw T ws a b d ka kb k c fp}
    (hP : ValidPool raw T c) (hprep : prepPool (ws.map Prod.fst) c = some fp)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 d ka kb = true) :
    Impossible T k (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  unfold prepPool at hprep
  dsimp only at hprep
  split at hprep
  · simp at hprep
  · simp only [Option.some.injEq] at hprep
    subst hprep
    unfold fastPoolCut at hcut
    dsimp only at hcut
    split at hcut
    · simp at hcut
    · next hmiss =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_filter, Bool.not_eq_true'] at hmiss
      have hsub := (delTwo_sub ws a b ka kb).map Prod.fst
      have h_all_avail : ((delTwo ws a b ka kb).map Prod.fst).all (availM c.dom c.pm) = true := by
        rw [List.all_eq_true]; intro w hw
        by_contra hna
        have hnf : availM c.dom c.pm w = false := Bool.eq_false_iff.mpr hna
        have hmem_ws : w ∈ ws.map Prod.fst := hsub.subset hw
        have hm := hmiss w ⟨hmem_ws, hnf⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
        have hne_ab : a ≠ b := fun e => hab (congrArg Prod.fst e)
        have hnot_in : ∀ (x : Decor) (kx : Bool), kx = false → x ∈ ws → x.1 ∉ (delTwo ws a b ka kb).map Prod.fst → True := fun _ _ _ _ _ => trivial
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            exact List.Nodup.not_mem_erase hnd_ws hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · have hu_eq : u = a := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa)
          exact hna' hka hu_eq
        · have hu_eq : u = b := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb)
          exact hnb' hkb hu_eq
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut
      simp only [choiceVal, h_all_avail, Bool.true_and, Bool.and_true, List.countP_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hcut ⊢
      rw [hcnt]
      rcases hcut with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          cases hcz : isConstM c.dom (bin d a.1 b.1) <;>
          simp only [hz, hcz, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
            Bool.and_eq_true, Bool.false_eq_true, ite_true, ite_false] at h1 ⊢ <;> omega
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          simp only [hz, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or] at h2 ⊢ <;>
          exact h2
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
  go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^128) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hfr_b : (ws.any (fun v => v.1 == z.1)) = false := by
    rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
    have hvz : v.1 = bin d a.1 b.1 := beq_iff_eq.mp heq
    exact hfr (hvz ▸ List.mem_map_of_mem hv)
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    have hdl := delTwo_len ws a b ka kb ha hb ne
    simp only [child, rest, List.length_map, List.length_cons]
    omega
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMoveBT at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAllBT, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma nodeBT_sound {raw T pos neg ws fpools autos prevBks cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (checks : cap = 0 ∨ testAllBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0
    intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPairBT, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMoveBT_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAllBT_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
def buildWiresBT (depth : Nat) (base : List Decor) (steps : List (Nat × Nat × Nat)) : BT Decor :=
  let init := (base.length, btOfList depth base)
  (steps.foldl (fun p s =>
    let a := btGet (0, 0, 0) p.2 s.2.1
    let b := btGet (0, 0, 0) p.2 s.2.2
    (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 a b))) init).2
lemma buildWiresBT_faithful {depth pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128)
        (ss.foldl (fun p s => (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 (btGet (0, 0, 0) p.2 s.2.1) (btGet (0, 0, 0) p.2 s.2.2)))) acc).2 := by
    intro ss
    induction ss with
    | nil => intro acc hacc; exact hacc
    | cons s ss ih =>
      intro acc hacc
      have ha := btAll_get hacc hdef s.2.1
      have hb := btAll_get hacc hdef s.2.2
      exact ih _ (btAll_set hacc ⟨faithful_bin s.1 ha.1 hb.1, bin_lt s.1 _ _ ha.2 hb.2⟩)
  exact hgo steps (base.length, btOfList depth base) h0
def buildPoolsBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : List PoolSpec) : BT (Option BoundPool) :=
  btOfList pdepth (pspecs.map fun (slIdx, chIdxs) =>
    match btGet none slices slIdx with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
      materialize raw cs dom lb)
lemma buildPoolsBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))} {pspecs : List PoolSpec}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsBT pdepth W raw slices pspecs) := by
  apply btAll_ofList
  intro o ho c hc
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp ho
  dsimp only at hmat
  have hsl := btAll_get (d := none) hSlices (fun _ h => by simp at h) slIdx
  cases heq : btGet none slices slIdx with
  | none => rw [heq] at hmat; exact absurd (hmat.trans hc) (by simp)
  | some sl =>
    rw [heq] at hmat
    exact materialize_sound (hsl sl heq) (hmat.trans hc)
def checkNodeBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals := ws.map Prod.fst
  let fpools := ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos := ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^128 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun fp hfp => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hfp
      cases heq : btGet none poolTable pIdx with
      | none => simp [heq] at hmat
      | some c =>
        simp only [heq] at hmat
        have hvc := btAll_get hPoolTable (fun _ h => by simp at h) pIdx c heq
        have hfp_eq : fp.1 = c := by
          unfold prepPool at hmat
          dsimp only at hmat
          split at hmat
          · simp at hmat
          · simp only [Option.some.injEq] at hmat; rw [← hmat]
        rw [hfp_eq]
        exact ⟨hvc, hmat⟩)
    (fun sw hsw => by
      obtain ⟨aIdx, _, rfl⟩ := List.mem_map.mp hsw
      exact btAll_get hAutos ⟨rfl, rfl⟩ aIdx)
    hPrev ok.2
def nodeValsBT (W : BT Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (btGet (0, 0, 0) W idx).1)
def buildBucketsBT (W : BT Decor) (nodes : List NodeSpec) : BT (List (List Nat)) :=
  nodes.foldl (fun acc ns =>
    let xs := nodeValsBT W ns
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := fun ns hns => by
    unfold nodeValsBT; rw [sortNats_toFinset]
    exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
lemma lower_of_forestBT {roots T cap} {topBks : BT (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : btAll (fun bk => ∀ xs ∈ bk, Impossible T cap xs.toFinset) topBks)
    (hRoot : bucketContainsBT topBks roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContainsBT at hRoot
    exact btAll_get hTop (fun _ h => (List.not_mem_nil h).elim) _ _ (List.contains_iff_mem.mp hRoot)
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def h2R : List Nat := varsOf 7
def h2G : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def h2Pos : List Nat := [5,6,3,3,6,5]
def h2Neg : List Nat := [4,4,1,2,2,1]
def h2Mask : Nat := fullMask 6
def h2Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,45,36),(0xcccccccccccccccccccccccccccccccc,30,24),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,51,3)]
def h2Steps : List (Nat × Nat × Nat) := []
def h2W : BT Decor := buildWiresBT 2 h2Base h2Steps
def h2AutoList : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2)],[(1,2),(0,1)],[(1,2),(0,2)]]
def h2Autos : BT (List (Nat × Nat)) := btOfList 3 h2AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Pairs : goodPairs h2G h2Pos h2Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2BaseOk : ∀ x ∈ h2Base, faithful h2Pos h2Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2WOk : btAll (fun x => faithful h2Pos h2Neg x ∧ x.1 < 2^128) h2W := buildWiresBT_faithful h2BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h2G = h2G) h2Autos := btAll_ofList (autos_of (by decide +kernel))
def h2SliceList : List (Option (Nat × Nat)) := []
def h2Slices : BT (Option (Nat × Nat)) := btOfList 1 h2SliceList
def h2Specs : List PoolSpec := []
def h2Pools : BT (Option BoundPool) := buildPoolsBT 1 h2W h2R h2Slices h2Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h2R h2G p.1 p.2) h2Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h2R h2G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h2R h2G c) h2Pools := buildPoolsBT_sound h2SlicesOk
def h2Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h2G (3 - 1) xs.toFinset) h2Empty := trivial
def h2Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Test3_0 : checkNodesBT h2W h2G h2Mask h2Pools h2Autos h2Empty 3 h2Block3_0 = true := by decide +kernel
def h2Nodes3 : List NodeSpec := h2Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Check3 : checkNodesBT h2W h2G h2Mask h2Pools h2Autos h2Empty 3 h2Nodes3 = true := h2Test3_0
def h2Bucket3 : BT (List (List Nat)) := buildBucketsBT h2W h2Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h2G 3 xs.toFinset) h2Bucket3 := buildBucketsBT_sound (by decide) h2Pairs h2WOk h2PoolsOk h2AutosOk h2EmptyOk h2Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h2Bound : Lower h2R h2G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5)]) (by decide +kernel) h2Bucket3Ok (by decide +kernel)
def h3R : List Nat := varsOf 15
def h3G : Nat := 0xece8ece8ece8ece8ece8ece8ece8ece8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h3Bound : Lower h3R h3G 5 := lift_of (z := 8) (o := 0) (essPairs := [(VAR 3,2,10)]) (by decide +kernel) h2Bound
def h4R : List Nat := varsOf 23
def h4G : Nat := 0xeaeae8e8eaeae8e8eaeae8e8eaeae8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h4Bound : Lower h4R h4G 5 := carry_of (swaps := [(3,4),(0,1)]) (roots2 := h3R) (T2 := h3G) (by decide +kernel) h3Bound
def h5R : List Nat := varsOf 27
def h5G : Nat := 0xeeaacc88eeaacc88eeaacc88eeaacc88
def h5Pos : List Nat := [10,3,3,25,26,10,25,17]
def h5Neg : List Nat := [8,1,2,24,24,2,9,1]
def h5Mask : Nat := fullMask 8
def h5Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,206,194),(0xcccccccccccccccccccccccccccccccc,55,36),(0xff00ff00ff00ff00ff00ff00ff00ff00,121,89),(0xffff0000ffff0000ffff0000ffff0000,216,24)]
def h5Steps : List (Nat × Nat × Nat) := []
def h5W : BT Decor := buildWiresBT 2 h5Base h5Steps
def h5AutoList : List (List (Nat × Nat)) := [[],[(3,4),(0,1)]]
def h5Autos : BT (List (Nat × Nat)) := btOfList 1 h5AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Pairs : goodPairs h5G h5Pos h5Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5BaseOk : ∀ x ∈ h5Base, faithful h5Pos h5Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5WOk : btAll (fun x => faithful h5Pos h5Neg x ∧ x.1 < 2^128) h5W := buildWiresBT_faithful h5BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h5G = h5G) h5Autos := btAll_ofList (autos_of (by decide +kernel))
def h5SliceList : List (Option (Nat × Nat)) := []
def h5Slices : BT (Option (Nat × Nat)) := btOfList 1 h5SliceList
def h5Specs : List PoolSpec := []
def h5Pools : BT (Option BoundPool) := buildPoolsBT 1 h5W h5R h5Slices h5Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h5R h5G p.1 p.2) h5Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h5R h5G p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h5R h5G c) h5Pools := buildPoolsBT_sound h5SlicesOk
def h5Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h5G (3 - 1) xs.toFinset) h5Empty := trivial
def h5Block3_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Test3_0 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Empty 3 h5Block3_0 = true := by decide +kernel
def h5Nodes3 : List NodeSpec := h5Block3_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Check3 : checkNodesBT h5W h5G h5Mask h5Pools h5Autos h5Empty 3 h5Nodes3 = true := h5Test3_0
def h5Bucket3 : BT (List (List Nat)) := buildBucketsBT h5W h5Nodes3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bucket3Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h5G 3 xs.toFinset) h5Bucket3 := buildBucketsBT_sound (by decide) h5Pairs h5WOk h5PoolsOk h5AutosOk h5EmptyOk h5Check3
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h5Bound : Lower h5R h5G 4 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,2,10),(VAR 4,1,17)]) (by decide +kernel) h5Bucket3Ok (by decide +kernel)
def h6R : List Nat := varsOf 21
def h6G : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h6Bound : Lower h6R h6G 4 := carry_of (swaps := [(2,3),(3,4),(1,2)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h7R : List Nat := varsOf 29
def h7G : Nat := 0xfaaaa0a0faaaa0a0faaaa0a0faaaa0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h7Bound : Lower h7R h7G 5 := lift_of (z := 0) (o := 8) (essPairs := [(VAR 3,20,28)]) (by decide +kernel) h6Bound
def h8R : List Nat := varsOf 14
def h8G : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h8Bound : Lower h8R h8G 4 := carry_of (swaps := [(2,3),(1,2),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h9R : List Nat := varsOf 30
def h9G : Nat := 0xfcc0ccc0fcc0ccc0fcc0ccc0fcc0ccc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h9Bound : Lower h9R h9G 5 := carry_of (swaps := [(3,4),(0,1)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h10R : List Nat := varsOf 15
def h10G : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h10Bound : Lower h10R h10G 5 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h8Bound
def h11R : List Nat := varsOf 23
def h11G : Nat := 0xfefeececfefeececfefeececfefeecec
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h11Bound : Lower h11R h11G 5 := carry_of (swaps := [(3,4),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h1R : List Nat := varsOf 31
def h1G : Nat := 0xfeeaece8feeaece8feeaece8feeaece8
def h1Pos : List Nat := [5,6,3,3,10,6,5,10,25,17,13,28,11,21,19,28,10,17,13,22,28,17,22,10,26,5,25]
def h1Neg : List Nat := [4,4,1,2,9,2,1,2,9,1,12,20,9,20,18,12,12,20,9,18,24,16,20,8,24,0,24]
def h1Mask : Nat := fullMask 27
def h1Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x626774d,0x41354),(0xcccccccccccccccccccccccccccccccc,0x1c950be,0x840a8),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x25cac63,0x43ac03),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x5959d90,0x5959510),(0xffff0000ffff0000ffff0000ffff0000,0x57aeb00,0x57a6800)]
def h1Steps : List (Nat × Nat × Nat) := [(1,0,1),(1,0,2),(1,1,2),(0,4,6),(1,5,6),(3,1,2),(3,1,4),(3,1,6),(3,2,5),(3,0,2),(1,0,3),(3,0,3),(2,6,11),(1,1,14)]
def h1W : BT Decor := buildWiresBT 5 h1Base h1Steps
def h1AutoList : List (List (Nat × Nat)) := [[],[(3,4),(0,1)]]
def h1Autos : BT (List (Nat × Nat)) := btOfList 1 h1AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Pairs : goodPairs h1G h1Pos h1Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1BaseOk : ∀ x ∈ h1Base, faithful h1Pos h1Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1WOk : btAll (fun x => faithful h1Pos h1Neg x ∧ x.1 < 2^128) h1W := buildWiresBT_faithful h1BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h1G = h1G) h1Autos := btAll_ofList (autos_of (by decide +kernel))
def h1SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 1 0,5),some (subcubeFast 1 16,4),some (subcubeFast 2 0,5),some (subcubeFast 2 8,4),some (subcubeFast 4 0,4),some (subcubeFast 8 0,5),some (subcubeFast 16 0,5),some (subcubeFast 24 0,4)]
def h1Slices : BT (Option (Nat × Nat)) := btOfList 4 h1SliceList
def h1Specs : List PoolSpec := [(2,[]),(4,[]),(3,[]),(5,[]),(0,[(1,0,1)]),(1,[(1,0,1)]),(6,[]),(7,[]),(0,[]),(8,[]),(1,[]),(1,[(1,0,2)]),(1,[(3,0,2)]),(4,[(1,0,3)]),(1,[(1,0,3)]),(8,[(1,0,3)]),(4,[(3,0,3)]),(1,[(3,0,3)]),(9,[]),(8,[(3,0,3)])]
def h1Pools : BT (Option BoundPool) := buildPoolsBT 5 h1W h1R h1Slices h1Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice9 : Slice h1R h1G (subcubeFast 24 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h2Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice8 : Slice h1R h1G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h3Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice7 : Slice h1R h1G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h4Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice6 : Slice h1R h1G (subcubeFast 4 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice5 : Slice h1R h1G (subcubeFast 2 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h6Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice4 : Slice h1R h1G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h7Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice3 : Slice h1R h1G (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h8Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice2 : Slice h1R h1G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h9Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice1 : Slice h1R h1G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h10Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Slice0 : Slice h1R h1G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h11Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h1R h1G p.1 p.2) h1Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h1R h1G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h1Slice0) (forall_cons (fun _ h => by cases h; exact h1Slice1) (forall_cons (fun _ h => by cases h; exact h1Slice2) (forall_cons (fun _ h => by cases h; exact h1Slice3) (forall_cons (fun _ h => by cases h; exact h1Slice4) (forall_cons (fun _ h => by cases h; exact h1Slice5) (forall_cons (fun _ h => by cases h; exact h1Slice6) (forall_cons (fun _ h => by cases h; exact h1Slice7) (forall_cons (fun _ h => by cases h; exact h1Slice8) (forall_cons (fun _ h => by cases h; exact h1Slice9) (fun _ h => (List.not_mem_nil h).elim)))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h1R h1G c) h1Pools := buildPoolsBT_sound h1SlicesOk
def h1Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G (4 - 1) xs.toFinset) h1Empty := trivial
def h1Block4_0 : List NodeSpec := nodesWithIdentity [([3,4,5,6,7],[]),([0,1,2,3,17],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test4_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 4 h1Block4_0 = true := by decide +kernel
def h1Nodes4 : List NodeSpec := h1Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check4 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Empty 4 h1Nodes4 = true := h1Test4_0
def h1Bucket4 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 4 xs.toFinset) h1Bucket4 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1EmptyOk h1Check4
def h1Block5_0 : List NodeSpec := nodesWithIdentity [([1,2,3,4,5,6],[1,2]),([0,1,2,3,4,9],[7,8,9,10]),([0,1,2,3,4,13],[]),([0,1,3,4,6,7],[0]),([0,1,3,4,6,10],[]),([0,1,2,3,6,11],[9]),([0,1,2,3,4,12],[9,10]),([0,1,2,3,6,8],[10]),([0,1,2,3,11,14],[]),([0,1,2,3,4,18],[7,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test5_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Block5_0 = true := by decide +kernel
def h1Nodes5 : List NodeSpec := h1Block5_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check5 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket4 5 h1Nodes5 = true := h1Test5_0
def h1Bucket5 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 5 xs.toFinset) h1Bucket5 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket4Ok h1Check5
def h1Block6_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,4,5,6,7,8,9,10],[0,1]),([0,1,2,3,4,6],[0,1,2,6,7,8,9,10,11],[0]),([0,1,2,3,4,14],[0,1,2,6,7,8,9,10,12],[0,1]),([0,1,2,4,15],[0,2,3,7,8,13,14,15],[0]),([0,1,2,4,16],[0,2,7,16,17,18,19],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test6_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Block6_0 = true := by decide +kernel
def h1Nodes6 : List NodeSpec := h1Block6_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check6 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket5 6 h1Nodes6 = true := h1Test6_0
def h1Bucket6 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 6 xs.toFinset) h1Bucket6 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket5Ok h1Check6
def h1Block7_0 : List NodeSpec := [([0,1,2,3,4],[0,1,7,8,9,10],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Test7_0 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket6 7 h1Block7_0 = true := by decide +kernel
def h1Nodes7 : List NodeSpec := h1Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Check7 : checkNodesBT h1W h1G h1Mask h1Pools h1Autos h1Bucket6 7 h1Nodes7 = true := h1Test7_0
def h1Bucket7 : BT (List (List Nat)) := buildBucketsBT h1W h1Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h1G 7 xs.toFinset) h1Bucket7 := buildBucketsBT_sound (by decide) h1Pairs h1WOk h1PoolsOk h1AutosOk h1Bucket6Ok h1Check7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h1Bound : Lower h1R h1G 8 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17)]) (by decide +kernel) h1Bucket7Ok (by decide +kernel)
namespace Cofactor12086
def G_0 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_0 : List Nat := varsOf 22
def pos_0 : List Nat := [6,6,18,18,20,20,6,18,20]
def neg_0 : List Nat := [4,2,16,2,16,4,16,4,2]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(0,3),(0,4),(0,2),(0,1)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0

def G_3 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def R_3 : List Nat := varsOf 19
lemma low_3_ok : carryOK [(0,2),(0,1)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0

def G_6 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def R_6 : List Nat := varsOf 21
lemma low_6_ok : carryOK [(0,1)] R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 4 := carry_of low_6_ok low_0

def G_17 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
def R_17 : List Nat := varsOf 23
def pos_17 : List Nat := [3,3,5,5,6,6,17,17,18,18,20,20,3,3,5,5,6,6,17,17,18,18,20,20]
def neg_17 : List Nat := [2,1,4,1,4,2,16,1,16,2,16,4,4,16,2,16,1,16,2,4,1,4,1,2]
def fmask_17 : Nat := fullMask 24
def base_17 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffff0000ffff0000ffff0000ffff0000,0xfc0fc0,0x2a540)]
def steps_17 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_17 : BT Decor := buildWiresBT 4 base_17 steps_17
def autosL_17 : List (List (Nat × Nat)) := [[],[(2,4)],[(0,1)],[(2,4),(0,1)],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def autos_17 : BT (List (Nat × Nat)) := btOfList 4 autosL_17
def slicesL_17 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 1 0,4),some (subcubeFast 16 0,4),some (subcubeFast 4 0,4)]
def slices_17 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_17
def ps_17 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_17 : BT (Option BoundPool) := buildPoolsBT 2 W_17 R_17 slices_17 ps_17
lemma gp_17 : goodPairs G_17 pos_17 neg_17 := goodPairs_of (by decide +kernel)
lemma base_17_ok : ∀ x ∈ base_17, faithful pos_17 neg_17 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_17_ok : btAll (fun x => faithful pos_17 neg_17 x ∧ x.1 < 2^128) W_17 := buildWiresBT_faithful base_17_ok
set_option maxRecDepth 500000 in
lemma autos_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_17 = G_17) autos_17 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_17_0_ok : sliceDirectCheck 2 0 0 R_17 G_17 R_6 G_6 = true := by decide +kernel
lemma sl_17_0 : Slice R_17 G_17 (subcubeFast 2 0) 4 := slice_fast_direct sl_17_0_ok low_6
lemma sl_17_1_ok : sliceDirectCheck 1 0 0 R_17 G_17 R_0 G_0 = true := by decide +kernel
lemma sl_17_1 : Slice R_17 G_17 (subcubeFast 1 0) 4 := slice_fast_direct sl_17_1_ok low_0
lemma sl_17_2_ok : sliceDirectCheck 16 0 0 R_17 G_17 R_1 G_1 = true := by decide +kernel
lemma sl_17_2 : Slice R_17 G_17 (subcubeFast 16 0) 4 := slice_fast_direct sl_17_2_ok low_1
lemma sl_17_3_ok : sliceDirectCheck 4 0 0 R_17 G_17 R_3 G_3 = true := by decide +kernel
lemma sl_17_3 : Slice R_17 G_17 (subcubeFast 4 0) 4 := slice_fast_direct sl_17_3_ok low_3
set_option maxRecDepth 500000 in
lemma slices_17_ok : btAll (fun o => ∀ p, o = some p → Slice R_17 G_17 p.1 p.2) slices_17 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_17 G_17 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_17_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_17 G_17 c) P_17 := buildPoolsBT_sound slices_17_ok
def bk_17_init : BT (List (List Nat)) := BT.empty
lemma bk_17_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 (0 - 1) xs.toFinset) bk_17_init := trivial
def nodes_17_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_0 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_init 0 nodes_17_0 = true := by decide +kernel
def bk_17_0 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_0
set_option maxRecDepth 500000 in
lemma bk_17_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 0 xs.toFinset) bk_17_0 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_init_ok chk_17_0
def nodes_17_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_1 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_0 1 nodes_17_1 = true := by decide +kernel
def bk_17_1 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_1
set_option maxRecDepth 500000 in
lemma bk_17_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 1 xs.toFinset) bk_17_1 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_0_ok chk_17_1
def nodes_17_2 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_2 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_1 2 nodes_17_2 = true := by decide +kernel
def bk_17_2 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_2
set_option maxRecDepth 500000 in
lemma bk_17_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 2 xs.toFinset) bk_17_2 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_1_ok chk_17_2
def nodes_17_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_3 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_2 3 nodes_17_3 = true := by decide +kernel
def bk_17_3 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_3
set_option maxRecDepth 500000 in
lemma bk_17_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 3 xs.toFinset) bk_17_3 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_2_ok chk_17_3
def nodes_17_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_4 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_3 4 nodes_17_4 = true := by decide +kernel
def bk_17_4 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_4
set_option maxRecDepth 500000 in
lemma bk_17_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 4 xs.toFinset) bk_17_4 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_3_ok chk_17_4
def nodes_17_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_5 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_4 5 nodes_17_5 = true := by decide +kernel
def bk_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_5
set_option maxRecDepth 500000 in
lemma bk_17_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 5 xs.toFinset) bk_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_4_ok chk_17_5
def nodes_17_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_6 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_5 6 nodes_17_6 = true := by decide +kernel
def bk_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_6
set_option maxRecDepth 500000 in
lemma bk_17_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 6 xs.toFinset) bk_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_5_ok chk_17_6
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck R_17 G_17 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT bk_17_6 R_17 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_17 : Lower R_17 G_17 7 := lower_of_forestBT root_17_ok bk_17_6_ok root_17_in

end Cofactor12086
def h13R : List Nat := varsOf 15
def h13G : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h13Bound : Lower h13R h13G 7 := carry_of (swaps := [(3,4)]) (roots2 := Cofactor12086.R_17) (T2 := Cofactor12086.G_17) (by decide +kernel) Cofactor12086.low_17
def h12R : List Nat := varsOf 47
def h12G : Nat := 0xfee8fee8ece8ece8fee8fee8ece8ece8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h12Bound : Lower h12R h12G 8 := lift_of (z := 0) (o := 32) (essPairs := [(VAR 5,9,41)]) (by decide +kernel) h13Bound
def h14R : List Nat := varsOf 51
def h14G : Nat := 0xeeee8888aaaa8888eeee8888aaaa8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h14Bound : Lower h14R h14G 5 := carry_of (swaps := [(3,4),(4,5),(3,4),(1,2)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h15R : List Nat := varsOf 53
def h15G : Nat := 0xfafaa0a0aaaaa0a0fafaa0a0aaaaa0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h15Bound : Lower h15R h15G 5 := carry_of (swaps := [(3,4),(4,5),(3,4)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h17R : List Nat := varsOf 38
def h17G : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h17Bound : Lower h17R h17G 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h16R : List Nat := varsOf 54
def h16G : Nat := 0xfcfcc0c0c0c0c0c0fcfcc0c0c0c0c0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h16Bound : Lower h16R h16G 5 := lift_of (z := 0) (o := 16) (essPairs := [(VAR 4,34,50)]) (by decide +kernel) h17Bound
def h18R : List Nat := varsOf 23
def h18G : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h18Bound : Lower h18R h18G 7 := carry_of (swaps := [(3,4)]) (roots2 := h13R) (T2 := h13G) (by decide +kernel) h13Bound
def h19R : List Nat := varsOf 55
def h19G : Nat := 0xfefee8e8eaeae8e8fefee8e8eaeae8e8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h19Bound : Lower h19R h19G 8 := carry_of (swaps := [(3,4),(0,1)]) (roots2 := h12R) (T2 := h12G) (by decide +kernel) h12Bound
def h20R : List Nat := varsOf 27
def h20G : Nat := 0xffeeee88ffeeee88ffeeee88ffeeee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h20Bound : Lower h20R h20G 7 := carry_of (swaps := [(3,4),(2,3)]) (roots2 := h13R) (T2 := h13G) (by decide +kernel) h13Bound
def h21R : List Nat := varsOf 51
def h21G : Nat := 0xffffeeeeeeeeccccffffeeeeeeeecccc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h21Bound : Lower h21R h21G 5 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h23R : List Nat := varsOf 43
def h23G : Nat := 0xee88ee88cc88cc88ee88ee88cc88cc88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h23Bound : Lower h23R h23G 5 := carry_of (swaps := [(3,4),(4,5),(1,2),(0,1)]) (roots2 := h7R) (T2 := h7G) (by decide +kernel) h7Bound
def h24R : List Nat := varsOf 19
def h24G : Nat := 0xeeee8888eeee8888eeee8888eeee8888
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h24Bound : Lower h24R h24G 4 := carry_of (swaps := [(2,3),(3,4)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h25R : List Nat := varsOf 49
def h25G : Nat := 0xffffaaaaaaaa0000ffffaaaaaaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h25Bound : Lower h25R h25G 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h26R : List Nat := varsOf 57
def h26G : Nat := 0xffaaaa00aaaa0000ffaaaa00aaaa0000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h26Bound : Lower h26R h26G 5 := carry_of (swaps := [(2,3),(3,4),(0,1)]) (roots2 := h16R) (T2 := h16G) (by decide +kernel) h16Bound
def h27R : List Nat := varsOf 26
def h27G : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h27Bound : Lower h27R h27G 4 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h28R : List Nat := varsOf 42
def h28G : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h28Bound : Lower h28R h28G 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h29R : List Nat := varsOf 58
def h29G : Nat := 0xffcccc00cc00cc00ffcccc00cc00cc00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h29Bound : Lower h29R h29G 5 := carry_of (swaps := [(2,3)]) (roots2 := h16R) (T2 := h16G) (by decide +kernel) h16Bound
def h30R : List Nat := varsOf 43
def h30G : Nat := 0xffeeffeeeeaaeeaaffeeffeeeeaaeeaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h30Bound : Lower h30R h30G 5 := carry_of (swaps := [(3,4),(4,5),(2,3)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h22R : List Nat := varsOf 59
def h22G : Nat := 0xffeeee88eeaacc88ffeeee88eeaacc88
def h22Pos : List Nat := [10,17,10,10,25,41,41,50,17,50,41,3,50,3,25,26,11,17,11,26,42,56,56,19,35,35,17,10,56,3,42,19,3,3,49,10,11,49,3,35,41,17,25]
def h22Neg : List Nat := [8,16,9,2,24,33,40,34,1,18,9,2,48,1,9,18,9,18,2,24,40,40,24,18,34,33,24,18,48,0,34,1,18,9,48,0,1,33,33,1,1,0,1]
def h22Mask : Nat := fullMask 43
def h22Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x7f7a7876d72,0x5f282016524),(0xcccccccccccccccccccccccccccccccc,0xdbeb9dba8d,0x149868a88),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x518587dc47d,0x204794455),(0xffff0000ffff0000ffff0000ffff0000,0x62494ead392,0x51cca9212),(0xffffffff00000000ffffffff00000000,0x1a4537016e0,0x64533010e0)]
def h22Steps : List (Nat × Nat × Nat) := [(0,0,1),(1,0,1),(2,0,1),(0,0,2),(1,0,2),(2,0,2),(3,0,2),(0,0,3),(1,0,3),(2,0,3),(3,0,3),(0,1,2),(1,1,2),(2,1,2),(3,1,2),(3,1,3),(0,2,3),(1,2,3),(2,2,3),(1,2,5),(2,2,5),(2,4,5),(1,1,11),(3,0,27),(0,2,6),(2,2,6),(0,4,6),(2,4,6),(1,0,21),(1,1,33),(3,1,33),(2,6,21),(1,0,29),(1,1,29),(0,4,9),(2,4,10),(0,4,17),(1,11,20),(1,1,12),(0,2,43),(1,2,43),(2,2,43),(3,2,43),(2,1,12),(1,2,12),(2,2,12),(2,4,12),(1,12,16),(1,12,41),(3,12,17),(1,12,18),(2,4,44),(0,4,45),(3,1,13),(0,4,13),(1,1,59),(2,1,59),(1,2,59),(2,2,59),(2,17,59),(0,13,17),(2,13,18),(0,2,60),(3,2,60),(1,1,14),(1,14,18),(0,4,22),(1,1,23)]
def h22W : BT Decor := buildWiresBT 7 h22Base h22Steps
def h22AutoList : List (List (Nat × Nat)) := [[],[(3,4),(0,1)]]
def h22Autos : BT (List (Nat × Nat)) := btOfList 1 h22AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Pairs : goodPairs h22G h22Pos h22Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22BaseOk : ∀ x ∈ h22Base, faithful h22Pos h22Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22WOk : btAll (fun x => faithful h22Pos h22Neg x ∧ x.1 < 2^128) h22W := buildWiresBT_faithful h22BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h22G = h22G) h22Autos := btAll_ofList (autos_of (by decide +kernel))
def h22SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,5),some (subcubeFast 0 16,5),some (subcubeFast 0 32,7),some (subcubeFast 1 0,5),some (subcubeFast 1 16,4),some (subcubeFast 1 32,4),some (subcubeFast 2 0,5),some (subcubeFast 2 8,4),some (subcubeFast 8 0,5),some (subcubeFast 8 32,4),some (subcubeFast 16 0,5),some (subcubeFast 32 0,4)]
def h22Slices : BT (Option (Nat × Nat)) := btOfList 4 h22SliceList
def h22Specs : List PoolSpec := [(3,[]),(6,[]),(2,[(0,0,1)]),(4,[]),(2,[(0,0,1),(1,2,5)]),(0,[]),(2,[(0,0,1),(2,2,5)]),(8,[]),(1,[]),(10,[]),(2,[]),(11,[]),(5,[]),(7,[]),(0,[(1,0,1)]),(2,[(1,0,1)]),(2,[(2,0,1)]),(2,[(0,0,2)]),(2,[(1,0,1),(0,2,6),(1,1,29)]),(2,[(1,0,2)]),(2,[(2,0,2)]),(8,[(2,4,10)]),(2,[(3,0,2)]),(1,[(3,0,2)]),(8,[(0,4,17)]),(6,[(0,4,17)]),(9,[]),(2,[(3,0,2),(1,1,2)]),(2,[(0,0,3)]),(2,[(1,0,1),(0,2,6),(1,0,29)]),(2,[(0,1,2)]),(1,[(2,4,12)]),(1,[(1,1,12)]),(2,[(0,0,3),(1,1,12)]),(2,[(1,1,2)]),(2,[(2,1,2)]),(2,[(3,1,2)]),(2,[(0,0,3),(2,1,12)]),(2,[(0,0,3),(1,2,12)]),(2,[(0,0,3),(2,2,12)]),(2,[(1,0,3)]),(10,[(0,4,13)]),(3,[(0,4,13)]),(2,[(2,0,3)]),(2,[(2,0,3),(1,1,14)]),(2,[(3,0,3)]),(2,[(0,2,3)]),(2,[(0,2,3),(1,0,21)]),(2,[(1,2,3)]),(8,[(0,4,22)]),(10,[(0,4,22)]),(2,[(2,2,3)])]
def h22Pools : BT (Option BoundPool) := buildPoolsBT 6 h22W h22R h22Slices h22Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice11 : Slice h22R h22G (subcubeFast 32 0) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h5Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice10 : Slice h22R h22G (subcubeFast 16 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h23Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice9 : Slice h22R h22G (subcubeFast 8 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h24Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice8 : Slice h22R h22G (subcubeFast 8 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice7 : Slice h22R h22G (subcubeFast 2 8) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h25Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice6 : Slice h22R h22G (subcubeFast 2 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h26Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice5 : Slice h22R h22G (subcubeFast 1 32) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h27Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice4 : Slice h22R h22G (subcubeFast 1 16) 4 := slice_fast_direct (zDead := 0) (by decide +kernel) h28Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice3 : Slice h22R h22G (subcubeFast 1 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h29Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice2 : Slice h22R h22G (subcubeFast 0 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice1 : Slice h22R h22G (subcubeFast 0 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h30Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Slice0 : Slice h22R h22G (subcubeFast 0 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h22R h22G p.1 p.2) h22Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h22R h22G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h22Slice0) (forall_cons (fun _ h => by cases h; exact h22Slice1) (forall_cons (fun _ h => by cases h; exact h22Slice2) (forall_cons (fun _ h => by cases h; exact h22Slice3) (forall_cons (fun _ h => by cases h; exact h22Slice4) (forall_cons (fun _ h => by cases h; exact h22Slice5) (forall_cons (fun _ h => by cases h; exact h22Slice6) (forall_cons (fun _ h => by cases h; exact h22Slice7) (forall_cons (fun _ h => by cases h; exact h22Slice8) (forall_cons (fun _ h => by cases h; exact h22Slice9) (forall_cons (fun _ h => by cases h; exact h22Slice10) (forall_cons (fun _ h => by cases h; exact h22Slice11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h22R h22G c) h22Pools := buildPoolsBT_sound h22SlicesOk
def h22Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G (4 - 1) xs.toFinset) h22Empty := trivial
def h22Block4_0 : List NodeSpec := nodesWithIdentity [([2,3,4,37,43],[]),([1,2,3,37,51],[]),([2,3,4,28,43],[]),([0,2,3,41,43],[]),([0,1,2,3,53],[]),([0,2,3,43,56],[]),([0,2,3,43,57],[]),([0,1,2,3,64],[]),([0,1,3,59,67],[]),([0,1,3,59,68],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test4_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Empty 4 h22Block4_0 = true := by decide +kernel
def h22Nodes4 : List NodeSpec := h22Block4_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check4 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Empty 4 h22Nodes4 = true := h22Test4_0
def h22Bucket4 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes4
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket4Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 4 xs.toFinset) h22Bucket4 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22EmptyOk h22Check4
def h22Block5_0 : List NodeSpec := nodesWithIdentity [([0,2,3,4,6,27],[7,10]),([1,2,3,4,6,33],[1,9]),([0,1,2,3,4,34],[5,7,10,11]),([0,1,2,3,4,36],[]),([0,1,3,11,41],[5,24,25]),([0,1,2,3,4,42],[]),([1,2,3,4,12,37],[1,7,14,29]),([0,1,2,3,16,51],[0,9,11,12,31]),([0,1,2,3,4,52],[0,1,10,11]),([1,2,3,4,12,28],[5]),([0,2,3,4,17,43],[0,9,32,33]),([0,1,2,3,17,51],[11,12]),([0,1,2,3,12,41],[5,11,24,25]),([0,1,2,3,4,54],[0,10,11]),([0,2,3,4,18,43],[]),([0,1,2,3,18,51],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_0 = true := by decide +kernel
def h22Block5_1 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,55],[0]),([0,2,3,4,19,43],[0]),([0,1,2,3,19,51],[]),([0,2,3,4,43,44],[0,9,32,33]),([0,2,3,4,43,45],[0,9,32,33]),([0,2,3,4,43,46],[]),([0,2,3,4,43,47],[]),([0,1,2,3,17,59],[11]),([0,1,2,3,4,65],[10,11]),([0,1,2,3,18,59],[8,41]),([0,1,2,3,4,66],[]),([0,2,3,4,19,58],[5]),([0,1,2,3,19,59],[]),([0,1,2,3,59,60],[]),([0,1,2,3,59,61],[8,40]),([0,1,2,3,59,62],[11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_1 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_1 = true := by decide +kernel
def h22Block5_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,59,63],[]),([0,1,2,3,4,60],[5,7,8]),([0,1,2,3,4,70],[]),([0,1,2,3,4,35],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test5_2 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Block5_2 = true := by decide +kernel
def h22Nodes5 : List NodeSpec := h22Block5_0 ++ h22Block5_1 ++ h22Block5_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check5 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket4 5 h22Nodes5 = true := by
  unfold h22Nodes5 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h22Test5_0,h22Test5_1⟩,h22Test5_2⟩
def h22Bucket5 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes5
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket5Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 5 xs.toFinset) h22Bucket5 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket4Ok h22Check5
def h22Block6_0 : List NodeSpec := [([0,1,3,4,24],[0,1,4,5],[0]),([0,1,3,4,25],[0,1,6,7],[0]),([0,1,2,3,26],[0,1,2,3,11,12],[0]),([0,1,2,3,4,6,11],[1,5,7,14],[0]),([0,1,2,3,4,6,21],[0,1,5,7,8,9],[0,1]),([0,1,2,3,4,6,29],[0,1,5,7,13],[0]),([0,1,2,3,4,6,30],[5,7,13],[0]),([0,1,2,3,4,31],[0,1,5,7,8,9,10,11,15],[0]),([0,1,2,3,4,32],[5,7,8,9,11,12,15],[0]),([0,1,2,3,4,6],[0,5,7,8,9,10,11,15],[0]),([0,1,2,3,4,38],[0,1,3,7,8,9,10,11,18],[0]),([0,1,2,3,4,39],[0,1,5,7,8,9,10,11,13,19],[0]),([0,1,2,3,40],[0,3,5,11,12,20,21],[0]),([0,1,3,4,11,17],[0,1,5,7,23,26,27],[0]),([0,1,2,3,4,11,20],[3,5,7,8,9],[0]),([0,1,2,3,4,27],[0,1,5,7,8,9,10,11,13],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_0 = true := by decide +kernel
def h22Block6_1 : List NodeSpec := [([0,1,2,3,4,12,16],[0,1,5,7,8,9,28,30],[0,1]),([0,1,2,3,4,12,17],[0,1,5,7,8,9,28,34],[0]),([0,1,2,3,4,12,18],[0,1,5,7,35],[0]),([0,1,2,3,4,12,19],[0,1,5,7,13,36],[0]),([0,2,3,4,43],[0,9,33],[0]),([0,1,2,3,4,43],[0,1,5,7,9,10,11,33],[0,1]),([0,2,3,4,48],[0,1,9,37],[0]),([0,1,3,4,49],[0,5,9,38],[0]),([0,1,3,4,50],[0,7,9,39],[0]),([0,1,2,3,51],[0,9,11,12,28],[0]),([0,1,2,3,4,13,17],[5,8,34,40],[0,1]),([0,1,2,3,4,13,18],[1,5,7,8,9,35],[0]),([0,1,2,3,4,13,19],[1,7,8,13,36],[0]),([0,1,2,3,4,58],[0,1,3,5,7,8,9,10,11],[0,1]),([0,1,2,3,59],[3,8,11,40,41,42],[0,1]),([0,1,2,3,4,59],[0,1,5,7,8,9,10,11,40],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_1 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_1 = true := by decide +kernel
def h22Block6_2 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,14,18],[0,1]),([0,1,2,3,4,14,19],[0,5,7,13]),([0,1,2,3,4,69],[0,1,5,7,8,10,11,44]),([0,1,2,3,4,15,19],[3,7,9]),([0,1,2,3,4,33],[0,1,3,5,7,9,10,11,47]),([0,1,2,3,71],[3,5,8,11,13,48,49,50]),([0,1,2,3,4,71],[0,1,3,5,7,10,11,13,48]),([0,1,2,3,4,72],[0,1,3,5,7,8,10,11])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test6_2 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Block6_2 = true := by decide +kernel
def h22Nodes6 : List NodeSpec := h22Block6_0 ++ h22Block6_1 ++ h22Block6_2
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check6 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket5 6 h22Nodes6 = true := by
  unfold h22Nodes6 checkNodesBT
  simp only [List.all_append, Bool.and_eq_true]
  exact ⟨⟨h22Test6_0,h22Test6_1⟩,h22Test6_2⟩
def h22Bucket6 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes6
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket6Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 6 xs.toFinset) h22Bucket6 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket5Ok h22Check6
def h22Block7_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,3,5,7,8,9,10,12],[0,1]),([0,1,2,3,4,6],[0,1,3,5,7,8,9,10,13,15],[0,1]),([0,1,2,3,4,7],[0,1,3,5,7,8,9,10,12,13,16],[0]),([0,1,2,3,4,8],[0,1,3,7,8,9,10,12,17],[0]),([0,1,2,3,4,9],[0,1,3,5,7,8,9,10,13,19],[0]),([0,1,2,3,4,10],[0,1,3,5,7,8,9,10,12,13,20],[0]),([0,1,2,3,4,11],[0,1,3,5,7,8,9,10,13,22,26],[0]),([0,1,2,3,4,12],[0,1,5,7,9,10,12,28],[0]),([0,1,2,3,4,13],[0,1,3,5,7,8,9,10,40],[0,1]),([0,1,2,3,4,14],[0,1,5,7,8,9,10,12,43],[0,1]),([0,1,2,3,4,15],[0,1,3,5,7,8,9,10,45],[0,1]),([0,1,2,3,4,21],[0,1,3,5,7,9,10,13,26,46],[0,1]),([0,1,2,3,4,22],[0,1,3,5,7,8,9,10,13,48],[0]),([0,1,2,3,4,23],[0,1,3,5,7,8,9,10,26,51],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test7_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket6 7 h22Block7_0 = true := by decide +kernel
def h22Nodes7 : List NodeSpec := h22Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check7 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket6 7 h22Nodes7 = true := h22Test7_0
def h22Bucket7 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 7 xs.toFinset) h22Bucket7 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket6Ok h22Check7
def h22Block8_0 : List NodeSpec := [([0,1,2,3,4],[10],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Test8_0 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket7 8 h22Block8_0 = true := by decide +kernel
def h22Nodes8 : List NodeSpec := h22Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Check8 : checkNodesBT h22W h22G h22Mask h22Pools h22Autos h22Bucket7 8 h22Nodes8 = true := h22Test8_0
def h22Bucket8 : BT (List (List Nat)) := buildBucketsBT h22W h22Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h22G 8 xs.toFinset) h22Bucket8 := buildBucketsBT_sound (by decide) h22Pairs h22WOk h22PoolsOk h22AutosOk h22Bucket7Ok h22Check8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h22Bound : Lower h22R h22G 9 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,9,41)]) (by decide +kernel) h22Bucket8Ok (by decide +kernel)
def h31R : List Nat := varsOf 45
def h31G : Nat := 0xfffafffafaaafaaafffafffafaaafaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h31Bound : Lower h31R h31G 5 := carry_of (swaps := [(3,4),(4,5),(2,3),(1,2)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h32R : List Nat := varsOf 53
def h32G : Nat := 0xfffffafafafaa0a0fffffafafafaa0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h32Bound : Lower h32R h32G 7 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2)]) (roots2 := h13R) (T2 := h13G) (by decide +kernel) h13Bound
def h33R : List Nat := varsOf 57
def h33G : Nat := 0xffffffaaffaaaaaaffffffaaffaaaaaa
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h33Bound : Lower h33R h33G 5 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(2,3)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
namespace Cofactor12116
def G_0 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def R_0 : List Nat := varsOf 44
def pos_0 : List Nat := [12,12,36,36,40,40,12,36,40]
def neg_0 : List Nat := [8,4,32,4,32,8,32,8,4]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xcf,0x10a),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x173,0xa1),(0xffffffff00000000ffffffff00000000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 2,12,8),(VAR 3,12,4),(VAR 5,36,4)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in

def G_8 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def R_8 : List Nat := varsOf 14
lemma low_8_ok : carryOK [(1,4),(1,5),(1,3),(1,2)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0

def G_9 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_9 : List Nat := varsOf 22
lemma low_9_ok : carryOK [(4,5),(1,3),(1,2)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0

def G_10 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_10 : List Nat := varsOf 38
lemma low_10_ok : carryOK [(1,3),(1,2)] R_10 G_10 R_0 G_0 = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 4 := carry_of low_10_ok low_0

def G_13 : Nat := 0xffcccc00ffcccc00ffcccc00ffcccc00
def R_13 : List Nat := varsOf 26
lemma low_13_ok : carryOK [(4,5),(1,2)] R_13 G_13 R_0 G_0 = true := by decide +kernel
lemma low_13 : Lower R_13 G_13 4 := carry_of low_13_ok low_0

def G_14 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def R_14 : List Nat := varsOf 42
lemma low_14_ok : carryOK [(1,2)] R_14 G_14 R_0 G_0 = true := by decide +kernel
lemma low_14 : Lower R_14 G_14 4 := carry_of low_14_ok low_0

def G_15 : Nat := 0xfff0f000fff0f000fff0f000fff0f000
def R_15 : List Nat := varsOf 28
lemma low_15_ok : carryOK [(4,5)] R_15 G_15 R_0 G_0 = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 4 := carry_of low_15_ok low_0

def G_17 : Nat := 0xffffcccccccc0000ffffcccccccc0000
def R_17 : List Nat := varsOf 50
lemma low_17_ok : carryOK [(3,4),(1,2)] R_17 G_17 R_0 G_0 = true := by decide +kernel
lemma low_17 : Lower R_17 G_17 4 := carry_of low_17_ok low_0

def G_18 : Nat := 0xfffff0f0f0f00000fffff0f0f0f00000
def R_18 : List Nat := varsOf 52
lemma low_18_ok : carryOK [(3,4)] R_18 G_18 R_0 G_0 = true := by decide +kernel
lemma low_18 : Lower R_18 G_18 4 := carry_of low_18_ok low_0

def G_20 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
def R_20 : List Nat := varsOf 46
def pos_20 : List Nat := [14,14,14,38,38,38,42,42,42,44,44,44,14,14,14,38,38,38,42,42,42,44,44,44]
def neg_20 : List Nat := [12,10,6,36,34,6,40,34,10,40,36,12,34,36,40,10,12,40,6,12,36,6,10,34]
def fmask_20 : Nat := fullMask 24
def base_20 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_20 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def W_20 : BT Decor := buildWiresBT 4 base_20 steps_20
def autosL_20 : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)],[(2,3)],[(2,5),(2,3)],[(1,2),(1,3)],[(2,5),(1,2),(1,3)],[(2,5),(1,3)]]
def autos_20 : BT (List (Nat × Nat)) := btOfList 4 autosL_20
def slicesL_20 : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def slices_20 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_20
def ps_20 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_20 : BT (Option BoundPool) := buildPoolsBT 2 W_20 R_20 slices_20 ps_20
lemma gp_20 : goodPairs G_20 pos_20 neg_20 := goodPairs_of (by decide +kernel)
lemma base_20_ok : ∀ x ∈ base_20, faithful pos_20 neg_20 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_20_ok : btAll (fun x => faithful pos_20 neg_20 x ∧ x.1 < 2^128) W_20 := buildWiresBT_faithful base_20_ok
set_option maxRecDepth 500000 in
lemma autos_20_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_20 = G_20) autos_20 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_20_0_ok : sliceDirectCheck 0 8 0 R_20 G_20 R_10 G_10 = true := by decide +kernel
lemma sl_20_0 : Slice R_20 G_20 (subcubeFast 0 8) 4 := slice_fast_direct sl_20_0_ok low_10
lemma sl_20_1_ok : sliceDirectCheck 0 2 0 R_20 G_20 R_0 G_0 = true := by decide +kernel
lemma sl_20_1 : Slice R_20 G_20 (subcubeFast 0 2) 4 := slice_fast_direct sl_20_1_ok low_0
lemma sl_20_2_ok : sliceDirectCheck 0 4 0 R_20 G_20 R_14 G_14 = true := by decide +kernel
lemma sl_20_2 : Slice R_20 G_20 (subcubeFast 0 4) 4 := slice_fast_direct sl_20_2_ok low_14
lemma sl_20_3_ok : sliceDirectCheck 0 32 0 R_20 G_20 R_8 G_8 = true := by decide +kernel
lemma sl_20_3 : Slice R_20 G_20 (subcubeFast 0 32) 4 := slice_fast_direct sl_20_3_ok low_8
set_option maxRecDepth 500000 in
lemma slices_20_ok : btAll (fun o => ∀ p, o = some p → Slice R_20 G_20 p.1 p.2) slices_20 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_20 G_20 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_20_0) (forall_cons (fun _ h => by cases h; exact sl_20_1) (forall_cons (fun _ h => by cases h; exact sl_20_2) (forall_cons (fun _ h => by cases h; exact sl_20_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_20_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_20 G_20 c) P_20 := buildPoolsBT_sound slices_20_ok
def bk_20_init : BT (List (List Nat)) := BT.empty
lemma bk_20_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 (0 - 1) xs.toFinset) bk_20_init := trivial
def nodes_20_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_20_0 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_init 0 nodes_20_0 = true := by decide +kernel
def bk_20_0 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_0
set_option maxRecDepth 500000 in
lemma bk_20_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 0 xs.toFinset) bk_20_0 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_init_ok chk_20_0
def nodes_20_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_20_1 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_0 1 nodes_20_1 = true := by decide +kernel
def bk_20_1 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_1
set_option maxRecDepth 500000 in
lemma bk_20_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 1 xs.toFinset) bk_20_1 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_0_ok chk_20_1
def nodes_20_2 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_20_2 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_1 2 nodes_20_2 = true := by decide +kernel
def bk_20_2 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_2
set_option maxRecDepth 500000 in
lemma bk_20_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 2 xs.toFinset) bk_20_2 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_1_ok chk_20_2
def nodes_20_3 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_20_3 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_2 3 nodes_20_3 = true := by decide +kernel
def bk_20_3 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_3
set_option maxRecDepth 500000 in
lemma bk_20_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 3 xs.toFinset) bk_20_3 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_2_ok chk_20_3
def nodes_20_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_20_4 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_3 4 nodes_20_4 = true := by decide +kernel
def bk_20_4 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_4
set_option maxRecDepth 500000 in
lemma bk_20_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 4 xs.toFinset) bk_20_4 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_3_ok chk_20_4
def nodes_20_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_20_5 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_4 5 nodes_20_5 = true := by decide +kernel
def bk_20_5 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_5
set_option maxRecDepth 500000 in
lemma bk_20_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 5 xs.toFinset) bk_20_5 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_4_ok chk_20_5
def nodes_20_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_20_6 : checkNodesBT W_20 G_20 fmask_20 P_20 autos_20 bk_20_5 6 nodes_20_6 = true := by decide +kernel
def bk_20_6 : BT (List (List Nat)) := buildBucketsBT W_20 nodes_20_6
set_option maxRecDepth 500000 in
lemma bk_20_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_20 6 xs.toFinset) bk_20_6 :=
  buildBucketsBT_sound (by decide) gp_20 W_20_ok P_20_ok autos_20_ok bk_20_5_ok chk_20_6
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_20_ok : forestRootCheck R_20 G_20 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_20_in : bucketContainsBT bk_20_6 R_20 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_20 : Lower R_20 G_20 7 := lower_of_forestBT root_20_ok bk_20_6_ok root_20_in

def G_21 : Nat := 0xfcc0fcc0fc00fc00fcc0fcc0fc00fc00
def R_21 : List Nat := varsOf 46
lemma low_21_ok : liftCheck 0 32 R_21 G_21 R_8 G_8 [(VAR 5,38,6)] = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 5 := lift_of low_21_ok low_8

def G_22 : Nat := 0xfff0f000f000f000fff0f000f000f000
def R_22 : List Nat := varsOf 60
lemma low_22_ok : liftCheck 0 16 R_22 G_22 R_0 G_0 [(VAR 4,52,36)] = true := by decide +kernel
lemma low_22 : Lower R_22 G_22 5 := lift_of low_22_ok low_0

def G_23 : Nat := 0xfffcfffcfcc0fcc0fffcfffcfcc0fcc0
def R_23 : List Nat := varsOf 46
def pos_23 : List Nat := [6,6,10,10,12,12,34,34,36,36,40,40,6,6,10,10,12,12,34,34,36,36,40,40]
def neg_23 : List Nat := [4,2,8,2,8,4,32,2,32,4,32,8,8,32,4,32,2,32,4,8,2,8,2,4]
def fmask_23 : Nat := fullMask 24
def base_23 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf0cf,0x51008a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x333333,0x844221),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xc3cc3c,0x281814),(0xffffffff00000000ffffffff00000000,0xfc0fc0,0x2a540)]
def steps_23 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_23 : BT Decor := buildWiresBT 4 base_23 steps_23
def autosL_23 : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)],[(2,3)],[(2,5),(2,3)],[(1,2),(1,3)],[(2,5),(1,2),(1,3)],[(2,5),(1,3)]]
def autos_23 : BT (List (Nat × Nat)) := btOfList 4 autosL_23
def slicesL_23 : List (Option (Nat × Nat)) := [some (subcubeFast 4 0,4),some (subcubeFast 2 0,4),some (subcubeFast 32 0,4),some (subcubeFast 8 0,4)]
def slices_23 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_23
def ps_23 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_23 : BT (Option BoundPool) := buildPoolsBT 2 W_23 R_23 slices_23 ps_23
lemma gp_23 : goodPairs G_23 pos_23 neg_23 := goodPairs_of (by decide +kernel)
lemma base_23_ok : ∀ x ∈ base_23, faithful pos_23 neg_23 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_23_ok : btAll (fun x => faithful pos_23 neg_23 x ∧ x.1 < 2^128) W_23 := buildWiresBT_faithful base_23_ok
set_option maxRecDepth 500000 in
lemma autos_23_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_23 = G_23) autos_23 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_23_0_ok : sliceDirectCheck 4 0 0 R_23 G_23 R_14 G_14 = true := by decide +kernel
lemma sl_23_0 : Slice R_23 G_23 (subcubeFast 4 0) 4 := slice_fast_direct sl_23_0_ok low_14
lemma sl_23_1_ok : sliceDirectCheck 2 0 0 R_23 G_23 R_0 G_0 = true := by decide +kernel
lemma sl_23_1 : Slice R_23 G_23 (subcubeFast 2 0) 4 := slice_fast_direct sl_23_1_ok low_0
lemma sl_23_2_ok : sliceDirectCheck 32 0 0 R_23 G_23 R_8 G_8 = true := by decide +kernel
lemma sl_23_2 : Slice R_23 G_23 (subcubeFast 32 0) 4 := slice_fast_direct sl_23_2_ok low_8
lemma sl_23_3_ok : sliceDirectCheck 8 0 0 R_23 G_23 R_10 G_10 = true := by decide +kernel
lemma sl_23_3 : Slice R_23 G_23 (subcubeFast 8 0) 4 := slice_fast_direct sl_23_3_ok low_10
set_option maxRecDepth 500000 in
lemma slices_23_ok : btAll (fun o => ∀ p, o = some p → Slice R_23 G_23 p.1 p.2) slices_23 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_23 G_23 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_23_0) (forall_cons (fun _ h => by cases h; exact sl_23_1) (forall_cons (fun _ h => by cases h; exact sl_23_2) (forall_cons (fun _ h => by cases h; exact sl_23_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_23_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_23 G_23 c) P_23 := buildPoolsBT_sound slices_23_ok
def bk_23_init : BT (List (List Nat)) := BT.empty
lemma bk_23_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 (0 - 1) xs.toFinset) bk_23_init := trivial
def nodes_23_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_23_0 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_init 0 nodes_23_0 = true := by decide +kernel
def bk_23_0 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_0
set_option maxRecDepth 500000 in
lemma bk_23_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 0 xs.toFinset) bk_23_0 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_init_ok chk_23_0
def nodes_23_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_23_1 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_0 1 nodes_23_1 = true := by decide +kernel
def bk_23_1 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_1
set_option maxRecDepth 500000 in
lemma bk_23_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 1 xs.toFinset) bk_23_1 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_0_ok chk_23_1
def nodes_23_2 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_23_2 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_1 2 nodes_23_2 = true := by decide +kernel
def bk_23_2 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_2
set_option maxRecDepth 500000 in
lemma bk_23_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 2 xs.toFinset) bk_23_2 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_1_ok chk_23_2
def nodes_23_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_23_3 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_2 3 nodes_23_3 = true := by decide +kernel
def bk_23_3 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_3
set_option maxRecDepth 500000 in
lemma bk_23_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 3 xs.toFinset) bk_23_3 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_2_ok chk_23_3
def nodes_23_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_23_4 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_3 4 nodes_23_4 = true := by decide +kernel
def bk_23_4 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_4
set_option maxRecDepth 500000 in
lemma bk_23_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 4 xs.toFinset) bk_23_4 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_3_ok chk_23_4
def nodes_23_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_23_5 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_4 5 nodes_23_5 = true := by decide +kernel
def bk_23_5 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_5
set_option maxRecDepth 500000 in
lemma bk_23_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 5 xs.toFinset) bk_23_5 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_4_ok chk_23_5
def nodes_23_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_23_6 : checkNodesBT W_23 G_23 fmask_23 P_23 autos_23 bk_23_5 6 nodes_23_6 = true := by decide +kernel
def bk_23_6 : BT (List (List Nat)) := buildBucketsBT W_23 nodes_23_6
set_option maxRecDepth 500000 in
lemma bk_23_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_23 6 xs.toFinset) bk_23_6 :=
  buildBucketsBT_sound (by decide) gp_23 W_23_ok P_23_ok autos_23_ok bk_23_5_ok chk_23_6
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_23_ok : forestRootCheck R_23 G_23 [(VAR 1,6,4),(VAR 2,6,2),(VAR 3,10,2),(VAR 5,34,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_23_in : bucketContainsBT bk_23_6 R_23 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_23 : Lower R_23 G_23 7 := lower_of_forestBT root_23_ok bk_23_6_ok root_23_in

def G_24 : Nat := 0xfffffff0fff0ff00fffffff0fff0ff00
def R_24 : List Nat := varsOf 60
lemma low_24_ok : liftCheck 8 0 R_24 G_24 R_18 G_18 [(VAR 3,8,0)] = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 5 := lift_of low_24_ok low_18

def G_41 : Nat := 0xfcc0fc00fcc0fc00fcc0fc00fcc0fc00
def R_41 : List Nat := varsOf 30
lemma low_41_ok : carryOK [(4,5)] R_41 G_41 R_21 G_21 = true := by decide +kernel
lemma low_41 : Lower R_41 G_41 5 := carry_of low_41_ok low_21

def G_42 : Nat := 0xfcfcc0c0c0c00000fcfcc0c0c0c00000
def R_42 : List Nat := varsOf 54
lemma low_42_ok : carryOK [(3,4)] R_42 G_42 R_20 G_20 = true := by decide +kernel
lemma low_42 : Lower R_42 G_42 7 := carry_of low_42_ok low_20

def G_48 : Nat := 0xffcccc00cc00cc00ffcccc00cc00cc00
def R_48 : List Nat := varsOf 58
lemma low_48_ok : carryOK [(1,2)] R_48 G_48 R_22 G_22 = true := by decide +kernel
lemma low_48 : Lower R_48 G_48 5 := carry_of low_48_ok low_22

def G_53 : Nat := 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0
def R_53 : List Nat := varsOf 30
lemma low_53_ok : carryOK [(4,5)] R_53 G_53 R_23 G_23 = true := by decide +kernel
lemma low_53 : Lower R_53 G_53 7 := carry_of low_53_ok low_23

def G_54 : Nat := 0xffffffccffccff00ffffffccffccff00
def R_54 : List Nat := varsOf 58
lemma low_54_ok : carryOK [(1,2)] R_54 G_54 R_24 G_24 = true := by decide +kernel
lemma low_54 : Lower R_54 G_54 5 := carry_of low_54_ok low_24

def G_60 : Nat := 0xfffcfcc0fcc0fc00fffcfcc0fcc0fc00
def R_60 : List Nat := varsOf 62
def pos_60 : List Nat := [10,10,12,12,14,22,22,22,26,26,28,28,38,38,38,42,42,44,44,50,50,50,52,52,52,56,56,56,10,10,10,10,10,10,10,10,12,12,12,12,12,12,12,12,22,22,22,22,22,38,38,38,38,38,50,50,50,50,50,52,52,52,52,52,56,56,56,56,56]
def neg_60 : List Nat := [8,2,8,4,6,20,18,6,24,18,24,20,36,34,6,40,34,40,36,48,34,18,48,36,20,48,40,24,6,18,20,24,34,36,40,48,6,18,20,24,34,36,40,48,24,34,36,40,48,18,20,24,40,48,6,20,24,36,40,6,18,24,34,40,6,18,20,34,36]
def fmask_60 : Nat := fullMask 69
def base_60 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x7fff00ff039f3f3,0xb58422131303162d2),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf83ffff001c67cfc,0x150ac44252518458b8),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x1f00000ffffe078f1f,0xa51894848c028505),(0xffff0000ffff0000ffff0000ffff0000,0x1fffc1f0000ff80fe0,0x631af18e8eb680f60),(0xffffffff00000000ffffffff00000000,0x1ffffe00000ffff000,0x18c631ef0f06dfb000)]
def steps_60 : List (Nat × Nat × Nat) := [(0,3,4),(3,0,3),(0,0,3),(2,0,2),(1,0,2),(0,0,1),(1,0,1),(3,2,3),(2,0,1),(1,0,5),(3,12,4),(3,12,0),(1,12,0),(3,1,4),(3,6,4),(0,6,4),(1,6,2),(3,6,1),(0,12,4),(0,1,4),(1,2,5),(3,7,1),(1,7,1),(0,8,3),(3,8,1),(3,2,4),(0,9,3),(0,1,9),(0,7,4),(0,1,3),(3,0,1),(2,13,2),(1,13,2),(3,1,3),(2,0,5),(1,7,2),(3,9,3),(3,13,3),(0,13,3),(2,10,2),(1,6,1),(3,7,4),(3,11,3),(0,11,3),(2,11,2),(1,10,2),(3,1,9),(3,8,3),(3,10,3),(1,11,2),(1,8,1),(0,10,3),(3,0,25),(2,0,25),(1,0,25),(0,0,25),(1,39,2),(1,39,1),(3,2,14),(1,1,5),(1,30,1),(1,18,2),(1,7,24),(1,33,2),(3,1,40),(0,40,4),(0,1,40),(1,26,2),(2,27,2),(2,1,5),(3,38,4),(3,34,4),(1,0,34),(2,9,5),(1,33,1),(0,9,4),(3,31,4),(0,31,4),(3,33,1),(2,1,31),(3,38,9),(3,40,4),(3,34,9),(1,34,2),(3,51,3),(3,1,14),(1,22,2),(0,32,3),(0,11,4),(3,10,11),(0,54,3),(2,11,5),(0,50,3),(1,13,34),(3,13,9),(1,34,9),(1,48,2),(3,48,4),(1,8,34),(3,50,3),(1,13,5),(0,34,4),(0,48,4),(3,56,4),(1,56,2),(2,0,34),(1,8,5),(1,10,5),(2,1,40),(3,32,3),(1,1,40),(1,11,5),(3,60,1),(1,60,1),(3,7,65),(2,67,2),(2,1,68),(0,1,68),(1,24,2),(0,115,4),(1,106,2),(3,39,9),(2,55,5),(2,1,82),(3,92,4),(0,0,88),(1,24,40),(3,71,4),(3,110,9),(3,23,11),(3,0,88),(2,49,5),(3,2,105),(1,23,13),(0,94,3),(3,24,40),(1,37,5),(0,1,59),(3,2,116),(3,39,11),(3,10,25),(1,107,2),(1,1,68),(2,54,5),(2,94,2),(3,13,25),(0,11,25),(3,1,59),(3,1,68),(2,50,5),(1,23,10),(1,51,34),(3,94,3),(1,94,2),(1,51,5),(3,44,11),(1,96,2),(3,74,9),(3,106,9),(3,2,112),(1,50,5),(3,60,59),(3,39,54),(3,157,4),(3,139,4),(1,94,5),(1,10,107),(3,71,115),(1,157,2),(3,12,94),(2,94,5),(1,12,94),(0,149,3),(1,139,2),(0,158,3),(0,157,4),(0,139,4),(3,158,3),(3,149,3),(3,174,4),(1,181,2),(0,11,165)]
def W_60 : BT Decor := buildWiresBT 8 base_60 steps_60
def autosL_60 : List (List (Nat × Nat)) := [[],[(4,5)],[(1,2)],[(4,5),(1,2)]]
def autos_60 : BT (List (Nat × Nat)) := btOfList 2 autosL_60
def slicesL_60 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,7),some (subcubeFast 0 32,7),some (subcubeFast 2 32,4),some (subcubeFast 4 32,4),some (subcubeFast 4 0,5),some (subcubeFast 0 2,5),some (subcubeFast 4 16,4),some (subcubeFast 8 2,4),some (subcubeFast 2 0,5),some (subcubeFast 8 0,7),some (subcubeFast 16 0,5),some (subcubeFast 32 0,5),some (subcubeFast 0 4,5),some (subcubeFast 8 32,4),some (subcubeFast 32 16,4),some (subcubeFast 16 32,4),some (subcubeFast 8 4,4),some (subcubeFast 2 16,4),some (subcubeFast 8 16,4)]
def slices_60 : BT (Option (Nat × Nat)) := btOfList 5 slicesL_60
def ps_60 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(9,[(0,0,3),(0,7,4)]),(10,[]),(11,[]),(12,[]),(1,[(1,0,2),(1,0,5),(1,2,5)]),(13,[]),(14,[]),(15,[]),(16,[]),(1,[(1,0,1),(1,11,5),(3,2,116)]),(1,[(1,0,1),(1,0,5),(1,1,5)]),(1,[(1,0,1),(1,11,2),(2,54,5)]),(1,[(1,0,2),(1,9,5),(3,1,59)]),(1,[(1,2,5),(3,0,25)]),(9,[(0,3,4),(2,0,5)]),(1,[(1,0,5),(3,2,14)]),(1,[(1,0,5),(1,2,5)]),(1,[(1,0,5),(1,1,5)]),(17,[]),(9,[(0,0,3),(3,7,1)]),(9,[(0,3,4),(2,1,5)]),(9,[(0,1,3),(0,3,4)]),(9,[(0,1,3),(3,34,4)]),(1,[(1,0,2),(2,9,5)]),(0,[(1,0,2),(2,9,5)]),(9,[(0,3,4),(2,9,5)]),(1,[(1,0,2),(1,9,5)]),(0,[(1,0,2),(1,2,5)]),(1,[(1,0,2),(1,2,5)]),(1,[(1,0,2),(1,0,5)]),(18,[]),(1,[(1,0,1),(1,0,5)]),(0,[(1,0,2),(3,34,9)]),(0,[(1,0,2),(1,34,2)]),(0,[(1,0,2),(3,1,9)]),(1,[(1,0,2),(3,1,9)]),(1,[(1,0,5),(3,1,14)]),(1,[(1,0,1),(2,11,5)]),(9,[(0,0,3),(0,3,4)]),(1,[(1,0,1),(1,11,2)]),(9,[(0,1,3),(0,34,4)]),(9,[(0,1,3),(2,0,34)]),(1,[(1,0,1),(2,11,2)]),(0,[(1,0,1),(2,11,2)]),(1,[(1,0,1),(1,0,2)]),(1,[(1,0,1),(1,11,5)]),(1,[(1,0,5)]),(9,[(0,12,4)]),(9,[(0,3,4)]),(9,[(0,8,3)]),(0,[(1,0,2)]),(1,[(1,0,2)]),(9,[(0,1,9)]),(9,[(0,1,3)]),(9,[(0,0,3)]),(9,[(0,0,1)]),(0,[(1,0,1)]),(9,[(0,0,3),(3,7,4)]),(0,[(1,7,2)]),(1,[(1,2,5)]),(9,[(0,9,3)]),(0,[(1,0,1),(1,11,2)]),(1,[(1,0,1)]),(0,[(1,0,1),(1,0,2)])]
def P_60 : BT (Option BoundPool) := buildPoolsBT 7 W_60 R_60 slices_60 ps_60
lemma gp_60 : goodPairs G_60 pos_60 neg_60 := goodPairs_of (by decide +kernel)
lemma base_60_ok : ∀ x ∈ base_60, faithful pos_60 neg_60 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_60_ok : btAll (fun x => faithful pos_60 neg_60 x ∧ x.1 < 2^128) W_60 := buildWiresBT_faithful base_60_ok
set_option maxRecDepth 500000 in
lemma autos_60_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_60 = G_60) autos_60 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_60_0_ok : sliceDirectCheck 0 16 0 R_60 G_60 R_23 G_23 = true := by decide +kernel
lemma sl_60_0 : Slice R_60 G_60 (subcubeFast 0 16) 7 := slice_fast_direct sl_60_0_ok low_23
lemma sl_60_1_ok : sliceDirectCheck 0 32 0 R_60 G_60 R_53 G_53 = true := by decide +kernel
lemma sl_60_1 : Slice R_60 G_60 (subcubeFast 0 32) 7 := slice_fast_direct sl_60_1_ok low_53
lemma sl_60_2_ok : sliceDirectCheck 2 32 0 R_60 G_60 R_15 G_15 = true := by decide +kernel
lemma sl_60_2 : Slice R_60 G_60 (subcubeFast 2 32) 4 := slice_fast_direct sl_60_2_ok low_15
lemma sl_60_3_ok : sliceDirectCheck 4 32 0 R_60 G_60 R_13 G_13 = true := by decide +kernel
lemma sl_60_3 : Slice R_60 G_60 (subcubeFast 4 32) 4 := slice_fast_direct sl_60_3_ok low_13
lemma sl_60_4_ok : sliceDirectCheck 4 0 0 R_60 G_60 R_48 G_48 = true := by decide +kernel
lemma sl_60_4 : Slice R_60 G_60 (subcubeFast 4 0) 5 := slice_fast_direct sl_60_4_ok low_48
lemma sl_60_5_ok : sliceDirectCheck 0 2 0 R_60 G_60 R_24 G_24 = true := by decide +kernel
lemma sl_60_5 : Slice R_60 G_60 (subcubeFast 0 2) 5 := slice_fast_direct sl_60_5_ok low_24
lemma sl_60_6_ok : sliceDirectCheck 4 16 0 R_60 G_60 R_14 G_14 = true := by decide +kernel
lemma sl_60_6 : Slice R_60 G_60 (subcubeFast 4 16) 4 := slice_fast_direct sl_60_6_ok low_14
lemma sl_60_7_ok : sliceDirectCheck 8 2 0 R_60 G_60 R_18 G_18 = true := by decide +kernel
lemma sl_60_7 : Slice R_60 G_60 (subcubeFast 8 2) 4 := slice_fast_direct sl_60_7_ok low_18
lemma sl_60_8_ok : sliceDirectCheck 2 0 0 R_60 G_60 R_22 G_22 = true := by decide +kernel
lemma sl_60_8 : Slice R_60 G_60 (subcubeFast 2 0) 5 := slice_fast_direct sl_60_8_ok low_22
lemma sl_60_9_ok : sliceDirectCheck 8 0 0 R_60 G_60 R_42 G_42 = true := by decide +kernel
lemma sl_60_9 : Slice R_60 G_60 (subcubeFast 8 0) 7 := slice_fast_direct sl_60_9_ok low_42
lemma sl_60_10_ok : sliceDirectCheck 16 0 0 R_60 G_60 R_21 G_21 = true := by decide +kernel
lemma sl_60_10 : Slice R_60 G_60 (subcubeFast 16 0) 5 := slice_fast_direct sl_60_10_ok low_21
lemma sl_60_11_ok : sliceDirectCheck 32 0 0 R_60 G_60 R_41 G_41 = true := by decide +kernel
lemma sl_60_11 : Slice R_60 G_60 (subcubeFast 32 0) 5 := slice_fast_direct sl_60_11_ok low_41
lemma sl_60_12_ok : sliceDirectCheck 0 4 0 R_60 G_60 R_54 G_54 = true := by decide +kernel
lemma sl_60_12 : Slice R_60 G_60 (subcubeFast 0 4) 5 := slice_fast_direct sl_60_12_ok low_54
lemma sl_60_13_ok : sliceDirectCheck 8 32 0 R_60 G_60 R_9 G_9 = true := by decide +kernel
lemma sl_60_13 : Slice R_60 G_60 (subcubeFast 8 32) 4 := slice_fast_direct sl_60_13_ok low_9
lemma sl_60_14_ok : sliceDirectCheck 32 16 0 R_60 G_60 R_8 G_8 = true := by decide +kernel
lemma sl_60_14 : Slice R_60 G_60 (subcubeFast 32 16) 4 := slice_fast_direct sl_60_14_ok low_8
lemma sl_60_15_ok : sliceDirectCheck 16 32 0 R_60 G_60 R_8 G_8 = true := by decide +kernel
lemma sl_60_15 : Slice R_60 G_60 (subcubeFast 16 32) 4 := slice_fast_direct sl_60_15_ok low_8
lemma sl_60_16_ok : sliceDirectCheck 8 4 0 R_60 G_60 R_17 G_17 = true := by decide +kernel
lemma sl_60_16 : Slice R_60 G_60 (subcubeFast 8 4) 4 := slice_fast_direct sl_60_16_ok low_17
lemma sl_60_17_ok : sliceDirectCheck 2 16 0 R_60 G_60 R_0 G_0 = true := by decide +kernel
lemma sl_60_17 : Slice R_60 G_60 (subcubeFast 2 16) 4 := slice_fast_direct sl_60_17_ok low_0
lemma sl_60_18_ok : sliceDirectCheck 8 16 0 R_60 G_60 R_10 G_10 = true := by decide +kernel
lemma sl_60_18 : Slice R_60 G_60 (subcubeFast 8 16) 4 := slice_fast_direct sl_60_18_ok low_10
set_option maxRecDepth 500000 in
lemma slices_60_ok : btAll (fun o => ∀ p, o = some p → Slice R_60 G_60 p.1 p.2) slices_60 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_60 G_60 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_60_0) (forall_cons (fun _ h => by cases h; exact sl_60_1) (forall_cons (fun _ h => by cases h; exact sl_60_2) (forall_cons (fun _ h => by cases h; exact sl_60_3) (forall_cons (fun _ h => by cases h; exact sl_60_4) (forall_cons (fun _ h => by cases h; exact sl_60_5) (forall_cons (fun _ h => by cases h; exact sl_60_6) (forall_cons (fun _ h => by cases h; exact sl_60_7) (forall_cons (fun _ h => by cases h; exact sl_60_8) (forall_cons (fun _ h => by cases h; exact sl_60_9) (forall_cons (fun _ h => by cases h; exact sl_60_10) (forall_cons (fun _ h => by cases h; exact sl_60_11) (forall_cons (fun _ h => by cases h; exact sl_60_12) (forall_cons (fun _ h => by cases h; exact sl_60_13) (forall_cons (fun _ h => by cases h; exact sl_60_14) (forall_cons (fun _ h => by cases h; exact sl_60_15) (forall_cons (fun _ h => by cases h; exact sl_60_16) (forall_cons (fun _ h => by cases h; exact sl_60_17) (forall_cons (fun _ h => by cases h; exact sl_60_18) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))
set_option maxRecDepth 500000 in
lemma P_60_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_60 G_60 c) P_60 := buildPoolsBT_sound slices_60_ok
def bk_60_init : BT (List (List Nat)) := BT.empty
lemma bk_60_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 (0 - 1) xs.toFinset) bk_60_init := trivial
def nodes_60_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_60_0 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_init 0 nodes_60_0 = true := by decide +kernel
def bk_60_0 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_0
set_option maxRecDepth 500000 in
lemma bk_60_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 0 xs.toFinset) bk_60_0 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_init_ok chk_60_0
def nodes_60_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_60_1 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_0 1 nodes_60_1 = true := by decide +kernel
def bk_60_1 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_1
set_option maxRecDepth 500000 in
lemma bk_60_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 1 xs.toFinset) bk_60_1 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_0_ok chk_60_1
def nodes_60_2 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_60_2 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_1 2 nodes_60_2 = true := by decide +kernel
def bk_60_2 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_2
set_option maxRecDepth 500000 in
lemma bk_60_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 2 xs.toFinset) bk_60_2 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_1_ok chk_60_2
def nodes_60_3 : List NodeSpec := [([48,2,170,4],[],[]),([94,146,3,4],[],[]),([174,157,2,4],[],[]),([94,184,2,3],[],[]),([175,157,2,4],[],[]),([94,185,3,4],[],[]),([186,2,3,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_60_3 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_2 3 nodes_60_3 = true := by decide +kernel
def bk_60_3 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_3
set_option maxRecDepth 500000 in
lemma bk_60_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 3 xs.toFinset) bk_60_3 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_2_ok chk_60_3
def nodes_60_4 : List NodeSpec := [([60,142,2,3,4],[],[0]),([166,1,2,3,4],[],[]),([120,0,1,2,5],[],[]),([121,153,0,3,4],[],[]),([0,1,2,131,5],[0,1],[]),([0,1,40,123,5],[2,3],[]),([0,71,2,124,3],[],[]),([48,11,2,112,4],[3],[]),([51,0,125,3,4],[],[]),([1,2,167,3,4],[],[]),([102,94,2,3,4],[],[]),([1,151,9,3,4],[],[]),([118,2,3,59,4],[],[0]),([94,168,2,3,4],[],[]),([10,151,2,3,4],[],[0]),([94,169,2,3,4],[],[]),([164,11,2,3,4],[],[]),([11,2,3,170,4],[4],[0,1]),([155,11,2,3,4],[],[]),([10,11,146,3,4],[],[0]),([171,11,2,3,4],[],[]),([96,94,2,3,4],[],[]),([94,48,2,5,4],[5,3],[0]),([172,0,2,3,4],[],[]),([94,157,48,2,4],[6],[]),([94,2,3,25,4],[],[]),([94,107,2,3,4],[4,7],[0]),([94,2,3,170,4],[],[]),([94,2,173,3,4],[],[]),([12,94,2,5,4],[3,7],[]),([23,94,2,3,4],[],[]),([174,94,2,3,4],[7,3],[0]),([118,9,3,25,4],[],[]),([94,158,50,3,4],[7],[]),([154,11,2,3,4],[],[]),([94,157,2,5,4],[3],[0]),([12,94,157,2,4],[7],[0]),([175,11,2,3,4],[],[]),([94,176,2,3,4],[],[]),([78,0,1,88,4],[],[]),([175,94,2,3,4],[3,6],[0,1]),([94,2,15,3,4],[],[]),([177,94,2,3,4],[],[]),([94,2,178,3,4],[],[]),([94,2,179,3,4],[],[]),([94,180,2,3,4],[],[]),([181,94,2,3,4],[7],[0]),([149,94,158,3,4],[7],[]),([139,94,157,2,4],[6],[]),([182,94,2,3,4],[],[]),([0,1,31,80,25],[],[]),([12,11,2,112,4],[3],[]),([94,2,183,3,4],[],[]),([11,2,3,165,4],[],[0]),([11,50,3,25,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_60_4 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_3 4 nodes_60_4 = true := by decide +kernel
def bk_60_4 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_4
set_option maxRecDepth 500000 in
lemma bk_60_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 4 xs.toFinset) bk_60_4 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_3_ok chk_60_4
def nodes_60_5 : List NodeSpec := [([58,57,1,2,3,4],[],[0]),([60,1,2,3,59,4],[],[0]),([117,0,2,3,25,4],[],[]),([0,118,2,3,25,4],[8],[0]),([63,0,1,3,25,4],[9,5],[]),([119,0,1,2,3,4],[],[]),([120,0,1,2,3,4],[],[0]),([121,0,1,68,3,4],[],[0]),([0,122,1,68,3,4],[10,8,11,12],[]),([0,1,40,123,3,4],[8,4],[0]),([113,69,0,2,3,4],[],[0]),([0,1,2,40,124,3],[13],[0]),([0,1,66,40,3,4],[13],[]),([0,1,72,40,3,4],[8],[]),([8,0,1,125,3,4],[11,5],[]),([74,0,55,2,3,4],[],[]),([57,1,9,3,25,4],[],[]),([69,26,0,2,3,4],[],[]),([60,1,9,3,25,4],[],[0]),([1,2,126,9,3,4],[8],[]),([127,0,1,2,3,4],[],[]),([1,9,3,14,25,4],[11,12,14],[]),([0,1,2,31,80,5],[15,5],[0]),([78,0,1,2,3,4],[],[]),([128,0,2,9,3,4],[],[]),([78,0,34,1,2,4],[13],[0]),([0,1,9,125,3,4],[4,11,16,17],[0]),([129,0,1,2,9,3],[],[]),([130,1,9,88,3,4],[18],[]),([86,0,1,2,40,5],[17],[]),([0,1,2,131,3,4],[0,1,11,13],[0]),([0,1,50,3,25,4],[11,12],[0]),([12,0,1,2,112,4],[3,0],[0]),([110,1,9,88,3,4],[4],[]),([132,0,1,2,40,3],[],[]),([1,133,2,9,3,4],[8],[]),([74,0,62,2,3,4],[],[]),([0,1,134,2,3,4],[],[]),([84,51,0,2,3,4],[],[]),([51,0,34,2,31,4],[5],[]),([51,0,9,88,3,4],[4],[]),([135,1,9,88,3,4],[],[]),([51,0,1,3,25,4],[],[]),([96,1,2,9,3,4],[9],[]),([39,51,1,2,3,4],[],[]),([51,0,34,2,5,4],[13],[]),([136,0,1,2,3,4],[],[]),([51,76,0,2,3,4],[],[]),([51,0,106,2,3,4],[5],[2,0]),([87,0,1,2,3,4],[],[]),([137,0,1,2,3,4],[],[]),([0,1,54,3,25,4],[11,12],[]),([138,0,1,2,3,4],[],[]),([0,1,61,3,25,4],[11,12],[]),([139,94,11,2,3,4],[6],[]),([0,32,34,2,31,4],[5],[]),([12,10,11,2,5,4],[3,7],[0]),([1,2,9,3,105,4],[],[]),([0,1,9,88,5,4],[3,18],[0]),([51,26,0,2,3,4],[],[]),([1,77,9,88,3,4],[4,11],[]),([13,35,2,15,3,4],[],[0]),([13,1,9,3,25,4],[],[]),([140,0,1,2,3,4],[],[]),([23,13,35,2,3,4],[],[0]),([39,1,2,54,3,4],[11,12],[0]),([96,8,1,2,3,4],[],[]),([0,1,2,3,141,4],[5],[]),([0,142,2,3,25,4],[5],[0]),([143,0,1,5,3,4],[19],[]),([1,144,11,2,3,4],[4,8],[]),([74,11,2,3,14,4],[4,11,12],[]),([11,2,3,14,64,4],[11,20,3],[]),([74,90,0,2,3,4],[],[]),([0,1,48,93,2,5],[5,13,3],[]),([145,0,1,2,3,4],[],[]),([0,1,11,146,3,4],[],[0]),([0,1,68,147,3,4],[8,11,16,17],[2]),([0,32,9,88,3,4],[6],[]),([0,1,31,9,88,4],[],[]),([96,0,1,2,3,4],[],[]),([87,0,1,2,5,4],[1],[]),([49,12,0,1,5,4],[7,18],[]),([10,11,2,15,3,4],[],[0]),([49,0,1,15,3,4],[],[]),([96,10,11,2,3,4],[4],[0]),([49,23,0,1,3,4],[5,13],[]),([39,49,1,2,3,4],[],[]),([74,8,11,2,3,4],[4],[]),([1,11,9,3,25,4],[],[0]),([148,0,1,2,3,4],[0,1,21],[]),([149,94,10,2,3,4],[7],[]),([0,1,150,2,3,4],[4],[]),([0,1,151,2,3,4],[5,13,11,9],[0,2]),([152,0,2,5,3,4],[22],[]),([78,1,11,2,3,4],[4],[]),([74,11,2,9,3,4],[4],[]),([78,13,1,2,3,4],[],[]),([153,0,1,68,3,4],[],[0]),([10,11,2,3,25,4],[4,5],[0]),([154,0,1,2,3,4],[],[0]),([155,0,1,2,3,4],[],[0]),([39,1,9,3,25,4],[11,12],[]),([0,1,31,9,25,4],[17],[0]),([0,34,2,156,3,4],[13],[]),([11,2,3,112,4],[6,3],[0,1]),([23,10,11,2,3,4],[4],[0]),([10,48,11,2,5,4],[5,3],[0]),([0,71,2,115,3,4],[],[0]),([102,10,11,2,3,4],[],[0]),([152,0,2,3,25,4],[],[]),([94,11,2,5,3,4],[5,6,3],[0,1]),([94,48,2,3,4],[6,7,3],[0]),([1,11,2,61,3,4],[4],[]),([94,157,2,3,4],[6,7,3],[0]),([1,99,2,31,3,4],[],[]),([11,2,50,5,3,4],[7,6,3],[0]),([94,10,2,158,3,4],[7],[0]),([11,2,5,3,112,4],[3,6],[]),([39,57,1,2,3,4],[],[]),([0,24,1,2,40,5],[3],[0]),([12,94,2,3,4],[6,7,3],[0]),([10,107,11,2,3,4],[4,7],[0]),([11,2,97,50,3,4],[4,7,6],[]),([139,94,2,3,4],[6,7,3],[0]),([0,1,67,2,5],[0,17],[0]),([73,0,1,40,3,4],[9,13],[]),([94,157,11,2,3,4],[6],[0]),([0,1,2,3,159,4],[5],[]),([94,2,5,3,4],[6,3,7],[0,1]),([160,2,3,4],[7,6,3],[]),([0,1,2,161,3,4],[0,1],[]),([0,1,2,162,3,4],[11],[]),([163,0,1,2,3,4],[11],[]),([12,0,1,2,105,4],[],[]),([164,0,1,2,3,4],[],[0]),([149,94,2,3,4],[7,6,3],[0,1]),([0,1,2,3,165,4],[13,5,1,0],[0]),([13,35,2,3,25,4],[],[0]),([12,13,35,2,5,4],[3,7],[0]),([104,11,2,50,3,4],[6],[]),([94,2,50,3,4],[7,4,6,3],[0]),([39,74,11,2,3,4],[4],[]),([94,2,158,3,4],[7,6,3],[0,1]),([0,1,37,3,25,4],[13],[]),([94,2,3,4],[7,6,3],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_60_5 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_4 5 nodes_60_5 = true := by decide +kernel
def bk_60_5 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_5
set_option maxRecDepth 500000 in
lemma bk_60_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 5 xs.toFinset) bk_60_5 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_4_ok chk_60_5
def nd_60_6_0 : List NodeSpec := [([57,0,1,2,5,3,4],[11,15,12,5,23],[0]),([58,0,1,2,3,25,4],[5,8],[0]),([0,1,2,3,25,59,4],[5,11,16,8,17],[0]),([60,0,1,2,3,25,4],[11,15,5,12,8],[0]),([0,1,2,61,5,3,4],[24,5,11,0,12,1,2],[0]),([0,1,62,2,5,3,4],[13,11,0,12,1,2],[0]),([0,1,2,61,3,4],[8,4,13,11,0,12,1],[0]),([63,0,1,2,5,3,4],[11,2,12,7,25],[0]),([0,1,2,3,14,25,4],[11,2,5,12,15,7,26],[0]),([0,1,2,3,14,64,4],[11,2,5,12,3,13,27],[0]),([6,0,1,65,2,3,4],[11,13,28,16],[]),([7,0,1,2,66,3,4],[15,11,3,18,12],[0]),([7,0,24,1,2,5],[17,2,16,3],[0,3]),([0,1,67,2,3,4],[0,5,2,17,16,9],[0]),([0,1,2,68,3,4],[8,10,4,13,11,12],[2]),([6,16,1,2,4],[11,8,7,17],[]),([69,7,0,1,2,3,4],[11,7,13],[0]),([0,1,2,70,40,3,4],[11,17,12],[]),([18,0,1,2,40,3,4],[7,13,3,17,12],[0]),([0,71,1,2,40,3,4],[7,8,13,11,17,4],[0,2]),([7,0,1,2,72,3,4],[29,13,8,5,11,0],[0]),([0,1,2,72,3,4],[8,5,4,11,0,12,1,3],[]),([73,7,0,1,2,3,4],[11,18,4],[0]),([0,1,27,2,40,3,4],[6,13,7],[2,0]),([74,8,0,1,2,3,4],[4,7,8,30],[0]),([8,0,1,75,2,3,4],[8,17,12,18],[]),([8,0,34,1,2,5,4],[11,2,16,17,31,18],[]),([8,76,0,1,2,3,4],[8,17,12,32],[]),([8,34,1,77,2,3,4],[11,8],[]),([0,1,55,2,5,3,4],[7,8,13,11,0,12,1,2],[0]),([78,0,1,2,5,3,4],[5,1,0,33],[]),([0,79,2,3,4],[13,8,11,12],[]),([78,0,1,2,9,3,4],[8,9,11],[]),([0,1,68,3,4],[8,11,12],[0]),([78,0,1,2,3,4],[11,9,4,13,8,0,1,34,33,35],[0,1]),([0,1,2,5,3,59,4],[3,0,36],[0]),([74,0,1,2,3,14,4],[5,2,11,12,4],[0]),([0,1,9,3,25,4],[15,8,11,37,12,38],[0,1]),([7,0,1,65,2,3,4],[13,3,11,12],[0]),([74,0,1,2,9,3,4],[5,8,4,11,16,17],[0,2]),([39,1,2,9,3,4],[18,8,11,12],[0]),([0,1,2,31,9,5,4],[5,0,15,17],[0]),([1,2,9,5,3,14,4],[7,11,12,8,39],[0]),([0,1,2,31,80,3,4],[11,15,0,12,40],[0]),([81,0,1,2,9,3,4],[0,1,5,17,12],[]),([39,74,0,1,2,3,4],[4,13,8],[0,2]),([0,1,2,82,9,3,4],[9,8,18],[0]),([83,0,2,3,4],[4,8,11,12],[]),([84,0,1,2,9,3,4],[5,8,0,40,4],[0]),([1,11,2,5,3,14,4],[3,11,12,8,41],[0]),([0,85,1,2,9,3,4],[11],[]),([86,0,1,2,40,3,4],[17,12],[0]),([0,34,1,2,9,5,4],[2,11,3,18,16],[0]),([87,0,1,2,3,4],[11,9,0,5,8,12,1,42],[0]),([76,0,1,2,9,3,4],[12,5,17,4,16],[0]),([0,34,1,9,88,3,4],[11,9,18,4],[0]),([39,0,1,2,3,25,4],[15,5,8],[0]),([0,1,9,88,3,4],[18,8,4,11,43,17],[0]),([0,1,89,2,9,3,4],[5,8,28,9,11,44],[0]),([51,0,1,2,5,3,4],[11,13,0,1,12,5,7,45],[0,1]),([0,32,1,2,31,3,4],[5,11,18,0,40,4],[0]),([90,0,1,2,5,3,4],[11,2,12,13,46],[0]),([0,1,9,5,3,25,4],[11,12,9,38],[0]),([38,0,32,2,9,3,4],[5,13],[]),([10,0,1,2,3,25,4],[15,4,8,5,13],[0]),([0,34,1,2,31,9,4],[5,0],[0]),([39,1,2,9,5,3,4],[5,24,11,12,2],[0]),([0,32,34,2,9,3,4],[5,13,6],[0]),([0,1,2,91,3,4],[7,4,6,12,1],[]),([13,35,2,5,3,4],[2,3,7,6],[0,1]),([13,1,2,5,3,14,4],[11,12,8,2],[]),([12,10,11,2,3,4],[4,6,7,3],[0]),([0,92,1,2,9,3,4],[9,8,15],[0]),([0,1,48,93,2,3,4],[11,3,0,12,6],[0]),([13,1,2,3,14,4],[5,7,11,2,4],[]),([7,1,2,14,4],[11,7,17],[]),([10,48,11,2,3,4],[4,6,5,7,3],[0]),([12,13,0,1,2,5,4],[40,11,3,17,16,7],[0]),([94,10,2,3,4],[5,7,6,3],[0]),([0,1,2,95,4],[5,13,11,17],[]),([96,0,1,2,5,3,4],[5,1,0,47],[]),([23,13,0,1,2,3,4],[11,13,5,8,16,17],[0]),([0,1,2,97,50,3,4],[4,7,6,11],[0]),([87,0,1,2,9,3,4],[8,9,11],[]),([0,1,2,40,5,4],[2,7,11,48,3],[2,0]),([0,1,98,2,3,4],[4,18,12,1,3],[]),([13,29,2,3,4],[8,4,7,3],[0]),([51,0,34,2,3,4],[13,0,5,18,44],[0]),([13,0,1,2,15,3,4],[13,17,12,16],[0]),([10,11,2,3,4],[4,5,7,3],[0]),([13,1,2,31,9,3,4],[5],[0]),([1,99,2,9,3,4],[9,5,18,8],[0,1]),([0,1,11,2,15,3,4],[15,12,5,17],[0]),([13,35,94,2,3,4],[13,7,6,3],[]),([87,0,34,1,2,3,4],[5,0,13],[]),([0,1,2,54,5,3,4],[5,13,7,11,0,12,1,49],[0,2]),([13,94,2,3,4],[5,13,18,6,28,3,2],[]),([0,1,2,50,3,4],[7,4,6,3],[]),([69,0,1,2,40,3,4],[7,11,4,13],[2,0]),([0,1,75,2,9,3,4],[3,13,12,5,17],[]),([12,0,1,11,2,5,4],[11,40,3,7,18,16,17],[0]),([0,1,48,11,2,5,4],[5,13,0,3,17],[0]),([0,34,1,2,100,3,4],[0,13,16,17],[0]),([18,0,1,2,21,3,4],[13,3,17],[]),([0,1,2,101,3,4],[0,5,7,13,18,11,17],[]),([96,0,1,2,3,4],[11,5,13,9,0],[0,2]),([102,0,1,11,2,3,4],[0,1,5,17,12],[0]),([0,34,1,103,2,3,4],[8],[]),([104,0,1,2,50,3,4],[6,11],[0]),([0,1,2,3,105,4],[2,11,5,28,9],[0,1]),([13,1,2,9,5,3,4],[8,7,2],[0]),([0,1,11,2,3,25,4],[5,8,13,4,15],[0,2]),([34,1,77,2,9,3,4],[8,7,11,4],[0]),([8,0,106,1,2,3,4],[11,7,8,50],[0]),([0,1,2,5,3,105,4],[13,0,1,2],[]),([94,0,2,3,4],[13,5,4,7,28,2],[]),([0,106,1,2,9,3,4],[5,8,9,11,4,16,17],[0]),([0,1,107,11,2,3,4],[5,8,4,7],[0]),([0,24,1,2,40,3,4],[7,4,13,12,1],[0]),([12,13,35,2,3,4],[13,18,5,7,6,3],[0]),([8,1,11,2,5,3,4],[3,7,8,18,2],[0]),([94,11,2,3,4],[4,7,6,3],[0,1]),([108,0,1,2,3],[8,4,12,11],[]),([10,11,2,5,3,4],[3,5,6,7],[0,1]),([32,11,2,3,4],[4,5,7,3],[]),([26,0,1,2,40,3,4],[7,13,4],[0,2]),([13,0,1,2,3,25,4],[15,16,11,13,5,8,4],[0]),([0,1,2,109,3,4],[8,4,11,17],[]),([110,34,1,2,9,3,4],[5,51,11,4],[0]),([57,0,1,2,3,25,4],[15,11,8,5],[0]),([0,1,2,5,3,111,4],[8,1,0,2],[]),([39,1,11,2,3,4],[4,8,11,12],[0,2]),([49,0,1,2,5,3,4],[11,7,0,12,1,13,52],[0,2,1]),([0,1,109,3,4],[4,8,11,17],[]),([0,1,2,5,3,112,4],[3,6],[0]),([113,0,1,2,40,3,4],[13,4],[0]),([110,1,2,9,3,4],[5,8,9,4,11,17,2],[0]),([12,10,0,1,2,5,4],[11,3,16,17,7],[0]),([0,1,11,2,5,3,4],[3,5,8,13,11,0,12],[0]),([0,1,2,3,112,4],[2,3,6,9],[0,1]),([49,12,0,1,3,4],[0,5,7,13,18,53],[0]),([96,0,1,11,2,3,4],[8,5,4,11],[0]),([10,0,1,2,15,3,4],[4,17,12],[0]),([94,0,1,2,3,4],[4,5,9,7,11,0,12,1,13,8],[]),([114,0,1,2,9,3,4],[11,0,18,6],[]),([51,0,1,2,31,3,4],[11,40,13],[0]),([0,1,2,50,5,3,4],[7,6,3,11,12],[0]),([0,1,2,40,115,3,4],[8,7,13,4,40,17],[0]),([94,10,11,2,3,4],[7,6,3],[]),([0,1,2,37,5,3,4],[7,8,11,18,0,1,12,2],[0]),([39,1,11,2,5,3,4],[3,5,11,12,2],[2]),([1,11,2,9,5,3,4],[3,18,15,5,54],[0]),([0,1,99,2,3,4],[5,8,11,0,12,1],[]),([94,2,3,4],[7,6,3],[0,1]),([30,7,0,1,2,5],[15,17,2,16,6,3,48,7],[]),([0,1,2,5,3,116,4],[15,0,55],[0]),([23,10,0,1,2,3,4],[11,4],[0]),([23,0,1,11,2,3,4],[5,8,13,4,11,15],[0]),([44,11,2,3,4],[4,7,3],[0]),([10,11,2,50,3,4],[4,7,6,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_60_6_0 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_5 6 nd_60_6_0 = true := by decide +kernel
def nd_60_6_1 : List NodeSpec := [([11,2,50,3,4],[7,4,6,3],[0,1]),([51,7,0,1,2,3,4],[11,40,13],[0]),([13,35,2,3,4],[13,5,7,3],[0]),([8,1,2,5,3,14,4],[11,12,8,2],[]),([51,0,34,2,9,3,4],[4,5,44],[0]),([26,0,1,2,9,3,4],[5,8,4,40],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_60_6_1 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_5 6 nd_60_6_1 = true := by decide +kernel
def nodes_60_6 : List NodeSpec := nd_60_6_0 ++ nd_60_6_1
set_option maxRecDepth 500000 in
lemma chk_60_6 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_5 6 nodes_60_6 = true := by
  unfold nodes_60_6 checkNodesBT; simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_60_6_0, chk_60_6_1⟩
def bk_60_6 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_6
set_option maxRecDepth 500000 in
lemma bk_60_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 6 xs.toFinset) bk_60_6 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_5_ok chk_60_6
def nodes_60_7 : List NodeSpec := [([0,1,2,5,3,14,4],[11,2,12,17,16,3,7,15,56],[0]),([0,1,2,15,3,4],[15,40,5,8,12,13,4],[0,2]),([16,0,1,2,3,4],[11,4,8,13,0,9,1,12,40,2],[0]),([0,17,1,2,3,4],[11,5,7,4,13,0,12,1,40,17],[3]),([18,6,0,1,2,3,4],[11,13,3,17,8,5,7,16,15],[3,0]),([0,19,1,2,3,4],[1,12,0,2,5,13,4,17,7,16],[2]),([20,0,1,2,3,4],[11,5,13,4,7,12],[]),([0,1,2,21,3,4],[7,13,4,11,40,17,12],[3,0]),([22,0,1,2,3,4],[4,0,13,9,11,1,12,5,7,6,3],[0]),([18,7,0,1,2,3,4],[11,13,3,17,8,5,7,16,15],[0]),([23,0,1,2,3,4],[11,5,8,13,4,57,12],[0,2]),([7,0,24,1,2,3,4],[17,2,16,13,4,15,7],[0,3]),([0,1,2,3,25,4],[15,58,11,16,8,5,4,13],[0,2]),([26,7,0,1,2,3,4],[13,6,11,5,0,7,17,29,8],[0,2]),([7,0,1,27,2,3,4],[11,8,6,18,17,7],[0,2]),([8,0,1,2,5,3,4],[15,3,2,58,7,11,0,12,1,18,28],[0,1]),([28,0,1,2,3,4],[11,8,13,4,59,1,12,17],[]),([0,29,1,2,3,4],[9,4,5,8,7,0,11,1,12,3],[0]),([0,1,2,9,5,3,4],[2,15,5,28,3,18,60,61,58,11,12],[0,1]),([30,6,0,1,2,3,4],[11,12,15,17,8,5,16,6,18,3,7],[0]),([7,0,1,2,5,4],[0,11,3,1,2,48],[0,2]),([0,1,2,31,9,3,4],[5,7,18,60,15,17],[0]),([0,32,1,2,9,3,4],[5,18,7,40,15,6,3],[0,1]),([0,32,1,2,3,4],[4,9,13,5,7,6,3,62],[0]),([33,0,1,2,3,4],[11,8,13,4,9,12,10],[0,2]),([8,0,1,9,3,4],[9,8,5,28,2],[]),([8,0,34,1,2,3,4],[18,11,8,7,28,4,63,17,16,15],[0]),([13,35,2,3,4],[13,18,6,28,3,2,7],[0,2,1]),([36,0,1,2,3,4],[13,8,18,0,11,1,12,2],[]),([0,1,2,37,3,4],[8,7,13,18,0,11,1,12,2,28],[0]),([38,0,1,2,9,3,4],[8,5,18,6,60,15,28,16,17],[0]),([7,0,1,2,9,3,4],[8,18,7,40,15,2,6,11],[0]),([13,0,11,2,3,4],[13,5,9,7,2],[0]),([13,35,0,1,2,3,4],[13,5,7,6,3],[0]),([39,0,1,2,3,4],[11,4,8,13,9,0,1,12,24,16,17],[0,2]),([7,0,1,2,40,3,4],[11,8,7,17,64,6],[0,2]),([41,0,1,2,3,4],[11,5,13,4,7,1,12,17],[]),([0,1,11,2,3,4],[5,4,7,13,11,0,12,1,3,6],[0]),([6,7,0,1,2,4],[9,0,11,17,7],[]),([0,1,42,2,3,4],[8,13,6,0,11,28,17],[]),([10,0,1,2,3,4],[4,13,9,0,11,1,12,5,8,7,6,3],[0]),([43,0,1,2,3,4],[11,8,13,18,1,12],[]),([44,0,1,2,3,4],[4,8,65,0,11,1,12,3],[0]),([12,0,1,11,2,3,4],[8,5,4,13,11,7,40,6,3,18,16,17,66],[0]),([0,1,45,2,3,4],[13,5,4,7,11,6,28,18,12,1],[]),([46,0,1,2,3,4],[0,8,1,12,13,4,17,2,67],[2]),([47,0,1,2,3,4],[11,5,13,7,1,12],[]),([13,10,1,2,3,4],[9,13,4,18,3],[0]),([0,1,48,2,3,4],[6,5,13,0,11,7,17],[0]),([30,7,0,1,2,3,4],[11,12,15,17,8,5,16,6,18,3,64],[0]),([8,13,1,2,3,4],[8,9,4,18,2],[0]),([49,0,1,2,3,4],[9,7,13,11,0,12,1,18,52,53],[0,1]),([13,1,2,9,3,4],[5,9,8,18,28,2],[0,1]),([10,0,1,2,50,3,4],[18,7,4,6,3,8],[0]),([8,1,11,2,3,4],[8,4,7,18,2,28],[0]),([10,0,1,2,5,3,4],[3,2,15,11,0,12,1,7,6],[0,1]),([12,6,0,1,2,4],[11,9,8,0,18,17,7],[0]),([0,1,2,40,3,4],[8,7,64,4,13,11,40,17,12,68],[2,0]),([10,0,1,2,9,3,4],[18,5,7,8,40,28,15,2,4],[]),([51,0,1,2,3,4],[13,9,4,18,0,11,1,12,5,44,45],[0,1]),([10,0,1,11,2,3,4],[4,5,7,6,3,13],[0]),([12,10,0,1,2,3,4],[11,4,40,6,8,5,7,3,18,65,17,16],[0]),([7,0,1,11,2,3,4],[8,13,4,6,7,3,2,11],[]),([0,1,2,5,3,25,4],[58,11,16,2,17,3,69],[0,2]),([12,0,1,2,5,4],[11,2,3,0,9,1,15,58,7,17,18],[0,2,1,3]),([13,0,1,2,5,3,4],[3,2,15,11,0,1,12,13,6,7,28],[0,1]),([51,0,1,2,9,3,4],[18,9,5,4,40,15,44,45],[0,1]),([10,11,2,3,4],[4,7,6,3],[0,1]),([0,1,2,52,3,4],[8,7,13,4,11,17],[]),([0,1,2,31,3,4],[28,5,7,70,11,13,4,60,17],[]),([53,0,1,2,3,4],[11,0,8,4,6,28,17],[]),([26,0,1,2,3,4],[0,4,5,9,11,1,12,8,29,6,17,3],[0,2]),([0,1,2,54,3,4],[5,13,7,11,0,12,1,49,71],[0,1]),([0,1,11,2,5,3,4],[2,3,5,28,13,6,15,11,0,66,12,1,72,7],[0,2,1]),([39,0,1,2,5,3,4],[11,3,2,15,5,0,1,12,16,24],[0,2]),([0,1,27,2,3,4],[8,13,5,18,6,11,17,2,12],[]),([0,1,55,2,3,4],[8,13,5,7,11,0,12,1,2,28],[0]),([56,0,1,2,3,4],[11,8,4,9,1,12,17],[0]),([13,0,34,1,2,3,4],[4,13,18,0,11,17,3,5,8],[0]),([8,38,0,1,2,3,4],[11,8,7,18,28,17,16,15],[0]),([0,34,1,2,9,3,4],[8,5,18,28,63,11,15,4,0,60,16,17],[0]),([0,1,2,50,3,4],[4,7,18,8,6,65,3,11,12],[0,1]),([0,1,2,3,14,4],[5,7,11,12,16,4,13,17,1,0],[0,1]),([12,13,0,1,2,3,4],[11,13,40,18,8,5,6,3,17,16,7,28],[0]),([13,35,0,2,3,4],[8,5,7,2],[0]),([1,11,2,9,3,4],[18,5,9,54,73],[0]),([10,0,11,2,3,4],[13,8,5,7,2],[0]),([13,0,1,2,3,4],[4,5,9,13,18,0,11,1,12,8,2],[0]),([13,0,1,2,9,3,4],[8,5,7,40,28,15,2,4,13],[0]),([0,1,48,11,2,3,4],[5,13,7,0,6,3,17,66],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_60_7 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_6 7 nodes_60_7 = true := by decide +kernel
def bk_60_7 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_7
set_option maxRecDepth 500000 in
lemma bk_60_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 7 xs.toFinset) bk_60_7 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_6_ok chk_60_7
def nodes_60_8 : List NodeSpec := [([0,1,2,5,3,4],[58,11,0,1],[0,2,1,3]),([6,0,1,2,3,4],[0,11,28,9,1,5,7,17],[2,0,3]),([7,0,1,2,3,4],[0,11,9,64,1,17,8,2],[0,2]),([8,0,1,2,3,4],[9,8,7,0,1,28,2],[0,1]),([0,1,2,9,3,4],[5,9,60,61],[0,1,2]),([10,0,1,2,3,4],[8,4,9,65,0,6,1,3,28,2],[0,2,1]),([0,1,11,2,3,4],[13,5,7,66,72,18,9],[0,2,1,3]),([12,0,1,2,3,4],[11,40,0,9,1,17],[0,2,1,3]),([13,0,1,2,3,4],[8,13,9,18,0,28,1,2],[0,1,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_60_8 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_7 8 nodes_60_8 = true := by decide +kernel
def bk_60_8 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_8
set_option maxRecDepth 500000 in
lemma bk_60_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 8 xs.toFinset) bk_60_8 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_7_ok chk_60_8
def nodes_60_9 : List NodeSpec := [([0,1,2,3,4],[9,0,1],[0,2,1,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_60_9 : checkNodesBT W_60 G_60 fmask_60 P_60 autos_60 bk_60_8 9 nodes_60_9 = true := by decide +kernel
def bk_60_9 : BT (List (List Nat)) := buildBucketsBT W_60 nodes_60_9
set_option maxRecDepth 500000 in
lemma bk_60_9_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_60 9 xs.toFinset) bk_60_9 :=
  buildBucketsBT_sound (by decide) gp_60 W_60_ok P_60_ok autos_60_ok bk_60_8_ok chk_60_9
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_60_ok : forestRootCheck R_60 G_60 [(VAR 1,10,8),(VAR 2,12,8),(VAR 3,10,2),(VAR 4,22,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_60_in : bucketContainsBT bk_60_9 R_60 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_60 : Lower R_60 G_60 10 := lower_of_forestBT root_60_ok bk_60_9_ok root_60_in

end Cofactor12116
def h34R : List Nat := varsOf 61
def h34G : Nat := 0xfffafaa0faaaa0a0fffafaa0faaaa0a0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h34Bound : Lower h34R h34G 10 := carry_of (swaps := [(2,3),(3,4),(1,2),(0,1)]) (roots2 := Cofactor12116.R_60) (T2 := Cofactor12116.G_60) (by decide +kernel) Cofactor12116.low_60
def h35R : List Nat := varsOf 46
def h35G : Nat := 0xfffcfffcfcc0fcc0fffcfffcfcc0fcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h35Bound : Lower h35R h35G 7 := carry_of (swaps := [(3,4),(4,5),(2,3),(1,2),(0,1)]) (roots2 := h13R) (T2 := h13G) (by decide +kernel) h13Bound
def h36R : List Nat := varsOf 58
def h36G : Nat := 0xffffffccffccccccffffffccffcccccc
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h36Bound : Lower h36R h36G 5 := carry_of (swaps := [(3,4),(4,5),(2,3),(3,4),(1,2),(2,3),(0,1)]) (roots2 := h10R) (T2 := h10G) (by decide +kernel) h10Bound
def h37R : List Nat := varsOf 62
def h37G : Nat := 0xfffcfcc0fcc0ccc0fffcfcc0fcc0ccc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h37Bound : Lower h37R h37G 10 := carry_of (swaps := [(3,4),(0,1)]) (roots2 := h34R) (T2 := h34G) (by decide +kernel) h34Bound
def h39R : List Nat := varsOf 11
def h39G : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h39Bound : Lower h39R h39G 4 := carry_of (swaps := [(2,3)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h40R : List Nat := varsOf 13
def h40G : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h40Bound : Lower h40R h40G 4 := carry_of (swaps := [(2,3),(1,2)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h41R : List Nat := varsOf 22
def h41G : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h41Bound : Lower h41R h41G 4 := carry_of (swaps := [(2,3),(3,4),(1,2),(0,1)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h42R : List Nat := varsOf 25
def h42G : Nat := 0xffaaaa00ffaaaa00ffaaaa00ffaaaa00
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h42Bound : Lower h42R h42G 4 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h43R : List Nat := varsOf 28
def h43G : Nat := 0xfff0f000fff0f000fff0f000fff0f000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h43Bound : Lower h43R h43G 4 := carry_of (swaps := [(2,3),(3,4),(1,2),(2,3),(0,1),(1,2)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h44R : List Nat := varsOf 29
def h44G : Nat := 0xfffafaa0fffafaa0fffafaa0fffafaa0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h44Bound : Lower h44R h44G 7 := carry_of (swaps := [(3,4),(2,3),(1,2)]) (roots2 := h13R) (T2 := h13G) (by decide +kernel) h13Bound
def h45R : List Nat := varsOf 30
def h45G : Nat := 0xfffcfcc0fffcfcc0fffcfcc0fffcfcc0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h45Bound : Lower h45R h45G 7 := carry_of (swaps := [(3,4),(2,3),(1,2),(0,1)]) (roots2 := h13R) (T2 := h13G) (by decide +kernel) h13Bound
def h38R : List Nat := varsOf 31
def h38G : Nat := 0xfffefee8fffefee8fffefee8fffefee8

private lemma rescueReach {roots : List Wire} {p : Nat} {bank : List Wire}
    (h : Reach roots p bank) : RescueK5.Reach true roots p bank := by
  have avail {pool : List Wire} {w : Wire} (hw : Avail pool w) :
      RescueK5.Available true pool w := by
    rcases hw with a | a | a
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr ⟨rfl, a⟩)
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact RescueK5.Reach.start
  | succ p ih =>
    obtain ⟨op, prev, a, b, h, ha, hb, rfl⟩ := h
    exact RescueK5.Reach.two op (ih h) (avail ha) (avail hb)

private lemma rescueObs (a : Nat) : RescueK5.observe (RescueK5.W a) = obs a :=
  funext fun r => RescueK5.bit_W r a

private lemma rescueK5Bound :
    Lower (varsOf 31) 0xfffefee8fffefee8fffefee8fffefee8 10 := by
  intro p bank h ha
  apply RescueK5.s7_L p bank
  · have hR : (RescueK5.rootsW RescueK5.s7_R).map RescueK5.observe = (varsOf 31).map obs := by
      simp only [RescueK5.rootsW, List.map_map, Function.comp_def, rescueObs]
      have h := congrArg (List.map obs) (by decide +kernel : RescueK5.s7_R.map RescueK5.xN = varsOf 31)
      simpa only [List.map_map, Function.comp_def] using h
    exact rescueReach (hR ▸ h)
  · change RescueK5.Available true bank (RescueK5.observe (RescueK5.W RescueK5.s7_T))
    rw [rescueObs]
    rcases ha with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨rfl, h⟩)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h38Bound : Lower h38R h38G 10 := by
  exact rescueK5Bound
def h46R : List Nat := varsOf 47
def h46G : Nat := 0xfffefffefeeafeeafffefffefeeafeea
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h46Bound : Lower h46R h46G 8 := lift_of (z := 1) (o := 0) (essPairs := [(VAR 0,0,1)]) (by decide +kernel) h35Bound
def h47R : List Nat := varsOf 55
def h47G : Nat := 0xfffffefefefeececfffffefefefeecec
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h47Bound : Lower h47R h47G 8 := carry_of (swaps := [(3,4),(0,1)]) (roots2 := h46R) (T2 := h46G) (by decide +kernel) h46Bound
def h49R : List Nat := varsOf 56
def h49G : Nat := 0xffffff00ff000000ffffff00ff000000
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h49Bound : Lower h49R h49G 4 := carry_of (swaps := [(2,3),(3,4),(4,5),(1,2),(2,3),(3,4),(0,1),(1,2),(2,3)]) (roots2 := h2R) (T2 := h2G) (by decide +kernel) h2Bound
def h48R : List Nat := varsOf 59
def h48G : Nat := 0xffffffeeffeeeeeeffffffeeffeeeeee
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h48Bound : Lower h48R h48G 6 := lift_of (z := 3) (o := 0) (essPairs := [(VAR 0,0,1),(VAR 1,0,2)]) (by decide +kernel) h49Bound
def h0R : List Nat := varsOf 63
def h0G : Nat := 0xfffefee8feeaece8fffefee8feeaece8
def h0Pos : List Nat := [5,6,3,3,6,5,10,13,41,28,17,17,44,35,41,10,22,50,35,50,13,28,28,37,5,44,44,25,41,26,22,52,50,14,11,37,42,13,25,52,26,10,56,56,56,25]
def h0Neg : List Nat := [4,4,1,2,2,1,2,12,33,12,1,16,12,34,9,8,20,34,33,18,9,20,24,33,9,40,36,24,40,24,18,48,48,12,9,36,40,1,9,36,18,18,24,48,40,1]
def h0Mask : Nat := fullMask 46
def h0Base : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x206c19946dad,0x206401944524),(0xcccccccccccccccccccccccccccccccc,0x317600fa05e,0x300400a2058),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xaac7f112b3,0x8a04211283),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3f763e70d3c0,0x14563b50d280),(0xffff0000ffff0000ffff0000ffff0000,0x3dc1e86b0e00,0xf01e8690800),(0xffffffff00000000ffffffff00000000,0x1c99968e7100,0x189996862100)]
def h0Steps : List (Nat × Nat × Nat) := [(1,2,3),(3,0,6),(3,2,3),(0,3,4),(1,3,4),(2,3,4),(1,0,8),(1,1,12),(3,0,13),(3,1,13),(1,1,8),(1,0,9),(1,1,17),(3,1,18),(1,2,17),(3,0,20),(3,2,20),(1,2,9),(3,2,10),(0,5,10),(1,1,11),(1,2,26),(3,1,27),(3,2,27),(1,2,11)]
def h0W : BT Decor := buildWiresBT 5 h0Base h0Steps
def h0AutoList : List (List (Nat × Nat)) := [[],[(3,4),(0,1)]]
def h0Autos : BT (List (Nat × Nat)) := btOfList 1 h0AutoList
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Pairs : goodPairs h0G h0Pos h0Neg := goodPairs_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0BaseOk : ∀ x ∈ h0Base, faithful h0Pos h0Neg x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0WOk : btAll (fun x => faithful h0Pos h0Neg x ∧ x.1 < 2^128) h0W := buildWiresBT_faithful h0BaseOk
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0AutosOk : btAll (fun sw => swapsValid sw = true ∧ permWord sw h0G = h0G) h0Autos := btAll_ofList (autos_of (by decide +kernel))
def h0SliceList : List (Option (Nat × Nat)) := [some (subcubeFast 0 4,6),some (subcubeFast 0 8,8),some (subcubeFast 0 16,8),some (subcubeFast 0 32,10),some (subcubeFast 1 0,10),some (subcubeFast 1 4,5),some (subcubeFast 1 16,7),some (subcubeFast 2 0,10),some (subcubeFast 2 4,5),some (subcubeFast 2 8,7),some (subcubeFast 2 16,5),some (subcubeFast 4 0,9),some (subcubeFast 4 8,5),some (subcubeFast 4 32,7),some (subcubeFast 8 0,8),some (subcubeFast 8 32,7),some (subcubeFast 9 0,5),some (subcubeFast 10 0,5),some (subcubeFast 12 0,5),some (subcubeFast 16 0,8),some (subcubeFast 32 0,8)]
def h0Slices : BT (Option (Nat × Nat)) := btOfList 5 h0SliceList
def h0Specs : List PoolSpec := [(4,[]),(7,[]),(11,[]),(4,[(1,2,3)]),(1,[]),(9,[]),(14,[]),(19,[]),(2,[]),(20,[]),(3,[]),(7,[(1,2,3)]),(3,[(1,2,3)]),(4,[(3,2,3)]),(4,[(3,2,3),(1,1,12)]),(8,[]),(5,[]),(4,[(3,2,3),(1,1,12),(3,1,13)]),(7,[(3,2,3),(1,0,8)]),(12,[]),(7,[(3,2,3)]),(4,[(3,2,3),(1,1,8)]),(0,[]),(3,[(3,2,3)]),(4,[(0,3,4)]),(4,[(0,3,4),(1,1,17)]),(17,[]),(16,[]),(4,[(0,3,4),(1,1,17),(3,1,18)]),(7,[(0,3,4),(1,0,9)]),(4,[(0,3,4),(1,2,17)]),(4,[(0,3,4),(1,2,17),(3,2,20)]),(11,[(0,3,4),(1,0,9)]),(14,[(1,2,17),(3,2,20)]),(19,[(1,2,17),(3,2,20)]),(6,[(1,2,17),(3,2,20)]),(13,[(0,3,4),(1,0,9)]),(15,[(1,2,17),(3,2,20)]),(7,[(0,3,4)]),(11,[(0,3,4)]),(3,[(0,3,4)]),(4,[(0,3,4),(1,2,9)]),(18,[]),(7,[(0,3,4),(1,2,9)]),(3,[(0,3,4),(1,2,9)]),(1,[(1,2,9)]),(4,[(1,3,4)]),(6,[]),(7,[(1,3,4)]),(11,[(1,3,4)]),(3,[(1,3,4)]),(4,[(1,3,4),(3,2,10)]),(7,[(1,3,4),(3,2,10)]),(3,[(1,3,4),(3,2,10)]),(14,[(3,2,10)]),(4,[(1,3,4),(0,5,10)]),(7,[(1,3,4),(0,5,10)]),(11,[(1,3,4),(0,5,10)]),(14,[(0,5,10)]),(19,[(0,5,10)]),(4,[(2,3,4)]),(7,[(2,3,4)]),(4,[(2,3,4),(1,1,11)]),(4,[(2,3,4),(1,1,11),(1,2,26)]),(7,[(2,3,4),(1,2,26)]),(7,[(2,3,4),(1,2,26),(3,2,27)]),(11,[(2,3,4),(1,1,11)]),(14,[(1,2,26),(3,2,27)]),(9,[(1,2,26),(3,2,27)]),(6,[(1,2,26),(3,2,27)]),(2,[(1,2,26),(3,2,27)]),(13,[(2,3,4),(1,1,11)]),(10,[]),(11,[(2,3,4)]),(3,[(2,3,4)]),(4,[(2,3,4),(1,2,11)]),(7,[(2,3,4),(1,2,11)]),(3,[(2,3,4),(1,2,11)]),(1,[(1,2,11)])]
def h0Pools : BT (Option BoundPool) := buildPoolsBT 7 h0W h0R h0Slices h0Specs
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice20 : Slice h0R h0G (subcubeFast 32 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h1Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice19 : Slice h0R h0G (subcubeFast 16 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h12Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice18 : Slice h0R h0G (subcubeFast 12 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h14Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice17 : Slice h0R h0G (subcubeFast 10 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h15Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice16 : Slice h0R h0G (subcubeFast 9 0) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h16Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice15 : Slice h0R h0G (subcubeFast 8 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h18Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice14 : Slice h0R h0G (subcubeFast 8 0) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h19Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice13 : Slice h0R h0G (subcubeFast 4 32) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h20Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice12 : Slice h0R h0G (subcubeFast 4 8) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h21Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice11 : Slice h0R h0G (subcubeFast 4 0) 9 := slice_fast_direct (zDead := 0) (by decide +kernel) h22Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice10 : Slice h0R h0G (subcubeFast 2 16) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h31Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice9 : Slice h0R h0G (subcubeFast 2 8) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h32Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice8 : Slice h0R h0G (subcubeFast 2 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h33Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice7 : Slice h0R h0G (subcubeFast 2 0) 10 := slice_fast_direct (zDead := 0) (by decide +kernel) h34Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice6 : Slice h0R h0G (subcubeFast 1 16) 7 := slice_fast_direct (zDead := 0) (by decide +kernel) h35Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice5 : Slice h0R h0G (subcubeFast 1 4) 5 := slice_fast_direct (zDead := 0) (by decide +kernel) h36Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice4 : Slice h0R h0G (subcubeFast 1 0) 10 := slice_fast_direct (zDead := 0) (by decide +kernel) h37Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice3 : Slice h0R h0G (subcubeFast 0 32) 10 := slice_fast_direct (zDead := 0) (by decide +kernel) h38Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice2 : Slice h0R h0G (subcubeFast 0 16) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h46Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice1 : Slice h0R h0G (subcubeFast 0 8) 8 := slice_fast_direct (zDead := 0) (by decide +kernel) h47Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Slice0 : Slice h0R h0G (subcubeFast 0 4) 6 := slice_fast_direct (zDead := 0) (by decide +kernel) h48Bound
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0SlicesOk : btAll (fun o => ∀ p, o = some p → Slice h0R h0G p.1 p.2) h0Slices := btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice h0R h0G p.1 p.2) (forall_cons (fun _ h => by cases h; exact h0Slice0) (forall_cons (fun _ h => by cases h; exact h0Slice1) (forall_cons (fun _ h => by cases h; exact h0Slice2) (forall_cons (fun _ h => by cases h; exact h0Slice3) (forall_cons (fun _ h => by cases h; exact h0Slice4) (forall_cons (fun _ h => by cases h; exact h0Slice5) (forall_cons (fun _ h => by cases h; exact h0Slice6) (forall_cons (fun _ h => by cases h; exact h0Slice7) (forall_cons (fun _ h => by cases h; exact h0Slice8) (forall_cons (fun _ h => by cases h; exact h0Slice9) (forall_cons (fun _ h => by cases h; exact h0Slice10) (forall_cons (fun _ h => by cases h; exact h0Slice11) (forall_cons (fun _ h => by cases h; exact h0Slice12) (forall_cons (fun _ h => by cases h; exact h0Slice13) (forall_cons (fun _ h => by cases h; exact h0Slice14) (forall_cons (fun _ h => by cases h; exact h0Slice15) (forall_cons (fun _ h => by cases h; exact h0Slice16) (forall_cons (fun _ h => by cases h; exact h0Slice17) (forall_cons (fun _ h => by cases h; exact h0Slice18) (forall_cons (fun _ h => by cases h; exact h0Slice19) (forall_cons (fun _ h => by cases h; exact h0Slice20) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0PoolsOk : btAll (fun o => ∀ c, o = some c → ValidPool h0R h0G c) h0Pools := buildPoolsBT_sound h0SlicesOk
def h0Empty : BT (List (List Nat)) := BT.empty
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0EmptyOk : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G (7 - 1) xs.toFinset) h0Empty := trivial
def h0Block7_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,18],[2,4,6,8,9,10,22,25,27])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test7_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 7 h0Block7_0 = true := by decide +kernel
def h0Nodes7 : List NodeSpec := h0Block7_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check7 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Empty 7 h0Nodes7 = true := h0Test7_0
def h0Bucket7 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes7
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket7Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 7 xs.toFinset) h0Bucket7 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0EmptyOk h0Check7
def h0Block8_0 : List NodeSpec := nodesWithIdentity [([0,1,2,3,4,5,13],[2,4,7,8,9,10,14,15,16]),([0,1,2,3,4,5,15],[0,5,6,7,8,9,10,17,18,19]),([0,1,2,3,4,5,14],[0,1,6,7,8,9,10,14,19,22]),([0,1,2,3,4,5,18],[2,4,6,8,9,10,22,25,26,27]),([0,1,2,3,4,5,19],[0,2,6,7,9,10,22,28,29]),([0,1,2,3,4,5,20],[1,4,6,8,9,10,15,16,22,30]),([0,1,2,3,4,5,22],[0,1,6,7,9,10,15,22,27,31,32,33,34,35,36,37]),([0,1,2,3,4,5,21],[0,1,2,6,7,9,10,16,22,30,42]),([0,1,2,3,4,5,27],[0,4,6,7,9,10,15,16,22,63,64]),([0,1,2,3,4,5,29],[0,1,6,8,9,10,16,22,65,66,67,68,69,70,71,72]),([0,1,2,3,4,5,28],[0,1,2,6,8,9,10,15,22,42,64])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test8_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Block8_0 = true := by decide +kernel
def h0Nodes8 : List NodeSpec := h0Block8_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check8 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket7 8 h0Nodes8 = true := h0Test8_0
def h0Bucket8 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes8
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket8Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 8 xs.toFinset) h0Bucket8 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket7Ok h0Check8
def h0Block9_0 : List NodeSpec := [([0,1,2,3,4,5,7],[0,1,2,3,4,5,6,7,8,9,10],[0]),([0,1,2,3,4,5,12],[0,1,2,4,6,7,8,9,10,13],[0]),([0,1,2,3,4,5,16],[0,1,2,4,6,7,8,9,10,20,21],[0]),([0,1,2,3,4,5,17],[0,1,2,4,6,9,10,24],[0]),([0,1,2,3,4,5,23],[0,1,2,4,6,7,9,10,39,41,43,44,45],[0,1]),([0,1,2,3,4,5,24],[0,1,2,4,5,6,8,9,10,47,49,51,52,53,54],[0]),([0,1,2,3,4,25],[4,8,9,50,55,56,57,58,59],[0]),([0,1,2,3,4,5,26],[0,1,2,4,6,9,10,47,61,62],[0]),([0,1,2,3,4,5,30],[0,1,2,4,6,8,9,10,47,73,75,76,77,78],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test9_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Block9_0 = true := by decide +kernel
def h0Nodes9 : List NodeSpec := h0Block9_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check9 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket8 9 h0Nodes9 = true := h0Test9_0
def h0Bucket9 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes9
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket9Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 9 xs.toFinset) h0Bucket9 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket8Ok h0Check9
def h0Block10_0 : List NodeSpec := [([0,1,2,3,4,5,6],[0,1,2,3,4,5,6,7,8,9,10,11,12],[0]),([0,1,2,3,4,5,8],[0,1,2,6,7,8,9,10,13,20,23],[0]),([0,1,2,3,4,5,9],[0,1,2,4,6,7,9,10,24,38,39,40],[0,1]),([0,1,2,3,4,5,10],[0,1,2,4,5,6,7,8,9,10,46,47,48,49,50],[0]),([0,1,2,3,4,5,11],[0,1,2,4,6,7,8,9,10,47,60,61,73,74],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test10_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Block10_0 = true := by decide +kernel
def h0Nodes10 : List NodeSpec := h0Block10_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check10 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket9 10 h0Nodes10 = true := h0Test10_0
def h0Bucket10 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes10
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket10Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 10 xs.toFinset) h0Bucket10 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket9Ok h0Check10
def h0Block11_0 : List NodeSpec := [([0,1,2,3,4,5],[0,1,2,10],[0,1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Test11_0 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket10 11 h0Block11_0 = true := by decide +kernel
def h0Nodes11 : List NodeSpec := h0Block11_0
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Check11 : checkNodesBT h0W h0G h0Mask h0Pools h0Autos h0Bucket10 11 h0Nodes11 = true := h0Test11_0
def h0Bucket11 : BT (List (List Nat)) := buildBucketsBT h0W h0Nodes11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bucket11Ok : btAll (fun bk => ∀ xs ∈ bk, Impossible h0G 11 xs.toFinset) h0Bucket11 := buildBucketsBT_sound (by decide) h0Pairs h0WOk h0PoolsOk h0AutosOk h0Bucket10Ok h0Check11
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma h0Bound : Lower h0R h0G 12 := lower_of_forestBT (essPairs := [(VAR 0,2,3),(VAR 1,1,3),(VAR 2,1,5),(VAR 3,2,10),(VAR 4,1,17),(VAR 5,9,41)]) (by decide +kernel) h0Bucket11Ok (by decide +kernel)
def wit : List PEqualNP.CircuitLowerBounds.Gate := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 3]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 4]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 14]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 15]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 16]⟩,⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 17]⟩]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by simp [PEqualNP.MetaComplexity.Monotone2, wit]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4294901480 * 2 ^ 32 + 4276808936) ||| ((4294901480 * 2 ^ 32 + 4276808936) <<< 64)).testBit r.val := by decide +kernel
lemma low_root : Lower (varsOf 63) ((4294901480 * 2 ^ 32 + 4276808936) ||| ((4294901480 * 2 ^ 32 + 4276808936) <<< 64)) 12 := h0Bound
end PEqualNP.Outside.L_meta_46988
theorem PEqualNP.Outside.L_meta_46988 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901480 * 2 ^ 32 + 4276808936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901480 * 2 ^ 32 + 4276808936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_46988.table2_of_lower (4294901480 * 2 ^ 32 + 4276808936) (by decide) (by decide) (by decide) (by decide)
    12 PEqualNP.Outside.L_meta_46988.low_root
    PEqualNP.Outside.L_meta_46988.wit PEqualNP.Outside.L_meta_46988.wo (by decide)
    PEqualNP.Outside.L_meta_46988.wit_mono PEqualNP.Outside.L_meta_46988.wit_eval s hcs
