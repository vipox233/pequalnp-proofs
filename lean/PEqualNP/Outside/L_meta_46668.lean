import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46668
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
theorem bin_four (o : Nat) : ∃ e, e < 4 ∧ ∀ a b, bin o a b = bin e a b := by
  by_cases h : o < 4
  · exact ⟨o,h,fun _ _ => rfl⟩
  · refine ⟨3,by omega,fun a b => ?_⟩
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
def LowN (R : List Nat) (T L : Nat) : Prop := Lower true (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice true (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

structure BaseP (T : Nat) (R : List Nat) : Prop where
  lt : T < 2^128
  plain : plainWord (W T) = true
  nodup : (rootsW R).Nodup
  plainR : (rootsW R).all plainWord = true
  ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a
  prop : proper (W T)

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

theorem lowOf {T R E K} (hB : baseOK T R E = true) (h : Impossible true (W T) K (rootsW R).toFinset) :
    LowN R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
theorem lowCount {T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN R T (K+1) := by
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

theorem mkSlice {R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN R T (d,L,vs) := by
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

def av (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || Nat.beq x (Nat.xor d m))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available true bank (RF f v)
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
theorem av_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS f bank P)
    (h : av d P v = true) : Available true bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | h⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv rfl e
    rwa [inv_inv'] at e'
theorem rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
theorem pay_nb {f : Row → Row} {roots bank p P} (o a b : Nat) (hr : Reach true roots p bank) (hP : PS f bank P)
    (ha : Available true bank (RF f a)) (hb : Available true bank (RF f b)) :
    ∃ next, Reach true roots (p+1) next ∧ PS f next P ∧ Available true next (RF f (nb o a b)) ∧
      ∀ v, Available true bank v → Available true next v := by
  obtain ⟨e,he,heq⟩ := bin_four o
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) (Or.inr ⟨rfl,he⟩) ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
theorem getD_ps {f : Row → Row} {bank P} (hP : PS f bank P) (i : Nat) : Available true bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
theorem mkPool_ok {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach true roots p bank)
    (hP : PS f bank P) : ∃ next, Reach true roots (p+cs.length) next ∧ PS f next (mkPool P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
    have : PS f next (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h2 v hv
      · rw [List.mem_singleton.mp hv]
        exact h3
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av c.1 c.2.2.2) && keepB c.1 c.2.2.2 ka a && keepB c.1 c.2.2.2 kb b &&
  (bif av c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av c.1 c.2.2.2 a && av c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def sepEval (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  let e := fun v => (Nat.testBit v p.1 == Nat.testBit v p.2)
  e z && (!ka || e a) && (!kb || e b) && rest.all e
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && (T.testBit p.1 != T.testBit p.2)

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

def CutP (R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach true (roots.map observe) c.2.2.1 bank ∧ PS f bank c.2.2.2 ∧
    ∀ p bank, Reach true (roots.map observe) p bank → Available true bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

theorem cut_sound {R T c k rest a b o ka kb} (hc : CutP R T c)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb c = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach true (roots.map observe) q bank' ∧ PS f bank' c.2.2.2 ∧ Available true bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply true bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available true bank' v := by
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

theorem sep_sound {T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval rest a b (nb o a b) ka kb p = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,bne_iff_ne] at hT
  obtain ⟨⟨p1,p2⟩,hd⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  intro k' _ run
  obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W]; exact hd)
  apply hne
  rw [List.mem_toFinset] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rw [bit_W,bit_W]; exact h1
  rcases mem_kept hv with rfl | hv'
  · cases ka
    · cases kb
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx
      · rcases List.mem_cons.mp hv with e | hv
        · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
        · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
          rw [←e,bit_W,bit_W]; exact h4 x hx
    · rw [bit_W,bit_W]; exact h2.resolve_left (by simp)
  · cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv'
      rw [←e,bit_W,bit_W]; exact h4 x hx
    · rcases List.mem_cons.mp hv' with e | hv
      · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx

abbrev StD := List Nat × List Nat × List Nat × List (List Nat)
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
def mkCut (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool (initPool s.1 s.2.2) c.2)
def hintOK (k : Nat) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 100 then (match cuts[i]? with
    | some c => cutEval k rest a b z ka kb c
    | none => false)
  else (match seps[i-100]? with
    | some q => sepEval rest a b z ka kb q
    | none => false)
def kidOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK k cuts seps rest a b z kk.1 kk.2) ||
  next.any (beqL (kidN rest a b z kk.1 kk.2))
def pairOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  [0,1,2,3].all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK k next cuts seps p.2.2 hints p.1 p.2.1 z)
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
def stOK (T : Nat) (K : List CutV) (P : List (Nat × Nat)) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) &&
  allZip (pairOK k next (st.2.1.filterMap fun i => K[i]?) (st.2.2.1.filterMap fun i => P[i]?) st.1) (pairs st.1) st.2.2.2
def levelOK (T : Nat) (K : List CutV) (P : List (Nat × Nat)) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK T K P k next)
def LevelN (R : List Nat) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible true (W T) k (st.1.map W).toFinset
theorem cutsGood {R T} {Z : List SliceD} {C : List (Nat × List (Nat × Nat × Nat))} (hZ : ∀ s ∈ Z, SliceN R T s)
    (hC : C.all (fun c => Nat.blt c.1 Z.length) = true) : ∀ c ∈ C.map (mkCut Z), CutP R T c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using List.all_eq_true.mp hC q hq
  have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
    exact List.getElem_mem hi
  obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
  have ps : PS f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
    intro v hv'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=true) (roots:=roots.map observe)) ps
  refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
  simpa [mkCut] using b1

theorem stStep {R T E K P k next st} (hB : baseOK T R E = true) (hK : ∀ c ∈ K, CutP R T c) (hP : P.all (sepOK T) = true)
    (hn : ∀ s ∈ next, Impossible true (W T) k (s.map W).toFinset)
    (h : stOK T K P k next st = true) : Impossible true (W T) (k+1) (st.1.map W).toFinset := by
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
  have good : ∀ c ∈ st.2.1.filterMap (fun i => K[i]?), CutP R T c := by
    intro c hc
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hc
    exact hK c (List.mem_of_getElem? hi)
  have hs : ∀ q ∈ st.2.2.1.filterMap (fun i => P[i]?), sepOK T q = true := by
    intro q hq
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hq
    exact List.all_eq_true.mp hP q (List.mem_of_getElem? hi)
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have hd4 : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp

  have core : ∀ (o : Nat) (ja jb : Bool), o < 4 → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible true (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (by
      have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      simpa using this)
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
    rcases hk with (hk | hk) | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      cases hb : Nat.blt i 100
      · rw [hb,cond_false] at hi
        cases hg : (st.2.2.1.filterMap (fun i => P[i]?))[i-100]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact sep_sound (hs q (List.mem_of_getElem? hg)) hi
      · rw [hb,cond_true] at hi
        cases hg : (st.2.1.filterMap (fun i => K[i]?))[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (good q (List.mem_of_getElem? hg)) nk hi
    · obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hk
      rw [←kid_fin]
      rw [beqL_ok e]
      exact hn s hs'
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
  · have r := core d ka kb hd4 (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have f4 : flipOp d < 4 := by
      rcases hfl.1 with h | ⟨_,h⟩ <;> omega
    have r := core (flipOp d) kb ka f4 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

theorem levelStep {R T E K P k D' D} (hB : baseOK T R E = true) (hK : ∀ c ∈ K, CutP R T c) (hP : P.all (sepOK T) = true)
    (hI : LevelN R T k D') (h : levelOK T K P k (D'.map Prod.fst) D = true) : LevelN R T (k+1) D := by
  intro st hst
  refine stStep hB hK hP ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
theorem chunks {T : Nat} {K : List CutV} {P : List (Nat × Nat)} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK T K P k next ((D.drop (i*c)).take c) = true) : levelOK T K P k next D = true := by
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
theorem lowSearch {R T E K D} (hB : baseOK T R E = true) (hI : LevelN R T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this

def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124264 * 2 ^ 32 + 4276812936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [0, 3]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.or, [2, 10]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.and, [9, 12]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.and, [11, 16]⟩,
    ⟨.or, [13, 17]⟩], 18⟩
theorem witnessMonotone : PEqualNP.MetaComplexity.Monotone2 smallCircuit := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.size = 13 := rfl

def decNat (b : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc.reverse
  | f+1, n, acc => bif Nat.beq n 0 then acc.reverse else decNat b f (n / b) ((n % b - 1) :: acc)
def dL (n : Nat) : List Nat := decNat 4096 200 n []
def dS (n : Nat) : List Nat := decNat 256 200 n []
def decH : Nat → Nat → List Nat → List (List Nat) → List (List Nat)
  | 0, _, cur, acc => (cur.reverse :: acc).reverse
  | f+1, n, cur, acc =>
    bif Nat.beq n 0 then (cur.reverse :: acc).reverse
    else bif Nat.beq (n % 256) 255 then decH f (n / 256) [] (cur.reverse :: acc)
    else decH f (n / 256) ((n % 256 - 1) :: cur) acc
def dH (n : Nat) : List (List Nat) := decH 4096 n [] []
def trip : List Nat → List (Nat × Nat × Nat)
  | a :: b :: c :: r => (a, b, c) :: trip r
  | _ => []
def aH (nc ns : Nat) : List (List Nat) := List.replicate 64 ((List.range ns).map (· + 100) ++ List.range nc)
def pH (n nc ns : Nat) : List (List Nat) := (decNat 16 64 n []).map (fun c => (List.range ns).map (· + 100) ++ c :: List.range nc)
def qH (pal ix : Nat) : List (List Nat) := (decNat 16 64 ix []).map (fun i => (dH pal).getD i [])
def bF (n off w : Nat) : Nat := (n >>> off) % (2 ^ w)
def tL : Nat → Nat → Nat → Nat → List Nat
  | 0, _, _, _ => []
  | c+1, n, off, w => bF n off w :: tL c n (off + w) w
def pHs (nc ns wc ws n : Nat) : Nat → Nat → List (List Nat)
  | 0, _ => []
  | p+1, off =>
    ((bif Nat.beq (bF n off wc) 0 then [] else [bF n off wc - 1]) ++
      (bif Nat.beq (bF n (off + wc) ws) 0 then [] else [bF n (off + wc) ws + 99]) ++
      List.range nc ++ (List.range ns).map (· + 100)) :: pHs nc ns wc ws n p (off + wc + ws)
def mkSt (ws : List Nat) (n : Nat) : StD :=
  (ws, tL (bF n 0 7) n 22 12, tL (bF n 7 8) n (22 + 12 * bF n 0 7) 8,
    pHs (bF n 0 7) (bF n 7 8) (bF n 15 3) (bF n 18 4) n 64 (22 + 12 * bF n 0 7 + 8 * bF n 7 8))
def dC (n : Nat) : Nat × List (Nat × Nat × Nat) :=
  match decNat 256 200 n [] with
  | s :: ds => (s, trip ds)
  | [] => (0, [])
def dw (n : Nat) : Nat := n * 18446744073709551617
def w0 : Nat := dw 0xf0f0f0f0f0f0f0f0
def w1 : Nat := dw 0xaaaaaaaaaaaaaaaa
def w2 : Nat := dw 0xcccccccccccccccc
def w3 : Nat := dw 0xff00ff00ff00ff00
def w4 : Nat := dw 0xffff0000ffff0000
def w5 : Nat := dw 0xffffffff00000000
def w6 : Nat := dw 0xeeeeeeeeeeeeeeee
def w7 : Nat := dw 0xf0f00000f0f00000
def w8 : Nat := dw 0xffccffccffccffcc
def w9 : Nat := dw 0xffaaffaaffaaffaa
def w10 : Nat := dw 0x4444444444444444
def w11 : Nat := dw 0xfafaaaaafafaaaaa
def w12 : Nat := dw 0xc0c0c0c0c0c0c0c0
def w13 : Nat := dw 0xffffccccffffcccc
def w14 : Nat := dw 0xf000f000f000f000
def w15 : Nat := dw 0xffffaaaaffffaaaa
def w16 : Nat := dw 0xcc00cc00cc00cc00
def w17 : Nat := dw 0x3030303030303030
def w18 : Nat := dw 0x5050505050505050
def w19 : Nat := dw 0xcccc0000cccc0000
def w20 : Nat := dw 0xfcfcfcfcfcfcfcfc
def w21 : Nat := dw 0xeaeaeaeaeaeaeaea
def w22 : Nat := dw 0x2222222222222222
def w23 : Nat := dw 0xff000000ff000000
def w24 : Nat := dw 0xfafafafafafafafa
def w25 : Nat := dw 0xee00ee00ee00ee
def w26 : Nat := dw 0xffff00000000
def w27 : Nat := dw 0xcc00cc00cc00cc
def w28 : Nat := dw 0x8888888888888888
def w29 : Nat := dw 0xffffffffffff0000
def w30 : Nat := dw 0xeeee0000eeee0000
def w31 : Nat := dw 0xff88ff88ff88ff88
def w32 : Nat := dw 0xe0e0e0e0e0e0e0e0
def w33 : Nat := dw 0xeeeeaaaaeeeeaaaa
def w34 : Nat := dw 0xfaaafaaafaaafaaa
def w35 : Nat := dw 0xffaaaaaaffaaaaaa
def w36 : Nat := dw 0x3322332233223322
def w37 : Nat := dw 0x3300330033003300
def w38 : Nat := dw 0xffff8888ffff8888
def w39 : Nat := dw 0x5555000055550000
def w40 : Nat := dw 0xe0e0e0e0e0e0e0e
def w41 : Nat := dw 0x5500550055005500
def w42 : Nat := dw 0xfff0fff0fff0fff0
def w43 : Nat := dw 0xc0ccccc0c0ccccc
def w44 : Nat := dw 0xf00ff000f00ff00
def w45 : Nat := dw 0xf000f000f000f0
def w46 : Nat := dw 0xfcccfcccfcccfccc
def w47 : Nat := dw 0xeeee0000eeee
def w48 : Nat := dw 0x5555555500000000
def w49 : Nat := dw 0xfffff0f0fffff0f0
def w50 : Nat := dw 0xc0c0c0c0c0c0c0c
def w51 : Nat := dw 0xfff00000fff00000
def w52 : Nat := dw 0xcccc0000cccc
def w53 : Nat := dw 0xa0a0a0a0a0a0a0a0
def w54 : Nat := dw 0xa0a0a0a0a0a0a0a
def w55 : Nat := dw 0xffaa0000ffaa0000
def w56 : Nat := dw 0xee00ee00ee00ee00
def w57 : Nat := dw 0xeeaaeeaaeeaaeeaa
def w58 : Nat := dw 0xf0f00000f0f0
def w59 : Nat := dw 0xffffeeeeffffeeee
def w60 : Nat := dw 0xfcfcccccfcfccccc
def w61 : Nat := dw 0xcc88cc88cc88cc88
def w62 : Nat := dw 0xfff0ff00fff0ff00
def w63 : Nat := dw 0xeeeeeeeecccccccc
def w64 : Nat := dw 0x3333333300000000
def w65 : Nat := dw 0x5544554455445544
def w66 : Nat := dw 0x3333000033330000
def w67 : Nat := dw 0xf0a0f0a0f0a0f0a0
def w68 : Nat := dw 0xf8f8f8f8f8f8f8f8
def w69 : Nat := dw 0xf0f0f0f000000000
def w70 : Nat := dw 0x7777000077770000
def w71 : Nat := dw 0xff000000ff0000
def w72 : Nat := dw 0xf0c0f0c0f0c0f0c0
def w73 : Nat := dw 0x33cc33cc33cc33cc
def w74 : Nat := dw 0xaa00aa00aa00aa
def w75 : Nat := dw 0xecececececececec
def w76 : Nat := dw 0xf0f0f0f00000000
def w77 : Nat := dw 0xaaaa0000aaaa
def w78 : Nat := dw 0xccc0ccc0ccc0ccc
def w79 : Nat := dw 0x5555444455554444
def w80 : Nat := dw 0xffffffffcccccccc
def w81 : Nat := dw 0xffffffffaaaaaaaa
def w82 : Nat := dw 0x3f003f003f003f00
def w83 : Nat := dw 0xbabababababababa
def w84 : Nat := dw 0xfff00000fff0000
def w85 : Nat := dw 0xfcf0cc00fcf0cc00
def w86 : Nat := dw 0x3333222233332222
def w87 : Nat := dw 0xffffeeee00000000
def w88 : Nat := dw 0xaaaaaaaa00000000
def w89 : Nat := dw 0x7070707070707070
def w90 : Nat := dw 0xdcdcdcdcdcdcdcdc
def w91 : Nat := dw 0x3300ff003300ff00
def w92 : Nat := dw 0xcccccc00cccccc
def w93 : Nat := dw 0xe0eeeee0e0eeeee
def w94 : Nat := dw 0xfaaaaaaafaaaaaaa
def w95 : Nat := dw 0xeaeaaaaaeaeaaaaa
def w96 : Nat := dw 0xf0affaa0f0affaa
def w97 : Nat := dw 0xffff3333ffff0000
def w98 : Nat := dw 0xeeeeeeee
def w99 : Nat := dw 0xe0e0e0eeeeeeeee
def w100 : Nat := dw 0xcccccccc00000000
def w101 : Nat := dw 0xaa00aa00aa00aa00
def w102 : Nat := dw 0xffeeffeeffeeffee
def w103 : Nat := dw 0xffcc0000ffcc0000
def w104 : Nat := dw 0xf0cffcc0f0cffcc
def w105 : Nat := dw 0xf000f000f000f00
def w106 : Nat := dw 0xf0f0f0f0
def w107 : Nat := dw 0xeeeeeeeeeeee0000
def w108 : Nat := dw 0xcccceeeecccceeee
def w109 : Nat := dw 0x3232323232323232
def w110 : Nat := dw 0x5454545454545454
def w111 : Nat := dw 0x5050000050500000
def w112 : Nat := dw 0xafaf0000afaf0000
def w113 : Nat := dw 0xa0a0f0f0a0a0f0f0
def w114 : Nat := dw 0xffc0ffc0ffc0ffc0
def w115 : Nat := dw 0xffccff00ffccff00
def w116 : Nat := dw 0xcececececececece
def w117 : Nat := dw 0xfffffffff0f0f0f0
def w118 : Nat := dw 0x5555555555550000
def w119 : Nat := dw 0xeeeeeeee00000000
def w120 : Nat := dw 0xfcfcfcfccccccccc
def w121 : Nat := dw 0xffffaaaaffff0000
def w122 : Nat := dw 0xffffff88ff00ff00
def w123 : Nat := dw 0x1e1e1e1e1e1e1e1e
def w124 : Nat := dw 0x7700770077007700
def w125 : Nat := dw 0x3330333033303330
def w126 : Nat := dw 0xff44ff44ff44ff44
def w127 : Nat := dw 0xffccccccffcccccc
def w128 : Nat := dw 0xee00aa00ee00aa
def w129 : Nat := dw 0xfffff0f0ffff0000
def w130 : Nat := dw 0xcccccccc
def w131 : Nat := dw 0xf0f0a0a0f0f0a0a0
def w132 : Nat := dw 0xaaaaaaaa
def w133 : Nat := dw 0xfcfcfcfcfcfc0000
def w134 : Nat := dw 0xfefefefefefefefe
def w135 : Nat := dw 0xaaeeaaeeaaeeaaee
def w136 : Nat := dw 0xff330000ff330000
def w137 : Nat := dw 0xbbbbaaaabbbbaaaa
def w138 : Nat := dw 0xf0fc00ccf0fc00cc
def w139 : Nat := dw 0x3222322232223222
def w140 : Nat := dw 0xeee0eee0eee0eee
def w141 : Nat := dw 0x3232222232322222
def w142 : Nat := dw 0x3322222233222222
def w143 : Nat := dw 0xf3f03300f3f03300
def w144 : Nat := dw 0xea00ea00ea00ea
def w145 : Nat := dw 0xfa00aa00fa00aa
def w146 : Nat := dw 0xddddddddcccccccc
def w147 : Nat := dw 0xfcfc0000fcfc
def w148 : Nat := dw 0xaaaa8888aaaa8888
def w149 : Nat := dw 0xfafafafaaaaaaaaa
def w150 : Nat := dw 0xeeeeeeeeaaaaaaaa
def w151 : Nat := dw 0xeeee0000cccc
def w152 : Nat := dw 0x11111111eeeeeeee
def w153 : Nat := dw 0xe000e00ee00ee
def w154 : Nat := dw 0xfe00fe00fe00fe
def w155 : Nat := dw 0x1010101010101010
def w156 : Nat := dw 0xff50ff50ff50ff50
def w157 : Nat := dw 0xddddccccddddcccc
def w158 : Nat := dw 0xc0c00000c0c00000
def w159 : Nat := dw 0x3f3f00003f3f0000
def w160 : Nat := dw 0x3030f0f03030f0f0
def w161 : Nat := dw 0xf0000000f0000000
def w162 : Nat := dw 0xaafaaafaaafaaafa
def w163 : Nat := dw 0xf0f0f000f0f0f0
def w164 : Nat := dw 0xaaffaaaaaaffaaaa
def w165 : Nat := dw 0xc888c888c888c888
def w166 : Nat := dw 0xc8c88888c8c88888
def w167 : Nat := dw 0xeeeeee00eeeeee
def w168 : Nat := dw 0xcc888888cc888888
def w169 : Nat := dw 0xea00ea00ea00ea00
def w170 : Nat := dw 0x3f2a3f2a3f2a3f2a
def w171 : Nat := dw 0xee00aa00ee00aa00
def w172 : Nat := dw 0x3322ffaa3322ffaa
def w173 : Nat := dw 0xfa00aa00fa00aa00
def w174 : Nat := dw 0xfac8aa88fac8aa88
def w175 : Nat := dw 0xaeaeeeeeaeaeeeee
def w176 : Nat := dw 0xafaaffaaafaaffaa
def w177 : Nat := dw 0xfeeefeeefeeefeee
def w178 : Nat := dw 0xfefeeeeefefeeeee
def w179 : Nat := dw 0xfffaffaafffaffaa
def w180 : Nat := dw 0xf5f50000f5f50000
def w181 : Nat := dw 0xfcfc0000fcfc0000
def w182 : Nat := dw 0xaeaeaeaeaeaeaeae
def w183 : Nat := dw 0xffff3030ffff3030
def w184 : Nat := dw 0xffffeeee
def w185 : Nat := dw 0xffff2222ffff2222
def w186 : Nat := dw 0xfafa0000fafa
def w187 : Nat := dw 0xccccfcfcccccfcfc
def w188 : Nat := dw 0x3333333333330000
def w189 : Nat := dw 0xffff5555ffff0000
def w190 : Nat := dw 0xf0f0a0a0f0f0a0a
def w191 : Nat := dw 0x30f030f030f030f0
def w192 : Nat := dw 0xaaaa0000aaaa0000
def w193 : Nat := dw 0x44004400440044
def w194 : Nat := dw 0xddccddccddccddcc
def w195 : Nat := dw 0xff55ff00ff55ff00
def w196 : Nat := dw 0xff30ff30ff30ff30
def w197 : Nat := dw 0xcfcf0000cfcf0000
def w198 : Nat := dw 0xbbaabbaabbaabbaa
def w199 : Nat := dw 0xc0c0f0f0c0c0f0f0
def w200 : Nat := dw 0xff0f0000ff0f0000
def w201 : Nat := dw 0xf000f0f0f000f0f0
def w202 : Nat := dw 0x1100ff001100ff00
def w203 : Nat := dw 0xfe00ee00fe00ee
def w204 : Nat := dw 0x3332332233323322
def w205 : Nat := dw 0xbfaabfaabfaabfaa
def w206 : Nat := dw 0xffeaffeaffeaffea
def w207 : Nat := dw 0xbbaaffaabbaaffaa
def w208 : Nat := dw 0xffeeffaaffeeffaa
def w209 : Nat := dw 0x5444544454445444
def w210 : Nat := dw 0xaeeeaeeeaeeeaeee
def w211 : Nat := dw 0xfeee0000feee0000
def w212 : Nat := dw 0xffc8ff88ffc8ff88
def w213 : Nat := dw 0xfecceeccfecceecc
def w214 : Nat := dw 0xaaeeeeeeaaeeeeee
def w215 : Nat := dw 0xffeeeeeeffeeeeee
def w216 : Nat := dw 0xcceecceecceeccee
def w217 : Nat := dw 0x7777777700000000
def w218 : Nat := dw 0x3333333322222222
def w219 : Nat := dw 0x5555555544444444
def w220 : Nat := dw 0xbbbbbbbbaaaaaaaa
def w221 : Nat := dw 0x1111111100000000
def w222 : Nat := dw 0xffffffffeeeeeeee
def w223 : Nat := dw 0xffff0f0fffff0000
def w224 : Nat := dw 0xffffa0a0ffffa0a0
def w225 : Nat := dw 0xfafafafafafa0000
def w226 : Nat := dw 0x3333303033333030
def w227 : Nat := dw 0xffffc0c0ffffc0c0
def w228 : Nat := dw 0xffffaaaa00000000
def w229 : Nat := dw 0xffff0c0cffff0c0c
def w230 : Nat := dw 0xcccc8888cccc8888
def w231 : Nat := dw 0x444400004444
def w232 : Nat := dw 0xffffccccffff0000
def w233 : Nat := dw 0x33332222ffffaaaa
def w234 : Nat := dw 0xf0f0a0affffaaaa
def w235 : Nat := dw 0xe0e0e0e0c0c0c0c0
def w236 : Nat := dw 0xe0e0e0e0c0c0c0c
def w237 : Nat := dw 0xff0eff0effeeffee
def w238 : Nat := dw 0xc000c000c000c000
def w239 : Nat := dw 0x22aa22aa22aa22aa
def w240 : Nat := dw 0xaaa0aaa0aaa0aaa
def w241 : Nat := dw 0x4444cccc4444cccc
def w242 : Nat := dw 0x2222aaaa2222aaaa
def w243 : Nat := dw 0xf0e0f0e0f0e0f0e
def w244 : Nat := dw 0x3332333233323332
def w245 : Nat := dw 0x5554555455545554
def w246 : Nat := dw 0xfffafffafffafffa
def w247 : Nat := dw 0xfa00fa00fa00fa
def w248 : Nat := dw 0xf0a0f0a0f0a0f0a
def w249 : Nat := dw 0xfffcfffcfffcfffc
def w250 : Nat := dw 0xfc00fc00fc00fc
def w251 : Nat := dw 0xf0c0f0c0f0c0f0c
def w252 : Nat := dw 0x5550555055505550
def w253 : Nat := dw 0x4400440044004400
def w254 : Nat := dw 0x8c8c8c8c8c8c8c8c
def w255 : Nat := dw 0xaaff0000aaff0000
def w256 : Nat := dw 0x8888cccc8888cccc
def w257 : Nat := dw 0x30003000300030
def w258 : Nat := dw 0x33ff000033ff0000
def w259 : Nat := dw 0xff33ff00ff33ff00
def w260 : Nat := dw 0xccffccccccffcccc
def w261 : Nat := dw 0xcc00cccccc00cccc
def w262 : Nat := dw 0x1f001f001f001f00
def w263 : Nat := dw 0xf0effee0f0effee
def w264 : Nat := dw 0xdc50cc00dc50cc00
def w265 : Nat := dw 0xc4c0c4c0c4c0c4c
def w266 : Nat := dw 0x44cccc0044cccc
def w267 : Nat := dw 0x5540554055405540
def w268 : Nat := dw 0xffea0000ffea0000
def w269 : Nat := dw 0x1500150015001500
def w270 : Nat := dw 0x1515000015150000
def w271 : Nat := dw 0xffeaeaeaffeaeaea
def w272 : Nat := dw 0xffc0c0c0ffc0c0c0
def w273 : Nat := dw 0x5540404055404040
def w274 : Nat := dw 0xe0a0e0a0e0a0e0a0
def w275 : Nat := dw 0x1050105010501050
def w276 : Nat := dw 0xeeaa0000eeaa0000
def w277 : Nat := dw 0x1155000011550000
def w278 : Nat := dw 0xfefaeeaafefaeeaa
def w279 : Nat := dw 0xe0aeeaa0e0aeeaa
def w280 : Nat := dw 0xf0c00000f0c00000
def w281 : Nat := dw 0xf3f00000f3f0000
def w282 : Nat := dw 0x30f0f00030f0f0
def w283 : Nat := dw 0x5450440054504400
def w284 : Nat := dw 0xfaeaaaaafaeaaaaa
def w285 : Nat := dw 0x5554554455545544
def w286 : Nat := dw 0x5544550055445500
def w287 : Nat := dw 0x1010505010105050
def w288 : Nat := dw 0xf0e0f0a0f0e0f0a0
def w289 : Nat := dw 0x1100550011005500
def w290 : Nat := dw 0xfeeefaaafeeefaaa
def w291 : Nat := dw 0x5444500054445000
def w292 : Nat := dw 0xfcccf000fcccf000
def w293 : Nat := dw 0x444044404440444
def w294 : Nat := dw 0x555000005550000
def w295 : Nat := dw 0x5454444454544444
def w296 : Nat := dw 0x5550550055505500
def w297 : Nat := dw 0xfe00ee00fe00ee00
def w298 : Nat := dw 0x404444404044444
def w299 : Nat := dw 0xccc8cc88ccc8cc88
def w300 : Nat := dw 0x500550005005500
def w301 : Nat := dw 0xfc00cc00fc00cc
def w302 : Nat := dw 0xff0cffccff0cffcc
def w303 : Nat := dw 0x3330330033303300
def w304 : Nat := dw 0xcfccffcccfccffcc
def w305 : Nat := dw 0x50505000505050
def w306 : Nat := dw 0x5544444455444444
def w307 : Nat := dw 0xf0e0e0e0f0e0e0e0
def w308 : Nat := dw 0x44444400444444
def w309 : Nat := dw 0x1010f0f01010f0f0
def w310 : Nat := dw 0xf444f444f444f444
def w311 : Nat := dw 0xeaaaeaaaeaaaeaaa
def w312 : Nat := dw 0xeeaaaaaaeeaaaaaa
def w313 : Nat := dw 0xffa0ffa0ffa0ffa0
def w314 : Nat := dw 0xaa88aa88aa88aa88
def w315 : Nat := dw 0x22002200220022
def w316 : Nat := dw 0x6666666666666666
def w317 : Nat := dw 0xaaa0aaa0aaa0aaa0
def w318 : Nat := dw 0xccc0ccc0ccc0ccc0
def w319 : Nat := dw 0xfefe0000fefe
def w320 : Nat := dw 0xf0f0e0e0f0f0e0e0
def w321 : Nat := dw 0xf0f0e0e0f0f0e0e
def w322 : Nat := dw 0xffffeeeeffff0000
def w323 : Nat := dw 0xffff0000eeee
def w324 : Nat := dw 0xeeeee0e0eeeee0e0
def w325 : Nat := dw 0xeeee0e0eeeee0e0e
def w326 : Nat := dw 0xeeeeeeeee0e0e0e0
def w327 : Nat := dw 0xeeeeeeee0e0e0e0e
def w328 : Nat := dw 0xe0e0e0e0eeeeeeee
def w329 : Nat := dw 0xffff4444ffff4444
def w330 : Nat := dw 0xecec0000ecec
def w331 : Nat := dw 0xffff0a0affff0a0a
def w332 : Nat := dw 0xffff5050ffff5050
def w333 : Nat := dw 0xfffffafafffffafa
def w334 : Nat := dw 0x505000005050
def w335 : Nat := dw 0xcfcfcfcfcccccccc
def w336 : Nat := dw 0xeaeaeaeac0c0c0c0
def w337 : Nat := dw 0xffaaff88ffaaff88
def w338 : Nat := dw 0x222200002222
def w339 : Nat := dw 0xf0f0c0c0f0f0c0c0
def w340 : Nat := dw 0xfffffcfcfffffcfc
def w341 : Nat := dw 0x303000003030
def w342 : Nat := dw 0xf0f0c0c0f0f0c0c
def w343 : Nat := dw 0xfcfc0000cccc
def w344 : Nat := dw 0xecececececec0000
def w345 : Nat := dw 0xc0c0e0ecccceeee
def w346 : Nat := dw 0x7f007f007f007f00
def w347 : Nat := dw 0x70f070f070f070f0
def w348 : Nat := dw 0x4ccc4ccc4ccc4ccc
def w349 : Nat := dw 0x2aaa2aaa2aaa2aaa
def w350 : Nat := dw 0x8080808080808080
def w351 : Nat := dw 0x8800880088008800
def w352 : Nat := dw 0x4c4c4c4c4c4c4c4c
def w353 : Nat := dw 0xa000a000a000a000
def w354 : Nat := dw 0x5f005f005f005f00
def w355 : Nat := dw 0x44cc44cc44cc44cc
def w356 : Nat := dw 0x50f050f050f050f0
def w357 : Nat := dw 0x2a2a2a2a2a2a2a2a
def w358 : Nat := dw 0xf8f8f0f0f8f8f0f0
def w359 : Nat := dw 0xff88ff00ff88ff00
def w360 : Nat := dw 0x8888000088880000
def w361 : Nat := dw 0x1100110011001100
def w362 : Nat := dw 0x1111000011110000
def w363 : Nat := dw 0x4040404040404040
def w364 : Nat := dw 0xb0b0b0b0b0b0b0b0
def w365 : Nat := dw 0xbb00bb00bb00bb00
def w366 : Nat := dw 0x4444000044440000
def w367 : Nat := dw 0xbbbb0000bbbb0000
def w368 : Nat := dw 0x5000500050005000
def w369 : Nat := dw 0x50005000500050
def w370 : Nat := dw 0xaf00af00af00af00
def w371 : Nat := dw 0x55000000550000
def w372 : Nat := dw 0x88cc88cc88cc88cc
def w373 : Nat := dw 0xa0f0a0f0a0f0a0f0
def w374 : Nat := dw 0x5500000055000000
def w375 : Nat := dw 0xaa00ff00aa00ff00
def w376 : Nat := dw 0xc000c000c000c0
def w377 : Nat := dw 0x3000300030003000
def w378 : Nat := dw 0xcf00cf00cf00cf00
def w379 : Nat := dw 0x3030000030300000
def w380 : Nat := dw 0xcc000000cc000000
def w381 : Nat := dw 0x33000000330000
def w382 : Nat := dw 0xf030f030f030f030
def w383 : Nat := dw 0xcc000000cc0000
def w384 : Nat := dw 0xc0f0c0f0c0f0c0f0
def w385 : Nat := dw 0x3300000033000000
def w386 : Nat := dw 0xccff0000ccff0000
def w387 : Nat := dw 0xcc00ff00cc00ff00
def w388 : Nat := dw 0xccfcccfcccfcccfc
def w389 : Nat := dw 0xcc0ccc0ccc0ccc0c
def w390 : Nat := dw 0xf0000000f00000
def w391 : Nat := dw 0x1fff00001fff0000
def w392 : Nat := dw 0x1f00ff001f00ff00
def w393 : Nat := dw 0x10f0f0f010f0f0f0
def w394 : Nat := dw 0xf0fe00eef0fe00ee
def w395 : Nat := dw 0xeeeeeee0eeeeeee
def w396 : Nat := dw 0xe0ee00eee0ee00ee
def w397 : Nat := dw 0xf04ff440f04ff44
def w398 : Nat := dw 0xdcdcdc00dcdcdc
def w399 : Nat := dw 0x3310ff503310ff50
def w400 : Nat := dw 0xaf8cffccaf8cffcc
def w401 : Nat := dw 0x50dc00cc50dc00cc
def w402 : Nat := dw 0x7350330073503300
def w403 : Nat := dw 0x3f7f00003f7f0000
def w404 : Nat := dw 0x3f2affaa3f2affaa
def w405 : Nat := dw 0x3070f0f03070f0f0
def w406 : Nat := dw 0xf3f23322f3f23322
def w407 : Nat := dw 0xc4ccccc0c4ccccc
def w408 : Nat := dw 0xf3a23322f3a23322
def w409 : Nat := dw 0xd0cddcc0d0cddcc
def w410 : Nat := dw 0xddd0ccc0ddd0ccc
def w411 : Nat := dw 0x3f153f003f153f00
def w412 : Nat := dw 0x15ff000015ff0000
def w413 : Nat := dw 0xeaeaea00eaeaea
def w414 : Nat := dw 0xea00aa00ea00aa00
def w415 : Nat := dw 0xffeaffaaffeaffaa
def w416 : Nat := dw 0xea00aa00ea00aa
def w417 : Nat := dw 0x1500550015005500
def w418 : Nat := dw 0x3f2a2a2a3f2a2a2a
def w419 : Nat := dw 0xbbeebbeebbeebbee
def w420 : Nat := dw 0x1144114411441144
def w421 : Nat := dw 0x30c030c030c030c0
def w422 : Nat := dw 0xc030c030c030c030
def w423 : Nat := dw 0x33cc000033cc0000
def w424 : Nat := dw 0xcc330000cc330000
def w425 : Nat := dw 0x32fa22aa32fa22aa
def w426 : Nat := dw 0x504554405045544
def w427 : Nat := dw 0xf3c03300f3c03300
def w428 : Nat := dw 0xf0cc00ccf0cc00cc
def w429 : Nat := dw 0xafaeffeeafaeffee
def w430 : Nat := dw 0xfafeaaeefafeaaee
def w431 : Nat := dw 0x5054004450540044
def w432 : Nat := dw 0xfa32aa22fa32aa22
def w433 : Nat := dw 0xfbfabbaafbfabbaa
def w434 : Nat := dw 0x5150110051501100
def w435 : Nat := dw 0xc8fa88aac8fa88aa
def w436 : Nat := dw 0x10f050f010f050f0
def w437 : Nat := dw 0xeee0aaa0eee0aaa
def w438 : Nat := dw 0x3222faaa3222faaa
def w439 : Nat := dw 0x3777000037770000
def w440 : Nat := dw 0xc8888888c8888888
def w441 : Nat := dw 0xfeeeeeeefeeeeeee
def w442 : Nat := dw 0x444444404444444
def w443 : Nat := dw 0x3222222232222222
def w444 : Nat := dw 0x3700770037007700
def w445 : Nat := dw 0x4cc44cc04cc44cc
def w446 : Nat := dw 0x3070707030707070
def w447 : Nat := dw 0xe000e000e000e000
def w448 : Nat := dw 0xe0e00000e0e00000
def w449 : Nat := dw 0x1f1f00001f1f0000
def w450 : Nat := dw 0x10f010f010f010f0
def w451 : Nat := dw 0xee000000ee000000
def w452 : Nat := dw 0x11ff000011ff0000
def w453 : Nat := dw 0xf0e0f0e0f0e0f0e0
def w454 : Nat := dw 0xffee0000ffee0000
def w455 : Nat := dw 0xf010f010f010f010
def w456 : Nat := dw 0xff110000ff110000
def w457 : Nat := dw 0xee0eee0eee0eee0e
def w458 : Nat := dw 0xee00eeeeee00eeee
def w459 : Nat := dw 0xf4f44444f4f44444
def w460 : Nat := dw 0xff444444ff444444
def w461 : Nat := dw 0xc080c080c080c080
def w462 : Nat := dw 0xcf8acf8acf8acf8a
def w463 : Nat := dw 0x3070307030703070
def w464 : Nat := dw 0xcc880000cc880000
def w465 : Nat := dw 0x3377000033770000
def w466 : Nat := dw 0xc0d0c0d0c0d0c0d0
def w467 : Nat := dw 0xccdd0000ccdd0000
def w468 : Nat := dw 0xcc88ffaacc88ffaa
def w469 : Nat := dw 0xf0a00000f0a00000
def w470 : Nat := dw 0xf5f00000f5f0000
def w471 : Nat := dw 0x50f0f00050f0f0
def w472 : Nat := dw 0xd5c0d5c0d5c0d5c0
def w473 : Nat := dw 0xddcc5500ddcc5500
def w474 : Nat := dw 0xf5f05500f5f05500
def w475 : Nat := dw 0xeaea0000eaea0000
def w476 : Nat := dw 0x3fff00003fff0000
def w477 : Nat := dw 0xffc0ff00ffc0ff00
def w478 : Nat := dw 0x3f00ff003f00ff00
def w479 : Nat := dw 0xefaaefaaefaaefaa
def w480 : Nat := dw 0x30f0f0f030f0f0f0
def w481 : Nat := dw 0xfaeafaeafaeafaea
def w482 : Nat := dw 0xfffcffccfffcffcc
def w483 : Nat := dw 0xffeeaaaaffeeaaaa
def w484 : Nat := dw 0xe0e0a0a0e0e0a0a0
def w485 : Nat := dw 0xeeaaffaaeeaaffaa
def w486 : Nat := dw 0xfaaa0000faaa0000
def w487 : Nat := dw 0xfcccccccfccccccc
def w488 : Nat := dw 0xccccccc0ccccccc
def w489 : Nat := dw 0xeeaeeeaeeeaeeeae
def w490 : Nat := dw 0xf0a0a0a0f0a0a0a0
def w491 : Nat := dw 0xeeaaeeeeeeaaeeee
def w492 : Nat := dw 0xf3e23322f3e23322
def w493 : Nat := dw 0xf0ee00eef0ee00ee
def w494 : Nat := dw 0x15ea15ea15ea15ea
def w495 : Nat := dw 0xf3fc33ccf3fc33cc
def w496 : Nat := dw 0x30c33cc030c33cc
def w497 : Nat := dw 0xfcc0cc00fcc0cc00
def w498 : Nat := dw 0x11ee55aa11ee55aa
def w499 : Nat := dw 0x3666366636663666
def w500 : Nat := dw 0x3636666636366666
def w501 : Nat := dw 0x5fa55aa05fa55aa
def w502 : Nat := dw 0x3366666633666666
def w503 : Nat := dw 0xfec8ee88fec8ee88
def w504 : Nat := dw 0xfafa0000fafa0000
def w505 : Nat := dw 0xeecceecceecceecc
def w506 : Nat := dw 0xf3f30000f3f30000
def w507 : Nat := dw 0xfcf0fcf0fcf0fcf0
def w508 : Nat := dw 0xcfcccfcccfcccfcc
def w509 : Nat := dw 0xf7f00000f7f0000
def w510 : Nat := dw 0xfff80000fff80000
def w511 : Nat := dw 0xfff88888fff88888
def w512 : Nat := dw 0xf0e0f000f0e0f000
def w513 : Nat := dw 0xf0e0f000f0e0f00
def w514 : Nat := dw 0xfeeef000feeef000
def w515 : Nat := dw 0x1110fff01110fff0
def w516 : Nat := dw 0xeeeee000eeeee
def w517 : Nat := dw 0x5777000057770000
def w518 : Nat := dw 0xaaa88888aaa88888
def w519 : Nat := dw 0x5554444455544444
def w520 : Nat := dw 0xf080f080f080f080
def w521 : Nat := dw 0xfff8fff8fff8fff8
def w522 : Nat := dw 0x70007000700070
def w523 : Nat := dw 0xf080f080f080f08
def w524 : Nat := dw 0xf888f888f888f888
def w525 : Nat := dw 0x7770777077707770
def w526 : Nat := dw 0x8f888f888f888f88
def w527 : Nat := dw 0xfefef0f0fefef0f0
def w528 : Nat := dw 0xffeeff00ffeeff00
def w529 : Nat := dw 0xeee0eee0eee0eee0
def w530 : Nat := dw 0xe0eee0eee0eee0ee
def w531 : Nat := dw 0xbbb0bbb0bbb0bbb0
def w532 : Nat := dw 0x4f444f444f444f44
def w533 : Nat := dw 0xffecffecffecffec
def w534 : Nat := dw 0xec00ec00ec00ec
def w535 : Nat := dw 0x3320332033203320
def w536 : Nat := dw 0x5f4c5f4c5f4c5f4c
def w537 : Nat := dw 0x30ba30ba30ba30ba
def w538 : Nat := dw 0xa888a888a888a888
def w539 : Nat := dw 0x222022202220222
def w540 : Nat := dw 0xfffaaaaafffaaaaa
def w541 : Nat := dw 0xaaaaa000aaaaa
def w542 : Nat := dw 0xfffcccccfffccccc
def w543 : Nat := dw 0xccccc000ccccc
def w544 : Nat := dw 0xff08ff08ff08ff08
def w545 : Nat := dw 0xf0f8f0f8f0f8f0f8
def w546 : Nat := dw 0xffc8ffc8ffc8ffc8
def w547 : Nat := dw 0xccc8ccc8ccc8ccc8
def w548 : Nat := dw 0xc0e0c0e0c0e0c0e
def w549 : Nat := dw 0xe0e0c0c0e0e0c0c
def w550 : Nat := dw 0xff88ffccff88ffcc
def w551 : Nat := dw 0xaaa8aaa8aaa8aaa8
def w552 : Nat := dw 0xae00ae00ae00ae
def w553 : Nat := dw 0xfaf8faf8faf8faf8
def w554 : Nat := dw 0xf8f8fafaf8f8fafa
def w555 : Nat := dw 0x808080808080808
def w556 : Nat := dw 0x88008800880088
def w557 : Nat := dw 0xf2f2f2f2f2f2f2f2
def w558 : Nat := dw 0x202020202020202
def w559 : Nat := dw 0xff22ff22ff22ff22
def w560 : Nat := dw 0xf4f4f4f4f4f4f4f4
def w561 : Nat := dw 0x404040404040404
def w562 : Nat := dw 0xc8c8c8c8c8c8c8c8
def w563 : Nat := dw 0xc4c4c4c4c4c4c4c4
def w564 : Nat := dw 0xff0aff0aff0aff0a
def w565 : Nat := dw 0xa000a000a000a
def w566 : Nat := dw 0xcc44cc44cc44cc44
def w567 : Nat := dw 0xf0faf0faf0faf0fa
def w568 : Nat := dw 0xeeeecccceeeecccc
def w569 : Nat := dw 0xa8a8a8a8a8a8a8a8
def w570 : Nat := dw 0xa2a2a2a2a2a2a2a2
def w571 : Nat := dw 0xff0cff0cff0cff0c
def w572 : Nat := dw 0xc000c000c000c
def w573 : Nat := dw 0xaa22aa22aa22aa22
def w574 : Nat := dw 0xf0fcf0fcf0fcf0fc
def w575 : Nat := dw 0x8888aaaa8888aaaa
def w576 : Nat := dw 0xf0f08080f0f08080
def w577 : Nat := dw 0xfffff8f8fffff8f8
def w578 : Nat := dw 0x707000007070
def w579 : Nat := dw 0xf0f08080f0f0808
def w580 : Nat := dw 0xffff888800000000
def w581 : Nat := dw 0xffffffffffff8888
def w582 : Nat := dw 0xffff8888
def w583 : Nat := dw 0x777700000000
def w584 : Nat := dw 0x7777707077777070
def w585 : Nat := dw 0x8888f8f88888f8f8
def w586 : Nat := dw 0xf8f8f8f888888888
def w587 : Nat := dw 0x7777777770707070
def w588 : Nat := dw 0x88888888f8f8f8f8
def w589 : Nat := dw 0x8f8f8f8f88888888
def w590 : Nat := dw 0x7777777777770000
def w591 : Nat := dw 0xeeee2222eeee2222
def w592 : Nat := dw 0xffffe0e0ffffe0e0
def w593 : Nat := dw 0xfefefefe00000000
def w594 : Nat := dw 0xfefefefe
def w595 : Nat := dw 0xffff0e0effff0e0e
def w596 : Nat := dw 0x1111101011111010
def w597 : Nat := dw 0xeeeefefeeeeefefe
def w598 : Nat := dw 0xfefefefeeeeeeeee
def w599 : Nat := dw 0x1111111110101010
def w600 : Nat := dw 0xeeeeeeeefefefefe
def w601 : Nat := dw 0xefefefefeeeeeeee
def w602 : Nat := dw 0x1111111111110000
def w603 : Nat := dw 0xddddd0d0ddddd0d0
def w604 : Nat := dw 0x2222f2f22222f2f2
def w605 : Nat := dw 0xf2f2f2f222222222
def w606 : Nat := dw 0xddddddddd0d0d0d0
def w607 : Nat := dw 0x22222222f2f2f2f2
def w608 : Nat := dw 0x2f2f2f2f22222222
def w609 : Nat := dw 0xdddddddddddd0000
def w610 : Nat := dw 0xbbbbb0b0bbbbb0b0
def w611 : Nat := dw 0x4444f4f44444f4f4
def w612 : Nat := dw 0xf4f4f4f444444444
def w613 : Nat := dw 0xbbbbbbbbb0b0b0b0
def w614 : Nat := dw 0x44444444f4f4f4f4
def w615 : Nat := dw 0x4f4f4f4f44444444
def w616 : Nat := dw 0xbbbbbbbbbbbb0000
def w617 : Nat := dw 0xffffececffffecec
def w618 : Nat := dw 0xecececec00000000
def w619 : Nat := dw 0xecececec
def w620 : Nat := dw 0x3333202033332020
def w621 : Nat := dw 0x5f5f4c4c5f5f4c4c
def w622 : Nat := dw 0xa0a0ececa0a0ecec
def w623 : Nat := dw 0xececececa0a0a0a0
def w624 : Nat := dw 0x5f5f5f5f4c4c4c4c
def w625 : Nat := dw 0xa0a0a0a0ecececec
def w626 : Nat := dw 0xb3b3b3b3a0a0a0a0
def w627 : Nat := dw 0x5f5f5f5f5f5f0000
def w628 : Nat := dw 0xffff3232ffff3232
def w629 : Nat := dw 0x323200003232
def w630 : Nat := dw 0xfafac8c8fafac8c8
def w631 : Nat := dw 0xfafa3232fafa3232
def w632 : Nat := dw 0x32323232fafafafa
def w633 : Nat := dw 0xfafafafac8c8c8c8
def w634 : Nat := dw 0xfafafafa32323232
def w635 : Nat := dw 0xc8c8c8c8fafafafa
def w636 : Nat := dw 0xccccfefeccccfefe
def w637 : Nat := dw 0xffffceceffffcece
def w638 : Nat := dw 0xcece0000cece
def w639 : Nat := dw 0x3333020233330202
def w640 : Nat := dw 0xf5f5c4c4f5f5c4c4
def w641 : Nat := dw 0xa0acece0a0acece
def w642 : Nat := dw 0xcececece0a0a0a0a
def w643 : Nat := dw 0xf5f5f5f5c4c4c4c4
def w644 : Nat := dw 0xa0a0a0acececece
def w645 : Nat := dw 0x3b3b3b3b0a0a0a0a
def w646 : Nat := dw 0xf5f5f5f5f5f50000
def w647 : Nat := dw 0xffffdcdcffffdcdc
def w648 : Nat := dw 0xdcdc0000dcdc
def w649 : Nat := dw 0x3333101033331010
def w650 : Nat := dw 0xafaf8c8cafaf8c8c
def w651 : Nat := dw 0x5050dcdc5050dcdc
def w652 : Nat := dw 0xdcdcdcdc50505050
def w653 : Nat := dw 0xafafafaf8c8c8c8c
def w654 : Nat := dw 0x50505050dcdcdcdc
def w655 : Nat := dw 0x7373737350505050
def w656 : Nat := dw 0xafafafafafaf0000
def w657 : Nat := dw 0xffffeaeaffffeaea
def w658 : Nat := dw 0x3f3f2a2a3f3f2a2a
def w659 : Nat := dw 0xfcfca8a8fcfca8a8
def w660 : Nat := dw 0x545400005454
def w661 : Nat := dw 0xffffaeaeffffaeae
def w662 : Nat := dw 0xf3f3a2a2f3f3a2a2
def w663 : Nat := dw 0xffffbabaffffbaba
def w664 : Nat := dw 0xcfcf8a8acfcf8a8a
def w665 : Nat := dw 0xffffeeeeffffaaaa
def w666 : Nat := dw 0xffffbbbbffffaaaa
def w667 : Nat := dw 0xcccc8888ffffaaaa
def w668 : Nat := dw 0xfcfcececfcfcecec
def w669 : Nat := dw 0xfffffafa00000000
def w670 : Nat := dw 0xcfcfcececfcfcece
def w671 : Nat := dw 0xfffffafaffffaaaa
def w672 : Nat := dw 0xffffafafffffaaaa
def w673 : Nat := dw 0xf0f0a0a0ffffaaaa
def w674 : Nat := dw 0xffffeeeecccccccc
def w675 : Nat := dw 0xc0c0e0e0c0c0e0e0
def w676 : Nat := dw 0xc0c0e0e0c0c0e0e
def w677 : Nat := dw 0xcccceeee00000000
def w678 : Nat := dw 0xc0c0eaeac0c0eaea
def w679 : Nat := dw 0xfcfc5454fcfc5454
def w680 : Nat := dw 0xc0caeae0c0caeae
def w681 : Nat := dw 0x3030baba3030baba
def w682 : Nat := dw 0xcccceeee0000aaaa
def w683 : Nat := dw 0x3333bbbb0000aaaa
def w684 : Nat := dw 0xf0f0fafa0000aaaa
def w685 : Nat := dw 0xf0fafaf0000aaaa
def w686 : Nat := dw 0xffffeeeeffffcccc
def w687 : Nat := dw 0x3333222233330000
def w688 : Nat := dw 0x54545454fcfcfcfc
def w689 : Nat := dw 0xaeaeaeae0c0c0c0c
def w690 : Nat := dw 0xbabababa30303030
def w691 : Nat := dw 0x55554444ffffcccc
def w692 : Nat := dw 0xaaaaeeee0000cccc
def w693 : Nat := dw 0x55555050fffff0f0
def w694 : Nat := dw 0xaaaafafa0000f0f0
def w695 : Nat := dw 0x3f3f3f3f2a2a2a2a
def w696 : Nat := dw 0xfcfcfcfca8a8a8a8
def w697 : Nat := dw 0xf3f3f3f3a2a2a2a2
def w698 : Nat := dw 0xcfcfcfcf8a8a8a8a
def w699 : Nat := dw 0xc0c0c0c0eaeaeaea
def w700 : Nat := dw 0xfcfcfcfc54545454
def w701 : Nat := dw 0xc0c0c0caeaeaeae
def w702 : Nat := dw 0x30303030babababa
def w703 : Nat := dw 0xffffddddffffcccc
def w704 : Nat := dw 0xdddd0000cccc
def w705 : Nat := dw 0x3333111133330000
def w706 : Nat := dw 0xd5d5d5d5c0c0c0c0
def w707 : Nat := dw 0xa8a8a8a8fcfcfcfc
def w708 : Nat := dw 0x5d5d5d5d0c0c0c0c
def w709 : Nat := dw 0x7575757530303030
def w710 : Nat := dw 0xaaaa8888ffffcccc
def w711 : Nat := dw 0x5555dddd0000cccc
def w712 : Nat := dw 0xaaaaa0a0fffff0f0
def w713 : Nat := dw 0x5555f5f50000f0f0
def w714 : Nat := dw 0xeaea0000eaea
def w715 : Nat := dw 0xeaeaeaea00000000
def w716 : Nat := dw 0xeaeaeaea
def w717 : Nat := dw 0x5555404055554040
def w718 : Nat := dw 0x3f3f3f3f3f3f0000
def w719 : Nat := dw 0xffff5454ffff5454
def w720 : Nat := dw 0xaaaafefeaaaafefe
def w721 : Nat := dw 0xaeae0000aeae
def w722 : Nat := dw 0x5555040455550404
def w723 : Nat := dw 0xf3f3f3f3f3f30000
def w724 : Nat := dw 0xbaba0000baba
def w725 : Nat := dw 0x5555101055551010
def w726 : Nat := dw 0xcfcfcfcfcfcf0000
def w727 : Nat := dw 0xfafaf8f8fafaf8f8
def w728 : Nat := dw 0x5050707050507070
def w729 : Nat := dw 0x5555777700000000
def w730 : Nat := dw 0xfffffcfcffffcccc
def w731 : Nat := dw 0xf0f0c0cffffcccc
def w732 : Nat := dw 0xffffcfcfffffcccc
def w733 : Nat := dw 0xf0f0c0c0ffffcccc
def w734 : Nat := dw 0xf0f0fcfc0000cccc
def w735 : Nat := dw 0xf0fcfcf0000cccc
def w736 : Nat := dw 0xeeee0000aaaa
def w737 : Nat := dw 0x5555444455550000
def w738 : Nat := dw 0x33333030fffff0f0
def w739 : Nat := dw 0xccccfcfc0000f0f0
def w740 : Nat := dw 0xbbbb0000aaaa
def w741 : Nat := dw 0x5555111155550000
def w742 : Nat := dw 0xf0f03030f0f00000
def w743 : Nat := dw 0xf0f03030f0f0000
def w744 : Nat := dw 0xccccc0c0fffff0f0
def w745 : Nat := dw 0x3333f3f30000f0f0
def w746 : Nat := dw 0xdddddcdcdddddcdc
def w747 : Nat := dw 0xbbbbbababbbbbaba
def w748 : Nat := dw 0x2222323222223232
def w749 : Nat := dw 0x4444545444445454
def w750 : Nat := dw 0xccccfcfc00000000
def w751 : Nat := dw 0x3232323222222222
def w752 : Nat := dw 0xfafa0000aaaa
def w753 : Nat := dw 0x5454545444444444
def w754 : Nat := dw 0x5555505055550000
def w755 : Nat := dw 0x3333303033330000
def w756 : Nat := dw 0xdddddddddcdcdcdc
def w757 : Nat := dw 0xbbbbbbbbbabababa
def w758 : Nat := dw 0x2222222232323232
def w759 : Nat := dw 0x4444444454545454
def w760 : Nat := dw 0x2323232322222222
def w761 : Nat := dw 0xafaf0000aaaa
def w762 : Nat := dw 0x4545454544444444
def w763 : Nat := dw 0xcfcf0000cccc
def w764 : Nat := dw 0x5555050555550000
def w765 : Nat := dw 0x3333030333330000
def w766 : Nat := dw 0xddddddddddddcccc
def w767 : Nat := dw 0xbbbbbbbbbbbbaaaa
def w768 : Nat := dw 0xffffffff88888888
def w769 : Nat := dw 0x555500000000
def w770 : Nat := dw 0xcccccccceeeeeeee
def w771 : Nat := dw 0xffffcccc00000000
def w772 : Nat := dw 0x333300000000
def w773 : Nat := dw 0xaaaaeeeeaaaaeeee
def w774 : Nat := dw 0xaaaaaaaaeeeeeeee
def w775 : Nat := dw 0x5555505055555050
def w776 : Nat := dw 0xaaaafafaaaaafafa
def w777 : Nat := dw 0x5555555550505050
def w778 : Nat := dw 0x3333333330303030
def w779 : Nat := dw 0xaaaaaaaafafafafa
def w780 : Nat := dw 0xccccccccfcfcfcfc
def w781 : Nat := dw 0xafafafafaaaaaaaa
def w782 : Nat := dw 0xf1f1f1f1e0e0e0e0
def w783 : Nat := dw 0x1f1f1f1f1f1f0000
def w784 : Nat := dw 0xfefefefe10101010
def w785 : Nat := dw 0xf1f1f1f1f1f10000
def w786 : Nat := dw 0xfefe0000eeee
def w787 : Nat := dw 0xeeeee0e0eeee0000
def w788 : Nat := dw 0xeeee0e0eeeee0000
def w789 : Nat := dw 0xfefefefefefef0f0
def w790 : Nat := dw 0x101010101010f0f0
def w791 : Nat := dw 0xfafa3232fafa0000
def w792 : Nat := dw 0xfefefefefefecccc
def w793 : Nat := dw 0x5454fcfcfcfc
def w794 : Nat := dw 0xffffbaba30303030
def w795 : Nat := dw 0x3333666633336666
def w796 : Nat := dw 0xf0f0e4e4f0f0e4e4
def w797 : Nat := dw 0xf0f5a5a0f0f5a5a
def w798 : Nat := dw 0xc0c0e0e0cccceeee
def w799 : Nat := dw 0xeeeee0e0ccccc0c0
def w800 : Nat := dw 0xeeee0e0ecccc0c0c
def w801 : Nat := dw 0xffffeaeaffffc0c0
def w802 : Nat := dw 0xeaeaeaeaeaea0000
def w803 : Nat := dw 0xfefefefefefeaaaa
def w804 : Nat := dw 0x20202020202aaaa
def w805 : Nat := dw 0x5555666655556666
def w806 : Nat := dw 0xf0f3c3c0f0f3c3c
def w807 : Nat := dw 0xfff0fffcff00ffcc
def w808 : Nat := dw 0xfcfcfcccfcccfccc
def w809 : Nat := dw 0x3333333033303330
def w810 : Nat := dw 0xffe1ffe1ff00ff00
def w811 : Nat := dw 0xffffe1e1ffff0000
def w812 : Nat := dw 0xf0f0f080f000f000
def w813 : Nat := dw 0xfffffff8fff0fff0
def w814 : Nat := dw 0x7000f000f0
def w815 : Nat := dw 0xf0f0f080f000f00
def w816 : Nat := dw 0x1e1e1e1e00000000
def w817 : Nat := dw 0xffffffff1e1e1e1e
def w818 : Nat := dw 0x1e1e1e1e
def w819 : Nat := dw 0xe1e1e1e100000000
def w820 : Nat := dw 0x10101010e0e0e0e0
def w821 : Nat := dw 0xf1f1f1f1fefefefe
def w822 : Nat := dw 0x10101010e0e0e0e
def w823 : Nat := dw 0xe0e0e0e010101010
def w824 : Nat := dw 0xfefe0000aaaa
def p4_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def p4_R : List Nat := [0, 1, 2]
def p4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
def p4_Z : List SliceD := []
theorem p4_Y : ∀ s ∈ p4_Z, SliceN p4_R p4_T s := by intro s h; cases h
noncomputable def p4_C : List (Nat × List (Nat × Nat × Nat)) := []
def p4_P : List (Nat × Nat) := [(4,6),(4,5),(1,3),(2,3),(2,6),(1,5)]
noncomputable def p4_K : List CutV := p4_C.map (mkCut p4_Z)
theorem p4_W : ∀ c ∈ p4_K, CutP p4_R p4_T c := cutsGood p4_Y (by decide +kernel)
theorem p4_Q : p4_P.all (sepOK p4_T) = true := by decide +kernel
def p4_D2 : List StD := []
theorem p4_I2 : LevelN p4_R p4_T 2 p4_D2 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p4_D3 : List StD := [
mkSt [w1,w2,w0] 0x6c014100c080400c0300]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p4_C3x0 : levelOK p4_T p4_K p4_P 2 (p4_D2.map Prod.fst) ((p4_D3.drop (0*64)).take 64) = true := by decide +kernel
theorem p4_I3 : LevelN p4_R p4_T 3 p4_D3 := levelStep p4_B p4_W p4_Q p4_I2 (chunks 64 p4_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p4_C3x0
  ))
theorem p4_L : LowN p4_R p4_T 4 := lowSearch p4_B p4_I3 (by decide +kernel)
def p3_T : Nat := 0xe880e880e880e880e880e880e880e880
def p3_R : List Nat := [0, 1, 2, 3]
def p3_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
theorem p3_S0 : SliceN p3_R p3_T (0xcccccccccccccccccccccccccccccccc,4,[0, 2, 3]) := mkSlice (w:=2) p3_B p4_B p4_L (by decide +kernel)
theorem p3_S1 : SliceN p3_R p3_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3]) := mkSlice (w:=1) p3_B p4_B p4_L (by decide +kernel)
theorem p3_S2 : SliceN p3_R p3_T (0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]) := mkSlice (w:=8) p3_B p4_B p4_L (by decide +kernel)
theorem p3_S3 : SliceN p3_R p3_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3]) := mkSlice (w:=4) p3_B p4_B p4_L (by decide +kernel)
def p3_Z : List SliceD := [(0xcccccccccccccccccccccccccccccccc,4,[0, 2, 3]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨p3_S0,p3_S1,p3_S2,p3_S3,by simp⟩
noncomputable def p3_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2,dC 0x3,dC 0x2010104,dC 0x4,dC 0x2010103,dC 0x2010101,dC 0x2010102,dC 0x3010101,dC 0x3010102,dC 0x3010103,dC 0x3010104,dC 0x3020102,dC 0x3020103,dC 0x3020104,dC 0x3020101]
def p3_P : List (Nat × Nat) := [(9,13),(6,7),(5,7),(3,7),(3,11),(2,11),(1,11),(12,13),(10,11),(6,14),(10,14),(5,13),(9,11),(12,14)]
noncomputable def p3_K : List CutV := p3_C.map (mkCut p3_Z)
theorem p3_W : ∀ c ∈ p3_K, CutP p3_R p3_T c := cutsGood p3_Y (by decide +kernel)
theorem p3_Q : p3_P.all (sepOK p3_T) = true := by decide +kernel
def p3_D2 : List StD := []
theorem p3_I2 : LevelN p3_R p3_T 2 p3_D2 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p3_D3 : List StD := [
mkSt [w346,w1,w2,w0] 0x1e61da0201c0c18140008100500480,
mkSt [w347,w1,w2,w3] 0xe35a0301c0c08000420c0380,
mkSt [w28,w53,w12,w3] 0x850107242c1008002401c018d0282,
mkSt [w28,w101,w16,w0] 0xc5014934280c241c0400024020d0302,
mkSt [w348,w1,w0,w3] 0xa3ea020300c0800041cc0380,
mkSt [w53,w101,w2,w14] 0xc021683434000810043003002cd0302,
mkSt [w349,w2,w0,w3] 0xdf0a0300c200800041cc0380,
mkSt [w1,w12,w16,w14] 0x6aa862000100820041c03c038d0302]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C3x0 : levelOK p3_T p3_K p3_P 2 (p3_D2.map Prod.fst) ((p3_D3.drop (0*64)).take 64) = true := by decide +kernel
theorem p3_I3 : LevelN p3_R p3_T 3 p3_D3 := levelStep p3_B p3_W p3_Q p3_I2 (chunks 64 p3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C3x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p3_D4 : List StD := [
mkSt [w350,w1,w2,w0,w3] 0x22a61dc19502c2824200c0804001c1000900501,
mkSt [w89,w1,w2,w0,w3] 0x269e55661d42c240034081c0430102100500,
mkSt [w351,w1,w2,w0,w3] 0x2a61e1d81500c342804103020081c0001100501,
mkSt [w124,w1,w2,w0,w3] 0x1959211d950282400341c080c0500400,
mkSt [w28,w53,w2,w0,w3] 0xb701cc22926002c001020081c2400c018d0382,
mkSt [w28,w101,w2,w0,w3] 0xb0098a3154800100c081c0400014020d0302,
mkSt [w28,w1,w12,w0,w3] 0xb53840628e0200c34100830042400c01cd0382,
mkSt [w28,w1,w16,w0,w3] 0x1681c01c60e500201028340c3008040001402510402,
mkSt [w352,w1,w2,w0,w3] 0x221e5561d94241028302004002c1d00480,
mkSt [w353,w1,w2,w0,w3] 0x29e621d9410283004342c001c0c200800100501,
mkSt [w354,w1,w2,w0,w3] 0x1d551261d503410280030200c080500480,
mkSt [w53,w101,w2,w0,w3] 0x489cc4154800102000081c043002802cd0382,
mkSt [w53,w1,w12,w2,w3] 0x16720700614380200824282c0c00041001801d10402,
mkSt [w53,w1,w2,w14,w3] 0x2039801c61200c20242834000c08043002803110402,
mkSt [w355,w1,w2,w0,w3] 0x1a1925219502824100c08042c001d00480,
mkSt [w356,w1,w2,w0,w3] 0x21995661d9434240c08041c10203100480,
mkSt [w101,w1,w16,w2,w0] 0xb6398032920203028002c241c0c020024d0382,
mkSt [w101,w1,w2,w14,w0] 0xe3b00a62406200034241030140802c030d0382,
mkSt [w357,w1,w2,w0,w3] 0x269a61a61902c10000c30081c28243500500,
mkSt [w1,w238,w2,w0,w3] 0x26a61d91500300c242834201c08000400500501,
mkSt [w82,w1,w2,w0,w3] 0x1954201d940201000300c081c0500400,
mkSt [w1,w12,w16,w0,w3] 0x7292c014c620100c300820041c034038d0382,
mkSt [w1,w12,w2,w14,w3] 0xc021603148220240c0008041c03403cd0302,
mkSt [w239,w1,w2,w0,w3] 0x299e5da5d900c2c100008300424342900500,
mkSt [w191,w1,w2,w0,w3] 0x1d54021d9401c2c00081030042100400,
mkSt [w1,w16,w2,w14,w0] 0x2001c58040a30c20002c2410181c200403803d10402,
mkSt [w240,w1,w2,w0,w3] 0x1d661d61d5030100c00080424283500480,
mkSt [w78,w1,w2,w0,w3] 0x1a1824219402010240c082c00041d00480]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C4x0 : levelOK p3_T p3_K p3_P 3 (p3_D3.map Prod.fst) ((p3_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p3_I4 : LevelN p3_R p3_T 4 p3_D4 := levelStep p3_B p3_W p3_Q p3_I3 (chunks 64 p3_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p3_D5 : List StD := [
mkSt [w28,w1,w2,w0,w3] 0x20ccb52c1206040c2c28100c240000400001400cd8304,
mkSt [w53,w1,w2,w0,w3] 0x1380bd04b201180c24342c081030004010028018d8304,
mkSt [w101,w1,w2,w0,w3] 0x132e0134b048180c283400300c0800400802c020d8304,
mkSt [w1,w12,w2,w0,w3] 0x2ccc4a0311890b602c102004241c01000003401cd8304,
mkSt [w1,w16,w2,w0,w3] 0x3412b0e810c623600c001c202804008000038024d8304,
mkSt [w1,w2,w14,w0,w3] 0x40c4733624ae040302004081c3400801003c030d8304]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C5x0 : levelOK p3_T p3_K p3_P 4 (p3_D4.map Prod.fst) ((p3_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p3_I5 : LevelN p3_R p3_T 5 p3_D5 := levelStep p3_B p3_W p3_Q p3_I4 (chunks 64 p3_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C5x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p3_D6 : List StD := [
mkSt [w1,w2,w0,w3] 0xc97284c80e00c083024201c10002c28043400801000000518604]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C6x0 : levelOK p3_T p3_K p3_P 5 (p3_D5.map Prod.fst) ((p3_D6.drop (0*64)).take 64) = true := by decide +kernel
theorem p3_I6 : LevelN p3_R p3_T 6 p3_D6 := levelStep p3_B p3_W p3_Q p3_I5 (chunks 64 p3_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C6x0
  ))
theorem p3_L : LowN p3_R p3_T 7 := lowSearch p3_B p3_I6 (by decide +kernel)
def p2_T : Nat := 0xeee8e8e0eee8e8e0eee8e8e0eee8e8e0
def p2_R : List Nat := [0, 1, 2, 3, 4]
def p2_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,3,11),(4,3,19)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
theorem p2_S0 : SliceN p2_R p2_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]) := mkSlice (w:=0) p2_B p3_B p3_L (by decide +kernel)
def p2_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4])]
theorem p2_Y : ∀ s ∈ p2_Z, SliceN p2_R p2_T s := by
  unfold p2_Z
  simp only [List.forall_mem_cons]
  exact ⟨p2_S0,by simp⟩
noncomputable def p2_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p2_P : List (Nat × Nat) := []
noncomputable def p2_K : List CutV := p2_C.map (mkCut p2_Z)
theorem p2_W : ∀ c ∈ p2_K, CutP p2_R p2_T c := cutsGood p2_Y (by decide +kernel)
theorem p2_Q : p2_P.all (sepOK p2_T) = true := by decide +kernel
def p2_D6 : List StD := []
theorem p2_I6 : LevelN p2_R p2_T 6 p2_D6 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p2_D7 : List StD := [
mkSt [w1,w2,w0,w3,w4] 0x1]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p2_C7x0 : levelOK p2_T p2_K p2_P 6 (p2_D6.map Prod.fst) ((p2_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p2_I7 : LevelN p2_R p2_T 7 p2_D7 := levelStep p2_B p2_W p2_Q p2_I6 (chunks 64 p2_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p2_C7x0
  ))
theorem p2_L : LowN p2_R p2_T 8 := lowSearch p2_B p2_I7 (by decide +kernel)
def p6_T : Nat := 0xfeecfeecfeecfeecfeecfeecfeecfeec
def p6_R : List Nat := [0, 1, 2, 3]
def p6_E : List (Nat × Nat × Nat) := [(0,4,5),(1,0,2),(2,1,5),(3,1,9)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
theorem p6_S0 : SliceN p6_R p6_T (0x33333333333333333333333333333333,4,[0, 2, 3]) := mkSlice (w:=0) p6_B p4_B p4_L (by decide +kernel)
def p6_Z : List SliceD := [(0x33333333333333333333333333333333,4,[0, 2, 3])]
theorem p6_Y : ∀ s ∈ p6_Z, SliceN p6_R p6_T s := by
  unfold p6_Z
  simp only [List.forall_mem_cons]
  exact ⟨p6_S0,by simp⟩
noncomputable def p6_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p6_P : List (Nat × Nat) := [(0,2),(4,5),(1,3)]
noncomputable def p6_K : List CutV := p6_C.map (mkCut p6_Z)
theorem p6_W : ∀ c ∈ p6_K, CutP p6_R p6_T c := cutsGood p6_Y (by decide +kernel)
theorem p6_Q : p6_P.all (sepOK p6_T) = true := by decide +kernel
def p6_D3 : List StD := []
theorem p6_I3 : LevelN p6_R p6_T 3 p6_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p6_D4 : List StD := [
mkSt [w1,w2,w0,w3] 0x8040000000181]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p6_C4x0 : levelOK p6_T p6_K p6_P 3 (p6_D3.map Prod.fst) ((p6_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p6_I4 : LevelN p6_R p6_T 4 p6_D4 := levelStep p6_B p6_W p6_Q p6_I3 (chunks 64 p6_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_C4x0
  ))
theorem p6_L : LowN p6_R p6_T 5 := lowSearch p6_B p6_I4 (by decide +kernel)
def p7_T : Nat := 0xfef8fef8fef8fef8fef8fef8fef8fef8
def p7_R : List Nat := [0, 1, 2, 3]
def p7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,0,4),(3,1,9)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
theorem p7_S0 : SliceN p7_R p7_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) p7_B p4_B p4_L (by decide +kernel)
def p7_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨p7_S0,by simp⟩
noncomputable def p7_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p7_P : List (Nat × Nat) := [(8,10),(8,9),(1,3),(2,3),(0,4),(1,5)]
noncomputable def p7_K : List CutV := p7_C.map (mkCut p7_Z)
theorem p7_W : ∀ c ∈ p7_K, CutP p7_R p7_T c := cutsGood p7_Y (by decide +kernel)
theorem p7_Q : p7_P.all (sepOK p7_T) = true := by decide +kernel
def p7_D3 : List StD := []
theorem p7_I3 : LevelN p7_R p7_T 3 p7_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p7_D4 : List StD := [
mkSt [w1,w2,w0,w3] 0x14100c08040000000301]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C4x0 : levelOK p7_T p7_K p7_P 3 (p7_D3.map Prod.fst) ((p7_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p7_I4 : LevelN p7_R p7_T 4 p7_D4 := levelStep p7_B p7_W p7_Q p7_I3 (chunks 64 p7_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C4x0
  ))
theorem p7_L : LowN p7_R p7_T 5 := lowSearch p7_B p7_I4 (by decide +kernel)
def p8_T : Nat := 0xe8a0e8a0e8a0e8a0e8a0e8a0e8a0e8a0
def p8_R : List Nat := [0, 1, 2, 3]
def p8_E : List (Nat × Nat × Nat) := [(0,4,5),(1,9,11),(2,1,5),(3,3,11)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
theorem p8_S0 : SliceN p8_R p8_T (0xcccccccccccccccccccccccccccccccc,4,[0, 2, 3]) := mkSlice (w:=2) p8_B p4_B p4_L (by decide +kernel)
def p8_Z : List SliceD := [(0xcccccccccccccccccccccccccccccccc,4,[0, 2, 3])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨p8_S0,by simp⟩
noncomputable def p8_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p8_P : List (Nat × Nat) := [(12,14),(4,5),(9,11),(6,7),(10,14),(10,11),(1,5),(6,14),(3,11)]
noncomputable def p8_K : List CutV := p8_C.map (mkCut p8_Z)
theorem p8_W : ∀ c ∈ p8_K, CutP p8_R p8_T c := cutsGood p8_Y (by decide +kernel)
theorem p8_Q : p8_P.all (sepOK p8_T) = true := by decide +kernel
def p8_D3 : List StD := []
theorem p8_I3 : LevelN p8_R p8_T 3 p8_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p8_D4 : List StD := [
mkSt [w1,w2,w0,w3] 0x201c1814100c08040000000481]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p8_C4x0 : levelOK p8_T p8_K p8_P 3 (p8_D3.map Prod.fst) ((p8_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p8_I4 : LevelN p8_R p8_T 4 p8_D4 := levelStep p8_B p8_W p8_Q p8_I3 (chunks 64 p8_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C4x0
  ))
theorem p8_L : LowN p8_R p8_T 5 := lowSearch p8_B p8_I4 (by decide +kernel)
def p9_T : Nat := 0xe8c0e8c0e8c0e8c0e8c0e8c0e8c0e8c0
def p9_R : List Nat := [0, 1, 2, 3]
def p9_E : List (Nat × Nat × Nat) := [(0,10,11),(1,4,6),(2,2,6),(3,3,11)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
theorem p9_S0 : SliceN p9_R p9_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3]) := mkSlice (w:=1) p9_B p4_B p4_L (by decide +kernel)
def p9_Z : List SliceD := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,4,[1, 2, 3])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨p9_S0,by simp⟩
noncomputable def p9_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p9_P : List (Nat × Nat) := [(4,6),(12,13),(5,7),(10,11),(2,6),(3,7)]
noncomputable def p9_K : List CutV := p9_C.map (mkCut p9_Z)
theorem p9_W : ∀ c ∈ p9_K, CutP p9_R p9_T c := cutsGood p9_Y (by decide +kernel)
theorem p9_Q : p9_P.all (sepOK p9_T) = true := by decide +kernel
def p9_D3 : List StD := []
theorem p9_I3 : LevelN p9_R p9_T 3 p9_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p9_D4 : List StD := [
mkSt [w1,w2,w0,w3] 0x14100c08040000000301]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C4x0 : levelOK p9_T p9_K p9_P 3 (p9_D3.map Prod.fst) ((p9_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p9_I4 : LevelN p9_R p9_T 4 p9_D4 := levelStep p9_B p9_W p9_Q p9_I3 (chunks 64 p9_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C4x0
  ))
theorem p9_L : LowN p9_R p9_T 5 := lowSearch p9_B p9_I4 (by decide +kernel)
def p10_T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def p10_R : List Nat := [0, 1, 2, 3]
def p10_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
theorem p10_S0 : SliceN p10_R p10_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) p10_B p4_B p4_L (by decide +kernel)
def p10_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3])]
theorem p10_Y : ∀ s ∈ p10_Z, SliceN p10_R p10_T s := by
  unfold p10_Z
  simp only [List.forall_mem_cons]
  exact ⟨p10_S0,by simp⟩
noncomputable def p10_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p10_P : List (Nat × Nat) := [(4,6),(4,5),(1,3),(2,3),(2,6),(1,5),(2,10),(1,9),(8,9),(8,10)]
noncomputable def p10_K : List CutV := p10_C.map (mkCut p10_Z)
theorem p10_W : ∀ c ∈ p10_K, CutP p10_R p10_T c := cutsGood p10_Y (by decide +kernel)
theorem p10_Q : p10_P.all (sepOK p10_T) = true := by decide +kernel
def p10_D3 : List StD := []
theorem p10_I3 : LevelN p10_R p10_T 3 p10_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p10_D4 : List StD := [
mkSt [w1,w2,w0,w3] 0x24201c1814100c08040000000501]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p10_C4x0 : levelOK p10_T p10_K p10_P 3 (p10_D3.map Prod.fst) ((p10_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p10_I4 : LevelN p10_R p10_T 4 p10_D4 := levelStep p10_B p10_W p10_Q p10_I3 (chunks 64 p10_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C4x0
  ))
theorem p10_L : LowN p10_R p10_T 5 := lowSearch p10_B p10_I4 (by decide +kernel)
def p5_T : Nat := 0xeee8eac0eee8eac0eee8eac0eee8eac0
def p5_R : List Nat := [0, 1, 2, 3, 4]
def p5_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,3,19)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
theorem p5_S0 : SliceN p5_R p5_T (0xcccccccccccccccccccccccccccccccc,5,[0, 2, 3, 4]) := mkSlice (w:=2) p5_B p6_B p6_L (by decide +kernel)
theorem p5_S1 : SliceN p5_R p5_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[1, 2, 3, 4]) := mkSlice (w:=1) p5_B p7_B p7_L (by decide +kernel)
theorem p5_S2 : SliceN p5_R p5_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]) := mkSlice (w:=0) p5_B p8_B p8_L (by decide +kernel)
theorem p5_S3 : SliceN p5_R p5_T (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,4,[0, 3, 4]) := mkSlice (w:=2) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S4 : SliceN p5_R p5_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p5_B p9_B p9_L (by decide +kernel)
theorem p5_S5 : SliceN p5_R p5_T (0xaa00aa00aa00aa00aa00aa00aa00aa,4,[1, 2, 4]) := mkSlice (w:=1) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S6 : SliceN p5_R p5_T (0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) p5_B p10_B p10_L (by decide +kernel)
theorem p5_S7 : SliceN p5_R p5_T (0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]) := mkSlice (w:=16) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S8 : SliceN p5_R p5_T (0xff000000ff000000ff000000ff0000,4,[0, 1, 2]) := mkSlice (w:=16) p5_B p4_B p4_L (by decide +kernel)
def p5_Z : List SliceD := [(0xcccccccccccccccccccccccccccccccc,5,[0, 2, 3, 4]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[1, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,4,[0, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xaa00aa00aa00aa00aa00aa00aa00aa,4,[1, 2, 4]),(0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]),(0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]),(0xff000000ff000000ff000000ff0000,4,[0, 1, 2])]
theorem p5_Y : ∀ s ∈ p5_Z, SliceN p5_R p5_T s := by
  unfold p5_Z
  simp only [List.forall_mem_cons]
  exact ⟨p5_S0,p5_S1,p5_S2,p5_S3,p5_S4,p5_S5,p5_S6,p5_S7,p5_S8,by simp⟩
noncomputable def p5_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2,dC 0x2010103,dC 0x4,dC 0x2010105,dC 0x6,dC 0x3010104,dC 0x3010106,dC 0x2010107,dC 0x3,dC 0x3010305,dC 0x8,dC 0x5,dC 0x7,dC 0x4010101,dC 0x4010103,dC 0x4010105,dC 0x4010102,dC 0x3020303,dC 0x9,dC 0x4020103,dC 0x4020105,dC 0x3020202,dC 0x4030207]
def p5_P : List (Nat × Nat) := [(2,6),(3,7),(1,9),(3,11),(5,21),(18,19),(17,19),(4,6),(5,6),(4,7),(20,21),(0,9),(8,9),(17,21),(6,20),(5,9),(9,17),(3,19),(20,22),(17,25),(5,13),(4,13),(12,13),(18,26),(10,11),(10,26),(6,18),(12,14),(5,7),(18,22),(10,14)]
noncomputable def p5_K : List CutV := p5_C.map (mkCut p5_Z)
theorem p5_W : ∀ c ∈ p5_K, CutP p5_R p5_T c := cutsGood p5_Y (by decide +kernel)
theorem p5_Q : p5_P.all (sepOK p5_T) = true := by decide +kernel
def p5_D3 : List StD := []
theorem p5_I3 : LevelN p5_R p5_T 3 p5_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p5_D4 : List StD := [
mkSt [w1,w2,w358,w3,w4] 0x3f39b72ee5c403c0c34302c0424201038081c280100780,
mkSt [w1,w2,w0,w359,w4] 0x3af5b2eaa5c403c08343004242010380c1c280100700]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C4x0 : levelOK p5_T p5_K p5_P 3 (p5_D3.map Prod.fst) ((p5_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p5_I4 : LevelN p5_R p5_T 4 p5_D4 := levelStep p5_B p5_W p5_Q p5_I3 (chunks 64 p5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p5_D5 : List StD := [
mkSt [w360,w1,w2,w0,w3,w4] 0x32ae8a4e0cd88150403c10342c1c44181428080001c01900602,
mkSt [w70,w1,w2,w0,w3,w4] 0x2a7a36599b2ea6183c0c20104c344818281408001c3100700,
mkSt [w241,w1,w2,w0,w3,w4] 0x2e32e61999ae61d83c64440c001c60141008342900600,
mkSt [w192,w1,w19,w2,w0,w3] 0xd0a7a8c2ca0491081c380503c68185c1c403444146410080003804510682,
mkSt [w242,w1,w2,w0,w3,w4] 0x2736e72e61ee61d43c3410440804701828641c5c0100680]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C5x0 : levelOK p5_T p5_K p5_P 4 (p5_D4.map Prod.fst) ((p5_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p5_I5 : LevelN p5_R p5_T 5 p5_D5 := levelStep p5_B p5_W p5_Q p5_I4 (chunks 64 p5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C5x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p5_D6 : List StD := [
mkSt [w28,w1,w2,w0,w3,w4] 0x1f29bf09fb94e7940701fb406003c1c34302c440c04402808001001401000800c00402000118687,
mkSt [w54,w1,w2,w0,w3,w4] 0x163c54715153a28316f9a83540058544408182810501c02c01402800400c02518486,
mkSt [w192,w1,w2,w0,w3,w4] 0x163738496661931e8c19f3350003c304c34185c00081c01404003c02c03803518486,
mkSt [w27,w1,w2,w0,w3,w4] 0x4c5908e0054f1e1224d012a0084643c3044001410283404c04800c01518484,
mkSt [w1,w19,w2,w0,w3,w4] 0x4627581c6960e33b04c9b1356803c340874301c145c002804c05405000c03404518506,
mkSt [w1,w2,w0,w3,w42,w4] 0x578e08f80003d2c51afd63c28344464503078141810281c02c05c00c01405802403118507]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C6x0 : levelOK p5_T p5_K p5_P 5 (p5_D5.map Prod.fst) ((p5_D6.drop (0*64)).take 64) = true := by decide +kernel
theorem p5_I6 : LevelN p5_R p5_T 6 p5_D6 := levelStep p5_B p5_W p5_Q p5_I5 (chunks 64 p5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C6x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p5_D7 : List StD := [
mkSt [w1,w2,w0,w3,w4] 0x1e7175316d2a2565100c078106c34305008145c0028641c04c00c02c01403403002400000520689]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C7x0 : levelOK p5_T p5_K p5_P 6 (p5_D6.map Prod.fst) ((p5_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p5_I7 : LevelN p5_R p5_T 7 p5_D7 := levelStep p5_B p5_W p5_Q p5_I6 (chunks 64 p5_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C7x0
  ))
theorem p5_L : LowN p5_R p5_T 8 := lowSearch p5_B p5_I7 (by decide +kernel)
def p12_T : Nat := 0xfee8fee8fee8fee8fee8fee8fee8fee8
def p12_R : List Nat := [0, 1, 2, 3]
def p12_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
theorem p12_S0 : SliceN p12_R p12_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) p12_B p4_B p4_L (by decide +kernel)
theorem p12_S1 : SliceN p12_R p12_T (0x33333333333333333333333333333333,4,[0, 2, 3]) := mkSlice (w:=0) p12_B p4_B p4_L (by decide +kernel)
theorem p12_S2 : SliceN p12_R p12_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]) := mkSlice (w:=0) p12_B p4_B p4_L (by decide +kernel)
theorem p12_S3 : SliceN p12_R p12_T (0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2]) := mkSlice (w:=0) p12_B p4_B p4_L (by decide +kernel)
def p12_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3]),(0x33333333333333333333333333333333,4,[0, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3]),(0xff00ff00ff00ff00ff00ff00ff00ff,4,[0, 1, 2])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨p12_S0,p12_S1,p12_S2,p12_S3,by simp⟩
noncomputable def p12_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2,dC 0x2010202,dC 0x2010201,dC 0x2010203,dC 0x3010202,dC 0x3010201,dC 0x2010204,dC 0x4,dC 0x3,dC 0x3010203,dC 0x3020201,dC 0x3010204,dC 0x3020203,dC 0x3020202,dC 0x3020204]
def p12_P : List (Nat × Nat) := [(4,5),(4,6),(1,3),(2,3),(1,9),(4,11),(2,10),(1,5),(4,12),(2,6),(3,8),(7,8),(8,9),(8,12),(8,10)]
noncomputable def p12_K : List CutV := p12_C.map (mkCut p12_Z)
theorem p12_W : ∀ c ∈ p12_K, CutP p12_R p12_T c := cutsGood p12_Y (by decide +kernel)
theorem p12_Q : p12_P.all (sepOK p12_T) = true := by decide +kernel
def p12_D2 : List StD := []
theorem p12_I2 : LevelN p12_R p12_T 2 p12_D2 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p12_D3 : List StD := [
mkSt [w6,w24,w20,w3] 0xc60149341814080c001000c008d0302,
mkSt [w6,w0,w9,w8] 0x73968b0240c04002c281c018014d0382,
mkSt [w154,w1,w2,w0] 0xfb500040c2008001018c0380,
mkSt [w243,w1,w2,w3] 0x21c1940383034081c040c0100400,
mkSt [w2,w24,w9,w42] 0x6ab08301000082c300402c028d0302,
mkSt [w244,w1,w0,w3] 0x21d940020300038100c080500400,
mkSt [w1,w20,w8,w42] 0x5a2c42018040c0030038034d0282,
mkSt [w245,w2,w0,w3] 0x21d94002038043010080c0100400]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C3x0 : levelOK p12_T p12_K p12_P 2 (p12_D2.map Prod.fst) ((p12_D3.drop (0*64)).take 64) = true := by decide +kernel
theorem p12_I3 : LevelN p12_R p12_T 3 p12_D3 := levelStep p12_B p12_W p12_Q p12_I2 (chunks 64 p12_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C3x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p12_D4 : List StD := [
mkSt [w2,w6,w0,w24,w3] 0x1c7a0700684500202420000c1c08041801000910402,
mkSt [w2,w6,w0,w3,w9] 0x2442201e818004201834300c101c08042401c01510482,
mkSt [w1,w6,w0,w20,w3] 0x1c7a0700684500201c200408240c001001000d10402,
mkSt [w1,w6,w0,w3,w8] 0x2441e022718004201038340818240c001c01c01910482,
mkSt [w1,w2,w0,w134,w3] 0x2a5a1d95102034380418300c08001002100501,
mkSt [w40,w1,w2,w0,w3] 0x1e15d11d95018101c080c04200100400,
mkSt [w1,w2,w0,w3,w102] 0x28261d591502034043800240c08301c02500501,
mkSt [w25,w1,w2,w0,w3] 0x1961191d95024101c080c38343100400,
mkSt [w2,w0,w24,w3,w9] 0x2400e8005084902018001c10243830040803002910482,
mkSt [w1,w2,w24,w20,w3] 0x2080089c684510001808241c0c04001000800d10402,
mkSt [w109,w1,w2,w0,w3] 0x21d9d11d95020101c040024180d00400,
mkSt [w1,w2,w24,w3,w42] 0x2401e322818010101038341c200c04000803002d10482,
mkSt [w1,w2,w0,w3,w246] 0x2a601d19550182420380c300410000800500501,
mkSt [w247,w1,w2,w0,w3] 0x1955121d95008101c040034383100400,
mkSt [w1,w2,w0,w9,w8] 0x41081e49850400041810002428301c01401910402,
mkSt [w36,w1,w2,w0,w3] 0x21d9191d95034101c083018240d00400,
mkSt [w1,w2,w0,w9,w42] 0x81e208198500201c2010003430080402802d10402,
mkSt [w248,w1,w2,w0,w3] 0x1e15115d95038101c083020040100400,
mkSt [w110,w1,w2,w0,w3] 0x21d5d95d95020182404001c100900400,
mkSt [w1,w0,w20,w3,w8] 0x2402270040838c2010380424181c30000c03c03510482,
mkSt [w1,w2,w20,w3,w42] 0x2402270040838c20103424200408300c0003c03910482,
mkSt [w1,w2,w0,w3,w249] 0x2a5a1d81510101c083824300c04340000100501,
mkSt [w250,w1,w2,w0,w3] 0x1954021d9400c1824043438003100400,
mkSt [w65,w1,w2,w0,w3] 0x2159d95d950341824380c101c0900400,
mkSt [w1,w2,w0,w8,w42] 0x81e614008206201c20180438340c0003403910402,
mkSt [w251,w1,w2,w0,w3] 0x1d56001d9403018243820040c0100400,
mkSt [w252,w1,w2,w0,w3] 0x1a15d95d9503820340400101c0900400,
mkSt [w125,w1,w2,w0,w3] 0x19da001d940302034041824000d00400]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C4x0 : levelOK p12_T p12_K p12_P 3 (p12_D3.map Prod.fst) ((p12_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p12_I4 : LevelN p12_R p12_T 4 p12_D4 := levelStep p12_B p12_W p12_Q p12_I3 (chunks 64 p12_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p12_D5 : List StD := [
mkSt [w1,w2,w6,w0,w3] 0x806203c580c98b0890341808240c20101c00400001c01118404,
mkSt [w1,w2,w0,w24,w3] 0x31101b8703098448ac20381c080018100402400003000918404,
mkSt [w1,w2,w0,w3,w9] 0x6a222068a021c268c3410382408301c0402000002801518404,
mkSt [w1,w2,w0,w20,w3] 0x71101bb0871830188c201830240c04100002400403c00d18404,
mkSt [w1,w2,w0,w3,w8] 0x6a2204384d03c508c3430181c0c38240002000403401918404,
mkSt [w1,w2,w0,w3,w42] 0x611618882d03c2680383020340c08000402002403802d18404]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C5x0 : levelOK p12_T p12_K p12_P 4 (p12_D4.map Prod.fst) ((p12_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p12_I5 : LevelN p12_R p12_T 5 p12_D5 := levelStep p12_B p12_W p12_Q p12_I4 (chunks 64 p12_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C5x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p12_D6 : List StD := [
mkSt [w1,w2,w0,w3] 0xc97284c80e0343804301c0c20181024080002002400400118604]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C6x0 : levelOK p12_T p12_K p12_P 5 (p12_D5.map Prod.fst) ((p12_D6.drop (0*64)).take 64) = true := by decide +kernel
theorem p12_I6 : LevelN p12_R p12_T 6 p12_D6 := levelStep p12_B p12_W p12_Q p12_I5 (chunks 64 p12_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C6x0
  ))
theorem p12_L : LowN p12_R p12_T 7 := lowSearch p12_B p12_I6 (by decide +kernel)
def p11_T : Nat := 0xfffefef8fffefef8fffefef8fffefef8
def p11_R : List Nat := [0, 1, 2, 3, 4]
def p11_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,0,4),(3,1,9),(4,1,17)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
theorem p11_S0 : SliceN p11_R p11_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p11_B p6_B p6_L (by decide +kernel)
theorem p11_S1 : SliceN p11_R p11_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4]) := mkSlice (w:=0) p11_B p12_B p12_L (by decide +kernel)
def p11_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,7,[0, 1, 3, 4])]
theorem p11_Y : ∀ s ∈ p11_Z, SliceN p11_R p11_T s := by
  unfold p11_Z
  simp only [List.forall_mem_cons]
  exact ⟨p11_S0,p11_S1,by simp⟩
noncomputable def p11_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2]
def p11_P : List (Nat × Nat) := [(8,9)]
noncomputable def p11_K : List CutV := p11_C.map (mkCut p11_Z)
theorem p11_W : ∀ c ∈ p11_K, CutP p11_R p11_T c := cutsGood p11_Y (by decide +kernel)
theorem p11_Q : p11_P.all (sepOK p11_T) = true := by decide +kernel
def p11_D6 : List StD := []
theorem p11_I6 : LevelN p11_R p11_T 6 p11_D6 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p11_D7 : List StD := [
mkSt [w1,w2,w0,w3,w4] 0x2aaaa80000400010082]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p11_C7x0 : levelOK p11_T p11_K p11_P 6 (p11_D6.map Prod.fst) ((p11_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p11_I7 : LevelN p11_R p11_T 7 p11_D7 := levelStep p11_B p11_W p11_Q p11_I6 (chunks 64 p11_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C7x0
  ))
theorem p11_L : LowN p11_R p11_T 8 := lowSearch p11_B p11_I7 (by decide +kernel)
def p14_T : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
def p14_R : List Nat := [0, 1, 2, 3]
def p14_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
theorem p14_S0 : SliceN p14_R p14_T (0x55555555555555555555555555555555,4,[1, 2, 3]) := mkSlice (w:=0) p14_B p4_B p4_L (by decide +kernel)
def p14_Z : List SliceD := [(0x55555555555555555555555555555555,4,[1, 2, 3])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨p14_S0,by simp⟩
noncomputable def p14_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p14_P : List (Nat × Nat) := [(4,6),(0,1)]
noncomputable def p14_K : List CutV := p14_C.map (mkCut p14_Z)
theorem p14_W : ∀ c ∈ p14_K, CutP p14_R p14_T c := cutsGood p14_Y (by decide +kernel)
theorem p14_Q : p14_P.all (sepOK p14_T) = true := by decide +kernel
def p14_D3 : List StD := []
theorem p14_I3 : LevelN p14_R p14_T 3 p14_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p14_D4 : List StD := [
mkSt [w1,w2,w0,w3] 0x40000000101]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p14_C4x0 : levelOK p14_T p14_K p14_P 3 (p14_D3.map Prod.fst) ((p14_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p14_I4 : LevelN p14_R p14_T 4 p14_D4 := levelStep p14_B p14_W p14_Q p14_I3 (chunks 64 p14_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C4x0
  ))
theorem p14_L : LowN p14_R p14_T 5 := lowSearch p14_B p14_I4 (by decide +kernel)
def p15_T : Nat := 0xe888e888e888e888e888e888e888e888
def p15_R : List Nat := [0, 1, 2, 3]
def p15_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,9,13),(3,5,13)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
theorem p15_S0 : SliceN p15_R p15_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3]) := mkSlice (w:=4) p15_B p4_B p4_L (by decide +kernel)
def p15_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3])]
theorem p15_Y : ∀ s ∈ p15_Z, SliceN p15_R p15_T s := by
  unfold p15_Z
  simp only [List.forall_mem_cons]
  exact ⟨p15_S0,by simp⟩
noncomputable def p15_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p15_P : List (Nat × Nat) := [(12,14),(12,13),(1,3),(2,3),(10,14),(9,13),(6,14),(5,13)]
noncomputable def p15_K : List CutV := p15_C.map (mkCut p15_Z)
theorem p15_W : ∀ c ∈ p15_K, CutP p15_R p15_T c := cutsGood p15_Y (by decide +kernel)
theorem p15_Q : p15_P.all (sepOK p15_T) = true := by decide +kernel
def p15_D3 : List StD := []
theorem p15_I3 : LevelN p15_R p15_T 3 p15_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p15_D4 : List StD := [
mkSt [w1,w2,w0,w3] 0x1c1814100c08040000000401]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p15_C4x0 : levelOK p15_T p15_K p15_P 3 (p15_D3.map Prod.fst) ((p15_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p15_I4 : LevelN p15_R p15_T 4 p15_D4 := levelStep p15_B p15_W p15_Q p15_I3 (chunks 64 p15_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C4x0
  ))
theorem p15_L : LowN p15_R p15_T 5 := lowSearch p15_B p15_I4 (by decide +kernel)
def p16_T : Nat := 0xea88ea88ea88ea88ea88ea88ea88ea88
def p16_R : List Nat := [0, 1, 2, 3]
def p16_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,10,14),(3,1,9)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
theorem p16_S0 : SliceN p16_R p16_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3]) := mkSlice (w:=4) p16_B p4_B p4_L (by decide +kernel)
def p16_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,4,[0, 1, 3])]
theorem p16_Y : ∀ s ∈ p16_Z, SliceN p16_R p16_T s := by
  unfold p16_Z
  simp only [List.forall_mem_cons]
  exact ⟨p16_S0,by simp⟩
noncomputable def p16_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p16_P : List (Nat × Nat) := [(12,14),(8,9),(1,3),(2,3),(10,14)]
noncomputable def p16_K : List CutV := p16_C.map (mkCut p16_Z)
theorem p16_W : ∀ c ∈ p16_K, CutP p16_R p16_T c := cutsGood p16_Y (by decide +kernel)
theorem p16_Q : p16_P.all (sepOK p16_T) = true := by decide +kernel
def p16_D3 : List StD := []
theorem p16_I3 : LevelN p16_R p16_T 3 p16_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p16_D4 : List StD := [
mkSt [w1,w2,w0,w3] 0x100c08040000000281]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p16_C4x0 : levelOK p16_T p16_K p16_P 3 (p16_D3.map Prod.fst) ((p16_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p16_I4 : LevelN p16_R p16_T 4 p16_D4 := levelStep p16_B p16_W p16_Q p16_I3 (chunks 64 p16_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C4x0
  ))
theorem p16_L : LowN p16_R p16_T 5 := lowSearch p16_B p16_I4 (by decide +kernel)
def p17_T : Nat := 0xe8a8e8a8e8a8e8a8e8a8e8a8e8a8e8a8
def p17_R : List Nat := [0, 1, 2, 3]
def p17_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,6,14)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
theorem p17_S0 : SliceN p17_R p17_T (0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]) := mkSlice (w:=8) p17_B p4_B p4_L (by decide +kernel)
def p17_Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2])]
theorem p17_Y : ∀ s ∈ p17_Z, SliceN p17_R p17_T s := by
  unfold p17_Z
  simp only [List.forall_mem_cons]
  exact ⟨p17_S0,by simp⟩
noncomputable def p17_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p17_P : List (Nat × Nat) := [(12,14),(4,5),(1,3),(2,3),(10,14),(1,5),(6,14)]
noncomputable def p17_K : List CutV := p17_C.map (mkCut p17_Z)
theorem p17_W : ∀ c ∈ p17_K, CutP p17_R p17_T c := cutsGood p17_Y (by decide +kernel)
theorem p17_Q : p17_P.all (sepOK p17_T) = true := by decide +kernel
def p17_D3 : List StD := []
theorem p17_I3 : LevelN p17_R p17_T 3 p17_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p17_D4 : List StD := [
mkSt [w1,w2,w0,w3] 0x1814100c08040000000381]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p17_C4x0 : levelOK p17_T p17_K p17_P 3 (p17_D3.map Prod.fst) ((p17_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p17_I4 : LevelN p17_R p17_T 4 p17_D4 := levelStep p17_B p17_W p17_Q p17_I3 (chunks 64 p17_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C4x0
  ))
theorem p17_L : LowN p17_R p17_T 5 := lowSearch p17_B p17_I4 (by decide +kernel)
def p13_T : Nat := 0xfee8ea88fee8ea88fee8ea88fee8ea88
def p13_R : List Nat := [0, 1, 2, 3, 4]
def p13_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,10,14),(3,1,9),(4,5,21)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
theorem p13_S0 : SliceN p13_R p13_T (0x55555555555555555555555555555555,7,[1, 2, 3, 4]) := mkSlice (w:=0) p13_B p3_B p3_L (by decide +kernel)
theorem p13_S1 : SliceN p13_R p13_T (0x33333333333333333333333333333333,5,[0, 2, 3, 4]) := mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S2 : SliceN p13_R p13_T (0xcccccccccccccccccccccccccccccccc,5,[0, 2, 3, 4]) := mkSlice (w:=2) p13_B p14_B p14_L (by decide +kernel)
theorem p13_S3 : SliceN p13_R p13_T (0x30303030303030303030303030303030,4,[0, 3, 4]) := mkSlice (w:=4) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S4 : SliceN p13_R p13_T (0x33330000333300003333000033330000,4,[0, 2, 3]) := mkSlice (w:=16) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S5 : SliceN p13_R p13_T (0x50505050505050505050505050505050,4,[1, 3, 4]) := mkSlice (w:=4) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S6 : SliceN p13_R p13_T (0x55005500550055005500550055005500,4,[1, 2, 4]) := mkSlice (w:=8) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S7 : SliceN p13_R p13_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p13_B p15_B p15_L (by decide +kernel)
theorem p13_S8 : SliceN p13_R p13_T (0xffff0000ffff0000ffff0000ffff0000,7,[0, 1, 2, 3]) := mkSlice (w:=16) p13_B p12_B p12_L (by decide +kernel)
theorem p13_S9 : SliceN p13_R p13_T (0xf000f000f000f000f000f000f000f0,4,[0, 1, 4]) := mkSlice (w:=4) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S10 : SliceN p13_R p13_T (0xff00ff00ff00ff00ff00ff00ff00ff00,5,[0, 1, 2, 4]) := mkSlice (w:=8) p13_B p14_B p14_L (by decide +kernel)
theorem p13_S11 : SliceN p13_R p13_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,7,[0, 1, 3, 4]) := mkSlice (w:=4) p13_B p12_B p12_L (by decide +kernel)
theorem p13_S12 : SliceN p13_R p13_T (0x44444444444444444444444444444444,4,[2, 3, 4]) := mkSlice (w:=2) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S13 : SliceN p13_R p13_T (0x55550000555500005555000055550000,4,[1, 2, 3]) := mkSlice (w:=16) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S14 : SliceN p13_R p13_T (0xff000000ff000000ff000000ff0000,4,[0, 1, 2]) := mkSlice (w:=16) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S15 : SliceN p13_R p13_T (0xffff0000ffff0000ffff0000ffff,5,[0, 1, 2, 3]) := mkSlice (w:=0) p13_B p16_B p16_L (by decide +kernel)
theorem p13_S16 : SliceN p13_R p13_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]) := mkSlice (w:=0) p13_B p17_B p17_L (by decide +kernel)
theorem p13_S17 : SliceN p13_R p13_T (0xf0f00000f0f00000f0f00000f0f0,4,[0, 1, 3]) := mkSlice (w:=4) p13_B p4_B p4_L (by decide +kernel)
theorem p13_S18 : SliceN p13_R p13_T (0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]) := mkSlice (w:=16) p13_B p4_B p4_L (by decide +kernel)
def p13_Z : List SliceD := [(0x55555555555555555555555555555555,7,[1, 2, 3, 4]),(0x33333333333333333333333333333333,5,[0, 2, 3, 4]),(0xcccccccccccccccccccccccccccccccc,5,[0, 2, 3, 4]),(0x30303030303030303030303030303030,4,[0, 3, 4]),(0x33330000333300003333000033330000,4,[0, 2, 3]),(0x50505050505050505050505050505050,4,[1, 3, 4]),(0x55005500550055005500550055005500,4,[1, 2, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff0000,7,[0, 1, 2, 3]),(0xf000f000f000f000f000f000f000f0,4,[0, 1, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff00,5,[0, 1, 2, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,7,[0, 1, 3, 4]),(0x44444444444444444444444444444444,4,[2, 3, 4]),(0x55550000555500005555000055550000,4,[1, 2, 3]),(0xff000000ff000000ff000000ff0000,4,[0, 1, 2]),(0xffff0000ffff0000ffff0000ffff,5,[0, 1, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]),(0xf0f00000f0f00000f0f00000f0f0,4,[0, 1, 3]),(0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3])]
theorem p13_Y : ∀ s ∈ p13_Z, SliceN p13_R p13_T s := by
  unfold p13_Z
  simp only [List.forall_mem_cons]
  exact ⟨p13_S0,p13_S1,p13_S2,p13_S3,p13_S4,p13_S5,p13_S6,p13_S7,p13_S8,p13_S9,p13_S10,p13_S11,p13_S12,p13_S13,p13_S14,p13_S15,p13_S16,p13_S17,p13_S18,by simp⟩
noncomputable def p13_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2,dC 0x3,dC 0x4,dC 0x5,dC 0x2010101,dC 0x6,dC 0x7,dC 0x3020403,dC 0x2010208,dC 0x5010303020401,dC 0x2010203020109,dC 0xa,dC 0x3010302,dC 0x302010b,dC 0x201020c,dC 0x3010101,dC 0x201020302010c,dC 0x2010204020109,dC 0x3010201,dC 0x3010203010101,dC 0x8,dC 0x3010204020101,dC 0x4020103,dC 0x3020107,dC 0x301010d,dC 0x302020201020c,dC 0x4020202010209,dC 0x3010301,dC 0x201020302030c,dC 0x2010204020309,dC 0x3010102010101,dC 0x4010103010101,dC 0x4010101,dC 0xe,dC 0x201020402010c,dC 0x4030303,dC 0x5010304030301,dC 0xf,dC 0x402010b,dC 0x2010209,dC 0x5030102010101,dC 0x5010303020101,dC 0x503030201020c,dC 0x5040102010101,dC 0x5010304020101,dC 0x5030102010209,dC 0x504030201020c,dC 0x4020403,dC 0x2010210,dC 0x503010201020c,dC 0x2010107,dC 0x201020a,dC 0x11,dC 0x3020103,dC 0x503040201020c,dC 0x504010201020c,dC 0x2010212,dC 0x2010213,dC 0x5030103010202010209,dC 0xb,dC 0x13,dC 0x2010401,dC 0x5030302010209,dC 0x2010211,dC 0x3020303,dC 0x5040103010101,dC 0x5010304030101,dC 0x5040102010209,dC 0x4030403,dC 0x3010107,dC 0x10,dC 0x201020f,dC 0x4030103,dC 0x503010301020201020c,dC 0x201020b,dC 0x5040104010202010209,dC 0x5020103010201,dC 0x503020201020c,dC 0xc,dC 0x403010b,dC 0x5040202010209,dC 0x5040103010201,dC 0x9,dC 0x2010304,dC 0x5020303010301,dC 0x5040402010209,dC 0x3010305,dC 0x5040303010301,dC 0x3020103010301,dC 0x4020103010301,dC 0x4030103010301,dC 0x3010401,dC 0x5040302010209,dC 0x4020303,dC 0x504010401020201020c,dC 0x12,dC 0x4010401,dC 0x3020101,dC 0x2010204,dC 0x5010103020101,dC 0x301020201020c,dC 0x5010202010204030109,dC 0x5010203020101,dC 0x2010205020304030109,dC 0x4030102010209,dC 0x501020201020403010c,dC 0x5040103020101,dC 0x403010201020c,dC 0x201020403040c,dC 0x4030110,dC 0x3020301,dC 0x2010204030309,dC 0x4020101,dC 0x402020401020201020c,dC 0x401020201020c,dC 0x3010204,dC 0x3010202010209,dC 0x5010204020101,dC 0x402020201020c,dC 0x201020402030c,dC 0x504020201020c,dC 0x5030202010209,dC 0x3010304,dC 0x504040201020c,dC 0x5030402010209,dC 0x201020403030c,dC 0x2010204030409,dC 0x4030111,dC 0x4030101,dC 0x3010205,dC 0x5010104030101,dC 0x4010202010209,dC 0x5010204030101,dC 0x201020502030403010c,dC 0x4030401,dC 0x5030102010409,dC 0x201040c,dC 0xd,dC 0x503010201040c,dC 0x5040102010409,dC 0x503020201040c,dC 0x5040202010409,dC 0x503040201040c,dC 0x5040402010409,dC 0x503030201040c,dC 0x5040302010409,dC 0x504010201040c,dC 0x2010409,dC 0x504030201040c,dC 0x302020201040c,dC 0x2010408,dC 0x4020202010409,dC 0x3020102,dC 0x2010411,dC 0x4030102010409,dC 0x3020104,dC 0x2010410,dC 0x2010413,dC 0x3020302,dC 0x201030d,dC 0x2010404030309,dC 0x4020102,dC 0x504020201040c,dC 0x402020201040c,dC 0x3020304,dC 0x403010201040c,dC 0x4030102,dC 0x201040a,dC 0x201040b,dC 0x4030402,dC 0x302040d,dC 0x201040403040c,dC 0x2010412,dC 0x2010201,dC 0x201030c,dC 0x5020203010409,dC 0x201030a,dC 0x2010207,dC 0x2010312,dC 0x2010301,dC 0x201010c,dC 0x5020303010409,dC 0x5040103010409,dC 0x3020201,dC 0x301030c,dC 0x301030402010c,dC 0x5040203010409,dC 0x201020d,dC 0x402040b,dC 0x3010312,dC 0x5040403010409,dC 0x3020401,dC 0x301010c,dC 0x5040303010409,dC 0x3020111,dC 0x3010404,dC 0x3020211,dC 0x3020311,dC 0x401040302030c,dC 0x3010404020309,dC 0x4020310,dC 0x3020411,dC 0x401040302040c,dC 0x3010404020409,dC 0x4020410,dC 0x301040a,dC 0x3010409,dC 0x4020401,dC 0x4020110,dC 0x3020113,dC 0x3010204020401,dC 0x4020210,dC 0x301040d,dC 0x3020213,dC 0x3020313,dC 0x401010302030c,dC 0x3020413,dC 0x401010302040c,dC 0x302010c,dC 0x2010402,dC 0x2010106,dC 0x3010408,dC 0x4020103010409,dC 0x302020302010c,dC 0x4020204020103010409,dC 0x3010204020103010101,dC 0x4020205030203010404020109,dC 0x4020103010101,dC 0x5030203010404020109,dC 0x504020302010c,dC 0x302020c,dC 0x2010206,dC 0x4020203010409,dC 0x501040302020c,dC 0x2010403,dC 0x301040b,dC 0x3010410,dC 0x2010306,dC 0x2010406,dC 0x302040c,dC 0x402010c,dC 0x4020111,dC 0x3010106,dC 0x4020104010101,dC 0x4020102010402,dC 0x4020411,dC 0x3010406,dC 0x402040c,dC 0x4030104020101,dC 0x4030103010408,dC 0x403010c,dC 0x4030411,dC 0x3020406,dC 0x403040c,dC 0x3010202,dC 0x3010211,dC 0x602010301020201020c,dC 0x4010205010203020109,dC 0x5030202010101,dC 0x5030302010101,dC 0x4010209,dC 0x2010103010401,dC 0x502040301020c,dC 0x301020501020402010c,dC 0x4010210,dC 0x301020402010c,dC 0x4010203020109,dC 0x3010213,dC 0x301020402040c,dC 0x502010301020c,dC 0x301020c,dC 0x3020110,dC 0x302040b,dC 0x3010203,dC 0x4010203020409,dC 0x301020302010c,dC 0x4010204020109,dC 0x302020301020c,dC 0x4020204010209,dC 0x301020302040c,dC 0x4010204020409,dC 0x3020103010101,dC 0x4030103010101,dC 0x5030304010101,dC 0x5020104010209,dC 0x6020104010202010209,dC 0x201010d,dC 0x302010d,dC 0x5020303010401,dC 0x5020404010209,dC 0x201030f,dC 0x5040303010401,dC 0x4010103010401,dC 0x5030302010301,dC 0x2010308,dC 0x4020103010401,dC 0x5030304010301,dC 0x5030104010101,dC 0x3010212,dC 0x5030204010101,dC 0x301020503030402010c,dC 0x302030b,dC 0x301020302030c,dC 0x4010204030109,dC 0x502030301020c,dC 0x5030304020101,dC 0x5030104010209,dC 0x504030301020c,dC 0x403040b,dC 0x6030104010203010209,dC 0x504010301020c,dC 0x403020301020401020c,dC 0x301020401020c,dC 0x301020a,dC 0x604010301020401020c,dC 0x4010203010209,dC 0x301020402030c,dC 0x4010203020309,dC 0x5030204020101,dC 0x403020301020c,dC 0x301020403030c,dC 0x504020301020c,dC 0x5040203010209,dC 0x504040301020c,dC 0x301030a,dC 0x5030404010209,dC 0x402030b,dC 0x301020403010c,dC 0x5020304010209,dC 0x502020301040c,dC 0x5020204010409,dC 0x502030301040c,dC 0x5020304010409,dC 0x301040c,dC 0x504010301040c,dC 0x4010409,dC 0x3020108,dC 0x3010402,dC 0x3020104010409,dC 0x302010a,dC 0x4010410,dC 0x3010405,dC 0x3010411,dC 0x3010403,dC 0x3020408,dC 0x2010407,dC 0x4010403020409,dC 0x3010413,dC 0x302020301040c,dC 0x4020204010409,dC 0x4020108,dC 0x402010301040c,dC 0x2010404,dC 0x4020408,dC 0x3010407,dC 0x301040402040c,dC 0x3010412,dC 0x4030108,dC 0x504020301040c,dC 0x302030a,dC 0x403020301040c,dC 0x4010201,dC 0x502020401040c,dC 0x2010309,dC 0x2010313,dC 0x3010207,dC 0x4010301,dC 0x502030401040c,dC 0x2010109,dC 0x401040c,dC 0x4020301,dC 0x3020112,dC 0x301030d,dC 0x3020212,dC 0x3010204020301,dC 0x3020312,dC 0x3010104020309,dC 0x3020412,dC 0x3010104020409,dC 0x4030201,dC 0x503020401040c,dC 0x302020d,dC 0x3010313,dC 0x4010309,dC 0x4030301,dC 0x503030401040c,dC 0x4010109,dC 0x3020109,dC 0x4010402,dC 0x201010e,dC 0x4020102010101,dC 0x4010411,dC 0x4020104010402,dC 0x4010403,dC 0x3020410,dC 0x201040e,dC 0x3020409,dC 0x4020109,dC 0x301010e,dC 0x302010401040c,dC 0x4010408,dC 0x4020204020109,dC 0x302020302010401040c,dC 0x302020504020401040302010c,dC 0x504020401040302010c,dC 0x5030204020109,dC 0x4020209,dC 0x302020401040c,dC 0x301020e,dC 0x5010404020209,dC 0x401040b,dC 0x301030e,dC 0x301040e,dC 0x4020409,dC 0x4030109,dC 0x4020103020101,dC 0x4030104010408,dC 0x4030310,dC 0x302030e,dC 0x4030309,dC 0x5010203020109,dC 0x5030402010101,dC 0x4030102010101,dC 0x2010104030401,dC 0x2010102010401,dC 0x5040103020109,dC 0x5040203020109,dC 0x5040403020109,dC 0x501020302040c,dC 0x5040303020109,dC 0x201040d,dC 0x3010102,dC 0x3010111,dC 0x4010110,dC 0x603020501020402010c,dC 0x6040205010203020109,dC 0x5040302010101,dC 0x3010202010101,dC 0x4020203020109,dC 0x3020104020409,dC 0x5010202010104020101,dC 0x3020203020109,dC 0x4030104020102,dC 0x3020104030108,dC 0x4030103020108,dC 0x501020403010c,dC 0x502020403010c,dC 0x302010f,dC 0x4030102010401,dC 0x5010203020409,dC 0x3020404,dC 0x5030102010401,dC 0x5040103020409,dC 0x5030202010401,dC 0x302030c,dC 0x5040203020409,dC 0x5030402010401,dC 0x5040403020409,dC 0x5030302010401,dC 0x501020302010c,dC 0x5040303020409,dC 0x5040102010401,dC 0x5040302010401,dC 0x302040f,dC 0x2010404030401,dC 0x5010204020109,dC 0x302020501020302010c,dC 0x4020205010204020109,dC 0x2010205,dC 0x3010103010301,dC 0x4020309,dC 0x5020303010101,dC 0x5030304020109,dC 0x3010103010401,dC 0x504010302010c,dC 0x5040303010101,dC 0x504030302010c,dC 0x6050403010203010101,dC 0x6050303010103010201,dC 0x605040302020302010c,dC 0x6050404020204020109,dC 0x6030104020204020109,dC 0x7030104020205030204020109,dC 0x4020205030204020109,dC 0x302020504020302010c,dC 0x704010302020504020302010c,dC 0x604010302020302010c,dC 0x3010203010301,dC 0x3010203010401,dC 0x3010204010101,dC 0x302020402010c,dC 0x4020204030109,dC 0x302020403030c,dC 0x504040302020c,dC 0x5030104020209,dC 0x504030302020c,dC 0x504010302020c,dC 0x2010203,dC 0x301020b,dC 0x403020302020402020c,dC 0x302020402020c,dC 0x3020204,dC 0x403020302020c,dC 0x504020302020c,dC 0x302020403010c,dC 0x4010203,dC 0x401020b,dC 0x5040303010201,dC 0x501020302030c,dC 0x5010204020309,dC 0x5030304020309,dC 0x5040103010301,dC 0x504010302030c,dC 0x504030302030c,dC 0x302040302030c,dC 0x4020404020309,dC 0x4030104020309,dC 0x504020302030c,dC 0x5030204020309,dC 0x302020a,dC 0x401020302030c,dC 0x3010204020309,dC 0x402020302030c,dC 0x403010302030c,dC 0x5010204020409,dC 0x5030304020409,dC 0x5040103010401,dC 0x504010302040c,dC 0x504030302040c,dC 0x402010302040c,dC 0x504020302040c,dC 0x5030204020409,dC 0x401020302040c,dC 0x3010204020409,dC 0x403020302040c,dC 0x501020402010c,dC 0x5030404010101,dC 0x3020104010101,dC 0x4010103020301,dC 0x5020304010101,dC 0x201040f,dC 0x503020402010c,dC 0x503030402010c,dC 0x302030d,dC 0x4010104010401,dC 0x5010204030109,dC 0x5020204030109,dC 0x3020104020102,dC 0x4030104020108,dC 0x4020103020102,dC 0x5010204010104020101,dC 0x402020402010c,dC 0x501020402040c,dC 0x3020104010401,dC 0x3020105,dC 0x3020305,dC 0x5020304010401,dC 0x5030204010401,dC 0x503020402040c,dC 0x5030304010401,dC 0x503030402040c,dC 0x302040a,dC 0x4010403020301,dC 0x5010403020101,dC 0x2010311,dC 0x502020301020c,dC 0x3020104020101,dC 0x5020304030109,dC 0x2010307,dC 0x3020103020301,dC 0x602010501020403010c,dC 0x2010111,dC 0x2010108,dC 0x2010110,dC 0x602020501020403010c,dC 0x6020205010204030109,dC 0x5040303020101,dC 0x5030203020104020101,dC 0x4030204030109,dC 0x5010204030309,dC 0x5010203020301,dC 0x5020204030309,dC 0x5010303020301,dC 0x5020304030309,dC 0x5040103020301,dC 0x5040303020301,dC 0x402020401020c,dC 0x401020c,dC 0x5010404020101,dC 0x2010310,dC 0x502040401020c,dC 0x3010209,dC 0x403020401020c,dC 0x5030404020101,dC 0x3010311,dC 0x4010310,dC 0x503040401020c,dC 0x5010104020101,dC 0x401020402040c,dC 0x5020203010209,dC 0x502020401020c,dC 0x5030104020101,dC 0x401020403040c,dC 0x503020401020c,dC 0x402020c,dC 0x501040402020c,dC 0x3020209,dC 0x403020402020c,dC 0x503040402020c,dC 0x501020402030c,dC 0x5010203020309,dC 0x402030c,dC 0x503020402030c,dC 0x3020309,dC 0x403020c,dC 0x501040403020c,dC 0x4030209,dC 0x502040403020c,dC 0x5030204030104020101,dC 0x403020403010c,dC 0x501020403030c,dC 0x5010204030409,dC 0x502020403030c,dC 0x4030409,dC 0x403030c,dC 0x5010404030101,dC 0x5020204010209,dC 0x502030403010c,dC 0x3010307,dC 0x5020304030101,dC 0x4030104030401,dC 0x501020403040c,dC 0x5010204030401,dC 0x502020403040c,dC 0x5010304030401,dC 0x502030403040c,dC 0x5020304030401]
def p13_P : List (Nat × Nat) := [(8,9),(6,7),(2,3),(10,11),(18,19),(5,7),(1,3),(12,13),(20,21),(17,21),(10,14),(5,21),(10,26),(6,14),(20,22),(24,28),(1,9),(4,14),(12,14),(16,26),(12,28),(6,22),(20,28),(3,5),(24,26),(18,26),(1,19),(18,22),(17,19),(5,13),(17,25),(3,17),(9,10),(17,28),(18,28),(5,9),(9,12),(10,28),(5,28),(6,28),(9,17),(24,25),(1,21),(9,24),(11,12),(7,12),(19,20),(7,20),(13,24),(19,24),(11,24),(0,3),(1,25),(8,14),(2,14),(20,29),(18,23),(3,10),(6,13),(6,11),(3,6),(17,22),(5,22),(3,18),(18,25),(11,18),(5,15),(20,25),(13,20),(4,22),(2,26),(4,21),(6,23),(5,14),(20,30),(20,26),(14,20),(0,9)]
noncomputable def p13_K : List CutV := p13_C.map (mkCut p13_Z)
theorem p13_W : ∀ c ∈ p13_K, CutP p13_R p13_T c := cutsGood p13_Y (by decide +kernel)
theorem p13_Q : p13_P.all (sepOK p13_T) = true := by decide +kernel
def p13_D2 : List StD := []
theorem p13_I2 : LevelN p13_R p13_T 2 p13_D2 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p13_D3 : List StD := [
mkSt [w1,w0,w503,w4] 0xfa8003824142818200cc0380]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C3x0 : levelOK p13_T p13_K p13_P 2 (p13_D2.map Prod.fst) ((p13_D3.drop (0*64)).take 64) = true := by decide +kernel
theorem p13_I3 : LevelN p13_R p13_T 3 p13_D3 := levelStep p13_B p13_W p13_Q p13_I2 (chunks 64 p13_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C3x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p13_D4 : List StD := [
mkSt [w6,w0,w174,w3,w4] 0x32ea661d59430100c28084800202c24046100600,
mkSt [w2,w32,w30,w11,w3] 0x1eea1e61d94641024400470142834180100580,
mkSt [w1,w0,w492,w3,w4] 0x2ea621d80003038482814102c2418040100580,
mkSt [w1,w2,w493,w0,w4] 0x2e9e61d800024584c143410281840040100580,
mkSt [w263,w1,w2,w3,w49] 0x372c02a61c034184804a83c5440281424002100680,
mkSt [w25,w2,w0,w94,w4] 0x2ea265d800010244c041464280018344100580,
mkSt [w93,w2,w34,w3,w4] 0x1d9e1d800003840041464206c1d00400,
mkSt [w6,w0,w11,w212,w4] 0x2aa6221c000300428482c340c24206100500,
mkSt [w203,w1,w2,w7,w49] 0x2a601c15940a818382058341440040100500,
mkSt [w93,w2,w0,w3,w35] 0x2b2aea5a21808044014a42454201828342d00600,
mkSt [w1,w264,w0,w8,w4] 0x1e669e61d9430281014040c2c24380100500,
mkSt [w18,w1,w85,w8,w4] 0x1223aa32a580028383404142438cc8381,
mkSt [w96,w2,w21,w3,w4] 0x299a6615dd458600c3c00044014202500500,
mkSt [w36,w95,w0,w3,w4] 0x2eaa4021d803028106048142c2418000500580,
mkSt [w2,w0,w174,w9,w4] 0x1f2d6a61d947804641c30340c282c20002500600,
mkSt [w96,w2,w33,w0,w3] 0x2d9aa61d5d45848140c5000104018202d00580,
mkSt [w2,w67,w11,w3,w55] 0x32daaa61dd430a4281c604808142c24001900600,
mkSt [w0,w11,w213,w9,w4] 0x2a5e5e19d9834300020282c480c642500500,
mkSt [w204,w1,w7,w3,w49] 0x32e80261d8034a83c20184838402414000500600,
mkSt [w39,w1,w0,w85,w8] 0x7524e811cd51818600c3850302810001465108501,
mkSt [w494,w1,w2,w0,w4] 0x3fb72ea62202c6018dc24145834080030043c444100780,
mkSt [w1,w2,w169,w0,w268] 0x2ea55661e54307834100800142c04406100580,
mkSt [w2,w21,w7,w3,w35] 0x2141e01a71428428303c2804241460540d020910402,
mkSt [w1,w2,w7,w3,w271] 0x4d1c854a0c7305054003c041428a4602420908501,
mkSt [w273,w1,w2,w7,w3] 0x1961d95d95054343c600440241500400,
mkSt [w57,w0,w11,w8,w4] 0x2aa6221c00030142835240c2c24206100500,
mkSt [w1,w0,w278,w8,w4] 0x29d261c01803824143400281860200d00500,
mkSt [w279,w1,w0,w8,w4] 0x22e800261c03c191814d4282c24380c2100580,
mkSt [w1,w0,w495,w8,w4] 0x2ea6261dd944450383c200c04304c280100580,
mkSt [w496,w1,w0,w8,w4] 0x2eaa6619d94302820041460002c34240d00580,
mkSt [w16,w0,w284,w8,w4] 0x1e20001d9402030440c2c00282500400,
mkSt [w1,w0,w497,w8,w4] 0x2661ddd9950303828200c042c240100480,
mkSt [w1,w72,w85,w8,w4] 0x931907340a41818281434200c04240078d08481,
mkSt [w1,w16,w0,w174,w4] 0x2dea51e61d838182c002524303420142900580,
mkSt [w283,w1,w0,w8,w4] 0xd6fd7eb03038280c2c1424c0380,
mkSt [w1,w0,w85,w103,w8] 0xb38b49118a400381830282c20100c04600079908581,
mkSt [w285,w2,w7,w3,w49] 0x32ea61c018034a83c18483820402414040100600,
mkSt [w498,w1,w2,w0,w4] 0x3fb72ea6220244c182cdc1458340400285010484100780,
mkSt [w1,w2,w171,w288,w4] 0x3672ea61e542874701864100400142408404900680,
mkSt [w2,w33,w7,w34,w3] 0x1d89428081c604385064102414301c6c12018d10402,
mkSt [w1,w2,w7,w290,w3] 0x3aa503390c5203c646c005010281c2418d08481,
mkSt [w291,w1,w2,w7,w3] 0x1961d95d9506c6450481040241500400,
mkSt [w499,w1,w0,w3,w4] 0x376f6ea61e0301c402438481400042c446c1900680,
mkSt [w1,w165,w0,w211,w3] 0x3372ea631ac743048701840201c0464002c1500680,
mkSt [w1,w0,w178,w212,w4] 0x29d261c01803824144800281860200d00500,
mkSt [w500,w1,w0,w3,w4] 0x32aaeea61e030802438481400042c20281900600,
mkSt [w1,w166,w0,w297,w4] 0x299a521ddd44c38188024043428142100500,
mkSt [w1,w0,w213,w179,w4] 0x229261c18003824341404286418200d00500,
mkSt [w1,w299,w0,w173,w4] 0x26a611c18002458381400281840e42100500,
mkSt [w501,w1,w2,w0,w4] 0x32ea6661ddc243814e4583404002818204100600,
mkSt [w502,w1,w0,w3,w4] 0x36ab2ea61e04c2c402438481400045434281900680,
mkSt [w1,w168,w307,w3,w4] 0x32eeaa61ee878286018a4401c043400241500600]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C4x0 : levelOK p13_T p13_K p13_P 3 (p13_D3.map Prod.fst) ((p13_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p13_I4 : LevelN p13_R p13_T 4 p13_D4 := levelStep p13_B p13_W p13_Q p13_I3 (chunks 64 p13_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p13_D5p0 : List StD := [
mkSt [w25,w82,w1,w2,w0,w4] 0x2ab29dea6dea61d8184c2c24140440483c44300100600,
mkSt [w6,w0,w11,w3,w8,w4] 0x3772ea6221d80000304010140c2804482c2408206100680,
mkSt [w93,w1,w0,w3,w8,w4] 0x277e3b59b2ea56184018340c0860142824044864383c2005500781,
mkSt [w44,w1,w6,w0,w8,w4] 0xcd6ac5b514e922062382418601000400c14583028480402508681,
mkSt [w104,w1,w6,w0,w3,w4] 0x1cb699cc5a889020f6005828602c04004018480c2438341406508701,
mkSt [w1,w6,w0,w138,w3,w4] 0x37f7b72eaaa621d8706c58144838100c0400284018600900780,
mkSt [w27,w6,w0,w11,w3,w4] 0x3fa37632eeea61d8301028482070340414382c2418600d00780,
mkSt [w27,w93,w1,w0,w3,w4] 0x3736b7fb729e61dc083040282404341814502c3c58203900780,
mkSt [w25,w91,w1,w2,w0,w4] 0x22aa59a61da61d944c2c241404345028480100500,
mkSt [w391,w1,w2,w6,w0,w3] 0x983dc76b0cb52128398583c40380c0080242c7010342850140540800,
mkSt [w25,w262,w1,w2,w0,w4] 0x26aa59a629a61d94602c241404403c30440100500,
mkSt [w392,w1,w2,w6,w0,w4] 0x1183dcd62cca4a0e839c282c2470183810008058400c503c14043540880,
mkSt [w1,w2,w32,w56,w14,w4] 0x9225625608946a059449038502c2470884018103c0c08148c64848030040d948901,
mkSt [w25,w1,w2,w32,w14,w4] 0x1ee549445a8c03a503305030146c103c348c64049024402c000d908781,
mkSt [w1,w2,w32,w30,w7,w3] 0xe340286b1a9a800a185092858643028409470143c100418003405c0e110702,
mkSt [w2,w32,w6,w34,w3,w4] 0x2623fa3722ea61d850902c741c7040046014843018643d00780,
mkSt [w2,w32,w6,w11,w3,w4] 0x663358651cd901cc5202c582428207040046014343c180ed08681,
mkSt [w393,w1,w2,w6,w3,w4] 0x119460f7358b525083982c58704038100c00802824140450343c180940900,
mkSt [w1,w2,w56,w30,w0,w23] 0x81579579c51e716510490383c242c9c704050100c14a0349880280412548801,
mkSt [w2,w56,w6,w0,w34,w4] 0x4a079c49a30719651240e3030082c24741c7004183840845064145812948801,
mkSt [w2,w56,w6,w0,w35,w4] 0x4a079c49a18731601240e3028082c2478a47004183840983c34581413148801,
mkSt [w2,w0,w11,w3,w102,w4] 0xbb8d30b18a2ca1892071c50305810202860384804142c24001811c0d510702,
mkSt [w43,w1,w0,w3,w102,w4] 0xcb8d2cc2ca2451480071850305838281020604814042c24180011c0d510702,
mkSt [w44,w1,w2,w0,w102,w4] 0xb9cb20a1c8245148007185058382030284800142c240411c0d510582,
mkSt [w263,w1,w2,w0,w3,w4] 0x10c5984a294a04e0f6282840182c342414003038582005d08601,
mkSt [w25,w202,w1,w2,w0,w4] 0x22aa59a61da61d944c2c241404345028480100500,
mkSt [w25,w1,w2,w30,w0,w23] 0x81779678858c50048e406303c24141854501064a03404ac2c40280012548801,
mkSt [w25,w2,w6,w0,w34,w4] 0xb83dc66b16a49c4801c300850247004144874641c902c18405802540801,
mkSt [w25,w2,w6,w0,w35,w4] 0xb83dc66b16a4a04701c28082c24700414447834a4ac3c18405802540801,
mkSt [w25,w1,w2,w161,w0,w4] 0x3b72ea25615d819424503c4c1410586434042818400000900701,
mkSt [w25,w84,w1,w2,w0,w4] 0x2621e5ea61d559942c244c1040642814003500500,
mkSt [w25,w1,w2,w14,w7,w4] 0x1ee1f54c5a92638d02302c584c48106c1c346404284024140014108781,
mkSt [w1,w2,w0,w394,w3,w4] 0x18cda94ac8907314a5282c582438481410043428180014108601,
mkSt [w25,w2,w0,w11,w3,w4] 0x2aa1ddeaedea61ec482c34042438200030142900580,
mkSt [w25,w43,w1,w0,w3,w4] 0x2a229de9a1aa61d82c34240048383028041500500,
mkSt [w25,w1,w2,w7,w0,w23] 0x1c3eb1695192641c623058246014a45464340430402c180014108701,
mkSt [w25,w163,w1,w2,w0,w4] 0x2aa29dea61d800002c24140464183000344100500,
mkSt [w2,w30,w6,w0,w11,w3] 0xe85b4e462f4941ca6285864102420400448702814345017d08681,
mkSt [w2,w30,w6,w0,w3,w35] 0x23627fb72ea619d8ac3c107824a404404870982814503500780,
mkSt [w6,w0,w34,w46,w3,w4] 0x1c9735cb128c34a094a064100c808c50b4b014241c042c4010108701,
mkSt [w78,w6,w0,w34,w3,w4] 0xdbc914e08d12450a2481c60107450249070408014382c1c64041802410110782,
mkSt [w165,w6,w0,w34,w3,w4] 0x1ad6758bca92940ee3a82c7424381c700414484018306019108681,
mkSt [w139,w6,w0,w34,w3,w4] 0x27a7b70002ea61c02c74046070648014300818401c3900700,
mkSt [w2,w6,w7,w34,w3,w4] 0x81e82c3cfaaaa4c2a0718502c1c7040042438806c146401c12010110583,
mkSt [w140,w1,w2,w7,w3,w4] 0x12c40ceb0190322503802c6c30403c1404342848241c0e908601,
mkSt [w2,w6,w0,w94,w3,w4] 0xd6af00000174651010de3000802c002470400414388018341980240c41a810118585,
mkSt [w395,w1,w2,w0,w3,w4] 0x1220352b530ab52507b43040142c343c3800048024505810108681,
mkSt [w93,w1,w2,w14,w3,w4] 0x32bb72a2ca192a603438640c3c6c0414302c244028200f100701,
mkSt [w6,w0,w11,w60,w3,w4] 0x832b26828000000920249002c4080305828b81404bc20341c810110602,
mkSt [w43,w6,w0,w11,w3,w4] 0xab272c1189a896489c61440102c582070400414488018340c410110602,
mkSt [w166,w6,w0,w11,w3,w4] 0x3bb7372eaaa4e1d82c4024482070041438302818346100700,
mkSt [w141,w6,w0,w11,w3,w4] 0x107a5c96b16b5a9283ac5810240448607034801838280814402140800,
mkSt [w203,w1,w2,w7,w0,w4] 0x372e6a61615d9d94282c241838205834043014400100680,
mkSt [w93,w1,w2,w0,w23,w3] 0x3fabab70adcea61c5840140c08502454041834282c30200f100781,
mkSt [w1,w2,w396,w0,w3,w4] 0x8b1b58b50922b80c0102c58246018141004343028480002508681,
mkSt [w2,w6,w7,w0,w3,w35] 0x83880e034a68a28920718500824c028a40440182c388054143401c0d110702,
mkSt [w167,w1,w2,w7,w0,w3] 0x1c96a10c5a928001203c3424540c08506000044028142c300d108701,
mkSt [w6,w0,w3,w35,w127,w4] 0x8a279c69858e58048924838541014a0400c2804c8c424800860342c3c02548881,
mkSt [w92,w6,w0,w3,w35,w4] 0x8a049e70668b29859449038107828082c247080401438ac60343c041802548881,
mkSt [w168,w6,w0,w3,w35,w4] 0x1bc26d684a9281dc76282c7828a448240414604018383c20d08681,
mkSt [w142,w6,w0,w3,w35,w4] 0x3fa3722c002a61c010782404487080341428081840a43900780,
mkSt [w44,w1,w2,w0,w126,w4] 0x25de59c001a61d80304028482c2414002100480,
mkSt [w397,w1,w2,w0,w3,w4] 0x2a66e25dde2ea61c3034284800042c5824142100580,
mkSt [w44,w10,w1,w0,w8,w4] 0x25deaaa61d8d4810202c382404404830280025d00501]
set_option maxHeartbeats 0 in
noncomputable def p13_D5p1 : List StD := [
mkSt [w104,w10,w1,w0,w3,w4] 0x3731ddd9b2ea61d85828047040180038243448201500680,
mkSt [w10,w2,w0,w94,w3,w4] 0x14a48927525655251730cc30340428381400242c4026908581,
mkSt [w398,w1,w2,w0,w3,w4] 0x2e229de8002a61c078543428382c402460040100580,
mkSt [w399,w1,w2,w0,w3,w4] 0x2a67232de62ea61c705034284800042c6408241500600,
mkSt [w1,w2,w264,w0,w3,w4] 0x32f372e4ea6199d83058281838100c042c2440140100680,
mkSt [w111,w1,w16,w0,w8,w4] 0x1f2b2ea5d121d8143044281050383c200c24341431100601,
mkSt [w1,w400,w2,w0,w3,w4] 0x2a66226ea60001c030342848042c582438002100580,
mkSt [w111,w65,w2,w0,w3,w4] 0x3b713353361d94cc6424401418100450dc3c2c20003406500701,
mkSt [w401,w1,w2,w0,w3,w4] 0x2b31de2c002ea1c0285458346c382c402448040100600,
mkSt [w402,w1,w2,w0,w3,w4] 0x2721e6e8002a61c0281850583c382c342414000500600,
mkSt [w1,w112,w16,w0,w8,w4] 0x22ae7672ea561d94442c70246014040c102834380100680,
mkSt [w65,w112,w2,w0,w3,w4] 0x2a21ddeea1c018002c3420246004642814100100580,
mkSt [w18,w1,w16,w7,w8,w4] 0x1ac716a1838462489c014402c440028382434040c601438438910582,
mkSt [w18,w1,w2,w85,w3,w4] 0x202904218424a18724858500c583c2838040024401439839510502,
mkSt [w18,w65,w2,w7,w3,w4] 0xd309ac424a1090e61a65860642c601024e00820044014280006006510682,
mkSt [w18,w1,w2,w138,w3,w4] 0x3ff7222eaaa6661c542c404810002838043424306c086100780,
mkSt [w18,w1,w2,w143,w3,w4] 0x2bfa3632ee26a61c2c584410003428380430243c08641500780,
mkSt [w2,w21,w0,w9,w114,w4] 0x8222e079c6982d609429038542c3ceca4401c60e85c0ce404182400303fd48881,
mkSt [w82,w2,w21,w0,w9,w4] 0x81e71a2d818a38e59449038542c24a41c785874e460f004143000403fd48801,
mkSt [w61,w21,w0,w3,w9,w4] 0x1ee68d8b529403a0e22c542c58f43c381c0460140c2430180040508781,
mkSt [w36,w21,w0,w3,w9,w4] 0x3f7b72eaaa6021cc54342c043c381c601400f02418300c3fd00781,
mkSt [w2,w169,w21,w0,w9,w4] 0xcc6b0cbd2498398a024642c24783400600418403058140a508681,
mkSt [w144,w2,w21,w0,w9,w4] 0x2ffb6f1ad9aae1d82c64a41c58783474e460300040041500780,
mkSt [w2,w21,w67,w3,w9,w4] 0x1073dcd62d6b5212839854642c043c6c1cf060140cf42430180140800,
mkSt [w2,w21,w7,w3,w9,w4] 0x7a6b2872039e92061e60058342c403c04600ce400241420822910582,
mkSt [w403,w1,w2,w0,w3,w9] 0x3fa1f632e1ea61e4346c48044054302438a4e4002c281500780,
mkSt [w170,w1,w2,w7,w3,w4] 0x10d62d07020e031ae6002c3c383040346c28140018240420908681,
mkSt [w2,w95,w0,w3,w9,w4] 0x3d9bc3d04c56e8c884e083054802c342474a404401c3048140ce418004084204244003fd18785,
mkSt [w404,w1,w2,w0,w3,w4] 0x1cd6898052d075270734302848402c3424380400e414546c3fd08701,
mkSt [w36,w1,w158,w0,w3,w4] 0x3b7726e95661d8143028546c1038604814002c2418040f100701,
mkSt [w36,w159,w1,w0,w3,w4] 0x21dd99e61d8000002c4c2410342800601500480,
mkSt [w1,w12,w61,w67,w3,w4] 0x1ac034cb1b16580b202585030185414a4401c0c38e4f4002c03843910682,
mkSt [w36,w1,w12,w67,w3,w4] 0x8d1b54ae016a489073054100438605c1400f02c24180803908681,
mkSt [w36,w1,w12,w7,w3,w4] 0x1cd4b163d192640867304c2c3834103c601400281824400405d08701,
mkSt [w96,w1,w12,w2,w3,w4] 0x3b31ded9a8a611d8544060140c2c3c6c00302418282000900701,
mkSt [w2,w0,w11,w9,w8,w4] 0x25de6dd569661d9440643014340c28002c202500580,
mkSt [w43,w1,w0,w9,w8,w4] 0xcc1610c59548224483864a40414280c4038300034243fd08601,
mkSt [w96,w1,w2,w0,w8,w4] 0x2362f2d99aa624986c14480c64402400605828342000500681,
mkSt [w104,w1,w2,w0,w9,w4] 0x16260921d1814000642c040c342400584006500481,
mkSt [w1,w2,w0,w143,w9,w4] 0x37fb372eeea619d85058343c3814a4041c0c306428180100780,
mkSt [w37,w2,w0,w11,w9,w4] 0x33f2faf722ea61d8a46438342878580040481474200c2500780,
mkSt [w96,w37,w1,w2,w0,w4] 0x3e3b7219adaaa1d86c18201c486424140458283800403500780,
mkSt [w405,w1,w2,w3,w9,w4] 0x128c1ef7358b721283a02c78343848a404e40c6c28141c544000241940900,
mkSt [w61,w33,w0,w3,w9,w4] 0x81e71869801659411038c2cf850586c28381c701048140c2c24180047948801,
mkSt [w1,w61,w19,w0,w3,w55] 0x1ae1230e68d88da928386c2c14a4401c380c7ce4f818240009d08701,
mkSt [w36,w33,w0,w3,w9,w4] 0x107b98d62d6b5240860cfc50346c28381c70481400102c18240c3fd40801,
mkSt [w36,w1,w19,w0,w3,w55] 0x6d22f6d600cb50907306c10387c48146000fc242c180409d08681,
mkSt [w265,w36,w1,w0,w3,w4] 0x2ab29e2ae1ea61d83c48304c6c081814342c240100600,
mkSt [w266,w36,w1,w0,w3,w4] 0x2dde99aa5daa5d944c5440382804142c34240100580,
mkSt [w160,w36,w1,w0,w3,w4] 0x2aa699aa55aa5d942c40382404143418300100500,
mkSt [w36,w1,w19,w7,w0,w3] 0x1ab618a2b9d6a1a4483834245010186000303814402c0405d08681,
mkSt [w78,w36,w1,w0,w3,w4] 0x2aae9deae1ea61d840304c6c04143444242c0100580,
mkSt [w1,w2,w0,w406,w3,w4] 0x169d2543c8903314a50058342c382810041424400005d08581,
mkSt [w36,w2,w0,w11,w3,w4] 0x2a9d99aa5daa5d942c34200024144030042900500,
mkSt [w44,w36,w1,w2,w0,w4] 0x26a69dea61d800002c24140064302804403500500,
mkSt [w92,w36,w1,w0,w3,w4] 0x2dde99aa5daa5d944c5440382804142c34240100580,
mkSt [w2,w33,w0,w9,w115,w4] 0x9222e079e91a2e059429e385104286c30401c7c4900140ce41000182c243fd48901,
mkSt [w91,w2,w33,w0,w9,w4] 0x92281e2dc68a80e594490382c286ca41c7018783474e448fc10142400403fd48901,
mkSt [w2,w171,w33,w0,w9,w4] 0x1ab332cb2692839963a4342c24647400701018401428584a908681,
mkSt [w128,w2,w33,w0,w9,w4] 0x9825e97358b3292839824a41c705818781074e448280040341540800,
mkSt [w2,w33,w7,w0,w3,w9] 0xc22aa092c8a83a489c60058342440501048180ce4002c1418c22910602,
mkSt [w2,w33,w0,w3,w55,w9] 0x128c1ee731ac5a9283981034506c28a4541cfc7048140cf82c24180140900,
mkSt [w172,w1,w2,w7,w0,w3] 0x14c5a927500e0358e600502464182854301400382c1018d08601,
mkSt [w96,w1,w19,w2,w0,w3] 0x3fb667222ca99260584818380c5054004028242c14302000900781]
set_option maxHeartbeats 0 in
noncomputable def p13_D5p2 : List StD := [
mkSt [w407,w1,w0,w3,w9,w4] 0x139460f7358b525283a02c7834282474a404e41c3848140c546c40001940980,
mkSt [w2,w67,w11,w3,w9,w4] 0x8e6898c52d49820e72830646c20281c38480c142c2400184d908701,
mkSt [w1,w2,w67,w7,w3,w55] 0xe00636099b0492071060a9064303460483814a4541c084000184dc14110702,
mkSt [w2,w0,w11,w9,w62,w4] 0xf78395d0e00000082081c002d10e424290c1c380c1430402000184004e110782,
mkSt [w44,w2,w0,w11,w9,w4] 0xab2a4aa18bac5049a071850a43820783400284840e4241442440110602,
mkSt [w2,w0,w173,w11,w9,w4] 0x8821ee6ad8b525270182c78580064247438344814302840201940800,
mkSt [w145,w2,w0,w11,w9,w4] 0x9825ee6b1865a928398a424641c38187820e47448280040341540800,
mkSt [w2,w0,w11,w3,w55,w9] 0x1ee6b07c20d624a0e70020342c54281c3860480c14243000184ed08781,
mkSt [w1,w2,w0,w408,w3,w4] 0x14a4dce712507514b7282c3438281004140030243fd08501,
mkSt [w204,w1,w7,w0,w3,w4] 0x2fb72ea5565a1d9428402c582420481838003034140500700,
mkSt [w43,w1,w194,w0,w3,w4] 0x25de61d61d661d9430342814042c40202500480,
mkSt [w409,w1,w2,w0,w3,w4] 0x2e66225ea5eea61c3034284804002c4038202500580,
mkSt [w41,w2,w95,w0,w3,w4] 0x148429685190452507b0dc30342800484004142c2454908581,
mkSt [w43,w41,w1,w0,w8,w4] 0x25dea9e61d8d4090202c582400143430042854900501,
mkSt [w104,w41,w1,w2,w0,w4] 0x3371f1db1aea61d83828007874140458482420344100680,
mkSt [w410,w1,w2,w0,w3,w4] 0x2af1de2c002ea1c0743064346c382c402448040100600,
mkSt [w113,w1,w16,w0,w8,w4] 0x2e61b1a6d6a61d9444380c2c142434043060180100600,
mkSt [w65,w113,w2,w0,w3,w4] 0x2eeae9eea1d800002c4020241410303418040100580,
mkSt [w411,w1,w2,w0,w3,w4] 0x26a1dde8002a61c030583c602c342414000500500,
mkSt [w39,w1,w16,w7,w0,w8] 0xca0b2859810e62481e014401824440038302c60100c341464c38910602,
mkSt [w39,w1,w2,w0,w85,w3] 0x90808852c92831492171440180c58503028381000401465865510582,
mkSt [w65,w39,w2,w7,w0,w3] 0xc22b10a209a486441880e90342418202d2004104014300006006510602,
mkSt [w39,w1,w2,w0,w138,w3] 0x3666232eeeeaa61c406000306c3810342c5404284900680,
mkSt [w39,w1,w2,w0,w143,w3] 0x2f66e273322ea61c640058303c3810502c0434281500680,
mkSt [w267,w2,w21,w0,w3,w4] 0x14a42963a94a052707a8dc2c403c0400600824301440d08581,
mkSt [w205,w2,w21,w0,w3,w4] 0x18c6b16d41125412e3983c30e41c1854f0140c3404242c3fd08681,
mkSt [w144,w82,w1,w2,w0,w4] 0x26aa59a629a61d94602c241404403c30440100500,
mkSt [w412,w1,w2,w21,w0,w3] 0x26e5ddea61d9999858342400143004403c602d00580,
mkSt [w1,w2,w169,w0,w206,w4] 0x16ff831b5b2ea71864783834300824000414582c3c406100780,
mkSt [w1,w2,w21,w0,w3,w268] 0xa42888d14a582506283034243c00144004602c0cd08501,
mkSt [w144,w269,w1,w2,w0,w4] 0x2a22a62a61d95540303c600078402c24143500500,
mkSt [w270,w1,w2,w21,w7,w3] 0x1150a61d019500c054284004582430343c01100481,
mkSt [w1,w2,w21,w7,w23,w3] 0x31dee1c028261d5058285434303c0400144024600d100601,
mkSt [w2,w21,w0,w3,w35,w4] 0x528a4091880079e414a0a2834f02ca4240414ac603c0d020910502,
mkSt [w1,w2,w0,w3,w271,w4] 0xf0b680f23a3c0e11cc061034582c283800a4243c1460040e443020910603,
mkSt [w413,w1,w2,w0,w3,w4] 0x26a1ddc0002a61c02c34241430583c6004a500500,
mkSt [w164,w2,w21,w0,w3,w4] 0x93a4c6c94a5820e62830342410144004602c0cd08481,
mkSt [w2,w414,w95,w0,w3,w4] 0x5cb64ea481612003606892314002c10e440240018143034046c86c46c00b118584,
mkSt [w2,w95,w0,w3,w415,w4] 0x3d9bc3d04c56e84884e083054802c342474a404401c3048140ce418006d06cc4244003fd18785,
mkSt [w416,w2,w95,w0,w3,w4] 0x2a22ae29a1aa61d8dc2c40240414003430482900580,
mkSt [w417,w2,w95,w0,w3,w4] 0x2a22ae29a1aa61d8dc303428004840042c142500580,
mkSt [w1,w12,w2,w7,w3,w35] 0x11b3b10b0216a4a0e60030541400343c60a44018282420908601,
mkSt [w1,w2,w7,w3,w272] 0x1b7d3a18be891f50542840202434043c1800602006f06ed10583,
mkSt [w418,w1,w2,w0,w3,w4] 0x32662a00002ea600782c4024181454342838a40500600,
mkSt [w273,w1,w2,w0,w3,w4] 0x291d99a61da61d947854343c60042c40241500500,
mkSt [w83,w2,w0,w3,w35,w4] 0x11a3d8c64a0e64a0e628782c1c4024143460382848108501,
mkSt [w1,w274,w57,w0,w8,w4] 0xa6524a8b14e0314641c185060243014000c2c3874d08501,
mkSt [w275,w1,w57,w0,w8,w4] 0xaa498a8b14e031480002418600c50383c282c1400d08501,
mkSt [w1,w276,w57,w0,w8,w4] 0xc52aac941ca0198a41c343c2c701428000c382475108501,
mkSt [w277,w1,w57,w0,w8,w4] 0x4819e8331060290600028340c50383c142401108401,
mkSt [w1,w57,w7,w0,w8,w4] 0x71f8581ccb683c8e620183860340c001475074c388d0383,
mkSt [w2,w57,w0,w11,w3,w4] 0xd34c2cb2c6a86187109207030e42834801838202c400c241411c0d510682,
mkSt [w1,w2,w0,w278,w3,w4] 0x280be020280072a49351040342824304814000c2040184e87541d110583,
mkSt [w279,w1,w2,w0,w3,w4] 0x2eae16800032ea003040282414502c583c380c2100600,
mkSt [w73,w1,w419,w16,w0,w4] 0x10942500100e6290001c3029080c7018142c2477d08481,
mkSt [w420,w73,w1,w16,w0,w4] 0x12a4880831407b14040030290814503c00382c2477d08501,
mkSt [w421,w73,w1,w0,w8,w4] 0xeb5a94038138380c5002820600c503c0434242c0078108581,
mkSt [w73,w1,w422,w0,w8,w4] 0xeb51c0942008380b018304c2420503c6034002c0c78108581,
mkSt [w423,w73,w1,w0,w8,w4] 0x18b3014a4c0c8380c500302820340c503c10602c240078508601,
mkSt [w73,w1,w424,w0,w8,w4] 0x18b2a805025293c0a01844282c205034143c6000240c78508601,
mkSt [w73,w1,w7,w0,w8,w4] 0x14de014942008300c320304c2d2824201460280034440c78108681,
mkSt [w1,w16,w280,w0,w8,w4] 0xc2222ca2489c614c10200382c50383c30442834200c240027006510602,
mkSt [w281,w1,w16,w0,w8,w4] 0x21ddb196eea61d9444200c2c702460101428340100600,
mkSt [w1,w16,w72,w7,w8,w4] 0xcac72a9006a071819451030182c28144c243420040c600078805d10602]
set_option maxHeartbeats 0 in
noncomputable def p13_D5p3 : List StD := [
mkSt [w1,w16,w0,w11,w8,w4] 0x98042059682821499c61600442c30380024142834200641d110502,
mkSt [w1,w7,w0,w85,w8,w4] 0x81c07700e020118c3b01838201400794288790d0283,
mkSt [w1,w0,w85,w8,w4] 0x220105a50a2718541830200c281438340079079510482,
mkSt [w104,w1,w16,w0,w8,w4] 0x108321462108945cc521280c30142834002c242029508501,
mkSt [w1,w16,w7,w0,w103,w8] 0xc2ea9802481c798414190303818302444602c10200c340079c05d10602,
mkSt [w282,w1,w16,w0,w8,w4] 0x2661b1aed6a61d9444200c2c142434043018600100600,
mkSt [w425,w1,w2,w0,w3,w4] 0x2a229e00002a61c02c40241434304828200d00500,
mkSt [w283,w1,w2,w0,w3,w4] 0x21dd8de61da61d94305828380c2c40142500480,
mkSt [w426,w1,w2,w0,w3,w4] 0x25de59e61da61d943034284800402c142500480,
mkSt [w43,w65,w1,w0,w3,w4] 0x32672e72e61d595430403828006018482c34241500600,
mkSt [w44,w65,w1,w2,w0,w4] 0x26a6a62a61d8000030284800642c1424344100500,
mkSt [w2,w0,w284,w3,w8,w4] 0x372ea9c0002615c0306440206014042c344800282500680,
mkSt [w1,w2,w72,w7,w3,w103] 0xcc08ee3a190c802613510106430346024481020044018001407c405d10603,
mkSt [w1,w2,w0,w174,w3,w4] 0x8edad45c08009148100144c5040142c300024203428480600d406510583,
mkSt [w1,w0,w60,w8,w62,w4] 0xa70389a0e00000061461401303464292c482004303860007943147d110603,
mkSt [w44,w1,w0,w60,w8,w4] 0x9e39aa9967dc3062d8512305438602040483400640435031429510503,
mkSt [w43,w1,w0,w8,w62,w4] 0xa670000008cc800718510302c382030341428043c003503147d910503,
mkSt [w43,w44,w1,w0,w8,w4] 0xe72a9483e4a8398a020204000301428342c240429508501,
mkSt [w1,w175,w0,w3,w8,w4] 0x27fb6ef252ea62d8304028602410140c04002c4838083c05500781,
mkSt [w1,w0,w427,w3,w8,w4] 0x32c28026221dd998706460283c2004144834240000500601,
mkSt [w1,w176,w2,w0,w8,w4] 0x2767fb7270ea61d8301428643ca4401c0c042c2434580000500781,
mkSt [w1,w2,w428,w0,w8,w4] 0x3222c2e4241dd99830643c602820042c2434480005500601,
mkSt [w285,w2,w7,w0,w3,w4] 0x2fb72e9e61d9559428402c582448183820043034140100700,
mkSt [w1,w429,w2,w0,w3,w4] 0x1642a40466d5941c87301850343c14100420282438005806508681,
mkSt [w135,w2,w0,w11,w3,w4] 0x129e18c6d814b4a186000460482c580024383428201406108601,
mkSt [w1,w2,w0,w430,w3,w4] 0x1ceeb18cd8149720ec002c3424384814580008042028401806108701,
mkSt [w431,w1,w2,w0,w3,w4] 0x2731adea5daa5d9428485458346c38042c40241500600,
mkSt [w1,w2,w0,w432,w3,w4] 0x165c14092a149320d7302c482834080430142024401d108581,
mkSt [w198,w2,w0,w11,w3,w4] 0x147c9926c00e6400e62864342c0024382814204006508501,
mkSt [w1,w2,w0,w433,w3,w4] 0x1cddb563e8143680e328582c2834481820041c380024144006508701,
mkSt [w434,w1,w2,w0,w3,w4] 0x231da2e69da61d9428184050583c38002c34241500600,
mkSt [w1,w435,w2,w0,w3,w4] 0x14a418e8565075000600304024483820342814004e908501,
mkSt [w286,w2,w33,w0,w3,w4] 0x148413885956052704a8dc70503424100048042c28144b108601,
mkSt [w207,w2,w33,w0,w3,w4] 0x1ae7358e514e44a2e3982850e41c14fc346c70640c102c243fd08701,
mkSt [w128,w91,w1,w2,w0,w4] 0x22a9a1a61da61d944c2c241410405028480100500,
mkSt [w287,w1,w2,w33,w7,w3] 0x115161d5019500c06c3010342428405000d00401,
mkSt [w436,w1,w2,w33,w3,w4] 0x2aa6ddea61d99998702c34001428105040482500580,
mkSt [w1,w2,w171,w0,w208,w4] 0x365703fb7b2ea718747034642c0428001014585024404900780,
mkSt [w1,w2,w33,w288,w3,w4] 0x14702a87594e5d200628702c50642800144010482411908581,
mkSt [w128,w289,w1,w2,w0,w4] 0x26eea62a61d595404c5028480074402c24146500580,
mkSt [w2,w33,w0,w34,w3,w4] 0xc2c24022059602818881c68402c24701018381cfc90641412018d10602,
mkSt [w1,w2,w0,w290,w3,w4] 0x7c3a6400049c696188300203424706438141800101c4ac0e818d10503,
mkSt [w437,w1,w2,w0,w3,w4] 0x2a22dec0002a61c0702c40241450342848101d00580,
mkSt [w1,w2,w33,w14,w7,w3] 0x2322e1c280261d5034306c64502810001440244812100601,
mkSt [w162,w2,w33,w0,w3,w4] 0x10b01acb51565c1c06282870182c6404143410482411908581,
mkSt [w438,w1,w2,w0,w3,w4] 0x26ade600002a61c0742c402414306c38641c1100580,
mkSt [w1,w19,w2,w7,w34,w3] 0x1375a58b4816a4a0e600286c38640050481c4014302418d08601,
mkSt [w291,w1,w2,w0,w3,w4] 0x212e9aa61da61d94747050646c48102c24401500580,
mkSt [w1,w2,w7,w292,w3] 0x38a270ecaca22506c40102024642804144850008783c889110603,
mkSt [w137,w2,w0,w34,w3,w4] 0x16b26d4781127011272830742000246c4840141c2c47d08581,
mkSt [w209,w2,w0,w34,w3,w4] 0x16b26da3d99875a4b71474cc2c1c64046c48004024143019d08681,
mkSt [w210,w2,w0,w34,w3,w4] 0x9bc03ce21f32b2890e020003074704804185024384080901c142c0240a910782,
mkSt [w78,w139,w1,w0,w3,w4] 0x2aae9e2ae1ea61d840304c6c04143444241c2d00580,
mkSt [w439,w1,w2,w0,w34,w3] 0x2ae29e2a61d999987440002438301c646c142d00580,
mkSt [w1,w165,w0,w177,w3,w4] 0xa33d707b9a062d4943474387048183040002404601c2c6c641540800,
mkSt [w1,w2,w0,w34,w211,w3] 0x12acad27d0007501072874403000246c481c64142c47d08581,
mkSt [w293,w139,w1,w0,w3,w4] 0x266e6de69ea61d804014304c6c04344448242d00580,
mkSt [w294,w1,w2,w7,w34,w3] 0x6f7498598580506424386c40140f4c0381,
mkSt [w440,w2,w0,w94,w3,w4] 0x5caa70000011664000f46300080302040382c0424140080348f88f41ac8f08ed18585,
mkSt [w2,w0,w94,w441,w3,w4] 0xdda331bcb000000010de3050002c1000240870403804148018349000240c48fc10118685,
mkSt [w442,w2,w0,w94,w3,w4] 0x2aa5ddea6dea61d8cc303404283814002c402500580,
mkSt [w443,w2,w0,w94,w3,w4] 0x2aa5ddea6dea61d8cc2c40002414043830342900580,
mkSt [w295,w2,w0,w11,w3,w4] 0x165d0ce0329875a8b724cc30402004283800142c34241d908601,
mkSt [w175,w2,w0,w11,w3,w4] 0x6a662011c59870849845054102c045838208014340c410110482]
set_option maxHeartbeats 0 in
noncomputable def p13_D5p4 : List StD := [
mkSt [w43,w141,w1,w0,w3,w4] 0x25dda1e61da61d9430342804142c40202500480,
mkSt [w296,w2,w0,w11,w3,w4] 0x124d8cc2aa9464a2962934483034002838042c24144fd08581,
mkSt [w176,w2,w0,w11,w3,w4] 0x3b0b103286a490459d5546030e41c480c3438202c58001442440110602,
mkSt [w145,w44,w1,w2,w0,w4] 0x226199e61da61d942c241420403028480100480,
mkSt [w1,w2,w0,w11,w212,w4] 0xa4c9007224072250700340024202c302848401d108481,
mkSt [w444,w1,w2,w0,w11,w4] 0x2e66326ea61d9998482c0024385834203028144100600,
mkSt [w1,w166,w0,w178,w3,w4] 0x3b55df2d02a6625858483c381880002404603428142100700,
mkSt [w1,w2,w0,w11,w297,w4] 0x14ac9ce7d086750907302c34042438203014402806508501,
mkSt [w203,w1,w2,w0,w11,w4] 0x2e66326ea6180000442c0024382058302814403500600,
mkSt [w298,w141,w1,w0,w3,w4] 0x219a1da1da61d9401430342804382c402500480,
mkSt [w1,w0,w11,w213,w3,w4] 0x1275270a490844a0e520483034382004242c28144e908501,
mkSt [w445,w1,w0,w11,w3,w4] 0x332e6672ea5a21d82c340024481838203040281500600,
mkSt [w1,w2,w0,w173,w179,w4] 0x32c372e952421c002464583814040028341840e42100680,
mkSt [w1,w299,w0,w11,w3,w4] 0x14aa18c6a8166520e600482c30580024384020281406108581,
mkSt [w204,w1,w0,w11,w3,w4] 0x332e2232e615dd942c342000244818143040283900600,
mkSt [w145,w300,w1,w2,w0,w4] 0x226261a619d5594030280048402c24145900480,
mkSt [w301,w44,w1,w2,w0,w4] 0x21ee99a61da61d946010546c3804343028480100580,
mkSt [w44,w1,w2,w0,w302,w4] 0x25dd99ea95661d942030402848002c24380500500,
mkSt [w43,w303,w1,w0,w3,w4] 0x32ff9df72deb21d8641050583c7044140448302818340100780,
mkSt [w43,w1,w304,w0,w3,w4] 0x21de61e956a61d942030342814042c58240100500,
mkSt [w305,w1,w2,w7,w3,w35] 0x2520dcc190c150c0303c48a4285438241403100481,
mkSt [w306,w2,w0,w3,w35,w4] 0xbc1dce732cc7517071478cc5404342860002c40142421508601,
mkSt [w214,w2,w0,w3,w35,w4] 0x1ee6b18249c0928e6a0010340c280824147804802caca43c6002508781,
mkSt [w92,w142,w1,w0,w3,w4] 0x3221ddeea1e661d84c2c404828a414543438240500600,
mkSt [w446,w1,w2,w3,w35,w4] 0x269d99e61d800000782c004018543438242900500,
mkSt [w1,w168,w0,w3,w215,w4] 0x372dd9c0002a61c04878442c00402438543428146100680,
mkSt [w1,w2,w307,w3,w35,w4] 0x13a354a5480c549cc520782c540040241434602848108501,
mkSt [w308,w142,w1,w0,w3,w4] 0x31dee9e65e621d804c2c4014482804543438602500600]
noncomputable def p13_D5 : List StD := p13_D5p0 ++ p13_D5p1 ++ p13_D5p2 ++ p13_D5p3 ++ p13_D5p4
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x0 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x1 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (1*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x2 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (2*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x3 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (3*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C5x4 : levelOK p13_T p13_K p13_P 4 (p13_D4.map Prod.fst) ((p13_D5.drop (4*64)).take 64) = true := by decide +kernel
theorem p13_I5 : LevelN p13_R p13_T 5 p13_D5 := levelStep p13_B p13_W p13_Q p13_I4 (chunks 64 p13_D5 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C5x0
  · exact p13_C5x1
  · exact p13_C5x2
  · exact p13_C5x3
  · exact p13_C5x4
  ))
set_option maxHeartbeats 0 in
noncomputable def p13_D6p0 : List StD := [
mkSt [w82,w1,w2,w6,w0,w3,w4] 0x2e48e402000001c60f30208b0950003c503c381028140c300402802400402110484,
mkSt [w25,w1,w12,w2,w0,w3,w4] 0x4b03a82aca0092071651451260e28054305c5428141034042c24180002803803510603,
mkSt [w1,w56,w0,w8,w4] 0xb750e3a86918b31828382414406020042818340c03000805405118584,
mkSt [w1,w6,w7,w0,w3,w8,w4] 0x20191e1d5b5956040914120446d2c610040e0d420a068403018642c2460100c08003448140406806003005c05958805,
mkSt [w27,w1,w32,w6,w0,w3,w4] 0x101c348d09f3868c162828512144070c00302050583c2c7424481000703414043040180c00807d50882,
mkSt [w27,w1,w30,w6,w0,w3,w4] 0xc162c84f9d3460b142028512203070c00302050583c2c78246000103470044028140c00808150802,
mkSt [w27,w1,w6,w7,w0,w3,w4] 0xd21b778d1c3068cc62c281c2284880f903050302c244060100070341838041448580c07400806150803,
mkSt [w91,w1,w2,w6,w0,w3,w4] 0x9e02e402000001c60f30209508b0003c503c381030140c280409402400409110484,
mkSt [w25,w1,w19,w2,w0,w3,w4] 0x6b02ac3a4a0092071241071a50a38044287c306c60102c340414240009409c03510603,
mkSt [w1,w2,w447,w6,w0,w3,w4] 0x14221e201e1c051a1800e2140e000004021c10000e4305058243428706408001404803c182c400a00a80040a558884,
mkSt [w262,w1,w2,w6,w0,w3,w4] 0x6dacf403032cc246134a071b50008248503c741838008030400c2c14040240ac02110683,
mkSt [w1,w2,w448,w6,w0,w3,w4] 0x200c182220081e031c00da18080000140212100004430582c24703418100800803c502804144001c0b40040b158884,
mkSt [w449,w1,w2,w6,w0,w3,w4] 0xcf1e808cb1236482c1ba06244070cc1000064403c480c0080305834701014040b80c40c00bd18684,
mkSt [w1,w2,w32,w56,w0,w3,w4] 0x17ad60bc143d8ac1410dab9648010d953654803c30586018100c081404802c0d40d000801c0cc0c807d18607,
mkSt [w25,w1,w2,w32,w0,w3,w4] 0x110c30815242858408c440204ac88e0180582058242c343c14043060000cc0d40d00dd18504,
mkSt [w1,w2,w32,w30,w0,w3,w4] 0x88040b14c200492001a8060d19144040a12202c642440701410341804000e80e40b80e118584,
mkSt [w1,w2,w32,w6,w14,w3,w4] 0xf2002800123c70941042091a0278a12203c605030246018100c3c0008148c4080042c03c0d950802,
mkSt [w1,w2,w32,w6,w7,w3,w4] 0x183f00f1ceb400348472c0ced1c61740582834686018100c3c00081404804003c0b805d10783,
mkSt [w450,w1,w2,w6,w0,w3,w4] 0xe08d3ad832b252ca24420708d980d44050584038100c0080241404182c080c810410110703,
mkSt [w1,w2,w451,w6,w0,w3,w4] 0x1e2214201e1c1a180900d6141200808682888e000482850583c306470341808000480242c144003c10c10800558884,
mkSt [w452,w1,w2,w6,w0,w3,w4] 0xd08c03db252e2a8424420718d880d440583c40380c00802c70101424041101140c510683,
mkSt [w1,w2,w56,w30,w0,w3,w4] 0x1631670b5f0060b9c15daa3403934bc41a5e80285058183848100c1404802412011c00801c11811008118607,
mkSt [w1,w2,w56,w6,w14,w0,w4] 0x109e03780082814001947041628487882038603050248c18384010200c142c5880640401c0c80d950803,
mkSt [w45,w1,w2,w56,w6,w0,w4] 0xa2240510012880f1c2828d1c2c509101c4050503c3840200c802c24583414042818083012c10550882,
mkSt [w1,w2,w56,w6,w0,w23,w4] 0xe13c0040a0a00a01b420516280c40e2038602824a02c18384010200c143c5880340401c11012550803,
mkSt [w71,w1,w2,w56,w6,w0,w4] 0x92044809014048f1c1428d1c2c509101c40503c503840200c802c24586470103014280412c11550882,
mkSt [w1,w2,w453,w3,w4] 0xb94ea4a28ed88c16a864246048141000342818040f00d400813518584,
mkSt [w1,w2,w7,w0,w3,w102,w4] 0x1dff0dc19f5806f682f80e9b281e61c0e10a0645830342c2460384018141020040014413814011c0d405c05918787,
mkSt [w1,w2,w0,w3,w454] 0x49729cc26e9a0b52a8303460481410002c40180411c0f000814918584,
mkSt [w1,w2,w6,w455,w0,w3,w4] 0x121e4ca80ec53961823b16911857a34e180094285058182c0800140480400dc1541000d80a815118586,
mkSt [w1,w2,w6,w0,w3,w456,w4] 0x1a2e05387304e0974ecd5b74e82942206200a8302458182c0c080014803c34041581240c410c16015d18686,
mkSt [w25,w1,w2,w30,w0,w3,w4] 0x100434a13182058c109030d08ac06e1a0058402c58503424144804002811811c12015918504,
mkSt [w25,w1,w2,w6,w14,w0,w4] 0x11de407c0c9164c49c340e4182c382d0001420302850481000148c243464042c5880400c0dc0d802550883,
mkSt [w25,w1,w2,w6,w0,w23,w4] 0x1223c00648b262459c07206182c1680e0014203028241844100014a02c6434043c5880400c15812402550903,
mkSt [w25,w1,w2,w14,w0,w4] 0x7ce003464916d2534705a0586ec30504c18101c144004642400582c481380dc1640d80f118785,
mkSt [w25,w1,w2,w7,w0,w3,w4] 0xe04002e04720c9f31028e985a00026405818341448040000816811c1580d40dc140d8387,
mkSt [w25,w1,w2,w0,w23,w4] 0xd9c3660b0729bb36b02c186ec3c2c6018a414400424345800284414415816c1240f118705,
mkSt [w309,w1,w2,w6,w0,w3,w4] 0xe34236e83db252ca244207362180d44058504048100c00802814041834080e017810110703,
mkSt [w202,w1,w2,w6,w0,w3,w4] 0xcd65f002cc2842418f32070061708238503c783800803428240c140402417409110603,
mkSt [w1,w2,w30,w6,w7,w0,w3] 0x1b40f401cc2e0031267280f059c60f4058643048700c500010140480400a00e005d10683,
mkSt [w1,w2,w30,w6,w0,w23,w3] 0xb4f0093ce25d02424d300a893480a603c2c2448700c50001014a0408004280a012510782,
mkSt [w2,w6,w14,w0,w34,w3,w4] 0xbb8914d08b300c3b1245042892010060108c745070408018382c1c64041401c02410110703,
mkSt [w2,w6,w0,w34,w3,w4] 0x1df5c2465a4035da919649d80d66400509080146c704064241c0418300541941001980d400402418c01c1892068a,
mkSt [w1,w6,w14,w0,w46,w3,w4] 0x10e05c154d54208124407601d3a10c141a0040648c28504840140804002c00c02410019d18584,
mkSt [w78,w1,w6,w14,w0,w3,w4] 0x1909fcc7c3460b96ed92748d04880f058050288c583c504808007040183804802c140241000a80d918784,
mkSt [w78,w1,w6,w0,w3,w4] 0x3a3a343a34080e2c94815a1d61418d42c5058100c0870181430244004483c0101a00a40040241000a80d920788,
mkSt [w1,w2,w14,w0,w177,w3,w4] 0x1d8f0530142f0d01301681408401c8180811002450342870381848100008042c141c0e81380a818016410118786,
mkSt [w140,w1,w2,w6,w0,w3,w4] 0x534524520c2ca009088024642200d160307064182c242804581450403c1001500a910683,
mkSt [w140,w1,w2,w14,w0,w3,w4] 0x6040c40e071430c6102083180c308d243c702c1404481c500dc0d810110403,
mkSt [w140,w1,w2,w0,w3,w4] 0x486890858a925cc4333964400e448182c240430403c1c501411c1000dc0d80e80a918586,
mkSt [w1,w2,w6,w161,w0,w3,w4] 0x61ce4f834301e05ed80e925d0c1401c042c001410450583c247034182c0800140480401a40241b00040c41000081ad20708,
mkSt [w84,w1,w2,w6,w0,w3,w4] 0x181a0070180c84ac00a82a4407001800000040380c00802c2470103414041201b40e80c518604,
mkSt [w1,w2,w6,w14,w7,w3,w4] 0x183c2571c1c041681c2bc701c58372d2b860a02c34704038100c6c2800142404806401c1b812010001118785,
mkSt [w1,w2,w457,w6,w0,w3,w4] 0x36119c6128c00e6ad8b534e8398503058282470403818100c2008802c3c14046410140981,
mkSt [w1,w2,w6,w0,w3,w200,w4] 0x8053d9b2984060019bc00244026e18284068283c7040341838100c08001404800c40e801c0d118704,
mkSt [w2,w6,w7,w0,w11,w3,w4] 0x1499b808201e0a00ec4aa12644884e181000802c24582070400418388014341cc1c40c410118604,
mkSt [w2,w6,w0,w11,w3,w4] 0x3a403411e1c25e701911de480d61c002c0c5870801428302040240418341d40c41cc11c0040d41001d01c520709,
mkSt [w1,w6,w7,w0,w60,w3,w4] 0x1102c00b09503840e43c8001d3a682141a00406c58381014080400401dc0c400c1001d918485,
mkSt [w43,w1,w6,w7,w0,w3,w4] 0x1b028bf1af864d18f1dc748d0480ae0d8050682c24583810080068401848041480341e00c41000b405d18785,
mkSt [w43,w1,w6,w0,w3,w4] 0x7041a1870d18edeb0931e3c0cb05824100c087018142c0450383c340b012c0040b40c410118706,
mkSt [w1,w2,w7,w0,w178,w3,w4] 0x7019df868270d403014b14094248e180a1500282c5824404818380c0008043414200301e81e41000b518785,
mkSt [w93,w1,w2,w6,w0,w3,w4] 0x914b14920524800c2ca0264c9200d940104008342824145004303c581001ec0b510603,
mkSt [w93,w1,w2,w7,w0,w3,w4] 0x60310312051830c41c20830360308d243c0c3414043820581f005c10110403,
mkSt [w93,w1,w2,w0,w3,w4] 0x575b96b985afe4c5121533700e44038500c0804283c345814201f40f01f005410005c0b518607]
set_option maxHeartbeats 0 in
noncomputable def p13_D6p1 : List StD := [
mkSt [w44,w1,w2,w6,w0,w3,w4] 0xcdb236f8d317c77a80f367a0386ca1380006c2c5818381000803034280c14041fc1f811c0d402400400918687,
mkSt [w1,w2,w6,w7,w0,w23,w3] 0x201b1207931e09521d061b52190e16155211078c0a05824284018380c3008540014342c048001c0d01b02000c400d58806,
mkSt [w2,w6,w0,w23,w3,w35,w4] 0x4f803080f41ac060c5ab362c509501c0060a0a07808a4247080401438343c041801c2040c402518704,
mkSt [w2,w6,w0,w3,w35,w4] 0x16424e7c141a6dd5b8326de40c000083c705404803414ac2c40a42818242100c40040540242081a801c20520789,
mkSt [w1,w6,w0,w23,w3,w127,w4] 0x1cf5e4b012813e04894b012a5407021800806070a034306460242c400408003c140100c402421518704,
mkSt [w92,w1,w6,w0,w23,w3,w4] 0x1f3868284c9e4c78ec427482d4888ec0305028a05058602408002c40183804803c140c402410c12518784,
mkSt [w92,w1,w6,w0,w3,w4] 0x38123e38081230acaa0161615e018d4405024100c081814282c343c04586000c2181080040c402410c12520788,
mkSt [w1,w2,w0,w23,w3,w215,w4] 0x17aecc00ec0d012269580489126ae193244c0a0343064283c3800a404081460240c416c10c0d00f518705,
mkSt [w167,w1,w2,w6,w0,w3,w4] 0x53472451cc14d0092870246421c0d160287018402c302404581450343c02415c10d10683,
mkSt [w167,w1,w2,w0,w23,w3,w4] 0xf80dc69aad24a88ca2a04040c0c1228502414043c60a40c4158024124d8384,
mkSt [w167,w1,w2,w0,w3,w4] 0x2ddb816d8a0d70b933362be00c4284060182c3424045014a4583c0d41580d012402410d18686,
mkSt [w163,w1,w2,w6,w0,w3,w4] 0x70018e86006bc002c539402038007180000002c704038100c00802414043418081c00e40d010118704,
mkSt [w1,w2,w458,w6,w0,w3,w4] 0x39ac83a307340a6296a3b0e83983c302c58284038700c201080502414043412d40881,
mkSt [w1,w2,w6,w201,w0,w3,w4] 0x1cb400d000203a800062380004074cc000407064507040341838100c080014048001c1200e410118704,
mkSt [w253,w1,w0,w8,w4] 0xc772a49371193b48a8382418100044600c2814043400c22800405118604,
mkSt [w1,w2,w7,w0,w3,w126,w4] 0x1a302a4165020111c0028014001c9120a4068306434244818200c14002380d414011c00c06518506,
mkSt [w10,w1,w7,w0,w3,w8,w4] 0xd2b0b2baa0903e4820822800700600506830186424003860041434482006000c06510683,
mkSt [w1,w2,w14,w0,w310,w3,w4] 0x39d1819ee6818b39d474a50841c64306c5034287018201c48408c242c140026540881,
mkSt [w10,w1,w14,w0,w46,w3,w4] 0x824824f38d300ac920a28a2481c6185024145034281c2c643848048c00304026426910782,
mkSt [w10,w1,w2,w161,w0,w3,w4] 0xa28134c2c2c7400a240c08cb1dc0185050583c2c40cc2438041428303427022826910683,
mkSt [w84,w10,w1,w2,w0,w3,w4] 0x898091202482802481c61400800000cc342838042c1400244027827510502,
mkSt [w10,w1,w2,w14,w7,w3,w4] 0x16c13456095ba14c954bb142440742992a406040201ccc306c283804146401c26c00c26918584,
mkSt [w10,w1,w2,w0,w3,w200,w4] 0xb0000822200081200082a90002071850301ccc3428380414003c4027827510582,
mkSt [w1,w2,w7,w0,w459,w3,w4] 0x9037031aca2602041c48a494716596402854586c4018203800143428c26828910583,
mkSt [w10,w1,w7,w0,w60,w3,w4] 0x12c2300822c50900a03b60e1c3846c142040601454586c2040483804003429027428826918584,
mkSt [w44,w10,w1,w2,w0,w3,w4] 0x516116020a082a458081c6164040080020cc243804303414002822829425d10503,
mkSt [w10,w1,w2,w7,w0,w23,w3] 0x3a29f280108920e30b9fa04224818504020a400cc28542c38041c14303401c29801110703,
mkSt [w1,w2,w0,w23,w3,w460,w4] 0x40cf701ac5ad6739ce74a54941c54343064283c20a41c602ca04024140029d40801,
mkSt [w10,w1,w0,w23,w3,w127,w4] 0x9384340b061862c928a2862481c71850a030643ca4543860280434002c2429c25d10702,
mkSt [w163,w10,w1,w2,w0,w3,w4] 0x98022480090e02892001c60021400000cc30403804241400342c2a026910502,
mkSt [w10,w1,w2,w201,w0,w3,w4] 0xca002002c81c000a9c00092070001850642820cc50343804140030402b426910602,
mkSt [w1,w2,w90,w0,w23,w3,w4] 0x11280466d024880004488000428284d1932640302c40382814a40400240f42c400c12518504,
mkSt [w71,w1,w2,w90,w0,w3,w4] 0x152410080c8ac504a01c304020a70c08035070d028142c5838481024002cc0981142c918504,
mkSt [w1,w19,w2,w0,w3,w156,w4] 0x14d9029000042870c0380ad00282464d803a742c28143034381c10002415003009c0f42e918505,
mkSt [w66,w1,w2,w0,w3,w156,w4] 0x11e6050a555ca4e141c0929448800dc284070406814082c58342438a428002f80102f42f118604,
mkSt [w111,w1,w16,w2,w0,w3,w4] 0xe000126184b4c2ca2400a2a011c600502c3424481004503c382030280c5831030d10702,
mkSt [w111,w1,w2,w0,w3,w8,w4] 0x1021d88b429c090028401ce283b601562000404024142c0050343c48200405831405406000406518586,
mkSt [w27,w111,w1,w2,w0,w3,w4] 0xf82b80d3c28b2040bc070c03a80c802982e004450583c203414040031032431c00832006031918487,
mkSt [w37,w111,w1,w2,w0,w3,w4] 0x182856d3d80b2e208400ee18280c802982e0044503c38204048000433833432c0f033006432918487,
mkSt [w1,w112,w16,w2,w0,w3,w4] 0x8900b2e02892070020000041a41400143428482c040c1040240034834510582,
mkSt [w1,w112,w2,w0,w3,w8,w4] 0x1215864cde2aa08d9c809098aa2420830204840142c643424604804100035835435034d18584,
mkSt [w27,w1,w112,w2,w0,w3,w4] 0x1c2c090e80070001049000060350040442c2434140448400036035c32510483,
mkSt [w37,w1,w112,w2,w0,w3,w4] 0x1c38090a80070001019000060350040442c2440480034140436836433510483,
mkSt [w18,w1,w16,w0,w8,w4] 0x1ea3391c626f0f0478c170446003018440c50383414602c22837005000c38438118506,
mkSt [w18,w1,w16,w2,w7,w3,w4] 0x170120954284a8001c2cb66d52a2880dd024204038303448080c5824280437c39000c30d18584,
mkSt [w18,w65,w2,w0,w3,w4] 0x68c2c6ea56b5462d49220047a0064306010503448240014202c4022804c3ac3b03a918685,
mkSt [w18,w1,w2,w7,w3,w8,w4] 0x1dde0b0b5723a07568b11214488611d294440402c140028346424486004083b40600640183a431405918607,
mkSt [w27,w18,w1,w2,w7,w3,w4] 0x1cf41a2781e8b50f5423348c9509901c305000402c44e0043034241400285848082283b432031801918705,
mkSt [w37,w18,w1,w2,w7,w3,w4] 0x6f83dd78090b50f5423348c9509901c3050002c1444e00430402448082834380001c3b433032801918705,
mkSt [w18,w1,w19,w2,w7,w3] 0x2c69cea60e0260cce8ca1c4cc44218c501464003404302824104822833c3b40640300980183d03d43c92058a,
mkSt [w18,w1,w2,w7,w23,w3] 0x2925231ee2860e610e0c44210dc58c406054a4002804302438083433c01c3b406000c0100183e43e82012060a,
mkSt [w12,w2,w21,w0,w3,w9,w4] 0x14280018d2e50672000b670de1916cc80200a0743000605c0414e41840544003fc22801518584,
mkSt [w2,w21,w0,w3,w9,w4] 0x78200073ebd0139fbcc16a85cb85478a4e43c0cf02c241460040040300541940040d03fc40822918787,
mkSt [w1,w12,w2,w0,w9,w114,w4] 0x14280019b2652c72ae52072a03810c1420300074605c5434284840042418002c4000303fc40d18684,
mkSt [w82,w1,w12,w2,w0,w9,w4] 0x1a0a64d78fa6bc76281290c952080e1a2b00285c54346c14047858241800e42c404003fc41003918704,
mkSt [w82,w1,w2,w0,w9,w4] 0x7fee61be8209c2d294dc33d7a94542c3818a41c0c784030240034146c0980a40544003fc41003918787,
mkSt [w1,w461,w2,w0,w3,w9,w4] 0x1c3402d182c48914241c060a03834c1512140054306c3c603828140840002c24184144100a405518704,
mkSt [w1,w12,w2,w0,w3,w206,w4] 0x13dff0999a2520d0b75201098281e608142448785818245c542c34402814a40804002081381804004183fc41118787,
mkSt [w170,w1,w12,w2,w0,w3,w4] 0xe0ceca68329ac03a188d24a86840c048786c2c0034045440041c3fc038d8384,
mkSt [w170,w1,w2,w0,w3,w9,w4] 0x93003072c514a1490285c1240e171440303c602c4024283800546c183fc2c441110603,
mkSt [w170,w1,w2,w0,w3,w4] 0x586ab60584b44cbd835804d8ae4342c24180030406c04385411c41c2080383fc41118586,
mkSt [w1,w158,w2,w0,w3,w9,w4] 0x1a120018cdd1f185adb5a40181601c1814104c0400028304818546c382c044024001442c4283fc0544244000f00b120688,
mkSt [w159,w1,w2,w0,w3,w9,w4] 0x6000d0e2a10a1800b140a28900000058003404e42c78242860a440001443443042420918604,
mkSt [w1,w12,w61,w0,w3,w9,w4] 0xc8a0f801ce03db4c124ac02481c114403018542814a420401c0c38e42c0022803843910703]
set_option maxHeartbeats 0 in
noncomputable def p13_D6p2 : List StD := [
mkSt [w36,w1,w12,w0,w3,w9,w4] 0x108b488e0d1401c39e3868c038c500050b382034305428a404401c605c2414002ce438180c41c0383fd50903,
mkSt [w36,w1,w12,w0,w3,w4] 0x68c8d2c50012d1bc77061ac0aec4c305434101800246004382c4013841c41803800918685,
mkSt [w1,w12,w2,w67,w3,w9,w4] 0xd04f34082d00e38d18619c34a2429c6064185414a408401c0c6c245ce4002c43c03910782,
mkSt [w1,w12,w2,w7,w3,w9,w4] 0x1a070d04dde04b94a2856a94d811220146aac342c1814a404403c0c2860e4240044020822840009842d18706,
mkSt [w1,w2,w462,w0,w3,w9,w4] 0x4a11739d003dcb5b16b525073ac5458307428246018a420e41c0c402c006c3844940901,
mkSt [w1,w2,w197,w0,w3,w9,w4] 0x11982c80d80207a320000021c316e19083040786c282460140440e41ca40c0042443022818d18684,
mkSt [w17,w1,w61,w0,w3,w9,w4] 0x11144050f1e2804e1e2868c0a38508101c305054586c1820e40c2c403824141c2874003044844550882,
mkSt [w1,w61,w0,w8,w4] 0xa770e429691cbb182824381460201c002840340c00c0f000405118584,
mkSt [w1,w2,w7,w0,w9,w8,w4] 0x201b045f455ad8040916121408d34610040e03420a0783074642c241460a4041c0c3448400045814000c06405958805,
mkSt [w37,w1,w2,w67,w0,w9,w4] 0x12054680f1c3468198405048934400070e303054642c34243814a4081c787448000c40301846046950902,
mkSt [w37,w1,w2,w7,w0,w9,w4] 0x1125c78031e3468eda30581c2144880990305030642c241838a4041c78587448004034140c4600f006550903,
mkSt [w37,w1,w2,w0,w55,w9,w4] 0x11a03c58e96306cc16245090e14400101c3030542c646c38702804a4783c480014400c240f046d50882,
mkSt [w463,w1,w2,w0,w3,w9,w4] 0xf30e0000071cd00c2ca007080a4802505458603008e4742438141c40002c1843840110782,
mkSt [w1,w464,w2,w0,w3,w9,w4] 0x1e3802c1a3058b14244008089b844c0d12140054786c28384818306004002c40241447043c10805518784,
mkSt [w465,w1,w2,w0,w3,w9,w4] 0xe0d1cc9e61a29c52ca1c6240e071a50346c04e42c782438a4402814004742f442510683,
mkSt [w1,w61,w19,w0,w3,w9,w4] 0x340fee140cc33828322c00692070c60286c2c7c14a420401c0c24e438180022847409d10783,
mkSt [w66,w1,w61,w0,w3,w9,w4] 0xf1e443900e3c04e0e1468c0e38508101c3050586c541420e40c2c40382460a4307800284482f550882,
mkSt [w1,w61,w2,w67,w0,w3,w4] 0x3e830a0003d3bf203530a100401ad4811366c38306c14a440e41c0c002c0f02284680d418c47c43918587,
mkSt [w1,w61,w2,w0,w3,w55,w4] 0x199009520758cf9a78505467c024498083e7c3854342814a440e41c0c00242080f011c22848047446d18607,
mkSt [w1,w466,w2,w0,w3,w9,w4] 0x1156845678eb06a359c30695c05580121c18405428382c4024001841c0384844004102c518406,
mkSt [w1,w2,w467,w0,w3,w9,w4] 0xb968417546d806969bb7ad6805580120c20d0306c481838142c400c002448809c49042447048d18586,
mkSt [w36,w1,w19,w0,w3,w9,w4] 0xd54c9708b441c3a00770d180c160052038203428306c5004401c7c2c4814600024e438180c48809c3fd50983,
mkSt [w36,w1,w2,w67,w0,w3,w4] 0xe0c10804684478c264478204a088f0180502024382c406c140030640847c0d418c41d18504,
mkSt [w36,w1,w2,w0,w3,w55,w4] 0x14183110a144098f161022f16180601e2c40402c38544034241400042848011c20848918504,
mkSt [w36,w1,w19,w0,w3,w4] 0x6cd980060b0911bba6b21c90aec2c646c1018140028480438243414448849409c00918685,
mkSt [w36,w1,w2,w14,w0,w3,w4] 0xbb4c2ea2440c20081651e51030801858308c503428101c14002c40240449849c0d910683,
mkSt [w36,w1,w2,w7,w0,w3,w4] 0x9048829c4a2002832648e4059800184038401400040f04a011c4880d441c05cd8287,
mkSt [w36,w1,w2,w0,w23,w3,w4] 0xc2ca182a670c01881289041c30061448a030643ca42c2414004028044a449c12510603,
mkSt [w19,w2,w33,w0,w3,w9,w4] 0xf360018c3021756304c750190006e803200a07828e41c7c14106c70004840244242283fc08518684,
mkSt [w2,w33,w0,w3,w9,w4] 0xfdfc017e2160fc987960bcb4a140bc6c742ce41c7028180cfc501448100040242100540041203fc42022958887,
mkSt [w160,w1,w2,w0,w3,w9,w4] 0x1b0e70000006a218145ba120042000003058002c343048a404e40c7424141c40180044c4ac18c40118784,
mkSt [w1,w19,w2,w0,w9,w115,w4] 0x1d26001902064b72a150072a13860a1008300078287c4830646c602c40041400244240983fc4b118704,
mkSt [w91,w1,w19,w2,w0,w9,w4] 0x190a58e98ede8c76e842904952088e182b0028287c54646c38042c34741400e424404243fc47009d18784,
mkSt [w91,w1,w2,w0,w9,w4] 0x38123e38081a30814e28a1419a214d46c5414a41c0c74402c2818240038640304b41080544243fc47009d20788,
mkSt [w1,w19,w2,w0,w3,w208,w4] 0x1a7706c162e6b921c500721c282c8080d204034287c143064406c2460041c100042418c4944700f43fd18706,
mkSt [w172,w1,w19,w2,w0,w3,w4] 0xd21c006c8538642819b608091208a90030048285464342400106c4244883fc09d18404,
mkSt [w172,w1,w2,w0,w3,w9,w4] 0x93002c72c410a1c90255c2240d5708607828482c302400403854146c3fc48c47110603,
mkSt [w172,w1,w2,w0,w3,w4] 0x2d6b812e0b0f4cc9835404e8ae464182c24140028405410386c0d448818c09c3fc47118606,
mkSt [w1,w19,w2,w7,w0,w3,w9] 0x1c034826ef425ca80a2b54a14d8a1204146aac3424483804401c500c3018e42c003c818c22842403042918706,
mkSt [w1,w19,w2,w0,w3,w55,w9] 0xbc0b4d04038434619634c2c2a4d1c60342c6c3804a4401c0c547c14e4002441409d10782,
mkSt [w1,w199,w2,w0,w3,w9,w4] 0xd584c00007288b0060000280074c1600360060485474281418a40440e40c1c002282084ac40118704,
mkSt [w1,w468,w2,w0,w3,w9,w4] 0x3db26458b5c18f0358b32928398586c48302c78281420e41c0c0054402438a444940901,
mkSt [w78,w1,w2,w0,w3,w9,w4] 0x1c346078c143a0161950910061a74002314068542c5908a404e4306c24140c40004bc4983fc4b918704,
mkSt [w265,w1,w2,w0,w3,w9,w4] 0xd0cc227188c0b1f8289064e30820144854581408e4306c24180c2c40003fc4c44b910683,
mkSt [w1,w2,w469,w0,w3,w9,w4] 0x2422000c08201e01001c1a1a181602d4120450000203078742c24384818a4041c0c6c54280040144c82280541ad58904,
mkSt [w470,w1,w2,w0,w3,w9,w4] 0x125f08708c2b544b423c160428a0000025684341804e430786c282438a44014004cc4244d44d118704,
mkSt [w1,w2,w67,w7,w3,w9,w4] 0x1ef03618e830c01ac12ca0a81c60bb0642874483814a408406c1c0ce4001843c4cc14110783,
mkSt [w1,w2,w67,w0,w3,w55,w4] 0x1829520012800014641286e08341428c0812602c744024604814a41c0818004304ac4cc4dd18604,
mkSt [w2,w7,w0,w11,w3,w9,w4] 0x133600232b003956805094000404881c38148878e4742c2024480c18384000144244e44001c518684,
mkSt [w2,w0,w11,w3,w9,w4] 0x1e7241cdd98da2516151f26c282821478a4e4741c30384814282c200c240040184f04241c40544e411c0d44e840120889,
mkSt [w43,w1,w2,w0,w3,w9,w4] 0xfcbe07cb8b3bb76d98f910071b7c00037406c2c3438a404e4302824140c40004f84f411c0d43fc0540f118687,
mkSt [w1,w2,w7,w0,w9,w62,w4] 0x12e80098ad03076a84581005427ac1422002074583c1838a440041c0c00144245000304004fd18605,
mkSt [w44,w1,w2,w7,w0,w9,w4] 0x1f411ee01edc195802d8d75412c80a810e0cc00a0682c58241838a4041c783474140040e4484245044004c814158805,
mkSt [w44,w1,w2,w0,w9,w4] 0x2208201e1e1c18c116d4d301910d0b0546c382818a41c0c78743040002c5848241ac4480544c842440158886,
mkSt [w1,w2,w7,w0,w3,w179,w4] 0x16ae80816d60076a41521009321aa10224460342c58402448183804200c140050c5084c840000d18685,
mkSt [w96,w1,w2,w7,w0,w3,w4] 0x90330332051c10440c20850364309424406c4834140058203851014040110483,
mkSt [w96,w1,w2,w0,w3,w9,w4] 0x514014820618d30b0296860c0e5818404818a41c402824145400306c384005144c910683,
mkSt [w96,w1,w2,w0,w3,w4] 0x673b757d8aafc93d94b6d474ce85440180c28004830146c20385180085104000044c814118607,
mkSt [w1,w2,w7,w0,w3,w55,w9] 0xe4030108f140051c286811728482ce0a28a034783074246048183804a4401c540ce400144144dc14150903,
mkSt [w92,w1,w2,w0,w3,w9,w4] 0x900b14a009c00178020943dd0005d03c346c54a4304028140c24004a43fc05451d10584,
mkSt [w266,w1,w2,w0,w3,w9,w4] 0xa28c1ab08ac091b1a07184c00826d448346c547004e428140c4024003fc52451d10603,
mkSt [w471,w1,w2,w0,w3,w9,w4] 0x11203c000003870d003058a0034040901c30503078343848a404e40c7428141c544000184dc40150882,
mkSt [w1,w2,w194,w7,w0,w3,w4] 0x118343071c306800003680ed8282c9cd951020406048140c08042003052c06011c5280d405d18407,
mkSt [w1,w12,w2,w472,w0,w3,w4] 0x3fe727b25b726c2a25de1c303c60542848342004245c182c400854500781]
set_option maxHeartbeats 0 in
noncomputable def p13_D6p3 : List StD := [
mkSt [w41,w1,w12,w2,w0,w114,w4] 0x924704f38d02c2c928728a2481c618506018542848042c583c34005c08243054454910782,
mkSt [w41,w1,w158,w2,w0,w3,w4] 0x2cb6085d8d00c2ca276e000b7185c040546c382cdc043428480040302455001c54910683,
mkSt [w159,w41,w1,w2,w0,w3,w4] 0x80872202880e02481c61400020000dc342814002c4004602455855510502,
mkSt [w41,w1,w12,w2,w7,w3,w4] 0xe812a9629623448c143b14244074c150a4460dc20180430343c2800406022854c03055d18584,
mkSt [w41,w1,w2,w197,w0,w3,w4] 0x1c72801c01818002438060081c0185030dc346c48004004281457055510502,
mkSt [w41,w1,w2,w7,w0,w8,w4] 0xd3140042cac0a0b820920800718000507830246008205834004064480406406003110683,
mkSt [w1,w19,w2,w473,w0,w3,w4] 0x260f725664adac4ac0a3a4e741c28745048306c606420102c7c1424400457d40801,
mkSt [w160,w41,w1,w2,w0,w3,w4] 0x90002670892800e92001c60001420000dc30344800244004142c58455d10502,
mkSt [w41,w1,w19,w2,w0,w115,w4] 0x91c738404d02c2c928728a2481c618507c306c6010503424640048042c2857c54910702,
mkSt [w41,w1,w19,w2,w7,w0,w3] 0xcd503158962244881d8854244070cd50a446018dc2014103428503000404822809855055518604,
mkSt [w41,w1,w199,w2,w0,w3,w4] 0x820032600800b00aa401802070060050602810dc543448004004301459455d10602,
mkSt [w1,w2,w7,w0,w474,w3,w4] 0x6036836b0b1a02872470679060e38e7028503c48183858080420401459c55c59910603,
mkSt [w43,w41,w1,w2,w0,w3,w4] 0x596714004a24a885a07006160044080010dc342400301440042801c5a054910503,
mkSt [w41,w1,w2,w7,w0,w62,w4] 0x10258a00a443402203b70e1c2056c1428406074503c38203458480004145a455459855d18584,
mkSt [w1,w2,w157,w14,w0,w3,w4] 0x12f04c09628189040018904003816811ab1620303428403814101c042c24001805b40100d918604,
mkSt [w45,w1,w2,w157,w0,w3,w4] 0x42c4c220c21250b2010307020a20e180350703028d81434243860042c005b40301045b918584,
mkSt [w113,w1,w16,w2,w0,w3,w4] 0xa08028b00a240207900106080140000014303448100c2404402c005d030d10582,
mkSt [w113,w1,w2,w0,w3,w8,w4] 0x1099d0800dc4290610421840814840dc28404040142c346424486004005dc5d85d431518504,
mkSt [w27,w113,w1,w2,w0,w3,w4] 0x2e000f9001d00108007004c360051000442c243414044840005e45e031910483,
mkSt [w37,w113,w1,w2,w0,w3,w4] 0x3e000b9001d00108007001c360051000442c244048003414045ec5e832910483,
mkSt [w1,w12,w2,w0,w3,w195,w4] 0x20404b74284c81022040001828266cc14366c30246018582814a404002c18015c09803918584,
mkSt [w17,w1,w2,w0,w3,w195,w4] 0x44968c011e1094e2a100908e40200dc284070343028d41804586424141c2c005fc00c4445f918684,
mkSt [w39,w1,w12,w2,w7,w3] 0x2c69cea60e0260cce8ca1c4cc44218c3c183400581028302404602285c862006409803008861c6244412058a,
mkSt [w39,w1,w16,w0,w8,w4] 0x15a334dc54615abd7a15aa846002818440c383c6034142422861401064c64918505,
mkSt [w39,w1,w16,w2,w7,w0,w3] 0xc840ec9eca27020c16616584492b12304038342848051c0c30102c5801031034510603,
mkSt [w65,w39,w2,w0,w3,w4] 0x51a32162cb813460b8922448800643c602c34044828140020244022862866c66918684,
mkSt [w39,w1,w2,w7,w0,w3,w8] 0x1803c25abac503a896889129448690d9004640402414006434302c6048100462006006408835066005918607,
mkSt [w27,w39,w1,w2,w7,w0,w3] 0x1ccd68c04dea856f541a468c9509111c3050004024451c1034282c14003058600422862031c32408918705,
mkSt [w37,w39,w1,w2,w7,w0,w3] 0x6def0d18c92816f541a468c9509111c3050002444191c1040282c48043064380001c62032c33408918705,
mkSt [w39,w1,w2,w14,w7,w3] 0x12825231ec6a20d0e620c450c21c58c406c481c003010282438046401c5c862006001000c0886806841b92060a,
mkSt [w1,w2,w21,w0,w3,w114,w4] 0x1c7b286dba00019a134e400471c6144040305c34042400183c602c0cc03040d10583,
mkSt [w82,w1,w2,w21,w0,w3,w4] 0x8e3420ac961b6c530022412370801b003400304060043c2c24140d00cc41110503,
mkSt [w144,w1,w12,w2,w0,w3,w4] 0x7dc1cabeca8092071712c59f60500008185428142c3404005c302403803469910583,
mkSt [w1,w2,w169,w21,w0,w3,w4] 0x13a750911891d70082201c3910234a093000883c3058340804142c24600d06940cc0d40a400518506,
mkSt [w1,w2,w21,w0,w3,w206,w4] 0x589d8a015050088e1a800ac409260244360ac583034243c001440042c606940d40d00cc41813918586,
mkSt [w144,w1,w2,w21,w0,w3,w4] 0xf1c2c71314b848810b830a012078c1483426058602c3424140418300cc0d003469918484,
mkSt [w269,w1,w2,w21,w0,w3,w4] 0x8a232050881a68282c32462270801a0034040830586040143c242c0d00cd10582,
mkSt [w1,w2,w475,w21,w0,w3,w4] 0x38180d20c2e800024596a809207005050582c7870342400046030143c400e469510702,
mkSt [w270,w1,w2,w21,w0,w3,w4] 0x2888061438838e02050091c69400e002c044030583c146034240e401110502,
mkSt [w1,w2,w21,w7,w3,w4] 0x4eacf67477ad982564b952500c82c30583c1404242860405986940d422806461c28918507,
mkSt [w1,w2,w21,w0,w23,w3,w4] 0xf640510ed4450801493244890080e00284060302c4004240014603c6940f00e40d069d18485,
mkSt [w71,w1,w2,w21,w0,w3,w4] 0x132a2a1a0d49c3494c9490a201870c150344405040002c5824701404300e46940980cc6a118505,
mkSt [w1,w2,w311,w0,w3,w4] 0x2d1b11e8406f5a13003562304683c3060402414382c0100540d40040a518405,
mkSt [w2,w311,w0,w3,w4] 0x39521d4970923b14a42c583c601838304024140100540d400518504,
mkSt [w476,w1,w2,w0,w3] 0x79109c476c960b54a4342838304024142c0540d400411d18404,
mkSt [w267,w1,w12,w2,w0,w3,w4] 0x924724634c20b0212020ca2485c600505c54280830403c60003418242c2a040d10682,
mkSt [w1,w205,w12,w2,w0,w3,w4] 0x140acd772d73b970033812d81802021828006078346c54241800042c406b44004183fc0cc41118506,
mkSt [w1,w205,w2,w0,w3,w4] 0x6edd95f5aab380457078d1d7208303c60182c2414a41c000c54380986b43fc6bc05441118686,
mkSt [w1,w2,w95,w0,w3,w4] 0x352b102be08d550c0094c9404a8283430142c4024480f011c0d40540040b118406,
mkSt [w2,w95,w0,w3,w4] 0x332eacecaa7740743000286018484004342c241411c0d400510603,
mkSt [w1,w2,w0,w477,w4] 0x48509c4162a23b64a4304028482c34241411c0f00d400518404,
mkSt [w478,w1,w2,w0,w4] 0x38f09cc86e9a2b54a430283858342c24144011c0d400405518484,
mkSt [w1,w12,w60,w3,w4] 0xaa7649584e86a952a8303c38141004541828006e84406e40d422918505,
mkSt [w1,w12,w2,w7,w23,w3] 0x6921543cc3042460b62a4961045440a43c28301834002404606103ec4406ec6f420118606,
mkSt [w1,w12,w2,w0,w3,w35,w4] 0x25500109659b0928ed0012a03810c142030005c5434281400402418a42c6f800843020869d18585,
mkSt [w1,w2,w0,w3,w272,w4] 0x53560c1c198cc214274dc4c82cc102c4024041834543c60000300100006fd18584,
mkSt [w1,w164,w12,w2,w0,w3,w4] 0x2a5aa468920c0701c0962a910310c1420304030281440241810002c1807000cc6a118484,
mkSt [w1,w83,w2,w0,w23,w3,w4] 0x1320046730a24960d903960d8a118e0430406034302024601400281c0f427048070518484,
mkSt [w71,w1,w83,w2,w0,w3,w4] 0xc1670001c00072c61872ca2481c00060d060002c582420303428141c70c2ad10602,
mkSt [w1,w2,w479,w0,w3,w4] 0x1dcb2ee84a6b6653589512304b0282c244018a40c1400506c3809822873005472d18605,
mkSt [w17,w1,w2,w0,w3,w35,w4] 0xe56b1b836a3a06ca23890c0a40740d92030406c4000182c74342414a4284306f800c48070518585,
mkSt [w17,w1,w164,w2,w0,w3,w4] 0x6eaa98824661a8b62030b7180144003c28d440002c24142018105687402ad10503,
mkSt [w1,w16,w57,w0,w8,w4] 0x275e367a18afd9ad007d18d0400503c310828140c2c2401075000c74c22800405118487,
mkSt [w1,w57,w0,w8,w4] 0x7b62ac87b019bd66102818503c140c3034602c2422800405075074d18585]
set_option maxHeartbeats 0 in
noncomputable def p13_D6p4 : List StD := [
mkSt [w1,w2,w274,w57,w0,w3,w4] 0x3a0ec3810b5008249088394c5a0507424183040000c142c58380d473108602,
mkSt [w275,w1,w2,w57,w0,w3,w4] 0x1ec61c14e961e4261d814024180c50583c1428382c400d400d00582,
mkSt [w1,w2,w276,w57,w0,w3,w4] 0x41ce04316a380834912541cc5a03c2c78704028000c1458243811c74908602,
mkSt [w277,w1,w2,w57,w0,w3,w4] 0xa941950e9219421d9410028180c50583c1438402411c01100502,
mkSt [w1,w2,w57,w7,w0,w3,w4] 0x4c3482e031511046d0c9866b42aa206058180c0014403811c0d4748730390d8385,
mkSt [w1,w16,w0,w8,w4] 0xc770e429711cbb182838241444602004002818340c38000800405118604,
mkSt [w1,w2,w312,w0,w3,w4] 0x4d1a902848655e4300b520b0468502834182c4014382411c05400c00410918485,
mkSt [w2,w312,w0,w3,w4] 0xa9109d4970963b24a45034244818382c40281411c05400c00518504,
mkSt [w480,w1,w2,w3,w4] 0x88d1dc476c862b54a4303438282c40142411c0540040d518404,
mkSt [w73,w1,w2,w0,w3,w4] 0x3488ac0000031c8b14d002b00842804503c002c240c01000c00422918404,
mkSt [w73,w1,w2,w0,w4] 0x880000c1689e33008428503c440c2c240001000c00422918404,
mkSt [w73,w1,w0,w3,w4] 0xf0430a2b402a8428503c002c240c09822803001cd8384,
mkSt [w73,w1,w16,w0,w8,w4] 0x1c884a6008831c8a14d002a0084302820503c002c240c01077800c22918484,
mkSt [w73,w1,w16,w0,w4] 0x9b565ad3709eb30880302908503c2c1424000c01000800c00477d18505,
mkSt [w73,w1,w0,w8,w4] 0xd982e24a85240580f044284c20343c0030502c600c2400422877878478118685,
mkSt [w1,w16,w72,w0,w8,w4] 0x59aa16405014e1bd7a4588d528c1830504c6020040c342c0038026400c78822918585,
mkSt [w1,w16,w7,w0,w8,w4] 0x1409240400871c313231409508418384460200c34140064805c38800d18484,
mkSt [w1,w16,w0,w103,w8,w4] 0x500166e1b07699d8635cb1228c183c4428602010040c34240064829c01079c22918605,
mkSt [w1,w16,w2,w0,w11,w3,w4] 0x14c02da4a84d200121d2900203860a10083000303428482c40001420240f00084e81d039118505,
mkSt [w1,w2,w7,w0,w85,w3,w4] 0x3038033c00e008020c61f6044141d440581838200440140039828865910403,
mkSt [w1,w2,w0,w85,w3,w4] 0x460719946048cf23a72a33c628c1830400c28041458380003028800000c65839918506,
mkSt [w65,w1,w2,w7,w0,w3,w4] 0x945882985560c90a200285858000162018204048140006066811c0d43a8064d8306,
mkSt [w1,w2,w280,w0,w3,w8,w4] 0x634603042c50092201870c080030a1010108030402850343c144820042c24007b87b400406518684,
mkSt [w281,w1,w2,w0,w3,w8,w4] 0x121e066ca023b061013a44040a9002082004c4014202c64342428604810007bc3500c07c118604,
mkSt [w1,w2,w72,w7,w3,w8,w4] 0x255806c1a52070c02a70818031460a182020402834641824486020040014039c7bc05d18584,
mkSt [w1,w2,w72,w0,w3,w103,w4] 0x14214200120000105c122500811148cc083860303440286048100418003585d87bc7c518504,
mkSt [w1,w2,w0,w481,w3,w4] 0x46ad34b05005a03d0a794820a64306440602404481c2c140f41387cc7c80d413518506,
mkSt [w1,w2,w0,w11,w3,w8,w4] 0xe9dc87201aa0448d0ba80002227040828404040142c34002448202805400406006405918485,
mkSt [w1,w7,w0,w60,w3,w8,w4] 0xb7d003ab40ea8b202a00061541041248644838346c20003500307d431400cd8385,
mkSt [w43,w1,w7,w0,w3,w8,w4] 0x132a030721403900203c704083838c15a0044c6438242014344860040035000c05c31518504,
mkSt [w43,w1,w0,w3,w8,w4] 0x30d012c58b183020b132a3c1910642024146004482c38340030280043503145a118684,
mkSt [w1,w2,w7,w0,w8,w62,w4] 0x126820802503072a02d70c11003a40c123440583c341460482004003507dc03031400d18485,
mkSt [w44,w1,w2,w7,w0,w8,w4] 0x150000014a444000003c7001d1048c150330405824602040346448000435014031403118504,
mkSt [w44,w1,w2,w0,w8,w4] 0x30b163404b1830584132a0c7910602024406400342c584804302805435031429518684,
mkSt [w1,w2,w7,w0,w3,w482,w4] 0x128680800d58014a43080c0932502d0225480406450583c14603820043448007e01c43147b918684,
mkSt [w104,w1,w2,w7,w0,w3,w4] 0x90330332050c208410104703643089403424044048005838207b805c31510483,
mkSt [w104,w1,w2,w0,w3,w8,w4] 0xe2848704203860a082010810087210c1100806458282c3848003424203147b400405d18504,
mkSt [w104,w1,w2,w0,w3,w4] 0x406cb9c165d2102ea01a0367080042c34482824005838207b83141405a029406518506,
mkSt [w1,w2,w7,w0,w3,w103,w8] 0x1345c018e9a852aa44008019a8308090b302040303464241448602c1020040065c7c414005d18684,
mkSt [w282,w1,w2,w0,w3,w8,w4] 0xb9ca2c0dcba441482230c1ae0dc614302c401420342448600464007c417831510583,
mkSt [w1,w2,w0,w3,w483,w4] 0x40af46b162152c0621402c38702c4034241048a414281441487ec7e818118485,
mkSt [w1,w135,w2,w7,w0,w3,w4] 0x541450124014d50a10e01c44100d0554419141008058181008041448004000c11c2287f87f40d406016920488,
mkSt [w1,w2,w7,w0,w138,w3,w4] 0x9029c2383a270206186de6d4410197402854586c6038200440480031881828910583,
mkSt [w1,w2,w0,w138,w3,w4] 0x250071ac90b15c91723502812a46c306028044058380081c31882006000d18485,
mkSt [w27,w1,w2,w0,w11,w3,w4] 0x1cc01a611884652a26201c181404081dd000c18c0804448282c4000341420240541d011c0d400882806082416920509,
mkSt [w27,w1,w7,w0,w60,w3,w4] 0x14c2500943058a00a4433060c4046c142040604854586c203034143804400082c32428831918604,
mkSt [w27,w1,w0,w60,w3,w4] 0x600b662c55b46cb92ad404d8af4304010146c0438605854002800c31882032422918605,
mkSt [w1,w198,w2,w7,w0,w3,w4] 0x194159011a014558a11001d84100c44d580d0c0408018a4401c3800041403011c01c8346b40d40644a120408,
mkSt [w1,w2,w7,w0,w143,w3,w4] 0xa02ac22c3b2b0246286de6d4410197402850583c441838200414340032884c05d10603,
mkSt [w1,w2,w0,w143,w3,w4] 0x2e095134c0c5aa1d743863014c05864443c0434283814008503280307d884c06518506,
mkSt [w37,w1,w2,w0,w11,w3,w4] 0x29002a6524045ce25604dc081804141dd000c18c0803428442c0014404820244e800411c0d40f08580648544a120509,
mkSt [w37,w1,w2,w7,w0,w62,w4] 0x10260b00a84b9122443302201856c1428406034503c38203040584800140485c33459832918604,
mkSt [w37,w1,w2,w0,w62,w4] 0x58bb70598b45cbd52d66c500f464303410403c005814385004280303287d833401d18685,
mkSt [w1,w2,w33,w0,w3,w115,w4] 0x3cfa1c1c734001c9134dc00c61811440347c64281000142c48241180984b110503,
mkSt [w91,w1,w2,w33,w0,w3,w4] 0x41f7cdbdc1dba0530022410c81f01b0064700034284810502c241412011847110583,
mkSt [w128,w1,w19,w2,w0,w3,w4] 0x7d45ec2c6a009a071350849d617000087c306c602c40241000142809c03486510583,
mkSt [w1,w2,w484,w33,w0,w3,w4] 0x1b8024800936c005a00163a4800700503c742470182c34001048281450400e886110702,
mkSt [w287,w1,w2,w33,w0,w3,w4] 0x1ac01c60039838e71800081c69400e002470181050342814482c400e800d10582,
mkSt [w1,w2,w171,w33,w0,w3,w4] 0x182b56337a805905018e1ce108030a083000805034284070180410142c244812011c8601180044a918606,
mkSt [w1,w2,w33,w0,w3,w208,w4] 0x18c5870345d3086dc2000adc21a60200b60ac342c50642800144840102411c86012011849414518586,
mkSt [w128,w1,w2,w33,w0,w3,w4] 0xd1024633104028808b0308011062a120322603470482c402410142811812003486518484,
mkSt [w289,w1,w2,w33,w0,w3,w4] 0x31e78851c49a70232c72460881e01a00706410043428484014502c2412011910602,
mkSt [w1,w2,w33,w14,w0,w3,w4] 0xe9a3cb0128097a10012264890010e18004060502870184024100014482c0f08601200e886918585,
mkSt [w45,w1,w2,w33,w0,w3,w4] 0xeae4c720c69d3470cb8905201874c140344403c7040002c3424141810280e886003011886d18585]
set_option maxHeartbeats 0 in
noncomputable def p13_D6p5 : List StD := [
mkSt [w1,w2,w33,w7,w0,w3] 0x4e8b7abce8ac1f2564a972500c8243428501814102c30484059886011c2280643d028918587,
mkSt [w286,w1,w19,w2,w0,w3,w4] 0x91c73861cd2cc0222c10ca2485c600507c306c4004503428480064142c248744b110702,
mkSt [w1,w207,w19,w2,w0,w3,w4] 0x1146d04d0ddc886ec33652e018060a042000402854646c2c40140004248344244943fc11847118506,
mkSt [w1,w207,w2,w0,w3,w4] 0x66bd75f528b380457078d1d72084028482c2414a41c000c6c388340303fc88005447118606,
mkSt [w1,w19,w2,w0,w34,w3,w4] 0x12da8010a849d94121d0940203860a100830007c30646c382c4000141c248880084ac18c86918585,
mkSt [w1,w2,w0,w292,w3,w4] 0x59b21022c7a71a053b668484ad0182c4010246c1464044850003c80f400c26400088d18606,
mkSt [w1,w19,w2,w14,w7,w3] 0x510c1546179063040b628cc61046c40501c30281464002410483c467c3c88988941b918606,
mkSt [w1,w162,w19,w2,w0,w3,w4] 0xca58a48892400631c32522510360a042030402830382c40140400240f455011886d18484,
mkSt [w1,w19,w0,w60,w3] 0xb354eba84f54a91aa8482814603004106c1838008a03c889c11c22918585,
mkSt [w1,w137,w2,w14,w0,w3,w4] 0xee9bc192200a74c818974c81a110e181840403034284024481420002c1808ac47c8a918504,
mkSt [w45,w1,w137,w2,w0,w3,w4] 0x496c2400090002c91062ca2481c00060d848002c342420284030a4148b028110602,
mkSt [w1,w2,w485,w0,w3,w4] 0x4bca56d84ab6e645588d12504b0282c2440181c0c1400543c380302287480548c118605,
mkSt [w66,w1,w2,w0,w34,w3,w4] 0x1506b1b8d54c4640d514612144070c81aa3040547400142c78246c381c304ac88801047c8a918585,
mkSt [w66,w1,w162,w2,w0,w3,w4] 0xe82e48080e124f42020f7180085004c286840002c382014240458c8c828110503,
mkSt [w1,w2,w0,w34,w46,w3,w4] 0xa073e8000a246d91cf8006c431071840308c140024481c406c2c47c00c19d10503,
mkSt [w78,w1,w2,w0,w34,w3,w4] 0x72002228589ea1830890402278061400480030646c141c2c402447c18c0a910503,
mkSt [w139,w1,w2,w14,w0,w3,w4] 0x71eb2a9207c73c07043165df140018088c5034282c141c042430400d88d48d110583,
mkSt [w1,w165,w2,w0,w34,w3,w4] 0x122812ac585569d19c1d0410130344940a40003064386c14001c2c402418c88847c4601900d518506,
mkSt [w1,w2,w0,w34,w177,w3,w4] 0x120303a1242d31601c909161038212004070a038304004246c48141c2c6488818c1648d80d447d18586,
mkSt [w293,w1,w2,w0,w34,w3,w4] 0x82002040c81c50c81cb0ca207022180000481c30643814406c242c47c18d10582,
mkSt [w139,w1,w2,w0,w34,w3,w4] 0xc181161214b42911630200941868441a9406074386c2c24141c403047c18c8d48d118484,
mkSt [w1,w2,w7,w34,w3,w4] 0x1eac76f277f5a02872d9a804ad42c3048646c1c282440143801c8888dc2880605980d518587,
mkSt [w1,w2,w0,w486,w34,w3,w4] 0x3b8d80c0e82001072aa80324020702c785474700024381c3040646c144ac88910702,
mkSt [w294,w1,w2,w0,w34,w3,w4] 0x6a800001840001800041c680512002c741c30642438406c144ac0f510502,
mkSt [w209,w1,w2,w14,w0,w3,w4] 0x924d300ac91470c11022832481c00d608c50280030646c04484014242c58419d10682,
mkSt [w1,w210,w2,w14,w0,w3,w4] 0x1189bc86128481c2c5c00c0c02120e158040603c705040080414002c480241647f410047c0a918506,
mkSt [w1,w210,w2,w0,w3,w4] 0x6361d7630ad6a25e1400e14514c8083064182c58243c100c0804504001047c1007f48e40240040a920688,
mkSt [w1,w2,w0,w94,w3,w4] 0x450a10eb40115e2e6494a0234a4303428142c24403800811c0540040d41ad18406,
mkSt [w2,w0,w94,w3,w4] 0x17ae67c076b9a0742c40142404303438002811c0540d510503,
mkSt [w1,w0,w487,w3,w4] 0x8850d8c562a23b64a4303414282c40382411c0540080d518404,
mkSt [w488,w1,w0,w3,w4] 0xa8521d4970963b14a43034284818382c40241411c0540d400518504,
mkSt [w1,w2,w14,w62,w4] 0xca56d5593086a964a4403430643c101c045024280090c1b89080d401d18605,
mkSt [w1,w2,w489,w0,w3,w4] 0x5ecd2ef5597192c30ab9aab04a8282c582418100c0838503c6401001c12c73000491d18606,
mkSt [w1,w2,w0,w11,w60,w3,w4] 0x111f0d0cc0106601811c1a00e9828288002040582c34242838204092c06411c00c1d80d518406,
mkSt [w43,w1,w2,w0,w11,w3,w4] 0x8117231c98dfacc4049080237c0218003800303414202c2824401d00640b510503,
mkSt [w141,w1,w2,w7,w0,w3,w4] 0x12c2a2a12a03b58c8213502891400b000030082c58246048403414200493c05c9388d493518505,
mkSt [w1,w2,w0,w11,w3,w62,w4] 0x1156000a097050aa011c1c39808284080020282c2448582838201406094411c0304fc0d518406,
mkSt [w44,w1,w2,w0,w11,w3,w4] 0x8d1ae330981b60f40090812370021b005800303448202c2824144e80604c910503,
mkSt [w145,w1,w2,w7,w0,w3,w4] 0x14c2ca8011c334869913284892000a0000480864342c2438401448200095414095094c94918505,
mkSt [w1,w166,w2,w0,w11,w3,w4] 0x140d48aa349559b15c02101013034294124000303448281400202c24401d006495c9580d518505,
mkSt [w1,w2,w0,w11,w178,w3,w4] 0x28180a30022a16000501160c30a0200386080482c3034042428381420401d096496006518584,
mkSt [w298,w1,w2,w0,w11,w3,w4] 0x80272218889e50c81cb0ca2278021800003820303448142c2824401d006510582,
mkSt [w141,w1,w2,w0,w11,w3,w4] 0x1218a860a08b45910a30500881862b019140605848282c40142024340641d08d493518484,
mkSt [w1,w2,w0,w173,w11,w3,w4] 0x175d55052025d50a81208b0042d74618005428303440482c0424382028144e806096c9680d518585,
mkSt [w1,w2,w0,w11,w3,w179,w4] 0x906004111980088008102ec30a602038662c34482c3058002438402820144e806097050d18604,
mkSt [w145,w1,w2,w0,w11,w3,w4] 0xd18d460508c04881c30300882062a01914860342838182c40142024480604e894c94918504,
mkSt [w300,w1,w2,w0,w11,w3,w4] 0x80052041081861082c9106207022180058200430344840282c24140604e910582,
mkSt [w295,w1,w2,w7,w0,w3,w4] 0x155e33054e425606d1c511100187ac160032405824a4303428381404402749782683101d918505,
mkSt [w1,w2,w0,w60,w3,w62,w4] 0x1396808c1178600a031508a00104a60c18306054503c2858100438000f098011c00803000c0d518487,
mkSt [w44,w1,w2,w0,w60,w3,w4] 0x1532d5874d29caa0cdcc2a405907ac000300542c245810543034286c38000482011c0d400800d18605,
mkSt [w301,w1,w2,w7,w0,w3,w4] 0x1502c88001c244661034264181008a0000424c7874503c20343848040098432414081831918505,
mkSt [w1,w175,w2,w7,w0,w3,w4] 0x118243090c29e906cd86800c0217c2158040403458100804143800400c498c9881000640b518486,
mkSt [w1,w2,w7,w0,w3,w302,w4] 0x16ed008021480001c2d54a112a3a60812344064402c34246038482004003509947b831414118585,
mkSt [w43,w1,w2,w0,w3,w62,w4] 0x16da847691a3ba74ea4d20405937600004304c2c3810503058283c14040011c0d47d80f003118585,
mkSt [w43,w44,w1,w2,w0,w3,w4] 0x59441401081a60855c4006960103080010340030281404247b85a029510403,
mkSt [w1,w175,w2,w0,w3,w4] 0x2a05656e2cad6a15a5400e1c594c808182c24100c08345804503c98c0c40f09881000540040b520588,
mkSt [w296,w1,w2,w7,w0,w3,w4] 0x155653054e41d802cdbd60f00085ac52003040582448104030283800145549a055c3384fd18505,
mkSt [w303,w1,w2,w7,w0,w3,w4] 0x1502d2b14a444a0c802c20295100888000304050583c68441420403800049a833484c32805d18585,
mkSt [w1,w2,w0,w23,w62] 0xbd4cb498ced4b616a46440343028a4042c503c0011c5989ac9b020001d18586,
mkSt [w1,w176,w2,w7,w0,w3,w4] 0x158253094c28e902c586620c0407cc15808040584814a4401c0c0004384249b89b44000604c918506,
mkSt [w1,w2,w304,w7,w0,w3,w4] 0xf02ba90ea004740003470a8020384091a30202c24586048142004009bc3507b831405d18485,
mkSt [w1,w176,w2,w0,w3,w4] 0x3205b1ae30a9ae0029a50e0c8d98408402c2414a41c0048380c546c9b84249b44000080040544c920608,
mkSt [w1,w2,w7,w0,w3,w35] 0x1dbc7a3a7cd624368201ebe4af42430483454a428182c40143801c6f83e428806059811d18607,
mkSt [w1,w2,w0,w3,w35,w127,w4] 0x3cd0287c06076183e401f1cc52070450a014004028a4602c342448001021510503]
set_option maxHeartbeats 0 in
noncomputable def p13_D6p6 : List StD := [
mkSt [w92,w1,w2,w0,w3,w35,w4] 0x25f75b61832b8db2247040080236d400600034402814a4542c2420848010d10503,
mkSt [w142,w1,w2,w0,w23,w3,w4] 0xb289181a27cb01b7084984dd0006d408a030643c2c2414a404402812449c9c910583,
mkSt [w1,w168,w2,w0,w3,w35,w4] 0x457298d020503d3a30508005b820c14084000483428140040a4382c2420811c4806f805420d18506,
mkSt [w1,w2,w0,w3,w35,w215,w4] 0x1a485560d88b0081048a0418209001c304060382c540440342414602811c20816c9cc6f848118506,
mkSt [w308,w1,w2,w0,w3,w35,w4] 0x21209e71c31489e32881c9080227980000143428386040542c2420848110502,
mkSt [w142,w1,w2,w0,w3,w35,w4] 0xc641150a143488516300441418620c8ac40607838342c2414a4402848020849c9c918484,
mkSt [w1,w2,w490,w0,w3,w35,w4] 0x90e3b4000900cac6984006a480c000606c7424182c00a41428403454384306f910682,
mkSt [w305,w1,w2,w0,w3,w35,w4] 0x70e3a000e19060070030041c00e5120018243c54402838342c1443003110502,
mkSt [w306,w1,w2,w0,w23,w3,w4] 0xd3009c72c51421c310a0422480070960a0303c005434280460402c142455821510682,
mkSt [w1,w214,w2,w0,w23,w3,w4] 0xfa8062a4c98d162d046060242180e0048406050242c40040814003c607f80c416c02448010d18506,
mkSt [w1,w214,w2,w0,w3,w4] 0x4fbef7392bb5e33d007d4a5340814282c505824100c0804343c7f848000c0249d400410d18607,
mkSt [w1,w2,w491,w0,w3,w4] 0x5bcd3add59d0d6e60a8deb60488282c5824180c083804503c3400c01c12c7480049ed18606]
noncomputable def p13_D6 : List StD := p13_D6p0 ++ p13_D6p1 ++ p13_D6p2 ++ p13_D6p3 ++ p13_D6p4 ++ p13_D6p5 ++ p13_D6p6
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x0 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x1 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (1*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x2 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (2*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x3 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (3*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x4 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (4*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x5 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (5*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x6 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (6*64)).take 64) = true := by decide +kernel
theorem p13_I6 : LevelN p13_R p13_T 6 p13_D6 := levelStep p13_B p13_W p13_Q p13_I5 (chunks 64 p13_D6 7 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C6x0
  · exact p13_C6x1
  · exact p13_C6x2
  · exact p13_C6x3
  · exact p13_C6x4
  · exact p13_C6x5
  · exact p13_C6x6
  ))
set_option maxHeartbeats 0 in
noncomputable def p13_D7p0 : List StD := [
mkSt [w10,w2,w6,w0,w3,w4] 0x6dcb8cada260000009b58e308103028201c1814100c082c24000401000000c00800518685,
mkSt [w1,w12,w2,w6,w0,w3,w4] 0x2e36302e2911010101000e088100c0c61c5840800483040505814100c08243c54340401002c03001c00801800401520688,
mkSt [w1,w16,w2,w6,w0,w3,w4] 0x2a0a25621d99818189400e018940c0c6104540800482c2450583c100430280c01004800800c04401c00404120508,
mkSt [w1,w6,w0,w3,w8,w4] 0x21195f5c1b0f4d07094b20c71552d102c40281834100c08002448606414300401c00804c06c06958805,
mkSt [w27,w1,w2,w6,w0,w3,w4] 0x1665d261de5940c0c0c005ca45408015c0d1420c8882850583c546c14040c01c04001007800c07400800407120489,
mkSt [w27,w1,w6,w0,w3,w4] 0x44fb13aacd18e24b0ed00540cd02850601034180c407014583004483c00404007801c07007400918787,
mkSt [w1,w19,w2,w6,w0,w3,w4] 0x302e2611292601010100010c8a00c0d85c4600800483428583c700c042c50646c1000c08c09801c00808800408520608,
mkSt [w1,w2,w32,w6,w0,w3,w4] 0x160af5d78c2d8a00c2db468c005b2e56b35a843c50582c3470100c00081404304003c01c0080b801518705,
mkSt [w1,w2,w32,w0,w3,w4] 0x224101124c81465d41010a544100044306010002c3404140f40b80540f000803c00c0d401520409,
mkSt [w155,w1,w2,w0,w3,w4] 0x672f6cbd2467e4cb345c54374c82c2460043c381c28140050580f40fc0540f00d40080f918607,
mkSt [w1,w2,w56,w6,w0,w3,w4] 0x81810eab76b00a6023d5b7400443048cd82f4503c70181020041430582c28240c00801c1100c804118705,
mkSt [w1,w2,w56,w0,w3,w4] 0x4e2c567032b19d35003952d5484301458240c202c280409803001c00805404118486,
mkSt [w1,w2,w0,w3,w102,w4] 0x484be5c0042cc1168392a40ce829319902c5828346038481410200024401804300f014c11c13c0d400804c14413960809,
mkSt [w25,w1,w2,w6,w0,w3,w4] 0xd301cbb566b52b140315865e956814e062ab02850583c18002c043024140c04000801c1580dc07118606,
mkSt [w25,w1,w2,w0,w3,w4] 0xa180615261510d21cdcca010616120583400301804282c240f011c0d40400080701580dd20488,
mkSt [w361,w1,w2,w0,w3,w4] 0x2eac7974b36fa1bb64b919b222828400c081450583c48000981740ac03017000918506,
mkSt [w1,w2,w30,w6,w0,w3,w4] 0x1b4ac80b8ed83a1202c3470c0055ae64b35a8450583c6424700c0004141028400a001c0080e008518685,
mkSt [w1,w2,w30,w0,w3,w4] 0x1012641608e411d4641011052400442864481410002404181800e00540f00080a001011c08520489,
mkSt [w362,w1,w2,w0,w3,w4] 0x76dd9975a1d5a49e351890e74c83028244810045038202c1400583c1800bc0540f000818518706,
mkSt [w1,w2,w6,w14,w0,w3,w4] 0x15b6caf180c0b18b12c25d9c2ede01cde5e2cdc0ddc305018100c081470402404642c05403c1000d40081881a418002400c01c0d92068c,
mkSt [w45,w1,w2,w6,w0,w3,w4] 0x299a2a2e69920c0d9200c8e98a010cc5812601a19d8504024140428303c18082c18003c00801c03000c1bc1c010520589,
mkSt [w1,w2,w6,w7,w0,w3,w4] 0x332b2a40af41b32eaa41d310225000cb18d648c090c3058287018100c081440043401c0a00c403003c11c0d40101000081c400c05d2060d,
mkSt [w1,w2,w6,w0,w23,w3,w4] 0x1301000715ede31282ae630809a4014f1d4d59400943c70182c0c0840340414280a00c40540f411c02400820401c1241b00112058c,
mkSt [w71,w1,w2,w6,w0,w3,w4] 0x2616259225aa52099c00ce2598c108e20105819d9983c402c701030500414240f40a000801c09801021c1b411520509,
mkSt [w363,w1,w2,w0,w3,w4] 0x673f6cfd2465e4cb247c54374c83024601c2838043c145408340102200540f00d400401518607,
mkSt [w1,w364,w2,w0,w3,w4] 0x4d060e2c4061023a063548058003014241008002c601c0f400c2240d40f918485,
mkSt [w253,w1,w2,w0,w3,w4] 0xbdf76f15cdfdf32be5711280004303428480c01023005400c22c040004d8387,
mkSt [w1,w2,w0,w3,w126,w4] 0x397601301556394d4e15786222144d42c3430604814201c002464180c280f011c0d422800423823404d20708,
mkSt [w193,w1,w2,w0,w3,w4] 0x2f9e757c538ddeb464bd29c22282814200c54346c38040102400f000c23c07000518487,
mkSt [w1,w365,w2,w0,w3,w4] 0x3f9eb5fc35afd92d463c50d2628284450403c4810040009824803024422805417118487,
mkSt [w366,w1,w2,w0,w3,w4] 0x771fb33da195e4cc351c90c74c82c2870142000303810504804646c11c0540f000c24c00408518707,
mkSt [w1,w367,w2,w0,w3,w4] 0x306f41c67cc830606010a55c0048282c040018242001018025425011c18518406,
mkSt [w10,w1,w0,w3,w8,w4] 0x66be128365f8db4f3719f2f4c142c343020483818646000282401c22800800404c26025918607,
mkSt [w27,w10,w1,w0,w3,w4] 0x6bea970a3bb2a9ad84e8235142824582000446004701828401c481400c22801c00407118705,
mkSt [w10,w1,w2,w14,w0,w3,w4] 0x2d884c698000e44c6040122e061226084c6040021e04050146c0420001c64302418818026c22825c01c26800d20588,
mkSt [w45,w10,w1,w2,w0,w3,w4] 0x2c62262a26221454562a122622001e0c421a021442040146428042400302c203c00c28027c26818022828401d20588,
mkSt [w10,w1,w2,w7,w0,w3,w4] 0xd8349011c33672780264890a3c6c24f0008b040581430040028203401c0100301c422826800d18487,
mkSt [w10,w1,w2,w0,w23,w3,w4] 0x8420013a30314202c97df3e3bf62840090ebc403c1820a42414540434002c282040f422801c29825c01118687,
mkSt [w71,w10,w1,w2,w0,w3,w4] 0x22263066222e1614546a262212001e1a020c42144204018143034042c00282420500102ac2a82a40f42282b001d20608,
mkSt [w1,w2,w90,w0,w3,w4] 0x2c2a2a14d0c224e4ca01d4585a0218c3028481410002c403824042bc0d411c0f00540082c02b920588,
mkSt [w254,w1,w2,w0,w3,w4] 0x5f3f4cfca863d88b147c903740c2c3c38d4140024483064080102d80540f02d40042d118587,
mkSt [w368,w1,w2,w0,w3,w4] 0x1f3faf3dba45e592927e1ba14c8743040240034281c646c5004480f42dc0040080540d418918687,
mkSt [w1,w2,w0,w3,w156,w4] 0x162a00e5010a2c122a2514410605184303428101c002c145824080f011c0080042e40d42ec2e120588,
mkSt [w369,w1,w2,w0,w3,w4] 0x172f6f7e3b47cdd2925e1ba14c82c64241c00346c0440280854380f42fc0040080f00d41bd18687,
mkSt [w1,w370,w2,w0,w3,w4] 0x1f3f8efd2967e103243c50b620cd82c586c401004342430600009830800400830405430118607,
mkSt [w111,w1,w2,w0,w3,w4] 0x77cf8bbe8c57e89aa33c94214e82c48241000503c2030342804583811c0540f00040080d41c518707,
mkSt [w1,w112,w2,w0,w3,w4] 0xcb9c3a278832c30197d90048282c040034144024100f411c34110503,
mkSt [w17,w18,w1,w2,w3,w4] 0x5b2d589c95d0e13e0a4d90564c83060086cd4241800282c5822813c01c0f40d40f918586,
mkSt [w18,w1,w16,w2,w0,w3,w4] 0x82048518da5a18342415f1f03131f1814030d8180018300c50581438402c2280403701800d401837400c01c30c37c37836d2048d,
mkSt [w18,w1,w2,w0,w3,w8,w4] 0x49a2e28401214a4820c8888a200221c009a0094800403014005034486460082c3a001c1800d40183143a422839d20589,
mkSt [w27,w18,w1,w2,w0,w3,w4] 0x1472564e6e526858424a6824400e424460425e4a40030442c58341400406048085400c3701800d40183b831832001d20609,
mkSt [w37,w18,w1,w2,w0,w3,w4] 0x26330f15556d694547116826016142c942ef021141430242c3438484414086450003c000c3ac18001c0d40182283bc3283783312060c,
mkSt [w18,w1,w19,w2,w0,w3,w4] 0x1aeec2cae882e6e082c2c6dd818d8d9ad6c18ac2c00241430640050342810482c0f43703c803001c0840980183cc00c3c52058b,
mkSt [w66,w18,w1,w2,w0,w3,w4] 0x208a8290ac4294a442a4608c801082980c40009440014240854042c00485830a43e03dc3d83ac09803001c0180f42292058a,
mkSt [w45,w18,w1,w2,w3,w4] 0x1eb758dae92ee33a0a6c2b264c8306400d83c2440082c281401c13c2280f40d41bd18586,
mkSt [w18,w1,w2,w7,w3,w4] 0x57cf6abb0547e4aa931e10784e82c583000280448244008343833c01c2280980100d41c518607,
mkSt [w18,w1,w2,w0,w23,w3,w4] 0x8b4c0b080001cace8c006122600221c88c0c21480030244060a4085428380014342c20400c2280180100300f43ed20688,
mkSt [w71,w18,w1,w2,w0,w3,w4] 0x108a82a0a842949442946090800c829800800c54400402450042c00343830103f83f43f03b001000c2280180f401d2050a,
mkSt [w41,w2,w0,w3,w9,w4] 0x5506126e30776983957420494a408300428a4e41c002c20240c0980000f003005518605,
mkSt [w1,w12,w2,w0,w3,w9,w4] 0x1308019aeeeed4167016d00249c0c00d80098edd8d87460245ca41c0c30185400402c18043c4000040d40f00143fc03822842c0312068c,
mkSt [w17,w1,w2,w0,w3,w9,w4] 0x2a5c00d1a5a5a1e1dde18cc11ccda1c5c1ddd9c195c546c1874241c3000282c1800f022843c00c0300f844c44520509,
mkSt [w1,w16,w2,w0,w3,w9,w4] 0x2e00c00a2980e620c0dd8e01010980c600800590448546c2c3824a41c0030280c0984540304502280f005404120588,
mkSt [w1,w2,w0,w9,w8,w4] 0x210d071e0f0b195b494f60c7150ed142c28741448a4041c002434646040300c2280f004c45c45958805,
mkSt [w37,w1,w2,w0,w3,w9,w4] 0x25c0c019e140d65e40ce45c080054a55c2108d40c88546c382850403c000c2280400984640304600f005417120489]
set_option maxHeartbeats 0 in
noncomputable def p13_D7p1 : List StD := [
mkSt [w37,w1,w2,w0,w9,w4] 0x3d79741d211d30c22cdd2901e90029034286ca424400c381878543000643c0540404484642281704600f120788,
mkSt [w1,w61,w2,w0,w3,w9,w4] 0x1b628051962a0bb748280810c05433629162c4546c38a420401c00302c28240c0f022847443804118685,
mkSt [w1,w61,w2,w0,w3,w4] 0x2a0a254e20894e018940c61845448482c243814201c0030280c01047422800c4380f000404120508,
mkSt [w36,w1,w2,w0,w3,w9,w4] 0x175a80a1352b48a94e317a94cac681929c0ab054306c38042c004024280c0400f022848841c17118586,
mkSt [w36,w1,w2,w0,w3,w4] 0x2518250a260610dcd0d20a260601120401404303800282c2400811c0400d40f017048841d20488,
mkSt [w1,w19,w2,w0,w3,w9,w4] 0x26e6c19ad28816d66814008249d000cec0c98d9d8d87c482c1c0c28186c0040244140f400411c0f00843fc09c0982284292058b,
mkSt [w66,w1,w2,w0,w3,w9,w4] 0x2dad80d1aa5821a1d9e5c98118cce1ddc1d9cdc195c546c18142c78a4302400280f40f02284140100981844342f520589,
mkSt [w1,w2,w14,w0,w3,w9,w4] 0x3e00c03214c0fa018180f20cc0eda886008020609c4545074301848a41c0c146c24382c000984c001822800c0f005418920788,
mkSt [w1,w2,w67,w0,w3,w9,w4] 0x1ae180ca142e00a141e0270eea0332e09d3ac454306ca408401c0c181400382c43c2280f04cc18918685,
mkSt [w1,w2,w67,w0,w3,w4] 0x60101120101ea25c10c8a04410014430646c101c002c1408400f40f000400843c0300d418920508,
mkSt [w1,w2,w7,w0,w3,w9,w4] 0x2ee2c0eaeaa28081e002eed4202a970ac0a0ca88d8c3028a4401c0c384818001440041443c11c0980d40f000c2281c40301412058c,
mkSt [w1,w2,w0,w23,w3,w9,w4] 0x30c0c000c181923a00f63198c0ec9624408024861c4786c3c546018a41c0c3824282c14000305200882280100f005420520788,
mkSt [w1,w2,w0,w3,w55,w9,w4] 0x141850a00295f6821ed17821d83b4cec142c46c7454601804a4401c0c14240028384142280f04dc20518785,
mkSt [w1,w2,w0,w3,w55,w4] 0x40e1dbb2241e13c641d511448454603428a4000440244140040080f009818020518487,
mkSt [w371,w1,w2,w0,w3,w4] 0x26cc3b35aac98d4e9319d0e24c830342400545810402c04386c1804d00040080f021d18606,
mkSt [w1,w2,w194,w0,w3,w4] 0x2e30122d0e11290e1101ec4e1c59190282c48140c0820302440600401c05411c0d400852c52804d20608,
mkSt [w372,w1,w2,w0,w3,w4] 0x2622214e1c89461455448e018940c48302848140044546c0401053422800c53005400407120488,
mkSt [w373,w1,w2,w0,w3,w4] 0x44074e6430631180420d9aa0600743040103424002c64040f40300d41bd18504,
mkSt [w374,w1,w2,w0,w3,w4] 0x773e7b7e2bd5e54e931dd1e14c8782c402810003058a454343c046011c03053c00400805420518707,
mkSt [w1,w255,w2,w0,w3,w4] 0x5307101cb88e9983060118c42007840282c58040034241018009811c21d18504,
mkSt [w41,w1,w12,w2,w0,w3,w4] 0x1248b980850d800100579e3e39f221dca100dc542c40183c00086004302401418001c22854c54803118587,
mkSt [w17,w41,w1,w2,w0,w3,w4] 0x2e2626306222146e2a14520026221e0c421a02144201840082860002404302c206c03056856456018001c56c22920608,
mkSt [w41,w1,w2,w0,w8,w4] 0x6ec0db704bdadb539d1dfaf4c142c30600820345840644804282401c2280f005404c57857518687,
mkSt [w37,w41,w1,w2,w0,w4] 0x211edd1a5906d68b14d2908f0cc28282438181008644400787448280414344003022805417158804,
mkSt [w41,w1,w19,w2,w0,w3,w4] 0xc44c94286c0401400179efe3bf621c4a100bc186c401410500048042c280840f401c22858054809918587,
mkSt [w66,w41,w1,w2,w0,w3,w4] 0x26262e222230562e2854660012221e1a020c42144201840083048002c042824205409858c5885600f401c59022920608,
mkSt [w41,w1,w2,w7,w0,w3,w4] 0xb831e000032e834679688f1a345c10f0012901838400820300028044822809800c1c401c55c03118507,
mkSt [w1,w2,w157,w0,w3,w4] 0x2e2e280214c4ca24d0c1ce18584218c3028381410004060042c245b011c0f00540d40085ac5a920588,
mkSt [w256,w1,w2,w0,w3,w4] 0x5f2f527c2283d8b4141cd14741c5025143814002c603428045c40540f000c5c00045bd18587,
mkSt [w113,w1,w2,w0,w3,w4] 0x9cb0e78032d90192c378300304824003414402c041800d45cd10483,
mkSt [w1,w2,w0,w3,w195,w4] 0x21a01ea04e4ea08e4d00e020cdc5c43064a4002c582804182460011c0d40080040f05f45f120508,
mkSt [w375,w1,w2,w0,w3,w4] 0x5f3e7abca8c3c50e621dd1e241d1854582434042c6428480060c03060800400805460518587,
mkSt [w39,w1,w12,w2,w0,w3,w4] 0x2eed2c2e88ac2e4a2c2c19d86cd8d8196d2cac2c002c1834280030583c04602418061444009801c0140300886180106112058b,
mkSt [w17,w39,w1,w2,w0,w3,w4] 0x28aa082ac5082a454a4400ca09082800c580094400182c046c1024006058281c63463062c62803009801c0881802292058a,
mkSt [w39,w1,w16,w2,w0,w3,w4] 0x86049914d6542436141831f1f131f0199940d4140018280c583c143840242280406140f411c08863c01c0103446446406392048d,
mkSt [w39,w1,w2,w0,w3,w8,w4] 0x122e28449e0ca482148008a220a200809e181480040281400643c603448042466401c0f411c08835066022865d20589,
mkSt [w27,w39,w1,w2,w0,w3,w4] 0x167254526e4e4258584a4028640e424260445e4a40028445824341400404860046c0106140f411c08867032431c01d20609,
mkSt [w37,w39,w1,w2,w0,w3,w4] 0xf372a2d557147056551416a242142ef02c9421141428182c64243848441404343c006780106280f401c11c08822867433464432d2068c,
mkSt [w66,w39,w1,w2,w0,w3] 0x43bc5a8935d2a1be0ac898564c84804543d142c143000245822814c01c18011c18518586,
mkSt [w39,w1,w2,w14,w0,w3,w4] 0x2c8480008100280165402a81629e81049941548002c40481c042438146c006418801022808800c0f401c64418067d2058a,
mkSt [w45,w39,w1,w2,w0,w3,w4] 0x28a9082ac64829454944010a4a0828000980c54400402c3c381024006414280469068c68862000c01022808818001d2058a,
mkSt [w39,w1,w2,w7,w0,w3] 0x6fa59ec37a5267d2930a38784e84024482c0030102818340458385c801c22803000c11c1c518687,
mkSt [w71,w39,w1,w2,w0,w3] 0x16bd4d7139319dba0a149b264c834280118502c400430243801c14c22818011c21d18586,
mkSt [w1,w12,w2,w21,w0,w3,w4] 0x198b6bcd7c1c6a52c046341403a6cc59826400243058185c5414043c60342c400300102286940d400401518687,
mkSt [w1,w2,w21,w0,w3,w4] 0x2425a9a422518dd5dd8198989180cc83c30581804602414402c0f00d422803c11c05400401469520509,
mkSt [w17,w1,w12,w2,w3,w4] 0x5708127cc0a5dd8478183050a18306c10043c1c242c002801000c13c0042286a400918507,
mkSt [w1,w238,w2,w0,w3,w4] 0x161a312e2d08c22924e05a1510cc4003c60342848102c40240414000106a814c0000540d40a400520608,
mkSt [w1,w12,w2,w0,w3,w114,w4] 0x17bf024dd3a5ed5ab25e074a6034cc041c5448303c605c543428481008182c2404000106ac0d403000440d18786,
mkSt [w1,w2,w0,w3,w114,w4] 0x145440e5e9e9e609d04dd45c5845d8424301008042c3428180001039c40c11c0300046ac01d20508,
mkSt [w376,w1,w2,w0,w3,w4] 0x366d2db42763891324d9523324824182854346c1404000106b06980d401c00518486,
mkSt [w82,w1,w12,w2,w0,w3,w4] 0xb97215d2d8d6970c03e32659935c0d084086454346c2c18303c0004240106b839c00441003118506,
mkSt [w82,w1,w2,w0,w3,w4] 0x274eb1bd1991c8bc609c1ac3844346c2c24143c306000040986b804c3c000441005518507,
mkSt [w1,w158,w2,w0,w3,w4] 0x675faf3da475c14b84fd82b4408283048546c38104024142c000411c0540f00000d40040b118687,
mkSt [w159,w1,w2,w0,w3,w4] 0x307109b3280dc1c66a4183260c2804142c402460003e00106d411d18404,
mkSt [w1,w12,w2,w0,w3,w8,w4] 0x15e7849e4a104061003f06900021ea448a38702c303c544820340424000106dc6d800403039c22918507,
mkSt [w37,w1,w12,w2,w0,w3,w4] 0x1226220000801d1a0002090e0e088891008601818e030245434145000043c03032839c4180106e000422920488,
mkSt [w1,w12,w2,w7,w3,w4] 0x6bc7692d306d6535864d43a4628302c3c603414202840182400046100980100d461d18685,
mkSt [w1,w12,w2,w0,w23,w3,w4] 0x777003cf3b67bcba670e30d17db3d554303c6054342840a4042c00182403069c01110683,
mkSt [w71,w1,w12,w2,w0,w3,w4] 0x172b14b752adbb5400590c52c572158a50a2450342840042c243070003c100100980386a018118605,
mkSt [w1,w83,w2,w0,w3,w4] 0x407cf83062c18316566d996561030282014341c242c00c0d40080f870822918406,
mkSt [w377,w1,w2,w0,w3,w4] 0x376f35bc5743c69418dd6a2325028401450583c481c000f47140542287100d400918487,
mkSt [w1,w2,w0,w3,w196,w4] 0x2ce8c1a460e0ee0a0a0a04da18c4ca05474286c6004583c10180000c22800811c71801c72071d20588,
mkSt [w257,w1,w2,w0,w3,w4] 0x376f35bc5743ca9418dd6a2325034183c2c58241420000f47280f02287240d400918487,
mkSt [w1,w2,w378,w0,w3,w4] 0x322e2d3200ed0a2965295a1451044d43028601848102c742404140009873422800c36c00872c05520608]
set_option maxHeartbeats 0 in
noncomputable def p13_D7p2 : List StD := [
mkSt [w379,w1,w2,w0,w3,w4] 0x6fcf92fd238dd9b4253c54474c8546c60482c243820302814005811c0540f00d422800873918687,
mkSt [w1,w2,w197,w0,w3,w4] 0xf37840f30efd830e03839c6c480440140000c3c42280080f473c11cd8307,
mkSt [w17,w1,w2,w0,w23,w3,w4] 0x7b700ca142c1bd782c13d582c882783390ac4306c60a4182c241c28047454000303ec00c1247040f518686,
mkSt [w71,w17,w1,w2,w0,w3,w4] 0x1e4870f183878c1d04f82e43a10c003971e1c3074242c341c50701018003000c1144447440f518487,
mkSt [w1,w16,w2,w57,w0,w3,w4] 0x1664c5f20f2d90714059111400772cda826400503c30280c2c2401022801c74800c730054004040e0389,
mkSt [w1,w2,w57,w0,w3,w4] 0x156d155d15ea62222621d1d5d1c021c303c18145038400c28242c0d422804011c01c74805473000520589,
mkSt [w27,w1,w16,w0,w3,w4] 0x4cc128da4d30a1688e40360ab0244460100c3818042848001400c00001c75805400518606,
mkSt [w27,w1,w2,w0,w3,w4] 0x4e8d10f3a28394ac14782940628302848140044546c0475c00871c05400407118486,
mkSt [w191,w1,w2,w0,w3,w4] 0x2e0000b4408d96004400019080060102c40042414000f476403076000c0d518406,
mkSt [w37,w1,w16,w2,w0,w4] 0x5e0002926951170078c4b000ab0246444100c58002834400400c00022876800400918586,
mkSt [w37,w1,w2,w0,w3,w4] 0x2e889963e463070b14b02a33228284414503c4804000540046783c017000918406,
mkSt [w1,w380,w2,w0,w3,w4] 0x3a161976316d2a2541205e19551040050383418306460104024042c140011c13c00005400c76c10800520708,
mkSt [w258,w1,w2,w0,w3,w4] 0xf834e8a01f2d44640000c003418400424142c380009818077477001011d18486,
mkSt [w1,w16,w2,w0,w3,w8,w4] 0x15eb822f32600820001f0000a3a1ec548c44882c24144820040c30280001064805000c38000422918507,
mkSt [w1,w16,w2,w0,w8,w4] 0x5ac870052012402482e9d0c54a8245814644820040c2840340000c05022800518604,
mkSt [w1,w16,w0,w3,w8,w4] 0x6a018ae1c010404948e9d0a18a838402414346020040c2818480003005001c05518684,
mkSt [w1,w16,w0,w8,w4] 0x11e5f525f01611e1082801844040c30203460282c14240000c64801022800800438005120688,
mkSt [w1,w16,w2,w7,w0,w3,w4] 0x9c227019c21c0f7a8cc8ef8031189c4a83244581838303428482040140c0003036c0d463830c39000d18607,
mkSt [w65,w1,w2,w0,w3,w4] 0x166012554e5d5452444d5552454d4102818202c4014302401c0f011c0d42280086683a804d20409,
mkSt [w27,w1,w2,w0,w8,w4] 0x4aaa7404200e9d0d54c403500a82458442064042840340000c7a000022800518505,
mkSt [w37,w1,w0,w3,w8,w4] 0x6a9992f265d0e1346ce81047cc8384424146420600028183404480300000542280087a518686,
mkSt [w1,w19,w2,w0,w3,w8,w4] 0x2c6c016a260a0140c1414000c94e00ec5c5446155542c282460200410346c640000c7ac7a800435009809c22920588,
mkSt [w1,w2,w14,w0,w3,w8,w4] 0x15c0049f0402f081000f040a00a2ee494164442c3024201c50600400480987b031400c0d805401d18507,
mkSt [w1,w2,w72,w0,w3,w8,w4] 0x26664ba162d00b140197211a8526ad215464c40305034641860200448002c39c0f02287bc00918605,
mkSt [w1,w2,w72,w0,w3,w4] 0x1a8181a681809291c1819a8d018451c5048102c24184000040f47bc22800c39c01c0f01340080d52048a,
mkSt [w1,w2,w7,w0,w3,w8,w4] 0x2d584163b9831cb05bb0ad71b83742313bb00646020044834000d43140f065c09801000811c14003000c39c05c058e038e,
mkSt [w1,w2,w0,w23,w3,w8,w4] 0x64003000c1cf4e02bc0040a14732e45321ea43c286020a404242c48000307e435012401005401d18507,
mkSt [w1,w2,w0,w3,w103,w8,w4] 0x14005abb2ae5136261d82142392acd5a4264c40283c3464146020100448002465c0f02287c400918685,
mkSt [w1,w2,w0,w3,w103,w4] 0x3636322e162a2a1d26222214121d064283c601810144840002c04241807c422801c0100f014800920688,
mkSt [w381,w1,w2,w0,w3,w4] 0x56943a13e1470f1428c970a4270542850142c58382000240f07c02287f018000918506,
mkSt [w1,w135,w2,w0,w3,w4] 0x226d1669c665e2525644e0d258ccc003060182c1008244004281401c0f022811c0d47f80707f400520589,
mkSt [w1,w16,w2,w0,w3,w4] 0xfb4dbc1b3f05ce930e2ca283028481004000c05400863836c040004d8386,
mkSt [w1,w2,w382,w0,w3,w4] 0xdc51451437d9965de8145a4102c04481840000f47fc0d401c0f015400cd8387,
mkSt [w1,w2,w0,w3,w8,w4] 0x579e19fc468bc185483cd0d28482c34242864486020000465c0040f039c05404c00918507,
mkSt [w383,w1,w2,w0,w3,w4] 0x4e4c9233a485890c24d952432482c301454646c38100011c80000c80401c00518486,
mkSt [w1,w2,w0,w3,w136,w4] 0x30c1a74e5d1a3396c183284c6428603418402414000418080801c0f016001118486,
mkSt [w27,w37,w1,w2,w0,w3,w4] 0x11e7bd000000f56b404700f592b3e08aa1160028503c480014546c0401081000c80c22800800518487,
mkSt [w27,w37,w1,w2,w0,w4] 0x5c00029bc012a64276c5a292600241040480064142858043400c22800800518584,
mkSt [w27,w37,w1,w0,w3,w4] 0xc802d8039064c436a9d34a60024100440603418382800144803001c0f005518604,
mkSt [w27,w1,w2,w14,w0,w3,w4] 0x260021020012009e1a09088a148e11018601808e0305024481c5404006c00c31839c16409881405401d20488,
mkSt [w27,w1,w2,w7,w0,w3,w4] 0xac2c8402582dedc625c46c984580c42c2824000cc458604820144404400075c39c71c09811c1400d431803016800d2048b,
mkSt [w27,w1,w2,w0,w23,w3,w4] 0x22a002522009e120a0894890e06018191008e0283c2c6024a46c04005401032465c16c03083005401d20508,
mkSt [w1,w198,w2,w0,w3,w4] 0x21ec21d6626a5661065255210d124002818a4401c342c1400302422800801c11c0d41708346b405520589,
mkSt [w1,w384,w2,w0,w3,w4] 0xbc38f7ac30e3103deb0d40c102c40340414000f48382280080304840d4d8387,
mkSt [w385,w1,w2,w0,w3,w4] 0x561d2a33a1478a1428d950a427030242c40505860a4003c11c84022883c03000918506,
mkSt [w1,w2,w386,w0,w3,w4] 0x44089c1c40811e37081121f08a0644818144024040018084422809800849011d18407,
mkSt [w37,w1,w19,w2,w0,w3,w4] 0x2a261200008000221d020a0e0d089486009101818e02c28646c38103c00045009833465c49400c84800422920508,
mkSt [w37,w1,w2,w7,w0,w3,w4] 0xe82a8808c828a8ca4a1c690909c09c280c080819086418382040440034140467801011c05c39c0d432800c0304a12050a,
mkSt [w1,w19,w2,w33,w0,w3,w4] 0x1b4adc0b9ee559510006351003a6ac5a0264002c34287c146c7010504864244009822811c00c86000408518687,
mkSt [w1,w2,w33,w0,w3,w4] 0x2ddddc11ea5c0de19981d1d49480cc8503470482818102c1440240f011c0a02280540d400408486120589,
mkSt [w160,w1,w2,w0,w3,w4] 0x44060ca3b2691803660c1a9260c304804242c40140063400c8700d518404,
mkSt [w1,w19,w2,w0,w3,w115,w4] 0x1dbb024d176e6b56a2d6072a2833cc0425544850287c4830646c600414242c100011c00c8780980044b118706,
mkSt [w1,w2,w0,w3,w115,w4] 0xe1600252a2a250a16200e1a1a2a1a0243028100464142c180001c4b00d400c11c87809800520508,
mkSt [w91,w1,w19,w2,w0,w3,w4] 0xc572e428d763b758011333a1bb620d723086454646c24141050284800042c00c87c0f000447009918606,
mkSt [w91,w1,w2,w0,w3,w4] 0x375ebabc95d1c8a670dc1ae3e4454642c1450282448000467803087c04c00447005518507,
mkSt [w66,w1,w19,w2,w0,w3] 0x5600025460ab070078c4f050ab028546c10502030242c0000c14c22888400400918506,
mkSt [w1,w19,w2,w14,w0,w3,w4] 0xf0200d6031ab98aedd3990c18326f01b35264502848306424401c146c102c000980f486800d18684,
mkSt [w45,w1,w19,w2,w0,w3,w4] 0xe72854b552ddaab403990152c572158a50a243c306440102c24281400500400c03009c86c0f518605,
mkSt [w1,w19,w2,w7,w0,w3] 0x73d58edd50729ab586a09ba462828502448186438203040142c00103c403000c11c3d118705,
mkSt [w1,w137,w2,w0,w3,w4] 0x468ce0b060c5830656599b356103028a41440202c2401011c0081848a422918406,
mkSt [w1,w199,w2,w0,w3,w4] 0x7ac116dc4b040c43a01171048540440140000c6102281800088b40d4d8307,
mkSt [w1,w2,w0,w3,w259,w4] 0x67ce16fd1931cb977e3d7a9325c54286c7860181004302414000102280088b80d48bc01d18607,
mkSt [w1,w387,w2,w0,w3,w4] 0x2622210e1da1a601611d9a14510d8843028482c78241400046382280100080308c48c005520488,
mkSt [w66,w1,w2,w14,w0,w3,w4] 0x176860a03305be1af053e1ab48827df060ac45428481c142c6c2030047824000980f467c0100d88a818118687]
set_option maxHeartbeats 0 in
noncomputable def p13_D7p3 : List StD := [
mkSt [w45,w66,w1,w2,w0,w3,w4] 0x25c424269c24261c24c26625e40124242584c48424482c782824002014043c1803d88c82f40108b01048cc0f520509,
mkSt [w1,w2,w14,w0,w34,w3,w4] 0x13eb832fac067b60035796e21223e6c11a00e48c507430402414646c481c2c380f401c88800c0540d418918687,
mkSt [w1,w2,w0,w34,w3,w4] 0xe2401e5cdd1e416201dd88c8251d8830386c1c6424402c140d401c43c11c00800405418888920489,
mkSt [w1,w2,w14,w0,w46,w3,w4] 0xfaf544dd256e060f15ea80a51a4cf142a64a08c502830646c10401c042c4824000f488c05400c0d419d18706,
mkSt [w1,w2,w0,w46,w3,w4] 0x26944662624e5450420e5549494a494302810042c4824004009839c0d411c00c22819c05488c0092048a,
mkSt [w78,w1,w2,w14,w0,w3,w4] 0xfc180de031bf696edd7980e1997ed15850664503c482c401c30642414046c000f48e00080540d40a800d18687,
mkSt [w78,w1,w2,w0,w3,w4] 0x474f713d1393e03c229c21c06443c482c40241444306c04000108e004c71c0540a800518587,
mkSt [w45,w1,w2,w14,w3,w4] 0x49c16b049258a3c58002850000303c101c6c04242c00280f413c01c8e80300d518506,
mkSt [w1,w2,w161,w0,w3,w4] 0x576f0f7e3b55e5c204fd1b204a050583c303428102404402c140011c0040080000540d41ad18687,
mkSt [w84,w1,w2,w0,w3,w4] 0x308f01c4760d23360a4184060c3428042c401424000980f490411d18404,
mkSt [w1,w2,w14,w7,w3,w4] 0x25e60d6eb5b8edd2942d1c274c02c3430646c48201c04284024140067c0100980d468118705,
mkSt [w1,w162,w2,w0,w3,w4] 0x67c5a0067c199960c6d9965610302840201404242c0300f00d41bc91001d18406,
mkSt [w1,w2,w388,w0,w3,w4] 0x26ad52a4528d64528d41d5169555150286c5038180400403c101403000c0f00d411c3c02289149180092058a,
mkSt [w1,w389,w2,w0,w3,w4] 0x1622156a2d60ea2d60c11a1550cc48464303428102c402414080001092001c0300f036c91c00520588,
mkSt [w390,w1,w2,w0,w3,w4] 0x76bd8b761b4d98b2a33a0ba24c86450343c042c582420304028380011c9240040080d401d18706,
mkSt [w1,w2,w0,w3,w200,w4] 0x106036d80186bc01867c0803c340440140003011c01c0f09280f43ecd8307,
mkSt [w1,w2,w7,w0,w11,w3,w4] 0x5829f0a14005940032e70e028a468410500a458304828142034403803094093000c11c0d41c518487,
mkSt [w1,w2,w0,w11,w3,w4] 0x2601d64dddc22620201dd218414dd8430482820342c2440140f094093011c0d40540080041c520489,
mkSt [w1,w2,w7,w0,w60,w3,w4] 0xf85dc51451791037b000566e820169805834200438400003011c97400c97c1d80d4d8387,
mkSt [w1,w2,w0,w60,w3,w4] 0x264244626082425c41c00a5509090903028381004546c004097c11c0d40f00542281d897400920489,
mkSt [w43,w1,w2,w7,w0,w3,w4] 0xe020140294218e465654620015d4859cc560181484583840203028143404009989900080d403011c0b400d20508,
mkSt [w43,w1,w2,w0,w3,w4] 0x563ceeb4a36ba03b255911b644830384024142c342804009980540f09900040b518506,
mkSt [w1,w2,w7,w0,w3,w62,w4] 0x16e005145144a4339fe05276810171804820580414003800c11c99c0309a44fc0d4d8387,
mkSt [w1,w2,w0,w3,w62,w4] 0x20201a202002610506086185844984302810045014583c009a411c0d44fc00800499c01d20488,
mkSt [w44,w1,w2,w7,w0,w3,w4] 0x1c3f80f83df91b6bd11ae805183159445838201448000411c0d499c00c9c04c8030d8387,
mkSt [w44,w1,w2,w0,w3,w4] 0x564c8eb4a86b89437159923344830582414342c284800049c00040089c40544c918506,
mkSt [w1,w2,w7,w0,w23,w3] 0x7d4acc2b3e7b715ba49650b84e0582434602854a42004301840142c0003000c3ec11c3e518785,
mkSt [w1,w2,w0,w23,w3,w35,w4] 0x1bb000e035169b372de714914d3c08d003ae4a0783c2c40281814543460a4243801c11c0306f801005420518707,
mkSt [w1,w2,w0,w3,w35,w4] 0x15cdc1d1d24da9e4219c15c0cc9898854383418a42c284024140d411c41401c0080040542046f920509,
mkSt [w1,w2,w0,w23,w3,w127,w4] 0x15b74acc0c1b66a96ed60528d257ca213a6aa0a0303c543440a4240428602c0011c0306fc01005421518686,
mkSt [w1,w2,w0,w3,w127,w4] 0x16a686a690625680cc504a894951494302810042c2460004065c03011c0100d42282140546fc0092048a,
mkSt [w92,w1,w2,w0,w23,w3,w4] 0xc7580170f1b9676c599a72e1a172cc28b0684503c6040a42454341404002c280089d003010c01118685,
mkSt [w92,w1,w2,w0,w3,w4] 0x5f3f15bd13b3e03d42dcb9d068450602c402454140428340075c04c00c9d005410c00518587,
mkSt [w163,w1,w2,w0,w3,w4] 0x1c066e23b0691d83600cda9060c304004242c3414006900309d80d518404,
mkSt [w71,w1,w2,w0,w23,w3] 0x5193024c8811e1c561428c62ac5028a454102c00302414c03001c9dc0f118485,
mkSt [w1,w164,w2,w0,w3,w4] 0x168c1a30670599860c5999b56103028402018102c2409811c0f021c9e001d18406,
mkSt [w1,w2,w260,w0,w3,w4] 0x2e6a664a46644a4664419656551515054303c381410000470504009801011c0f00d42289e49e800920589,
mkSt [w1,w261,w2,w0,w3,w4] 0x161e15a6219d26219d015a15910c4843034282c402470040063801c0980f000c9f09ec00520488,
mkSt [w1,w2,w201,w0,w3,w4] 0x7b41341035af10439f1048050340440140003067c01c1800f09f40d4d8307]
noncomputable def p13_D7 : List StD := p13_D7p0 ++ p13_D7p1 ++ p13_D7p2 ++ p13_D7p3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x0 : levelOK p13_T p13_K p13_P 6 (p13_D6.map Prod.fst) ((p13_D7.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x1 : levelOK p13_T p13_K p13_P 6 (p13_D6.map Prod.fst) ((p13_D7.drop (1*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x2 : levelOK p13_T p13_K p13_P 6 (p13_D6.map Prod.fst) ((p13_D7.drop (2*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x3 : levelOK p13_T p13_K p13_P 6 (p13_D6.map Prod.fst) ((p13_D7.drop (3*64)).take 64) = true := by decide +kernel
theorem p13_I7 : LevelN p13_R p13_T 7 p13_D7 := levelStep p13_B p13_W p13_Q p13_I6 (chunks 64 p13_D7 4 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C7x0
  · exact p13_C7x1
  · exact p13_C7x2
  · exact p13_C7x3
  ))
set_option maxHeartbeats 0 in
noncomputable def p13_D8 : List StD := [
mkSt [w1,w2,w6,w0,w3,w4] 0x20221c201e1c060818010d1513110902850583c7018100c0800340430142c40240000a003c00958884,
mkSt [w10,w1,w2,w0,w3,w4] 0x346862448b0f6abd9ac14100b14182014040030342c40282400025022422800518585,
mkSt [w18,w1,w2,w0,w3,w4] 0x43cad71d8aab2605990100470143048180050382408342c401413c00033c0180d518605,
mkSt [w1,w2,w0,w3,w9,w4] 0x784012070210341850d2e0c6930546c38a4041c0030480c282c18244000041443c0f118784,
mkSt [w41,w1,w2,w0,w3,w4] 0x586961a58c0f6ed59ac02a05114184008200004304828242c1400054053801c05518605,
mkSt [w39,w1,w2,w0,w3,w4] 0x657baf2d8a61664c98118288014402c4818003828583c0434241414c0005c808811d18685,
mkSt [w1,w12,w2,w0,w3,w4] 0x68db968582b4144d0a820358100303c605428041024342c40180013c61001001400518685,
mkSt [w17,w1,w2,w0,w3,w4] 0x30dbb50604ac2c0db0c284d0b0028600458241c6c2c401834300013c0f863400c22918685,
mkSt [w1,w16,w2,w0,w3,w4] 0x327156314834316d1428114d1824240183034480c100424282c40140009803001000c63805436c04000520689,
mkSt [w1,w2,w0,w3,w8,w4] 0x1f7fb1790c97e848907e0342020406448146020340430282c240065c01c2280f039c04c00918687,
mkSt [w27,w1,w2,w0,w3,w4] 0x6f9fb3be8b87f41440bf05ca0804840346c142844306054042c240075c01000c71c07000401d18707,
mkSt [w37,w1,w2,w0,w3,w4] 0x4efdd6340d079428809b030b0a02864184048443414303c00502c24046780981700303c022918786,
mkSt [w1,w19,w2,w0,w3,w4] 0x75dba0ee0b155c300b1542030405028481830042c646c402414100014c00c3c408400518705,
mkSt [w66,w1,w2,w0,w3,w4] 0x757b60ee8c036c28a1360280a2054481840042c583034242014280014c1840103e022918705,
mkSt [w1,w2,w14,w0,w3,w4] 0x67cc9b806dd82a5ea06123691005028306c481c04102464402c140009813c0f40540d467c18918707,
mkSt [w45,w1,w2,w0,w3,w4] 0x28aab5858aac140d40c02cd8020642824143c2c400418300013c1bc69003001d18585,
mkSt [w1,w2,w7,w0,w3,w4] 0x5c992c1e0097284b803180b70c058304828382004183440140014c13c0d41c518604,
mkSt [w1,w2,w0,w23,w3,w4] 0x25ea15ab0d196c58a11504830a0303c546018a42c3428044024140014c0303ec20405518705,
mkSt [w71,w1,w2,w0,w3,w4] 0x35cac32d8a03582841342a880203034182c385040241014280014c21c3f809801d18605]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C8x0 : levelOK p13_T p13_K p13_P 7 (p13_D7.map Prod.fst) ((p13_D8.drop (0*64)).take 64) = true := by decide +kernel
theorem p13_I8 : LevelN p13_R p13_T 8 p13_D8 := levelStep p13_B p13_W p13_Q p13_I7 (chunks 64 p13_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C8x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p13_D9 : List StD := [
mkSt [w1,w2,w0,w3,w4] 0x331b2e9256430481804103428242c40140014c13c00100603]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C9x0 : levelOK p13_T p13_K p13_P 8 (p13_D8.map Prod.fst) ((p13_D9.drop (0*64)).take 64) = true := by decide +kernel
theorem p13_I9 : LevelN p13_R p13_T 9 p13_D9 := levelStep p13_B p13_W p13_Q p13_I8 (chunks 64 p13_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C9x0
  ))
theorem p13_L : LowN p13_R p13_T 10 := lowSearch p13_B p13_I9 (by decide +kernel)
def p19_T : Nat := 0xe8e0e8e0e8e0e8e0e8e0e8e0e8e0e8e0
def p19_R : List Nat := [0, 1, 2, 3]
def p19_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,3,11)]
theorem p19_B : baseOK p19_T p19_R p19_E = true := by decide +kernel
theorem p19_S0 : SliceN p19_R p19_T (0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]) := mkSlice (w:=8) p19_B p4_B p4_L (by decide +kernel)
def p19_Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2])]
theorem p19_Y : ∀ s ∈ p19_Z, SliceN p19_R p19_T s := by
  unfold p19_Z
  simp only [List.forall_mem_cons]
  exact ⟨p19_S0,by simp⟩
noncomputable def p19_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p19_P : List (Nat × Nat) := [(4,6),(4,5),(9,11),(10,11),(2,6),(1,5)]
noncomputable def p19_K : List CutV := p19_C.map (mkCut p19_Z)
theorem p19_W : ∀ c ∈ p19_K, CutP p19_R p19_T c := cutsGood p19_Y (by decide +kernel)
theorem p19_Q : p19_P.all (sepOK p19_T) = true := by decide +kernel
def p19_D3 : List StD := []
theorem p19_I3 : LevelN p19_R p19_T 3 p19_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p19_D4 : List StD := [
mkSt [w1,w2,w0,w3] 0x14100c08040000000301]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p19_C4x0 : levelOK p19_T p19_K p19_P 3 (p19_D3.map Prod.fst) ((p19_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p19_I4 : LevelN p19_R p19_T 4 p19_D4 := levelStep p19_B p19_W p19_Q p19_I3 (chunks 64 p19_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C4x0
  ))
theorem p19_L : LowN p19_R p19_T 5 := lowSearch p19_B p19_I4 (by decide +kernel)
def p20_T : Nat := 0xe8c8e8c8e8c8e8c8e8c8e8c8e8c8e8c8
def p20_R : List Nat := [0, 1, 2, 3]
def p20_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,5,13)]
theorem p20_B : baseOK p20_T p20_R p20_E = true := by decide +kernel
theorem p20_S0 : SliceN p20_R p20_T (0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2]) := mkSlice (w:=8) p20_B p4_B p4_L (by decide +kernel)
def p20_Z : List SliceD := [(0xff00ff00ff00ff00ff00ff00ff00ff00,4,[0, 1, 2])]
theorem p20_Y : ∀ s ∈ p20_Z, SliceN p20_R p20_T s := by
  unfold p20_Z
  simp only [List.forall_mem_cons]
  exact ⟨p20_S0,by simp⟩
noncomputable def p20_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p20_P : List (Nat × Nat) := [(4,6),(12,13),(1,3),(2,3),(2,6),(9,13)]
noncomputable def p20_K : List CutV := p20_C.map (mkCut p20_Z)
theorem p20_W : ∀ c ∈ p20_K, CutP p20_R p20_T c := cutsGood p20_Y (by decide +kernel)
theorem p20_Q : p20_P.all (sepOK p20_T) = true := by decide +kernel
def p20_D3 : List StD := []
theorem p20_I3 : LevelN p20_R p20_T 3 p20_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p20_D4 : List StD := [
mkSt [w1,w2,w0,w3] 0x14100c08040000000301]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p20_C4x0 : levelOK p20_T p20_K p20_P 3 (p20_D3.map Prod.fst) ((p20_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p20_I4 : LevelN p20_R p20_T 4 p20_D4 := levelStep p20_B p20_W p20_Q p20_I3 (chunks 64 p20_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C4x0
  ))
theorem p20_L : LowN p20_R p20_T 5 := lowSearch p20_B p20_I4 (by decide +kernel)
def p21_T : Nat := 0xfc88fc88fc88fc88fc88fc88fc88fc88
def p21_R : List Nat := [0, 1, 2, 3]
def p21_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10)]
theorem p21_B : baseOK p21_T p21_R p21_E = true := by decide +kernel
def p21_Z : List SliceD := []
theorem p21_Y : ∀ s ∈ p21_Z, SliceN p21_R p21_T s := by intro s h; cases h
noncomputable def p21_C : List (Nat × List (Nat × Nat × Nat)) := []
def p21_P : List (Nat × Nat) := [(8,10),(1,3),(2,3),(3,6),(2,7),(5,12),(2,10),(3,5),(1,7),(6,10),(0,12)]
noncomputable def p21_K : List CutV := p21_C.map (mkCut p21_Z)
theorem p21_W : ∀ c ∈ p21_K, CutP p21_R p21_T c := cutsGood p21_Y (by decide +kernel)
theorem p21_Q : p21_P.all (sepOK p21_T) = true := by decide +kernel
def p21_D2 : List StD := []
theorem p21_I2 : LevelN p21_R p21_T 2 p21_D2 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p21_D3 : List StD := [
mkSt [w1,w2,w0,w3] 0x2c29a40282010241c18140c08040100580]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p21_C3x0 : levelOK p21_T p21_K p21_P 2 (p21_D2.map Prod.fst) ((p21_D3.drop (0*64)).take 64) = true := by decide +kernel
theorem p21_I3 : LevelN p21_R p21_T 3 p21_D3 := levelStep p21_B p21_W p21_Q p21_I2 (chunks 64 p21_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p21_C3x0
  ))
theorem p21_L : LowN p21_R p21_T 4 := lowSearch p21_B p21_I3 (by decide +kernel)
def p18_T : Nat := 0xfee8fc88fee8fc88fee8fc88fee8fc88
def p18_R : List Nat := [0, 1, 2, 3, 4]
def p18_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,5,21)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
theorem p18_S0 : SliceN p18_R p18_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p18_B p19_B p19_L (by decide +kernel)
theorem p18_S1 : SliceN p18_R p18_T (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[1, 2, 3, 4]) := mkSlice (w:=1) p18_B p14_B p14_L (by decide +kernel)
theorem p18_S2 : SliceN p18_R p18_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 1, 3, 4]) := mkSlice (w:=4) p18_B p7_B p7_L (by decide +kernel)
theorem p18_S3 : SliceN p18_R p18_T (0x33333333333333333333333333333333,5,[0, 2, 3, 4]) := mkSlice (w:=0) p18_B p9_B p9_L (by decide +kernel)
theorem p18_S4 : SliceN p18_R p18_T (0xffff0000ffff0000ffff0000ffff0000,7,[0, 1, 2, 3]) := mkSlice (w:=16) p18_B p12_B p12_L (by decide +kernel)
theorem p18_S5 : SliceN p18_R p18_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]) := mkSlice (w:=0) p18_B p20_B p20_L (by decide +kernel)
theorem p18_S6 : SliceN p18_R p18_T (0x22222222222222222222222222222222,4,[2, 3, 4]) := mkSlice (w:=1) p18_B p4_B p4_L (by decide +kernel)
theorem p18_S7 : SliceN p18_R p18_T (0xf000f000f000f000f000f000f000f0,4,[0, 1, 4]) := mkSlice (w:=4) p18_B p4_B p4_L (by decide +kernel)
theorem p18_S8 : SliceN p18_R p18_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p18_B p15_B p15_L (by decide +kernel)
theorem p18_S9 : SliceN p18_R p18_T (0xffff0000ffff0000ffff0000ffff,4,[0, 1, 2, 3]) := mkSlice (w:=0) p18_B p21_B p21_L (by decide +kernel)
theorem p18_S10 : SliceN p18_R p18_T (0x55550000555500005555000055550000,4,[1, 2, 3]) := mkSlice (w:=16) p18_B p4_B p4_L (by decide +kernel)
theorem p18_S11 : SliceN p18_R p18_T (0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]) := mkSlice (w:=16) p18_B p4_B p4_L (by decide +kernel)
theorem p18_S12 : SliceN p18_R p18_T (0x33330000333300003333000033330000,4,[0, 2, 3]) := mkSlice (w:=16) p18_B p4_B p4_L (by decide +kernel)
def p18_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,5,[1, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 1, 3, 4]),(0x33333333333333333333333333333333,5,[0, 2, 3, 4]),(0xffff0000ffff0000ffff0000ffff0000,7,[0, 1, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]),(0x22222222222222222222222222222222,4,[2, 3, 4]),(0xf000f000f000f000f000f000f000f0,4,[0, 1, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff,4,[0, 1, 2, 3]),(0x55550000555500005555000055550000,4,[1, 2, 3]),(0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]),(0x33330000333300003333000033330000,4,[0, 2, 3])]
theorem p18_Y : ∀ s ∈ p18_Z, SliceN p18_R p18_T s := by
  unfold p18_Z
  simp only [List.forall_mem_cons]
  exact ⟨p18_S0,p18_S1,p18_S2,p18_S3,p18_S4,p18_S5,p18_S6,p18_S7,p18_S8,p18_S9,p18_S10,p18_S11,p18_S12,by simp⟩
noncomputable def p18_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2,dC 0x3,dC 0x4,dC 0x5030202010105,dC 0x6,dC 0x2010402,dC 0x5030302010105,dC 0x5040202010105,dC 0x2010107,dC 0x3020101,dC 0x5040204030102010105,dC 0x3020201,dC 0x2010207,dC 0x4030205040202010105,dC 0x3020301,dC 0x2010108,dC 0x6030105040202010105,dC 0x6030205040202010105,dC 0x9,dC 0x3010402,dC 0x5040302010105,dC 0x2010105,dC 0x4010402,dC 0xa,dC 0xb,dC 0x302010b,dC 0x302020b,dC 0x2010106,dC 0x4030102010105,dC 0x5020202010104030105,dC 0x201010c,dC 0x2010103,dC 0x4030202010105,dC 0x4030106,dC 0x2010104030305,dC 0x3020401,dC 0x2010109,dC 0x2010104030405,dC 0x3010304,dC 0x2010208,dC 0x2010204010305,dC 0x4010101,dC 0x4010103010304,dC 0x7,dC 0x3010301,dC 0x5040402010205,dC 0x3020102,dC 0x3020302,dC 0x2010205,dC 0x4010104,dC 0x4030302,dC 0x5040302010205,dC 0x3020402,dC 0x2010206,dC 0x5020202010204030105,dC 0x201020c,dC 0x4030102010205,dC 0x5,dC 0x3020202,dC 0x2010203,dC 0x4030202010205,dC 0x2010204030305,dC 0x2010204030405,dC 0x2010306,dC 0x4030102010305,dC 0x2010303,dC 0x4030202010305,dC 0x2010307,dC 0x2010407,dC 0x2010305,dC 0x5040202010405,dC 0x2010408,dC 0x2010405,dC 0x2010406,dC 0x3020104,dC 0x4030102010405,dC 0x2010403,dC 0x4030202010405,dC 0x3010201,dC 0x5020203010105,dC 0x3020206,dC 0x301020b,dC 0x8,dC 0x5040203010105,dC 0x3010105,dC 0x3010205,dC 0x4020101,dC 0x5020203010305,dC 0x3010305,dC 0x5040203010405,dC 0x3010405,dC 0x5020204010105,dC 0x4010105,dC 0x4010205,dC 0x5020204010305,dC 0x4010305,dC 0x2010401,dC 0x3010306,dC 0x4010405,dC 0x4030401,dC 0x5040203020105,dC 0x3020105,dC 0x3020205,dC 0x3020305,dC 0x4020406,dC 0xd,dC 0x5040203020405,dC 0x3020405,dC 0x3020203,dC 0x3020409,dC 0x4030203020405,dC 0x4030103020409,dC 0x5010204020105,dC 0x5010304020105,dC 0x5030204020105,dC 0x5030304020105,dC 0x4020105,dC 0x4020205,dC 0x4020305,dC 0x4020405,dC 0x5010204030105,dC 0x5010304030105,dC 0x4030105,dC 0x5020204030105,dC 0x6010105020204030105,dC 0x6010205020204030105,dC 0x5020304030105,dC 0xc,dC 0x4030205,dC 0x5020404030205,dC 0x4030109,dC 0x4020303,dC 0x5020304030205,dC 0x4030305,dC 0x5020204030405,dC 0x4030405]
def p18_P : List (Nat × Nat) := [(2,3),(3,6),(20,21),(24,25),(3,5),(8,10),(20,22),(17,21),(8,12),(5,21),(9,25),(9,11),(6,22),(6,10),(2,10),(4,12),(0,12),(17,25),(1,3),(9,10),(3,17),(6,7),(18,19),(18,22),(5,7),(17,19),(18,26),(5,13),(12,20),(1,13),(1,21),(10,18),(1,25),(9,13),(0,3),(4,7),(6,14),(3,9),(5,12),(2,7),(20,28),(2,11),(1,7),(24,28),(24,26),(0,10),(4,21),(10,24),(4,22)]
noncomputable def p18_K : List CutV := p18_C.map (mkCut p18_Z)
theorem p18_W : ∀ c ∈ p18_K, CutP p18_R p18_T c := cutsGood p18_Y (by decide +kernel)
theorem p18_Q : p18_P.all (sepOK p18_T) = true := by decide +kernel
def p18_D3 : List StD := []
theorem p18_I3 : LevelN p18_R p18_T 3 p18_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p18_D4 : List StD := [
mkSt [w1,w0,w46,w31,w4] 0x2e66ea619d8283818241408341c300c2d00580,
mkSt [w84,w1,w2,w0,w31] 0x1aaa5a1dd54180c14281c24082c203100500,
mkSt [w125,w1,w0,w31,w4] 0x2eea621ddd8283c2408182c2034300c1500580,
mkSt [w1,w2,w0,w31,w51] 0x332a6661dd8281c3c18240c14203430082d00600,
mkSt [w509,w1,w2,w0,w31] 0x1aaa5a1dd54180c14281c24082c203100500,
mkSt [w1,w2,w0,w31,w510] 0x3326221d994281c204018240c143430082d00600,
mkSt [w70,w1,w0,w46,w3] 0x35f2c026a4014200c30241838341c1028080100680,
mkSt [w1,w2,w0,w3,w511] 0x3326221d994281c204018000c4c3430081500600,
mkSt [w25,w1,w0,w46,w4] 0x372c02a65c064245c5444183428141c38000d00680,
mkSt [w1,w2,w30,w512,w3] 0x1e1d6a61d945c643420581044001c1500500,
mkSt [w513,w1,w2,w30,w3] 0x21a6159dd94643c1c14584420001100480,
mkSt [w1,w30,w0,w46,w3] 0x2f726ea61d81c606424382c5458342844001500680,
mkSt [w1,w2,w0,w514,w3] 0x2772aea61d81c2464603858542c342844001500680,
mkSt [w515,w1,w2,w0,w3] 0x2332daa6658603c2c28201854441c14300100600,
mkSt [w516,w1,w2,w0,w3] 0x2dde80265c03c0c241c2c34202818000900580,
mkSt [w517,w1,w0,w46,w3] 0x35f2c026a4014200c30241838341c1028080100680,
mkSt [w1,w0,w46,w211,w3] 0x2272ea61d946490246038582c542844001500600,
mkSt [w518,w2,w0,w3,w51] 0x32ea664200038ac40180c7030203414000900600,
mkSt [w519,w2,w0,w3,w51] 0x372eaa81c0028ac402ca8100c24203418000900680]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C4x0 : levelOK p18_T p18_K p18_P 3 (p18_D3.map Prod.fst) ((p18_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p18_I4 : LevelN p18_R p18_T 4 p18_D4 := levelStep p18_B p18_W p18_Q p18_I3 (chunks 64 p18_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p18_D5 : List StD := [
mkSt [w1,w2,w14,w0,w31,w4] 0x4efa0b9201d070400000018281c3c201814083834242c02c02802510583,
mkSt [w1,w2,w0,w31,w42,w4] 0xae3c8f9201c471c000000183828241c3c180c140820342c03803003510603,
mkSt [w45,w1,w2,w0,w31,w4] 0x14a61ce7118cb5270730402c243c1c180820380c281403d08601,
mkSt [w105,w1,w2,w0,w31,w4] 0x2ab5ddf19aea61d840302c283820140c3c1c24081900680,
mkSt [w1,w2,w520,w0,w31,w4] 0x4efa0b9201d070400000018281c3c201814083834242c04402802510583,
mkSt [w1,w2,w0,w31,w521,w4] 0xae3c0f9201c471c000000183828241c3c180c140820342c04803003510603,
mkSt [w522,w1,w2,w0,w31,w4] 0x2ab5ddf19aea61d840302c243c1c18082038280c1500680,
mkSt [w523,w1,w2,w0,w31,w4] 0x2ab5ddf19aea61d840302c283820140c3c1c24081900680,
mkSt [w70,w1,w2,w14,w0,w3] 0xb289177cb0ec0d85200086c1c3c20281808383424140002406006910583,
mkSt [w70,w1,w2,w0,w3,w42] 0x372e99965682cc54381c3c480c282418083420001406006d00682,
mkSt [w45,w70,w1,w2,w0,w3] 0x3222ddd9a1ea61d8400c3c1c180824203814280100600,
mkSt [w105,w70,w1,w2,w0,w3] 0x3221edd9a1ea61d840083820140c283c1c18240100600,
mkSt [w1,w2,w0,w524,w3,w4] 0x6b3988c58044e451910980010a0283c1c2c1824000c4c3430140806006802807118684,
mkSt [w28,w1,w0,w46,w3,w4] 0x7d3400b00ae48002dc6005034300c08382c00144c241c07807004110583,
mkSt [w84,w28,w1,w2,w0,w3] 0x6130f3b2cac3920a1f414000c08382c00281c30144c202404006007d10603,
mkSt [w525,w1,w2,w0,w3,w4] 0xdd3d07730a2c5040e585c503c180c24381c142c082034004806c06003110683,
mkSt [w125,w28,w1,w0,w3,w4] 0x3bab732e921dc19428300c50382000184c2c4824081408100701,
mkSt [w28,w1,w2,w0,w3,w51] 0x63c0e281b31425c88031d805080281c300c0838202c00144c2406004008808118604,
mkSt [w526,w1,w2,w0,w3,w4] 0x14a61ce71188b5271730402c283820140c3c1c08241809108601,
mkSt [w74,w2,w30,w0,w3] 0x38d1c830b83aa6883c68606454584820240c0014385c0040a80ad10703,
mkSt [w25,w1,w2,w14,w0,w4] 0x113c1ee2a1a50316a488282064605444346c480024703c1c0c38140bd40881,
mkSt [w25,w45,w1,w2,w0,w4] 0x18e5350262d464a12034640c281c604420183c00742414380c108701,
mkSt [w1,w2,w30,w0,w527,w3] 0xec00d6ac2128394c5203c281c60643854582c44001406108601,
mkSt [w309,w1,w2,w30,w0,w3] 0x2b39df71adea61d8786444583c202460541c2838001500700,
mkSt [w1,w2,w30,w0,w3,w528] 0x3d33b72eae9e61d83824281c60646854582c7c2044001500780,
mkSt [w202,w1,w2,w30,w0,w3] 0x72872490a31c08881c60a088060382028002468141c0d00cd10502,
mkSt [w1,w2,w30,w14,w0,w3] 0x68c162850382c9a396208007080343c20286454582c0014245c380600240a80bd18684,
mkSt [w1,w2,w30,w0,w3,w42] 0x3fb5732aaea261d8381c342860643c54582c24206c001406100781,
mkSt [w45,w1,w2,w30,w0,w3] 0x3a21df71adea61d8406438083c1c246054204400281500700,
mkSt [w105,w1,w2,w30,w0,w3] 0x39ddb712e9a61d804060645408382028141c3c0024480a80d500702,
mkSt [w1,w6,w0,w46,w3,w4] 0x8df700c00bcca801e07005034241458382c54081c444c000dc0d80a110603,
mkSt [w140,w1,w2,w0,w3,w4] 0x1e412b8304ec7280e07195460442c2438201408004c1c3c0e00600d910603,
mkSt [w84,w1,w2,w6,w0,w3] 0x3fe33b722eb241503c601438084c281c30582c002024440600e100782,
mkSt [w1,w2,w529,w0,w3,w4] 0x3ff82372aea61dd8283484646048583c544c24206c002c0e806100782,
mkSt [w1,w2,w6,w0,w3,w51] 0x108240e6a92c5a928398281c3c846014303854084c202c00246c06140801,
mkSt [w1,w2,w530,w0,w3,w4] 0x3aefb6ea26001c00246c381c646048543c282014000d00700,
mkSt [w22,w1,w0,w46,w3,w4] 0x12a48987525675251730348824442c1c0800145c303810108601,
mkSt [w84,w22,w1,w2,w0,w3] 0x1ef6df2dea6219985c88442c08281c24001438203100680,
mkSt [w22,w125,w1,w0,w3,w4] 0x1c54b5236300b52487342458188c643820082c2848006c1410908701,
mkSt [w22,w1,w2,w0,w3,w51] 0x3ba6a72a62ea61d8281c1888246c842c08001420303900700,
mkSt [w1,w2,w0,w310,w3,w4] 0x1a96888c4a97a49d1030441c146024000c885c902c300812908681,
mkSt [w10,w1,w0,w46,w3,w4] 0x26a771ea6dea61d82834883038145c002c08241c4500680,
mkSt [w84,w10,w1,w2,w0,w3] 0x1f2f9f72ea6219984488385c1400281c302c083c202500700,
mkSt [w1,w531,w2,w0,w3,w4] 0x36ab26b2ea41c00068243c202c140c3038485c080100680,
mkSt [w10,w1,w2,w0,w3,w51] 0x37626126eea60194281c0c8830382014002c083c2408813500682,
mkSt [w532,w1,w2,w0,w3,w4] 0x2eeb2271de2ea61c3028385c140c003c1c48082500600,
mkSt [w1,w75,w0,w3,w8,w4] 0x16b731ac5934c110e8383c102028381c54009414600c245c13d08701,
mkSt [w1,w2,w0,w3,w533,w4] 0x9211e089c1a07141212960e0a0c920283c1c5c34241860100854003014200c14806014413d58804,
mkSt [w534,w1,w2,w0,w3,w4] 0x25ded98028261d80305424385c60282014000d00580,
mkSt [w1,w2,w0,w313,w8,w4] 0x1ad4c92a6b16a3a4e8382418385c6c040014949820300c14508681,
mkSt [w535,w1,w2,w0,w3,w4] 0x2dde61c028261d806854246c201430385c0c0100580,
mkSt [w536,w1,w2,w0,w3,w4] 0x2a22ddc2402a61c03028382014246c1c60000900580,
mkSt [w1,w216,w0,w3,w8,w4] 0x16b625295a349120c0303c28382048540094140c241c13d08601,
mkSt [w537,w1,w2,w0,w3,w4] 0x2aa6de2d99ea61d830243c1c4808385c140c2900580,
mkSt [w1,w2,w0,w196,w8,w4] 0x14a5c96752507318c0303c244838200094145c300814508581,
mkSt [w17,w1,w2,w3,w51] 0x3ee34830b2a68398a0b0340c2cac84246c20303c0800140080881c110783,
mkSt [w538,w1,w0,w46,w3,w4] 0x7cf300b80ae48001dc6004090300c08382c1c00144c241f407004110583,
mkSt [w1,w0,w46,w177,w3,w4] 0x7fb3175b002c0001dc61400246414901c605838082c54444c001f80a00d910703,
mkSt [w539,w1,w0,w46,w3,w4] 0x26a771ea6dea61d828348824442c1c080014305c3900680,
mkSt [w209,w1,w0,w46,w3,w4] 0x26a771ea6dea61d82834883038145c002c08241c4500680,
mkSt [w1,w2,w0,w3,w51,w540] 0x18b2a8893210800ae73030382040180c14a0ac34082c06108601,
mkSt [w541,w1,w2,w0,w3,w51] 0x3b67332e61ea61d8a05c18b8246c842c00083020381500700,
mkSt [w1,w2,w0,w3,w51,w542] 0x3fbb76ea62001c0024a0ac5c341430b00cbc183c20000900780,
mkSt [w543,w1,w2,w0,w3,w51] 0x78272ca0842441081e09440c0180c303820140024b00821421110582]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C5x0 : levelOK p18_T p18_K p18_P 4 (p18_D4.map Prod.fst) ((p18_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p18_I5 : LevelN p18_R p18_T 5 p18_D5 := levelStep p18_B p18_W p18_Q p18_I4 (chunks 64 p18_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C5x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p18_D6 : List StD := [
mkSt [w1,w2,w68,w3,w4] 0xa93259474ec6316628282018140c08241c100401000800c00118504,
mkSt [w89,w1,w2,w3,w4] 0x9ad592d82a8ebb262c280c1c14002420180801c01801400c00118485,
mkSt [w1,w2,w0,w3,w31,w4] 0x4c980a64580b152a5451dbb76cc281c0c2c141808242001402000000c04118485,
mkSt [w1,w2,w0,w31,w4] 0x2bae41e288f75d002820180c3c1c3824082c02000c00110503,
mkSt [w124,w1,w2,w0,w4] 0xaa5592d92a8ebb262c240844381800283c140c05405004c00c00118505,
mkSt [w70,w1,w2,w0,w3] 0xb10e1d172ee6cd8a74200c2414003c1c3828180806406000c05c00118585,
mkSt [w28,w1,w2,w14,w0,w3,w4] 0x14e9c80901c3466cc2d00b202a808000004060281c3c2014082c00344c02407404007002918505,
mkSt [w28,w1,w2,w0,w3,w42,w4] 0x156d81b424450d120060cf1c300a002034060381c34140c083c2c004c2003408404001403008118586,
mkSt [w45,w28,w1,w2,w0,w3,w4] 0x18b15ba94a94880edc040001828c480c5276002840142444082c003c1c204c08c07004003d18604,
mkSt [w105,w28,w1,w2,w0,w3,w4] 0xb154c2a50928182a0050801c305480c121400404c2c00283820140c09809401408009118485,
mkSt [w74,w2,w6,w0,w3,w4] 0x7dfbc22cce91501006b422bb94c2820645808480c30605400383c5c2c0a400400009c0a118785,
mkSt [w25,w1,w2,w0,w3,w4] 0x573f417ad9afe9a35b1c1966a8c3c5c240048140c281c200b80140b009c0040b40a118507,
mkSt [w1,w2,w30,w0,w3] 0xc179b55aa115cb08943c44605458202400141c28380600b00c40040c80a918606,
mkSt [w1,w2,w6,w14,w0,w3,w4] 0xfa1e38d628060a14044785124880e08005060343c2014303854082c005c4c0e40a00240d80000bd18606,
mkSt [w1,w2,w6,w0,w3,w42,w4] 0xcfc41f01e00008060764b0328264900c2840381c348464486014583c6c540800204c2c0f40f00ed50883,
mkSt [w45,w1,w2,w6,w0,w3,w4] 0x152c70080c92446a305aa462440b0e180350604024143038084c3c1c602c5420000f80a00c00d918704,
mkSt [w105,w1,w2,w6,w0,w3,w4] 0x155deb0b4020d402f058a04e44076c140046004014303c084c2838202c1c00480fc0140f00000d518685,
mkSt [w22,w1,w2,w14,w0,w3,w4] 0xcf7c0fb288f22a00000007000000185028383c201814882c0834245c0010402402910683,
mkSt [w22,w1,w2,w0,w3,w42,w4] 0x11e70d582c1c074cd682501848d00e03050802438281c3418886c3c842c0814002010c03410803118784,
mkSt [w45,w22,w1,w2,w0,w3,w4] 0x26759180030002ea61d80040882c08243c1c14203800182803c11100682,
mkSt [w105,w22,w1,w2,w0,w3,w4] 0x26759980030002ea61d80040882c08283820183c1c00142409011500682,
mkSt [w1,w2,w0,w3,w126,w4] 0x64b80ae55a0f1dbb765254a94ec2428200c2c1460089038301c01411c00c00412118605,
mkSt [w10,w1,w2,w14,w0,w3,w4] 0x955500b2202c483022840201bc50804003040343c208808303814005c13012c0001280bd18505,
mkSt [w10,w1,w2,w0,w3,w42,w4] 0x146f8e1a304da0c243b082c9c37601980508038281c3424482c883090140008203c1380000ec01413518785,
mkSt [w45,w10,w1,w2,w0,w3,w4] 0xdb6cecaaa12032412001c636510a8b002840242c883814003c1c2008301281200c110683,
mkSt [w105,w10,w1,w2,w0,w3,w4] 0xa06d28c0ea1442ca1442480671838a00403c883014003820905c2c0c281340d510682,
mkSt [w1,w2,w75,w0,w3,w4] 0x153aeaac8091663c001020409102438605c540c0020283c1400b00a001400118505,
mkSt [w1,w2,w0,w3,w313,w4] 0x5d9a00204987680c08b421408a824186c5c8420002c300c1415014c03400001518585,
mkSt [w53,w1,w2,w0,w3,w8,w4] 0xc21008411e300400d30068002b160d00000402890302c3814082414413c14c0b118404,
mkSt [w1,w2,w0,w504,w3] 0x84e9d0c689052954904420180014081c380b015c14c00518404,
mkSt [w1,w2,w116,w0,w3,w4] 0xd9b126c404b562b000000000a8283864482c0800243c16014c0080b000118485,
mkSt [w1,w2,w0,w3,w156,w4] 0x64c800e3a74329cb96d18b1342ca0283c4818101c002c24200c141680b001400518684,
mkSt [w1,w2,w505,w0,w3,w4] 0x1cb96ea4a8752543003190b52a420303c5c2c980824381c0017014c04c00118584,
mkSt [w1,w2,w216,w0,w3,w4] 0x1dcb83682c8b514a000000000a8242064605c540c004838283c1c17c0140a00b000118685,
mkSt [w74,w17,w1,w2,w0,w3,w4] 0x10d12a78cc9a008108225410184406001010002830143c244448000b014c18818518404,
mkSt [w74,w1,w2,w0,w3,w8,w4] 0x618014514b2886400000079a0005803030185c382c241c1400282013c0b110582,
mkSt [w1,w255,w2,w0,w3] 0xac50f4a8cf090e78a420441c1824082814380014c1900b006004c00518506,
mkSt [w1,w2,w0,w3,w114,w4] 0xdf700f79e1edb6a6e594a54286448100c901c002c242008141940140b110683,
mkSt [w1,w2,w0,w506,w3] 0x9accac13a2df1e2cb828180c1c140830202c0b01a80600081a400d18486,
mkSt [w1,w2,w0,w3,w196,w4] 0x7d5a00183567419306d5a5306c024a064485c0c6c8420003c2c3014081ac00014c03401518785,
mkSt [w17,w1,w2,w0,w3,w8,w4] 0x608b0002a90084030c70031a000400383c9030140c24381c0828001b414414d10583,
mkSt [w17,w1,w2,w3,w42,w4] 0x1b6340db5f1c1b4b18140d510cc10cca028644834300c6c2cac1c84205c08143c001bc0080141b803558905,
mkSt [w2,w57,w0,w3,w4] 0x39321ac76a5a3364a824440c2c00283c18081c404c00c00518484,
mkSt [w239,w2,w0,w3,w4] 0x39321bc76e863352282438140c08283c18001c804c00c00118484,
mkSt [w1,w2,w507,w3,w4] 0x785098c762a23b64a424341c18304420481cc04c00800d18404,
mkSt [w191,w1,w2,w3,w4] 0x88509cc86e962b64a42438145c2030442c1c1d004c00c01518484,
mkSt [w258,w1,w2,w0,w3] 0x99120bc62cd62b162c38140c00283c18083004c1a80600b118484,
mkSt [w314,w1,w2,w0,w3,w8,w4] 0x820018618c2c7680000005a20006963030185c202838842c1400241c13c0b110602,
mkSt [w315,w1,w2,w0,w3,w8,w4] 0x618014514b2896000000071a000580403018385c00241c080c282013c0b110582,
mkSt [w1,w2,w72,w0,w3,w8,w4] 0xb34c00026b809a070024001041801640284430389020b00c540024140814414d10682,
mkSt [w257,w1,w2,w0,w3,w8,w4] 0x608c0002c90084041070041a00050048445c2030140c241c0834280014414d10602,
mkSt [w2,w0,w34,w3,w4] 0x38d0da4962a23b64a4343044001c2438085c1e404c00401518484,
mkSt [w240,w2,w0,w3,w4] 0x38921cc86e863354a4303c1c0c0824385c001e804c01400118484,
mkSt [w1,w2,w0,w46,w3,w4] 0x256a8cad3845518284f65bc84e0340c5c002444381c30081f000004c01402518505,
mkSt [w1,w0,w46,w3,w4] 0x27ae65ee76b9a074342438005c2c3044081c141f004c01510583,
mkSt [w78,w1,w0,w3,w4] 0x88f1dcc86e860b64a4243820181430441c2c1fc04c01400d18484,
mkSt [w84,w1,w2,w0,w3] 0xbbf1be1a2795d745c3800281c242c440814203004c06020110603,
mkSt [w125,w1,w2,w0,w3,w4] 0x1eac7231c849a62a80f9a2a0454200c48243c5c3038080020800014c1b800803518506,
mkSt [w1,w2,w0,w3,w51] 0xdb896d8aa89c559500a0ac186c8400242c382030081414c20c08800806118685,
mkSt [w1,w2,w508,w0,w3,w4] 0x35baceab374b59ba04b61ba48802824b00c5c3830002c081421c00004c00811518585]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C6x0 : levelOK p18_T p18_K p18_P 5 (p18_D5.map Prod.fst) ((p18_D6.drop (0*64)).take 64) = true := by decide +kernel
theorem p18_I6 : LevelN p18_R p18_T 6 p18_D6 := levelStep p18_B p18_W p18_Q p18_I5 (chunks 64 p18_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C6x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p18_D7 : List StD := [
mkSt [w28,w1,w2,w0,w3,w4] 0x62c562bd7ae4a4c98e000000ce42820140c4c003c1c3818240800c00404c01400805800118607,
mkSt [w1,w2,w6,w0,w3,w4] 0x3636300230908e2929000a08a080dd0243c646058544c281c202c00380c404c0080140b000c00400120688,
mkSt [w22,w1,w2,w0,w3,w4] 0x5cb94264a9400000840000006e42420148808003c281c38181180040b000118584,
mkSt [w10,w1,w2,w0,w3,w4] 0x62c560fd7ae6a4c98e688890ce428202c0c88003c600830385c00c00004c01400812400518607,
mkSt [w53,w1,w2,w0,w3,w4] 0x6dcb92ed058f60cc82f4882120c28203038040c24085c00146c6015401414c0b000118685,
mkSt [w1,w2,w0,w24,w3,w4] 0xe0c2a74208d85b3667850544cc843c18141c045408381580140000b014c00518486,
mkSt [w54,w1,w2,w0,w3,w4] 0x2c596ea4b86b09bb62b098212843c30385c9c08280054442c16414c0b000118584,
mkSt [w18,w1,w2,w0,w3,w4] 0x65cb61ed3a6f654236f450436002838140c0030089c1c18843c16c0000b000414d18605,
mkSt [w101,w1,w2,w0,w3,w4] 0x2c290ea4b86b1d9362b0113128430385c9808280c00842c17414c0b000118504,
mkSt [w1,w2,w0,w3,w9,w4] 0x2eac16b1291199c386b803a750c286c140c183098445c201780000140b000414d18506,
mkSt [w74,w1,w2,w0,w3,w4] 0x6ddb82ed090b61c386b41131600282030145c0c00a4243c381c481800140000b014d18685,
mkSt [w41,w1,w2,w0,w3,w4] 0x4418ece1b36d158b341118b3444281c00a438140c2018c14c0b000518404,
mkSt [w1,w12,w2,w0,w3,w4] 0x652b722d199144bc0475593366c281c1410305c180c005420901980140b014c00d18605,
mkSt [w1,w2,w0,w20,w3,w4] 0x4fbf92fcc015e606755e622746044283038085c3c100c00186019c01400014c0b000800d18607,
mkSt [w50,w1,w2,w0,w3,w4] 0x97d93592b3642ca1646d1282030a8385c14001a014c0080b000cd8385,
mkSt [w17,w1,w2,w0,w3,w4] 0x665d0eb58875a44370b89800a2c2838300c5c00a8242c143c081b000800001414c0b118606,
mkSt [w1,w16,w2,w0,w3,w4] 0x54992de437611980525119324002820944838140c08001c1d414c0b000d18504,
mkSt [w1,w2,w0,w3,w8,w4] 0x76dc0f760b0b802060b9c50312024281c900c2c94085c30382014001d801400000c0b014d18706,
mkSt [w27,w1,w2,w0,w3,w4] 0x5ebd40f4a94da1b3667828a00cc2820140c1800b444303c5c1dc1d80140b000c14d18586,
mkSt [w37,w1,w2,w0,w3,w4] 0x266cce742a73a13370980330a285c30380020b42818480c1e01d800014c04c0b118506,
mkSt [w1,w2,w14,w0,w3,w4] 0x4e5da8362b35a541015a54100e0343c2024385c002c30441c08141ec00c00000404c01518686,
mkSt [w1,w2,w0,w3,w42,w4] 0x20e001a00f52a30ad18aa14a520940344890246c843020002c3c081420400c00400014c04c00801520688,
mkSt [w45,w1,w2,w0,w3,w4] 0xac0cafa80bea02402274000402438003c1c202c3044081421814c01510603,
mkSt [w105,w1,w2,w0,w3,w4] 0x1f35bed67936abc9806833922244090303c1c00206c5c2c28140c04c01400c00000422000918687]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C7x0 : levelOK p18_T p18_K p18_P 6 (p18_D6.map Prod.fst) ((p18_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p18_I7 : LevelN p18_R p18_T 7 p18_D7 := levelStep p18_B p18_W p18_Q p18_I6 (chunks 64 p18_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C7x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p18_D8 : List StD := [
mkSt [w1,w2,w0,w3,w4] 0xfff99d6b36850283c18240c2c5c1c304400382008140e908781]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p18_C8x0 : levelOK p18_T p18_K p18_P 7 (p18_D7.map Prod.fst) ((p18_D8.drop (0*64)).take 64) = true := by decide +kernel
theorem p18_I8 : LevelN p18_R p18_T 8 p18_D8 := levelStep p18_B p18_W p18_Q p18_I7 (chunks 64 p18_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C8x0
  ))
theorem p18_L : LowN p18_R p18_T 9 := lowSearch p18_B p18_I8 (by decide +kernel)
def p23_T : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8
def p23_R : List Nat := [0, 1, 2, 3]
def p23_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
theorem p23_B : baseOK p23_T p23_R p23_E = true := by decide +kernel
def p23_Z : List SliceD := []
theorem p23_Y : ∀ s ∈ p23_Z, SliceN p23_R p23_T s := by intro s h; cases h
noncomputable def p23_C : List (Nat × List (Nat × Nat × Nat)) := []
def p23_P : List (Nat × Nat) := [(4,6),(1,3),(2,3),(9,12),(2,6),(1,9),(0,9),(6,12),(5,9)]
noncomputable def p23_K : List CutV := p23_C.map (mkCut p23_Z)
theorem p23_W : ∀ c ∈ p23_K, CutP p23_R p23_T c := cutsGood p23_Y (by decide +kernel)
theorem p23_Q : p23_P.all (sepOK p23_T) = true := by decide +kernel
def p23_D2 : List StD := []
theorem p23_I2 : LevelN p23_R p23_T 2 p23_D2 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p23_D3 : List StD := [
mkSt [w1,w2,w0,w3] 0x2601d80201c18100c0814040100480]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p23_C3x0 : levelOK p23_T p23_K p23_P 2 (p23_D2.map Prod.fst) ((p23_D3.drop (0*64)).take 64) = true := by decide +kernel
theorem p23_I3 : LevelN p23_R p23_T 3 p23_D3 := levelStep p23_B p23_W p23_Q p23_I2 (chunks 64 p23_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p23_C3x0
  ))
theorem p23_L : LowN p23_R p23_T 4 := lowSearch p23_B p23_I3 (by decide +kernel)
def p22_T : Nat := 0xfeeafc88feeafc88feeafc88feeafc88
def p22_R : List Nat := [0, 1, 2, 3, 4]
def p22_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,1,17)]
theorem p22_B : baseOK p22_T p22_R p22_E = true := by decide +kernel
theorem p22_S0 : SliceN p22_R p22_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p22_B p19_B p19_L (by decide +kernel)
theorem p22_S1 : SliceN p22_R p22_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p22_B p16_B p16_L (by decide +kernel)
theorem p22_S2 : SliceN p22_R p22_T (0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) p22_B p14_B p14_L (by decide +kernel)
theorem p22_S3 : SliceN p22_R p22_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3, 4]) := mkSlice (w:=0) p22_B p23_B p23_L (by decide +kernel)
theorem p22_S4 : SliceN p22_R p22_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 1, 3, 4]) := mkSlice (w:=4) p22_B p7_B p7_L (by decide +kernel)
theorem p22_S5 : SliceN p22_R p22_T (0xf000f000f000f000f000f000f000f0,4,[0, 1, 4]) := mkSlice (w:=4) p22_B p4_B p4_L (by decide +kernel)
theorem p22_S6 : SliceN p22_R p22_T (0xffff0000ffff0000ffff0000ffff,4,[0, 1, 2, 3]) := mkSlice (w:=0) p22_B p21_B p21_L (by decide +kernel)
theorem p22_S7 : SliceN p22_R p22_T (0x55550000555500005555000055550000,4,[1, 2, 3]) := mkSlice (w:=16) p22_B p4_B p4_L (by decide +kernel)
def p22_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,4,[0, 1, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,5,[0, 1, 3, 4]),(0xf000f000f000f000f000f000f000f0,4,[0, 1, 4]),(0xffff0000ffff0000ffff0000ffff,4,[0, 1, 2, 3]),(0x55550000555500005555000055550000,4,[1, 2, 3])]
theorem p22_Y : ∀ s ∈ p22_Z, SliceN p22_R p22_T s := by
  unfold p22_Z
  simp only [List.forall_mem_cons]
  exact ⟨p22_S0,p22_S1,p22_S2,p22_S3,p22_S4,p22_S5,p22_S6,p22_S7,by simp⟩
noncomputable def p22_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2010202,dC 0x2010203,dC 0x4,dC 0x2010205,dC 0x2010206,dC 0x7,dC 0x3010208,dC 0x8,dC 0x4010101,dC 0x2010405,dC 0x2010402,dC 0x2010406,dC 0x5,dC 0x2010301,dC 0x2010308,dC 0x6,dC 0x3010403,dC 0x3010205,dC 0x2,dC 0x3010201,dC 0x2010102,dC 0x2010106,dC 0x3010101,dC 0x3010108,dC 0x3,dC 0x2010101,dC 0x2010108,dC 0x3020103,dC 0x2010401,dC 0x3020403,dC 0x3020205,dC 0x3020102,dC 0x4020203,dC 0x3010301,dC 0x3010308,dC 0x4020303,dC 0x4020105,dC 0x3020106,dC 0x4020102,dC 0x4010401,dC 0x4020405,dC 0x4020402,dC 0x4020101,dC 0x4020305,dC 0x4030401,dC 0x3020306,dC 0x4030405]
def p22_P : List (Nat × Nat) := [(16,17),(9,10),(2,3),(2,7),(3,6),(2,10),(4,12),(2,19),(1,17),(1,3),(3,5),(1,7),(6,22),(9,12),(8,12),(8,17),(9,17),(6,7),(8,10),(17,18),(8,13),(5,12),(24,25),(5,13),(18,22),(18,19),(5,7),(9,11),(20,22),(9,25),(9,13),(8,14),(6,12),(6,14),(20,21),(5,21),(24,26),(18,26),(24,28),(20,28),(4,22)]
noncomputable def p22_K : List CutV := p22_C.map (mkCut p22_Z)
theorem p22_W : ∀ c ∈ p22_K, CutP p22_R p22_T c := cutsGood p22_Y (by decide +kernel)
theorem p22_Q : p22_P.all (sepOK p22_T) = true := by decide +kernel
def p22_D3 : List StD := []
theorem p22_I3 : LevelN p22_R p22_T 3 p22_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p22_D4 : List StD := [
mkSt [w10,w2,w30,w0,w3] 0x2b22ae2a61c3c2c1810300428240c08140100600,
mkSt [w2,w30,w0,w3,w9] 0x32ed69662d414345808242c28204c04603100600,
mkSt [w1,w2,w72,w9,w4] 0x2ab6b2ea61c38142c2000502404803460483100680,
mkSt [w27,w1,w2,w72,w4] 0x22282421d806044208424181430080100500]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p22_C4x0 : levelOK p22_T p22_K p22_P 3 (p22_D3.map Prod.fst) ((p22_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p22_I4 : LevelN p22_R p22_T 4 p22_D4 := levelStep p22_B p22_W p22_Q p22_I3 (chunks 64 p22_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p22_D5 : List StD := [
mkSt [w10,w2,w6,w0,w3,w4] 0x1072ceb7b96d0396a0004038302c1c181004340028240c08201400140801,
mkSt [w2,w6,w0,w3,w9,w4] 0x62489880c79f79a6161124040140c585450204c242c485c38283408043000548901,
mkSt [w1,w2,w0,w3,w102,w4] 0x5c29e3100d09284a44c1c3214904018385c20307048680058442404140801c01801400d18804,
mkSt [w25,w1,w2,w0,w3,w4] 0x25ded9c028261d80304420146024744838085900580,
mkSt [w1,w2,w30,w6,w0,w3] 0x27fb68272d26029818604068482014446404383024085c00900781,
mkSt [w1,w2,w30,w0,w3] 0x2cdb2b28359962747430146844642408603820485c01802510682,
mkSt [w1,w2,w0,w3,w126,w4] 0x10d6200b416a541ee4287418601468205834480004383000c03108682,
mkSt [w193,w1,w2,w0,w3,w4] 0x3dde79e72ea61d9474241858340430146070084800203900780,
mkSt [w1,w2,w90,w0,w3,w4] 0x3666f26ea615d954405c301460245844082018780100680,
mkSt [w254,w1,w2,w0,w3,w4] 0x18e93493042ca180e485c60307c5c7814602408702038001801803c03910683,
mkSt [w1,w2,w0,w9,w8,w4] 0x16b5714c5b9ac5a90728241460205c54003480584804303805108701,
mkSt [w1,w61,w2,w0,w3,w4] 0x6ba4429e8c078284b15640a6aa4186024205834704c088030380001805c00c06005805518686,
mkSt [w36,w1,w2,w0,w3,w4] 0x2dde61c028261d804044205c3824301460580900580,
mkSt [w1,w2,w21,w0,w3,w4] 0x27481289a564d25052068205c783810002448301401806d08582,
mkSt [w1,w83,w2,w0,w3,w4] 0x2e229a2a61aa619440205c783424001430486100580,
mkSt [w65,w1,w2,w0,w3,w4] 0x2e625aa61da61d9440683014384808785c202500580,
mkSt [w27,w1,w2,w0,w8,w4] 0x222e029125202810186044208414800838300004d00581,
mkSt [w1,w2,w72,w3,w8,w4] 0x374242b2ea59a1d82090241460584408804838740007d00681,
mkSt [w1,w2,w72,w3,w4] 0x39d96c1955cb6680946090584478242014380800304800c08110702,
mkSt [w1,w135,w2,w0,w3,w4] 0xe150caa01f45c9cc520206064185c44240048083801808d08582,
mkSt [w1,w2,w0,w3,w115,w4] 0x19c5b00a4a303218c12074143890486858440824600000c09908602,
mkSt [w1,w2,w0,w3,w259,w4] 0x3772eeea66155d947414389048685844083060240100680,
mkSt [w1,w2,w0,w60,w3,w4] 0x32ea222ea615d59494301424605844082018380100600,
mkSt [w43,w1,w2,w0,w3,w4] 0xd0003090052c014aa40005094a058301460382408702018000b000d10682,
mkSt [w1,w2,w260,w0,w3,w4] 0x2e66ea6ea6159d94301460244458087418380100580,
mkSt [w1,w261,w2,w0,w3,w4] 0x1c46354c5e809320263074a060301824584408702014380000c0b908702]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p22_C5x0 : levelOK p22_T p22_K p22_P 4 (p22_D4.map Prod.fst) ((p22_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p22_I5 : LevelN p22_R p22_T 5 p22_D5 := levelStep p22_B p22_W p22_Q p22_I4 (chunks 64 p22_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C5x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p22_D6 : List StD := [
mkSt [w1,w2,w6,w0,w3,w4] 0x7e6c81b70a1bb05006d89c3766c7418306c6860640800204414245c3802000800c00000401118786,
mkSt [w10,w1,w2,w0,w3,w4] 0x6d3aa26e0a076dbba735420070c746c582430080034146020183802000c00002c02918685,
mkSt [w18,w1,w2,w0,w3,w4] 0xd062e6c30735d836454582520c20145800704408301802004404000000d18485,
mkSt [w1,w2,w0,w3,w9,w4] 0x4d7a00ab4293603a687410048a430705c60245820784802004004804c00118485,
mkSt [w1,w12,w2,w0,w3,w4] 0x5e0a1684e0b467410aa1f05402474308460587820245c004404003401807006800d18586,
mkSt [w17,w1,w2,w0,w3,w4] 0x5e0a1684e0ae23057044f310aa47430145c08388824188c0004003401807807400d18586,
mkSt [w1,w2,w0,w3,w8,w4] 0x68a7ed72e5da019bcc8105b8ce018903060581444786c94380848002004007c01804c08405118786,
mkSt [w27,w1,w2,w0,w3,w4] 0x633a768538a819dda0a25c5068074786c1460185c300838200004001804c09008918605,
mkSt [w1,w19,w2,w0,w3,w4] 0x60c60358a138f16009a0a172f8182430586444480094603801802400c09c09402118586,
mkSt [w66,w1,w2,w0,w3,w4] 0x60d80360b0da8c96318b3e00d8146058782098004824089c380180a000c0a80a402118606,
mkSt [w1,w2,w7,w0,w3,w4] 0x5081025e00167048435f0464a49c201470588808241848000400180340ac00c02118586,
mkSt [w71,w1,w2,w0,w3,w4] 0x11404d8a89e95421400d64881838547024001408600400bc0b401802118485]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p22_C6x0 : levelOK p22_T p22_K p22_P 5 (p22_D5.map Prod.fst) ((p22_D6.drop (0*64)).take 64) = true := by decide +kernel
theorem p22_I6 : LevelN p22_R p22_T 6 p22_D6 := levelStep p22_B p22_W p22_Q p22_I5 (chunks 64 p22_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C6x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p22_D7 : List StD := [
mkSt [w1,w2,w0,w3,w4] 0xdab5b65b1026d031207430485808600c14205c78240004006402004c03400118686]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p22_C7x0 : levelOK p22_T p22_K p22_P 6 (p22_D6.map Prod.fst) ((p22_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p22_I7 : LevelN p22_R p22_T 7 p22_D7 := levelStep p22_B p22_W p22_Q p22_I6 (chunks 64 p22_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C7x0
  ))
theorem p22_L : LowN p22_R p22_T 8 := lowSearch p22_B p22_I7 (by decide +kernel)
def p24_T : Nat := 0xeee8eac8eee8eac8eee8eac8eee8eac8
def p24_R : List Nat := [0, 1, 2, 3, 4]
def p24_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,5,21)]
theorem p24_B : baseOK p24_T p24_R p24_E = true := by decide +kernel
theorem p24_S0 : SliceN p24_R p24_T (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]) := mkSlice (w:=0) p24_B p17_B p17_L (by decide +kernel)
theorem p24_S1 : SliceN p24_R p24_T (0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]) := mkSlice (w:=0) p24_B p20_B p20_L (by decide +kernel)
theorem p24_S2 : SliceN p24_R p24_T (0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]) := mkSlice (w:=16) p24_B p4_B p4_L (by decide +kernel)
theorem p24_S3 : SliceN p24_R p24_T (0xffff0000ffff0000ffff0000ffff,4,[0, 1, 2, 3]) := mkSlice (w:=0) p24_B p23_B p23_L (by decide +kernel)
theorem p24_S4 : SliceN p24_R p24_T (0xff000000ff000000ff000000ff0000,4,[0, 1, 2]) := mkSlice (w:=16) p24_B p4_B p4_L (by decide +kernel)
theorem p24_S5 : SliceN p24_R p24_T (0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) p24_B p10_B p10_L (by decide +kernel)
def p24_Z : List SliceD := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,5,[0, 1, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,5,[0, 1, 2, 4]),(0xf0f00000f0f00000f0f00000f0f0000,4,[0, 1, 3]),(0xffff0000ffff0000ffff0000ffff,4,[0, 1, 2, 3]),(0xff000000ff000000ff000000ff0000,4,[0, 1, 2]),(0xffff0000ffff0000ffff0000ffff0000,5,[0, 1, 2, 3])]
theorem p24_Y : ∀ s ∈ p24_Z, SliceN p24_R p24_T s := by
  unfold p24_Z
  simp only [List.forall_mem_cons]
  exact ⟨p24_S0,p24_S1,p24_S2,p24_S3,p24_S4,p24_S5,by simp⟩
noncomputable def p24_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2010101,dC 0x2,dC 0x2010103,dC 0x4,dC 0x2010102,dC 0x2010105,dC 0x2010106,dC 0x6,dC 0x2010201,dC 0x2010202,dC 0x2010203,dC 0x2010205,dC 0x2010206,dC 0x2010301,dC 0x2010303,dC 0x2010302,dC 0x2010305,dC 0x2010306,dC 0x2010401,dC 0x2010403,dC 0x2010402,dC 0x2010405,dC 0x2010406,dC 0x3010202,dC 0x3,dC 0x3010203,dC 0x3010302,dC 0x3010303,dC 0x3010306,dC 0x4010401,dC 0x3010201,dC 0x4010206,dC 0x5,dC 0x4010102,dC 0x3010301,dC 0x3020202,dC 0x3020203,dC 0x3020206,dC 0x4020101,dC 0x3020302,dC 0x3020303,dC 0x3020201,dC 0x3020301,dC 0x4020306,dC 0x4020402,dC 0x3010102,dC 0x3010401,dC 0x3020101,dC 0x3020402,dC 0x4030206,dC 0x4030101,dC 0x4030102]
def p24_P : List (Nat × Nat) := [(5,6),(2,6),(9,12),(8,9),(20,21),(0,3),(17,21),(3,4),(3,12),(1,9),(3,20),(4,19),(5,9),(9,17),(5,21),(2,3),(3,10),(3,18),(6,12),(4,6),(6,20),(1,3),(18,26),(10,26),(3,5),(3,17),(24,26),(5,13),(10,14),(9,10),(4,13),(12,13),(10,11),(18,19),(5,7),(8,14),(12,14),(17,19),(26,28),(6,10),(1,7),(2,7),(18,22),(24,25),(21,28),(17,25),(1,11),(2,11),(20,22)]
noncomputable def p24_K : List CutV := p24_C.map (mkCut p24_Z)
theorem p24_W : ∀ c ∈ p24_K, CutP p24_R p24_T c := cutsGood p24_Y (by decide +kernel)
theorem p24_Q : p24_P.all (sepOK p24_T) = true := by decide +kernel
def p24_D3 : List StD := []
theorem p24_I3 : LevelN p24_R p24_T 3 p24_D3 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p24_D4 : List StD := [
mkSt [w22,w2,w68,w3,w4] 0x3ab72ea669c38302c201810080034281c240c0500700,
mkSt [w10,w1,w0,w31,w4] 0x1961d95d950305c58040038241900400,
mkSt [w1,w2,w68,w31,w4] 0x25eea5e25d8305c580c1820003810240500580,
mkSt [w124,w1,w2,w68,w4] 0x2ae8025e1c05c181c3058003804240c1100580,
mkSt [w1,w2,w68,w3,w38] 0x25eea5e25d8305c580c1828003810240500580,
mkSt [w70,w1,w2,w68,w3] 0x2ea4021ddc03058041c5c00241838100d00580,
mkSt [w2,w6,w68,w3,w4] 0x21b2eea6194300c08382400041c5c10581900600,
mkSt [w1,w2,w68,w3,w4] 0x25eea5e21d8705c580c181c003824100500580,
mkSt [w1,w2,w0,w544,w4] 0x262ea61ddd8705c5804100c003824184100580,
mkSt [w89,w1,w2,w31,w4] 0x2aea66018005c58100c0070382440180500580,
mkSt [w89,w124,w1,w2,w4] 0x29e621d99945c3c580c18703824100500500,
mkSt [w89,w70,w1,w2,w3] 0x29e621d8000583c5c107024380c180500500,
mkSt [w1,w2,w0,w31,w38] 0x29e6221999458706804100024180c4d00500,
mkSt [w70,w1,w2,w0,w31] 0x2a6001d9980705804405c241838100d00500,
mkSt [w1,w6,w0,w31,w4] 0x21aa6661d94704c5c40180c0068380500500,
mkSt [w1,w2,w545,w3,w4] 0x25eea5e21d8705c580c181c003824100500580,
mkSt [w1,w2,w0,w31,w4] 0x262ea61ddd8705c5804100c003824184100580,
mkSt [w124,w70,w1,w2,w0] 0x29e621d8000043c5c106c18380c582500500,
mkSt [w316,w1,w0,w3,w4] 0x226a615dd946c5c58684c003824541500500,
mkSt [w316,w2,w0,w3,w4] 0x226a61d95946c382400103c5c14580d00500,
mkSt [w40,w1,w2,w3,w4] 0x2aea26018005c587c10007038243c180500580,
mkSt [w1,w2,w32,w56,w4] 0x29f2e9e61d8705c58848018140038243c0500600,
mkSt [w25,w1,w2,w32,w4] 0x22a26159d945c84046c583c3818240900500,
mkSt [w1,w2,w32,w30,w3] 0x26dea5e21e070585c841814002438080500580,
mkSt [w154,w1,w2,w0,w4] 0x26a40219d805c043c6c58381824100d00500,
mkSt [w40,w1,w2,w56,w4] 0x2aea26018005c588010007038243c180500580,
mkSt [w25,w40,w1,w2,w4] 0x2a61ddd9994948400185830543c042500500,
mkSt [w40,w1,w2,w30,w3] 0x32ea6258000588c947c84007024543c180500600,
mkSt [w47,w40,w1,w2,w3] 0x2a5a001dd805880705c3c243810041900500,
mkSt [w25,w1,w2,w0,w4] 0x2aea6159d945c0484786c583c3818240d00580,
mkSt [w1,w2,w56,w30,w0] 0x272a6ea61d8705c58048480140038243c1900600,
mkSt [w243,w1,w2,w3,w4] 0x2aea62018005c58100c007038243c180500580,
mkSt [w25,w1,w2,w30,w0] 0x2aea615d994045c78846c583c1838240d00580,
mkSt [w47,w25,w1,w2,w0] 0x2eea621dddc04546c585c343c0018243900580,
mkSt [w1,w2,w180,w24,w3] 0x2e66aa5e254704c5c0c101c000408681900580,
mkSt [w1,w2,w24,w181,w3] 0x2aeaea6e9d8585c8c100c1c080098241900580,
mkSt [w1,w2,w0,w546,w4] 0x21de61d99945c587010403824180d00480,
mkSt [w317,w2,w24,w3,w4] 0x2ea6221dd9458847068100c003004081d00580,
mkSt [w1,w2,w24,w3,w51] 0x2eea66621d45c704c080c1c001804106900580,
mkSt [w1,w547,w0,w3,w4] 0x36ab32a6698386848700c08140034244c101900680,
mkSt [w244,w1,w0,w3,w4] 0x29a6161dd9458701068180c244c041500500,
mkSt [w50,w1,w2,w180,w3] 0x1e5d5d61d94587018540824045c3d00480,
mkSt [w74,w1,w2,w0,w55] 0x2edae5add94580c18346c483c0424385500580,
mkSt [w1,w2,w0,w55,w8] 0x2a66ea61d944c5804b0ac7c3c2438180d00580,
mkSt [w548,w1,w2,w3,w4] 0x2aea62018005c581008007038303c180500580,
mkSt [w74,w1,w2,w0,w136] 0x26daa5a1d9468ac18b46c48100c04245500580,
mkSt [w74,w1,w2,w0,w51] 0x265e69e61d80c586c4810080424385500500,
mkSt [w549,w1,w2,w3,w4] 0x2aea62018005c581008007038243c180500580,
mkSt [w1,w2,w0,w550,w4] 0x21de61d99945c5804103c3824180d00480,
mkSt [w50,w1,w2,w181,w3] 0x2ae96561d94585c1070a854082418043d00580,
mkSt [w551,w2,w0,w3,w4] 0x3fb732a21d45ca8704c488c601008140038680c0500780,
mkSt [w245,w2,w0,w3,w4] 0x2ea621d9594581870684c103c2404140d00580,
mkSt [w552,w1,w2,w0,w4] 0x2aea6159d945c7084786c583c3818240d00580,
mkSt [w50,w1,w2,w3,w51] 0x266a59a61d84c187054084824045c3d00500,
mkSt [w1,w2,w553,w3,w4] 0x25e6a5e25d85c5808181c003810300500500,
mkSt [w1,w2,w0,w136,w8] 0x1d9a1d955504c5804103c38180d00400,
mkSt [w1,w318,w0,w8,w4] 0x219a1d955505c4c70108038180d00400,
mkSt [w1,w2,w0,w8,w51] 0x3325e1d99945818046c4c48103c3824680d00600,
mkSt [w128,w1,w2,w0,w4] 0x26a42019d805c04786c58381824840d00500,
mkSt [w1,w2,w554,w3,w4] 0x25e6a5e25d85c5808181c003810240500500]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p24_C4x0 : levelOK p24_T p24_K p24_P 3 (p24_D3.map Prod.fst) ((p24_D4.drop (0*64)).take 64) = true := by decide +kernel
theorem p24_I4 : LevelN p24_R p24_T 4 p24_D4 := levelStep p24_B p24_W p24_Q p24_I3 (chunks 64 p24_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p24_C4x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p24_D5p0 : List StD := [
mkSt [w22,w28,w2,w0,w3,w4] 0x11741e7735855a94e400343050184440141008004c483c38240c0400140881,
mkSt [w22,w1,w2,w0,w3,w4] 0x2632a62a62ea61d83014382418540c3c4c5c580500600,
mkSt [w10,w28,w1,w0,w3,w4] 0x21f261ed56a61d803064145c580400546038241800100601,
mkSt [w10,w1,w2,w0,w3,w4] 0x2632a62a62ea61d830145c58044c3c540c38241900600,
mkSt [w28,w1,w2,w68,w3,w4] 0x26aea5aa614801c0305c581060180c004c382400500581,
mkSt [w1,w2,w0,w68,w3,w4] 0x2eeaea6222199994386c04686010005c240c4d00580,
mkSt [w1,w2,w68,w3,w4] 0x2237332eee8706810606c382418585c040c4d00680,
mkSt [w555,w1,w2,w0,w3,w4] 0x130b10a108289200c401c60186c58100c543c044c00382401000800d10603,
mkSt [w89,w28,w1,w2,w3,w4] 0x132b2a421d592c058100c38543c70184c00042400d00601,
mkSt [w28,w1,w2,w0,w31,w4] 0x2e2ae62de1c800185c7068180c4010004c380401500581,
mkSt [w1,w2,w0,w3,w31,w4] 0x2ee9e662221999945c24706804100038180c4d00580,
mkSt [w1,w2,w0,w31,w4] 0x2237332eee8706810406c382418585c040c4d00680,
mkSt [w556,w1,w2,w0,w3,w4] 0xb04a1092071c81c0c0118505c7068180c543c4c00380401000001910583,
mkSt [w124,w28,w1,w2,w0,w4] 0xef156e8e619d940184c38543c6c580c0004102401900601,
mkSt [w28,w1,w2,w0,w3,w38] 0x616a0898871e81c0d8510306c68100c240464444c0001001800d10503,
mkSt [w70,w28,w1,w2,w0,w3] 0x373156e9261dcdc070680024543c5c1810044c380c01d00681,
mkSt [w70,w1,w2,w0,w3] 0x3b2f2f72e1c703c58186c5468104c24385c0c0500700,
mkSt [w28,w1,w6,w0,w3,w4] 0x32bfbbb72a615c18704c5c5800180c64603c546838240500780,
mkSt [w28,w2,w6,w0,w3,w4] 0x2ebfbb72ea61d418700c085c58184c4440543c1038240500780,
mkSt [w22,w1,w6,w0,w3,w4] 0x21b2eee61aa61814704c145c585418006838240400100601,
mkSt [w10,w2,w6,w0,w3,w4] 0x1db2eea1da61d814700c08145c5804001038241800100601,
mkSt [w2,w6,w0,w24,w3,w4] 0x51651681e71a1c6594488306c047c780838247454184c3c00105c5802548801,
mkSt [w54,w2,w6,w0,w3,w4] 0x24ffb53242ea61d86c7c785c4c4458180c543c1038240002500781,
mkSt [w1,w6,w0,w3,w8,w4] 0x88c81041e70719650a490383824709058488c8474180c5c5400683c0402948881,
mkSt [w27,w1,w6,w0,w3,w4] 0xe746057b9ac5a9283b470908c5c74040c6458884c0068183c543802940881,
mkSt [w1,w2,w32,w6,w3,w4] 0x2f95b412e98a1d903870942468848008045854003c1802d00701,
mkSt [w1,w2,w0,w134,w3,w4] 0x3c3324dc0ceca272e071b60705c5868047c0c100038243c1802c00801110683,
mkSt [w40,w1,w2,w6,w3,w4] 0x339372ea61d581543894244c84801000701858543c0402500701,
mkSt [w40,w1,w2,w0,w3,w4] 0x2a62699695661d94585c2404543c384c6c1100500,
mkSt [w40,w1,w2,w3,w4] 0x1ffa36a72a4948c7c702454183c585c386c104c0500780,
mkSt [w1,w2,w56,w6,w0,w4] 0x2382b4162e921d94387094482484041080543c00581803100701,
mkSt [w1,w2,w0,w3,w102,w4] 0xec02b33bdf0be81e06dc60705c4c580484107c0c003818243c03000001110703,
mkSt [w25,w1,w2,w6,w0,w4] 0x274b26ea61d5815438946884040c006c24543c185802900681,
mkSt [w25,w1,w2,w0,w3,w4] 0x26dd9ae569661d94187c382404543c5c70680d00580,
mkSt [w25,w1,w2,w0,w4] 0x1ebfb6a32a48884786c04543c2418385c7058680d00780,
mkSt [w1,w2,w30,w6,w0,w3] 0x350320322ea61d9470244c9480040c840058543c1803500681,
mkSt [w1,w2,w30,w0,w3] 0x820ef4b96d62c7090947c843c6c5424185804385c0c4d40800,
mkSt [w47,w1,w2,w6,w0,w3] 0xd1313392cae481cc2709c306c246880041054385c583c001803001002d10683,
mkSt [w28,w1,w2,w0,w3,w4] 0x3371609d2210e14880f182840606c68100c382404543c4c0001001c01400518584,
mkSt [w1,w2,w6,w0,w3,w4] 0x5cd1c362010b2c38a07213860a06c3894244c8480040c54583c001803401002802518704,
mkSt [w1,w2,w0,w557,w3,w4] 0x3fbfb72eeee6a66458383004687c3c081400185c244c1100780,
mkSt [w558,w1,w2,w0,w3,w4] 0x1f6e9ea5e201d9505c046c4c3c102418540c00385801003d00682,
mkSt [w1,w2,w0,w3,w559,w4] 0xd6210b52728296a8283858704c6804847c0c34243c1801004508682,
mkSt [w315,w1,w2,w0,w3,w4] 0x2a36b22ae2ea61d8704c3c382418541068480c5c0500680,
mkSt [w22,w10,w1,w0,w3,w4] 0x1d6e9d69d669d500705c3c945854180c38240500580,
mkSt [w22,w10,w2,w0,w3,w4] 0x256ea56a562a5500705c584c0c10185438240500580,
mkSt [w22,w2,w0,w24,w3,w4] 0x10741cd62d6b5a528398583c3830044c1c7c0c08005c1824106940800,
mkSt [w54,w22,w2,w0,w3,w4] 0x3712ecaa8261d9405838687c00848018146c3c4c1003900681,
mkSt [w1,w2,w0,w560,w3,w4] 0x807b9ac0a9394207348585c701894904c0c1400382410045401005108782,
mkSt [w561,w1,w2,w0,w3,w4] 0xb6418b7b16e6b16a4a06c540c145c5804683c4c18100800382540800,
mkSt [w1,w2,w0,w3,w126,w4] 0x332ddea665d999945c247054480410803868180d00600,
mkSt [w193,w1,w2,w0,w3,w4] 0x31aea58cda01d9505c7054688058044c3c0c381801005900602,
mkSt [w10,w1,w0,w3,w8,w4] 0x2ab5df2aedea61d82470105c4c48043c58680c381900680,
mkSt [w27,w10,w1,w0,w3,w4] 0x1ab7348b6b16a4a1662c705c68043c945888144c0c54381805508701,
mkSt [w54,w1,w2,w24,w3,w4] 0x26a6eeea41964180685c5810304c180838245400100581,
mkSt [w1,w2,w24,w20,w3,w4] 0x112ca3023dcd62d6a49c245c70509054987c080c1c00303804184c1140900,
mkSt [w1,w562,w2,w0,w3,w4] 0x2351c35e0b0b1050902e04030e46c5c5818044c103c98382468740c01000c00800518704,
mkSt [w109,w1,w2,w0,w3,w4] 0x21ea61c200261d80703824184c5c5804103d00500,
mkSt [w1,w2,w24,w3,w42,w4] 0xad734944a92940c4750245c309c5468100c00387018084c06108701,
mkSt [w1,w2,w0,w3,w246,w4] 0x32e6a44604d955c38342458047068543c10000c184c01006900702,
mkSt [w247,w1,w2,w0,w3,w4] 0x25dd998002a61d80803824184c5c7068100d00500,
mkSt [w1,w2,w116,w0,w3,w4] 0x2bb7b72ea601c0005c6c189424a04c7c380454583c1100700,
mkSt [w1,w563,w2,w0,w3,w4] 0x1626b16a62d4942d07346c5c58184c10143c54040c382404d08681,
mkSt [w1,w2,w0,w3,w564,w4] 0x2aaea661e1d9999c585c706854100038040c4d00580]
set_option maxHeartbeats 0 in
noncomputable def p24_D5p1 : List StD := [
mkSt [w565,w1,w2,w0,w3,w4] 0x2b2864628d41d9505c046c680c2418543c10384c01007100602,
mkSt [w54,w1,w2,w0,w180,w3] 0x26da5a256a24021c6ca424540c385c10044c5807500581,
mkSt [w1,w2,w0,w180,w3] 0x86f36b01d5ac870a86810545c3c0424580c384c07908681,
mkSt [w54,w50,w1,w2,w3,w4] 0xf83e0f735eb511e83945c5888a870541030a008a418384c042540800,
mkSt [w74,w1,w2,w0,w9,w4] 0x32e6d9ac25ac2580585c0c18346c4c244004385400900601,
mkSt [w1,w2,w0,w9,w8,w4] 0x3f77333fb72ea71c5c4c5804acb0107c40684824380c1900780,
mkSt [w1,w61,w2,w0,w3,w4] 0x2f26f72ea61ddd984c185c5870541080482438040d00680,
mkSt [w36,w1,w2,w0,w3,w4] 0x21ea61e55d661d9470382418540c5c583c0500500,
mkSt [w248,w1,w2,w0,w3,w4] 0x2662a99555a61d94685c2418540c386c4c1100500,
mkSt [w1,w2,w0,w3,w55,w9] 0x36ab2eeea61d94b46c4c043cac407c806824180c08100681,
mkSt [w1,w2,w0,w3,w55] 0xec378cbaeba48b46c68ac7c3c38545c2418040c4c08908701,
mkSt [w1,w2,w216,w0,w3,w4] 0x4056fc18f10bd9a8481cd9c36605c702494b854044c847c0c003858183c03000001150803,
mkSt [w1,w566,w2,w0,w3,w4] 0x262ea62a61d99954705c58044c10803824180d00580,
mkSt [w1,w2,w0,w567,w3,w4] 0x2f2f2ea6661999a038580468541810005c6c0c4d00600,
mkSt [w74,w27,w1,w2,w0,w4] 0x37f7f79b72eb61d45c741848bcb46cb81038580c68240500780,
mkSt [w74,w1,w2,w0,w42,w4] 0x826acc05b0665a3062804bc5c24306c7054105878384808d08681,
mkSt [w1,w2,w568,w0,w3,w4] 0xed0090c02481c024511406c5c946458044c847c0c183c2401002d10682,
mkSt [w241,w1,w2,w0,w3,w4] 0x21ea61e55d661d94705c58044c3c38240c1900500,
mkSt [w1,w2,w157,w0,w3,w4] 0x2a72ea6ea61d5954705c58044c847c3c3824180d00600,
mkSt [w256,w1,w2,w0,w3,w4] 0xa8090081400850c018510345870683824044c3c0c1801001910502,
mkSt [w569,w1,w2,w0,w3,w4] 0x32a6b36b2dea61d860580c386c18881008044c5c2500680,
mkSt [w110,w1,w2,w0,w3,w4] 0x21ea61a61da61d94705c58044c103824185500500,
mkSt [w50,w1,w2,w20,w3,w4] 0x2b2ae825556e8014185c5810a870600c0438243c00100601,
mkSt [w1,w2,w0,w3,w249,w4] 0x8c1ee6ad8b584263985c24a81870544c488c60100c003868043c01009540882,
mkSt [w250,w1,w2,w0,w3,w4] 0x265d998002a61d803c3858044c5c7068100d00500,
mkSt [w1,w2,w0,w181,w20,w3] 0x3b83413aea5de21c58709054c060100c00a8044c243c09900701,
mkSt [w1,w2,w0,w181,w3] 0x77778b8214ac870a890c010543c245c3804584c0c09d08701,
mkSt [w1,w182,w2,w0,w3,w4] 0xbf8dc7c070ec3c72e07d8505c6c9024048480a4540c38183c4c02c00801110703,
mkSt [w570,w1,w2,w0,w3,w4] 0x21ea61e61da61d9470382418880c5c4c580500500,
mkSt [w1,w2,w0,w3,w571,w4] 0x2eea2226661dd9d85c246870100c00384c183d00580,
mkSt [w572,w1,w2,w0,w3,w4] 0x2aea66452101d9505c6c4c105804543c68380c0100a500582,
mkSt [w50,w1,w2,w3,w42,w4] 0x826ad83594055a3062824a038049c7030543c188c5c080a108681,
mkSt [w314,w1,w2,w0,w3,w4] 0x6027c05e8d18ec50907201072c070685c58181024540cb00038044c01001800001518704,
mkSt [w65,w1,w2,w0,w3,w4] 0x21e999e61da61d94705c5804680c3824185500500,
mkSt [w27,w1,w2,w0,w8,w4] 0x259a41a2211c18105c105804483c38180c00900481,
mkSt [w1,w2,w0,w8,w42,w4] 0xad2558440d28398e7305c0470304c48103c386c58680c0a908681,
mkSt [w251,w1,w2,w0,w3,w4] 0x2261998002a61d803c5c580468386c4c0c1100500,
mkSt [w1,w135,w2,w0,w3,w4] 0x3a32ee3b72ea62d83858706884bc04000c5c243c541900700,
mkSt [w573,w1,w2,w0,w3,w4] 0x48629285250b52507b07014385818540c3c4c245c0404108601,
mkSt [w1,w2,w0,w574,w3,w4] 0x3bb3b2eaaa9d99d838a82418680460100c005c6c4c3d00700,
mkSt [w27,w1,w2,w0,w3,w136] 0x1632ea25a58021d87038b810044c3c5c6824180c0b100601,
mkSt [w1,w2,w0,w3,w136] 0xdc337bba80a48b46c68103c38544c5c2418040c0b508681,
mkSt [w1,w2,w33,w0,w3,w4] 0x280c0021801c61101c61440709438844424180c4c54580401003110602,
mkSt [w242,w1,w2,w0,w3,w4] 0x21ea61a61da61d9470382418540c5c58044d00500,
mkSt [w1,w137,w2,w0,w3,w4] 0x2a32adeae1ea61d8702438ac184c0c10585c045500600,
mkSt [w575,w1,w2,w0,w3,w4] 0x2a90060801881001851130186c10382404540c4c5801000d10502,
mkSt [w317,w1,w2,w0,w3,w4] 0x495a56c4ad464a0f62854583c382418880c046c5c4c0b908601,
mkSt [w252,w1,w2,w0,w3,w4] 0x1424318752d07527073068bc5c58704c0c3c241838540bd08601,
mkSt [w1,w318,w2,w0,w3,w4] 0x1424296852707318c528545c58704c10802418380c0c108581,
mkSt [w125,w1,w2,w0,w3,w4] 0x4a6a9ac59966525173058a0103824184c0c54046c5c3c0c508681,
mkSt [w1,w2,w0,w3,w51,w42] 0x839ed2ad8c5a9294ac24045c38684c3c0c0814006c307010540c940801,
mkSt [w1,w2,w0,w3,w51] 0xaea2a9587a5803068043c243854105c0c4c0d00cd10582]
noncomputable def p24_D5 : List StD := p24_D5p0 ++ p24_D5p1
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p24_C5x0 : levelOK p24_T p24_K p24_P 4 (p24_D4.map Prod.fst) ((p24_D5.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p24_C5x1 : levelOK p24_T p24_K p24_P 4 (p24_D4.map Prod.fst) ((p24_D5.drop (1*64)).take 64) = true := by decide +kernel
theorem p24_I5 : LevelN p24_R p24_T 5 p24_D5 := levelStep p24_B p24_W p24_Q p24_I4 (chunks 64 p24_D5 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p24_C5x0
  · exact p24_C5x1
  ))
set_option maxHeartbeats 0 in
noncomputable def p24_D6 : List StD := [
mkSt [w28,w1,w2,w0,w3,w4] 0x6e3de3770a1b9c50507ca88c16070685c543c18006c58100c4c38240402001c00800001001400518787,
mkSt [w1,w2,w6,w0,w3,w4] 0xf99a205c742198e1e1c19960c140a07094884c8438800c006c2418543c585c0402003400800001002802558887,
mkSt [w22,w1,w2,w0,w3,w4] 0x11bdbaf36f192ea47068803c18540c146c384c24585c0401004804003900784,
mkSt [w10,w1,w2,w0,w3,w4] 0x193f2f9af71ad2a470881054584c3c146c5c0c0418382401005c05404d00784,
mkSt [w1,w2,w0,w24,w3,w4] 0x4e3323cac8e8a268dc096606c046818387c54105c24584c06400006110603,
mkSt [w54,w1,w2,w0,w3,w4] 0xad7cabb1aae48a05cc7100870685c7c101804385424584c06400006d10603,
mkSt [w1,w2,w0,w3,w9,w4] 0x6dbe2f536bd0894bc23a890b4586cac387c8024685c18540c044c08400807d10783,
mkSt [w74,w1,w2,w0,w3,w4] 0x3e7da7c949dab289e05100870687c803824580c18545c044c08400808d10683,
mkSt [w192,w1,w2,w0,w3,w4] 0x15004c860a64370c4e1312083058044c383c0cb4189408406402001118504,
mkSt [w39,w1,w2,w0,w3,w4] 0x15004c860a64370c4e131208302418545c3c0c58a86808406402001118504,
mkSt [w1,w2,w0,w20,w3,w4] 0x7df42beb4aec08ead082680a87018c09038103c5c0488244c580c06400009110783,
mkSt [w50,w1,w2,w0,w3,w4] 0x9cfda7c1a9d4ba89d4802406c9010885c04184c583c38240c0640000a110683,
mkSt [w1,w2,w0,w3,w8,w4] 0x9d3c2732e9c25a89dc89c602470903858103c685c18040c0840080a910603,
mkSt [w27,w1,w2,w0,w3,w4] 0xad7cab8acada9205dc302406c905c10685824383c04180c0840080ad10603,
mkSt [w1,w19,w2,w0,w3,w4] 0x1b014c778525b040263b60a4305ca838241018548458040c4c08406402001118684,
mkSt [w66,w1,w2,w0,w3,w4] 0x1701549602a4b80e4e1304c43058043c3810544cb4180c08406402001118584,
mkSt [w1,w2,w0,w3,w42,w4] 0x2468026020130c525331c3282e06838103c6c705c540c4c0640c800800118504]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p24_C6x0 : levelOK p24_T p24_K p24_P 5 (p24_D5.map Prod.fst) ((p24_D6.drop (0*64)).take 64) = true := by decide +kernel
theorem p24_I6 : LevelN p24_R p24_T 6 p24_D6 := levelStep p24_B p24_W p24_Q p24_I5 (chunks 64 p24_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p24_C6x0
  ))
set_option maxHeartbeats 0 in
noncomputable def p24_D7 : List StD := [
mkSt [w1,w2,w0,w3,w4] 0x233b35f22e8706838103c6c241854585c040c4c08406402000800100705]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p24_C7x0 : levelOK p24_T p24_K p24_P 6 (p24_D6.map Prod.fst) ((p24_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p24_I7 : LevelN p24_R p24_T 7 p24_D7 := levelStep p24_B p24_W p24_Q p24_I6 (chunks 64 p24_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p24_C7x0
  ))
theorem p24_L : LowN p24_R p24_T 8 := lowSearch p24_B p24_I7 (by decide +kernel)
def p25_T : Nat := 0xfefefee8fefefee8fefefee8fefefee8
def p25_R : List Nat := [0, 1, 2, 3, 4]
def p25_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p25_B : baseOK p25_T p25_R p25_E = true := by decide +kernel
theorem p25_S0 : SliceN p25_R p25_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p25_B p10_B p10_L (by decide +kernel)
theorem p25_S1 : SliceN p25_R p25_T (0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4]) := mkSlice (w:=0) p25_B p12_B p12_L (by decide +kernel)
def p25_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4]),(0xff00ff00ff00ff00ff00ff00ff00ff,7,[0, 1, 2, 4])]
theorem p25_Y : ∀ s ∈ p25_Z, SliceN p25_R p25_T s := by
  unfold p25_Z
  simp only [List.forall_mem_cons]
  exact ⟨p25_S0,p25_S1,by simp⟩
noncomputable def p25_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2]
def p25_P : List (Nat × Nat) := [(4,5)]
noncomputable def p25_K : List CutV := p25_C.map (mkCut p25_Z)
theorem p25_W : ∀ c ∈ p25_K, CutP p25_R p25_T c := cutsGood p25_Y (by decide +kernel)
theorem p25_Q : p25_P.all (sepOK p25_T) = true := by decide +kernel
def p25_D6 : List StD := []
theorem p25_I6 : LevelN p25_R p25_T 6 p25_D6 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p25_D7 : List StD := [
mkSt [w1,w2,w0,w3,w4] 0x2aaaa80000400010082]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p25_C7x0 : levelOK p25_T p25_K p25_P 6 (p25_D6.map Prod.fst) ((p25_D7.drop (0*64)).take 64) = true := by decide +kernel
theorem p25_I7 : LevelN p25_R p25_T 7 p25_D7 := levelStep p25_B p25_W p25_Q p25_I6 (chunks 64 p25_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p25_C7x0
  ))
theorem p25_L : LowN p25_R p25_T 8 := lowSearch p25_B p25_I7 (by decide +kernel)
def p26_T : Nat := 0xfffeffeafffeffeafffeffeafffeffea
def p26_R : List Nat := [0, 1, 2, 3, 4]
def p26_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,0,8),(4,2,18)]
theorem p26_B : baseOK p26_T p26_R p26_E = true := by decide +kernel
theorem p26_S0 : SliceN p26_R p26_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p26_B p7_B p7_L (by decide +kernel)
def p26_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4])]
theorem p26_Y : ∀ s ∈ p26_Z, SliceN p26_R p26_T s := by
  unfold p26_Z
  simp only [List.forall_mem_cons]
  exact ⟨p26_S0,by simp⟩
noncomputable def p26_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p26_P : List (Nat × Nat) := [(4,6),(0,1)]
noncomputable def p26_K : List CutV := p26_C.map (mkCut p26_Z)
theorem p26_W : ∀ c ∈ p26_K, CutP p26_R p26_T c := cutsGood p26_Y (by decide +kernel)
theorem p26_Q : p26_P.all (sepOK p26_T) = true := by decide +kernel
def p26_D4 : List StD := []
theorem p26_I4 : LevelN p26_R p26_T 4 p26_D4 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p26_D5 : List StD := [
mkSt [w1,w2,w0,w3,w4] 0x40000000101]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p26_C5x0 : levelOK p26_T p26_K p26_P 4 (p26_D4.map Prod.fst) ((p26_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p26_I5 : LevelN p26_R p26_T 5 p26_D5 := levelStep p26_B p26_W p26_Q p26_I4 (chunks 64 p26_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p26_C5x0
  ))
theorem p26_L : LowN p26_R p26_T 6 := lowSearch p26_B p26_I5 (by decide +kernel)
def p27_T : Nat := 0xfefefeeafefefeeafefefeeafefefeea
def p27_R : List Nat := [0, 1, 2, 3, 4]
def p27_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10),(4,2,18)]
theorem p27_B : baseOK p27_T p27_R p27_E = true := by decide +kernel
theorem p27_S0 : SliceN p27_R p27_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p27_B p10_B p10_L (by decide +kernel)
def p27_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4])]
theorem p27_Y : ∀ s ∈ p27_Z, SliceN p27_R p27_T s := by
  unfold p27_Z
  simp only [List.forall_mem_cons]
  exact ⟨p27_S0,by simp⟩
noncomputable def p27_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p27_P : List (Nat × Nat) := [(4,6),(0,1)]
noncomputable def p27_K : List CutV := p27_C.map (mkCut p27_Z)
theorem p27_W : ∀ c ∈ p27_K, CutP p27_R p27_T c := cutsGood p27_Y (by decide +kernel)
theorem p27_Q : p27_P.all (sepOK p27_T) = true := by decide +kernel
def p27_D4 : List StD := []
theorem p27_I4 : LevelN p27_R p27_T 4 p27_D4 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p27_D5 : List StD := [
mkSt [w1,w2,w0,w3,w4] 0x40000000101]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p27_C5x0 : levelOK p27_T p27_K p27_P 4 (p27_D4.map Prod.fst) ((p27_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p27_I5 : LevelN p27_R p27_T 5 p27_D5 := levelStep p27_B p27_W p27_Q p27_I4 (chunks 64 p27_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p27_C5x0
  ))
theorem p27_L : LowN p27_R p27_T 6 := lowSearch p27_B p27_I5 (by decide +kernel)
def p28_T : Nat := 0xfffefefafffefefafffefefafffefefa
def p28_R : List Nat := [0, 1, 2, 3, 4]
def p28_E : List (Nat × Nat × Nat) := [(0,0,1),(1,8,10),(2,0,4),(3,2,10),(4,2,18)]
theorem p28_B : baseOK p28_T p28_R p28_E = true := by decide +kernel
theorem p28_S0 : SliceN p28_R p28_T (0x55555555555555555555555555555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) p28_B p6_B p6_L (by decide +kernel)
def p28_Z : List SliceD := [(0x55555555555555555555555555555555,5,[1, 2, 3, 4])]
theorem p28_Y : ∀ s ∈ p28_Z, SliceN p28_R p28_T s := by
  unfold p28_Z
  simp only [List.forall_mem_cons]
  exact ⟨p28_S0,by simp⟩
noncomputable def p28_C : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1]
def p28_P : List (Nat × Nat) := [(8,10),(0,1)]
noncomputable def p28_K : List CutV := p28_C.map (mkCut p28_Z)
theorem p28_W : ∀ c ∈ p28_K, CutP p28_R p28_T c := cutsGood p28_Y (by decide +kernel)
theorem p28_Q : p28_P.all (sepOK p28_T) = true := by decide +kernel
def p28_D4 : List StD := []
theorem p28_I4 : LevelN p28_R p28_T 4 p28_D4 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def p28_D5 : List StD := [
mkSt [w1,w2,w0,w3,w4] 0x40000000101]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p28_C5x0 : levelOK p28_T p28_K p28_P 4 (p28_D4.map Prod.fst) ((p28_D5.drop (0*64)).take 64) = true := by decide +kernel
theorem p28_I5 : LevelN p28_R p28_T 5 p28_D5 := levelStep p28_B p28_W p28_Q p28_I4 (chunks 64 p28_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p28_C5x0
  ))
theorem p28_L : LowN p28_R p28_T 6 := lowSearch p28_B p28_I5 (by decide +kernel)
def ptopT : Nat := 0xfefefee8feeafc88fefefee8feeafc88
def ptopR : List Nat := [0, 1, 2, 3, 4, 5]
def ptopE : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,1,17),(5,5,37)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
theorem ptopS0 : SliceN ptopR ptopT (0x55555555555555555555555555555555,8,[1, 2, 3, 4, 5]) := mkSlice (w:=0) ptopB p2_B p2_L (by decide +kernel)
theorem ptopS1 : SliceN ptopR ptopT (0x33333333333333333333333333333333,8,[0, 2, 3, 4, 5]) := mkSlice (w:=0) ptopB p5_B p5_L (by decide +kernel)
theorem ptopS2 : SliceN ptopR ptopT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,8,[0, 1, 3, 4, 5]) := mkSlice (w:=4) ptopB p11_B p11_L (by decide +kernel)
theorem ptopS3 : SliceN ptopR ptopT (0xff00ff00ff00ff00ff00ff00ff00ff,10,[0, 1, 2, 4, 5]) := mkSlice (w:=0) ptopB p13_B p13_L (by decide +kernel)
theorem ptopS4 : SliceN ptopR ptopT (0xffff0000ffff0000ffff0000ffff,9,[0, 1, 2, 3, 5]) := mkSlice (w:=0) ptopB p18_B p18_L (by decide +kernel)
theorem ptopS5 : SliceN ptopR ptopT (0xffffffff00000000ffffffff,8,[0, 1, 2, 3, 4]) := mkSlice (w:=0) ptopB p22_B p22_L (by decide +kernel)
theorem ptopS6 : SliceN ptopR ptopT (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,8,[0, 1, 3, 4, 5]) := mkSlice (w:=0) ptopB p24_B p24_L (by decide +kernel)
theorem ptopS7 : SliceN ptopR ptopT (0x550055005500550055005500550055,7,[1, 2, 4, 5]) := mkSlice (w:=0) ptopB p3_B p3_L (by decide +kernel)
theorem ptopS8 : SliceN ptopR ptopT (0x555500000000000055550000,4,[1, 2, 3]) := mkSlice (w:=16) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS9 : SliceN ptopR ptopT (0xffff000000000000ffff00000000,7,[0, 1, 2, 3]) := mkSlice (w:=32) ptopB p12_B p12_L (by decide +kernel)
theorem ptopS10 : SliceN ptopR ptopT (0xffffffff00000000ffffffff00000000,8,[0, 1, 2, 3, 4]) := mkSlice (w:=32) ptopB p25_B p25_L (by decide +kernel)
theorem ptopS11 : SliceN ptopR ptopT (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,6,[1, 2, 3, 4, 5]) := mkSlice (w:=1) ptopB p26_B p26_L (by decide +kernel)
theorem ptopS12 : SliceN ptopR ptopT (0x22222222222222222222222222222222,5,[2, 3, 4, 5]) := mkSlice (w:=1) ptopB p7_B p7_L (by decide +kernel)
theorem ptopS13 : SliceN ptopR ptopT (0xffff0000ffff0000ffff0000ffff0000,6,[0, 1, 2, 3, 5]) := mkSlice (w:=16) ptopB p27_B p27_L (by decide +kernel)
theorem ptopS14 : SliceN ptopR ptopT (0xffff000000000000ffff0000,5,[0, 1, 2, 3]) := mkSlice (w:=16) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS15 : SliceN ptopR ptopT (0x5555000055550000555500005555,5,[1, 2, 3, 5]) := mkSlice (w:=0) ptopB p19_B p19_L (by decide +kernel)
theorem ptopS16 : SliceN ptopR ptopT (0x5555000000000000555500000000,4,[1, 2, 3]) := mkSlice (w:=32) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS17 : SliceN ptopR ptopT (0x2222000022220000222200002222,4,[2, 3, 5]) := mkSlice (w:=1) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS18 : SliceN ptopR ptopT (0x50505050505050505050505050505050,5,[1, 3, 4, 5]) := mkSlice (w:=4) ptopB p6_B p6_L (by decide +kernel)
theorem ptopS19 : SliceN ptopR ptopT (0xf0f00000f0f00000f0f00000f0f,5,[0, 1, 3, 5]) := mkSlice (w:=0) ptopB p20_B p20_L (by decide +kernel)
theorem ptopS20 : SliceN ptopR ptopT (0x55550000555500005555000055550000,5,[1, 2, 3, 5]) := mkSlice (w:=16) ptopB p10_B p10_L (by decide +kernel)
theorem ptopS21 : SliceN ptopR ptopT (0xf0f00000f0f00000f0f00000f0f0,5,[0, 1, 3, 5]) := mkSlice (w:=4) ptopB p7_B p7_L (by decide +kernel)
theorem ptopS22 : SliceN ptopR ptopT (0x555555550000000055555555,5,[1, 2, 3, 4]) := mkSlice (w:=0) ptopB p19_B p19_L (by decide +kernel)
theorem ptopS23 : SliceN ptopR ptopT (0x55555555000000005555555500000000,5,[1, 2, 3, 4]) := mkSlice (w:=32) ptopB p10_B p10_L (by decide +kernel)
theorem ptopS24 : SliceN ptopR ptopT (0xf0f0f0f000000000f0f0f0f0,5,[0, 1, 3, 4]) := mkSlice (w:=4) ptopB p7_B p7_L (by decide +kernel)
theorem ptopS25 : SliceN ptopR ptopT (0xf0f0f0f000000000f0f0f0f00000000,5,[0, 1, 3, 4]) := mkSlice (w:=32) ptopB p10_B p10_L (by decide +kernel)
theorem ptopS26 : SliceN ptopR ptopT (0x44444444444444444444444444444444,5,[2, 3, 4, 5]) := mkSlice (w:=2) ptopB p6_B p6_L (by decide +kernel)
theorem ptopS27 : SliceN ptopR ptopT (0xcccccccccccccccccccccccccccccccc,6,[0, 2, 3, 4, 5]) := mkSlice (w:=2) ptopB p28_B p28_L (by decide +kernel)
theorem ptopS28 : SliceN ptopR ptopT (0xaaaa0000aaaa0000aaaa0000aaaa,5,[1, 2, 3, 5]) := mkSlice (w:=1) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS29 : SliceN ptopR ptopT (0x30303030303030303030303030303030,5,[0, 3, 4, 5]) := mkSlice (w:=4) ptopB p6_B p6_L (by decide +kernel)
theorem ptopS30 : SliceN ptopR ptopT (0x3333000033330000333300003333,5,[0, 2, 3, 5]) := mkSlice (w:=0) ptopB p9_B p9_L (by decide +kernel)
theorem ptopS31 : SliceN ptopR ptopT (0x550000005500000055000000550000,4,[1, 2, 5]) := mkSlice (w:=16) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS32 : SliceN ptopR ptopT (0xcc00cc00cc00cc00cc00cc00cc00cc,5,[0, 2, 4, 5]) := mkSlice (w:=2) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS33 : SliceN ptopR ptopT (0xf0f0f0f000000000f0f0f0f,4,[0, 1, 3, 4]) := mkSlice (w:=0) ptopB p23_B p23_L (by decide +kernel)
theorem ptopS34 : SliceN ptopR ptopT (0xf000f000f000f000f000f000f000f0,7,[0, 1, 4, 5]) := mkSlice (w:=4) ptopB p12_B p12_L (by decide +kernel)
theorem ptopS35 : SliceN ptopR ptopT (0xf0000000f0000000f0000000f0,4,[0, 1, 5]) := mkSlice (w:=4) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS36 : SliceN ptopR ptopT (0xf000f000f000f000f000f000f000f,5,[0, 1, 4, 5]) := mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel)
theorem ptopS37 : SliceN ptopR ptopT (0xff00ff0000000000ff00ff00000000,7,[0, 1, 2, 4]) := mkSlice (w:=32) ptopB p12_B p12_L (by decide +kernel)
theorem ptopS38 : SliceN ptopR ptopT (0xffff000000000000ffff,4,[0, 1, 2, 3]) := mkSlice (w:=0) ptopB p21_B p21_L (by decide +kernel)
theorem ptopS39 : SliceN ptopR ptopT (0x440044004400440044004400440044,4,[2, 4, 5]) := mkSlice (w:=2) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS40 : SliceN ptopR ptopT (0x33333333000000003333333300000000,5,[0, 2, 3, 4]) := mkSlice (w:=32) ptopB p10_B p10_L (by decide +kernel)
theorem ptopS41 : SliceN ptopR ptopT (0xff000000ff000000ff000000ff0000,5,[0, 1, 2, 5]) := mkSlice (w:=16) ptopB p14_B p14_L (by decide +kernel)
theorem ptopS42 : SliceN ptopR ptopT (0x500050005000500050005000500050,4,[1, 4, 5]) := mkSlice (w:=4) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS43 : SliceN ptopR ptopT (0x300030003000300030003000300030,4,[0, 4, 5]) := mkSlice (w:=4) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS44 : SliceN ptopR ptopT (0x330033000000000033003300000000,4,[0, 2, 4]) := mkSlice (w:=32) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS45 : SliceN ptopR ptopT (0xf0f0000000000000f0f00000000,4,[0, 1, 3]) := mkSlice (w:=32) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS46 : SliceN ptopR ptopT (0x550055000000000055005500000000,4,[1, 2, 4]) := mkSlice (w:=32) ptopB p4_B p4_L (by decide +kernel)
theorem ptopS47 : SliceN ptopR ptopT (0x3333000000000000333300000000,4,[0, 2, 3]) := mkSlice (w:=32) ptopB p4_B p4_L (by decide +kernel)
def ptopZ : List SliceD := [(0x55555555555555555555555555555555,8,[1, 2, 3, 4, 5]),(0x33333333333333333333333333333333,8,[0, 2, 3, 4, 5]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,8,[0, 1, 3, 4, 5]),(0xff00ff00ff00ff00ff00ff00ff00ff,10,[0, 1, 2, 4, 5]),(0xffff0000ffff0000ffff0000ffff,9,[0, 1, 2, 3, 5]),(0xffffffff00000000ffffffff,8,[0, 1, 2, 3, 4]),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,8,[0, 1, 3, 4, 5]),(0x550055005500550055005500550055,7,[1, 2, 4, 5]),(0x555500000000000055550000,4,[1, 2, 3]),(0xffff000000000000ffff00000000,7,[0, 1, 2, 3]),(0xffffffff00000000ffffffff00000000,8,[0, 1, 2, 3, 4]),(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,6,[1, 2, 3, 4, 5]),(0x22222222222222222222222222222222,5,[2, 3, 4, 5]),(0xffff0000ffff0000ffff0000ffff0000,6,[0, 1, 2, 3, 5]),(0xffff000000000000ffff0000,5,[0, 1, 2, 3]),(0x5555000055550000555500005555,5,[1, 2, 3, 5]),(0x5555000000000000555500000000,4,[1, 2, 3]),(0x2222000022220000222200002222,4,[2, 3, 5]),(0x50505050505050505050505050505050,5,[1, 3, 4, 5]),(0xf0f00000f0f00000f0f00000f0f,5,[0, 1, 3, 5]),(0x55550000555500005555000055550000,5,[1, 2, 3, 5]),(0xf0f00000f0f00000f0f00000f0f0,5,[0, 1, 3, 5]),(0x555555550000000055555555,5,[1, 2, 3, 4]),(0x55555555000000005555555500000000,5,[1, 2, 3, 4]),(0xf0f0f0f000000000f0f0f0f0,5,[0, 1, 3, 4]),(0xf0f0f0f000000000f0f0f0f00000000,5,[0, 1, 3, 4]),(0x44444444444444444444444444444444,5,[2, 3, 4, 5]),(0xcccccccccccccccccccccccccccccccc,6,[0, 2, 3, 4, 5]),(0xaaaa0000aaaa0000aaaa0000aaaa,5,[1, 2, 3, 5]),(0x30303030303030303030303030303030,5,[0, 3, 4, 5]),(0x3333000033330000333300003333,5,[0, 2, 3, 5]),(0x550000005500000055000000550000,4,[1, 2, 5]),(0xcc00cc00cc00cc00cc00cc00cc00cc,5,[0, 2, 4, 5]),(0xf0f0f0f000000000f0f0f0f,4,[0, 1, 3, 4]),(0xf000f000f000f000f000f000f000f0,7,[0, 1, 4, 5]),(0xf0000000f0000000f0000000f0,4,[0, 1, 5]),(0xf000f000f000f000f000f000f000f,5,[0, 1, 4, 5]),(0xff00ff0000000000ff00ff00000000,7,[0, 1, 2, 4]),(0xffff000000000000ffff,4,[0, 1, 2, 3]),(0x440044004400440044004400440044,4,[2, 4, 5]),(0x33333333000000003333333300000000,5,[0, 2, 3, 4]),(0xff000000ff000000ff000000ff0000,5,[0, 1, 2, 5]),(0x500050005000500050005000500050,4,[1, 4, 5]),(0x300030003000300030003000300030,4,[0, 4, 5]),(0x330033000000000033003300000000,4,[0, 2, 4]),(0xf0f0000000000000f0f00000000,4,[0, 1, 3]),(0x550055000000000055005500000000,4,[1, 2, 4]),(0x3333000000000000333300000000,4,[0, 2, 3])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨ptopS0,ptopS1,ptopS2,ptopS3,ptopS4,ptopS5,ptopS6,ptopS7,ptopS8,ptopS9,ptopS10,ptopS11,ptopS12,ptopS13,ptopS14,ptopS15,ptopS16,ptopS17,ptopS18,ptopS19,ptopS20,ptopS21,ptopS22,ptopS23,ptopS24,ptopS25,ptopS26,ptopS27,ptopS28,ptopS29,ptopS30,ptopS31,ptopS32,ptopS33,ptopS34,ptopS35,ptopS36,ptopS37,ptopS38,ptopS39,ptopS40,ptopS41,ptopS42,ptopS43,ptopS44,ptopS45,ptopS46,ptopS47,by simp⟩
noncomputable def ptopC : List (Nat × List (Nat × Nat × Nat)) := [dC 0x1,dC 0x2,dC 0x3,dC 0x6030202010104,dC 0x6030202010105,dC 0x5040201,dC 0x5040202,dC 0x5040203,dC 0x5040206030202010104,dC 0x6030202010106,dC 0x5040401,dC 0x5040402,dC 0x5040403,dC 0x6030205040402010104,dC 0x7,dC 0x6030302010104,dC 0x6030302010105,dC 0x5040207,dC 0x5040206030302010104,dC 0x6030302010106,dC 0x5040407,dC 0x6030305040402010104,dC 0x2010104,dC 0x8,dC 0x6040202010105,dC 0x4020201,dC 0x4020202,dC 0x6030202010107,dC 0x6030202010103,dC 0x3020208,dC 0x9,dC 0x4020301,dC 0x4020302,dC 0x3020308,dC 0x504020201010a,dC 0x5020101,dC 0x5020102,dC 0x4020108,dC 0x5020201,dC 0x5020202,dC 0x6040202010106,dC 0x5030206040202010105,dC 0x4020208,dC 0x604020201010b,dC 0x5020301,dC 0x5020302,dC 0x4020308,dC 0x5020401,dC 0x5020402,dC 0x4020408,dC 0x301020c,dC 0x6010405040202,dC 0xd,dC 0x4030208,dC 0x6040205010402010105,dC 0x6040205010402010106,dC 0x4030408,dC 0x6040202010104,dC 0x2010105,dC 0x6040202010107,dC 0x6040202010103,dC 0xe,dC 0x4030206040202010104,dC 0xf,dC 0x6040204030302010104,dC 0x201010a,dC 0x10,dC 0x401020c,dC 0x6050205010402010106,dC 0x605020201010b,dC 0x5040206040202010104,dC 0x6050202010106,dC 0x6040205040402010104,dC 0x6,dC 0x4020101,dC 0x4020102,dC 0x7030106040202010104,dC 0x11,dC 0x7030206040202010104,dC 0x7030306040202010104,dC 0x4020401,dC 0x4020402,dC 0x7030406040202010104,dC 0x6040205030102010104,dC 0x5030206040202010104,dC 0x6040205030302010104,dC 0x6040205030402010104,dC 0x5040101,dC 0x5040102,dC 0x7050106040202010104,dC 0x6030205040101,dC 0x6030205040102,dC 0x2010112,dC 0x7020106030205040101,dC 0x8030107050106040202010104,dC 0x6050204030102010106,dC 0x7020206030205040102,dC 0x4030206050202010106,dC 0x3020211,dC 0x7050206040202010104,dC 0x5040301,dC 0x5040302,dC 0x7050406040202010104,dC 0x7050306040202010104,dC 0x5,dC 0xb,dC 0x6050202010104,dC 0x6050202010105,dC 0xa,dC 0x6050302010104,dC 0x6050302010105,dC 0x6050302010107,dC 0x6050302010103,dC 0x4030206050302010104,dC 0x5030206,dC 0x5030306,dC 0x6050304030302010104,dC 0x2010103,dC 0x4030202010104,dC 0x13,dC 0x6040302010107,dC 0x14,dC 0x2010107,dC 0x6040302010103,dC 0x15,dC 0x16,dC 0x2010104030304,dC 0x2010106,dC 0x17,dC 0x5030102010104,dC 0x5030105,dC 0x5030202010104,dC 0x18,dC 0x19,dC 0x2010105030304,dC 0x1a,dC 0x2010105030404,dC 0x5030405,dC 0x5040202010104,dC 0x201010b,dC 0x6050302010106,dC 0x2010106010405040204,dC 0x2010105010405,dC 0x2010105040404,dC 0xc,dC 0x2010202,dC 0x2010203,dC 0x1b,dC 0x2010401,dC 0x1c,dC 0x2010206020403010204,dC 0x2010206020403010205,dC 0x1d,dC 0x3010202010204,dC 0x3010206,dC 0x301020b,dC 0x2010206,dC 0x201020b,dC 0x2010201,dC 0x2010402,dC 0x2010207,dC 0x2010206020203010404,dC 0x2010206020203010405,dC 0x2010203010404,dC 0x3010406,dC 0x301040b,dC 0x2010204,dC 0x4010202,dC 0x2010205,dC 0x4010201,dC 0x4020204010202010204,dC 0x201020f,dC 0x201020a,dC 0x4010401,dC 0x2010202010305,dC 0x2010206020404010204,dC 0x4010207,dC 0x4010203,dC 0x4010202010204,dC 0x4010301,dC 0x4010204010302,dC 0x4010206040402010204,dC 0x6040402010207,dC 0x5010202,dC 0x5010401,dC 0x2010206020405010204,dC 0x2010206020405010205,dC 0x5010207,dC 0x5010203,dC 0x5010202010204,dC 0x5010201,dC 0x2010206020205010404,dC 0x2010206020205010405,dC 0x5010402,dC 0x2010205010404,dC 0x5010407,dC 0x5010403,dC 0x2010206010403020204,dC 0x2010206010403020205,dC 0x3020202010204,dC 0x3020202010205,dC 0x2010204010301,dC 0x4010302,dC 0x6040402010203,dC 0x302020e,dC 0x201021d,dC 0x12,dC 0x3020206040402010204,dC 0x3020206,dC 0x302020201020a,dC 0x302020f,dC 0x504041c,dC 0x3020206050402010206,dC 0x302020b,dC 0x6040402010201,dC 0x201020e,dC 0x4010101,dC 0x2010204020307,dC 0x2010206040403020204,dC 0x201020302020a,dC 0x2010203020205,dC 0x504021c,dC 0x5040202010203,dC 0x6010105040202,dC 0x6010105040201,dC 0x201021a,dC 0x6050102010206,dC 0x302020201020b,dC 0x2010215,dC 0x3020202010206,dC 0x2010205040403,dC 0x2010206010203020404,dC 0x2010206010203020405,dC 0x2010203020404,dC 0x6040202010401,dC 0x6040202010203020404,dC 0x3020402010205,dC 0x302040201020a,dC 0x2010203020405,dC 0x2010404010301,dC 0x201041d,dC 0x3020406040402010204,dC 0x3020406,dC 0x302040f,dC 0x302040b,dC 0x201020302040b,dC 0x1e,dC 0x5040202010207,dC 0x6050404020303,dC 0x201020302040a,dC 0x2010203020406,dC 0x2010205040407,dC 0x4020202010204,dC 0x2010206010404020204,dC 0x4010402,dC 0x2010202010405,dC 0x201020201040a,dC 0x4020207,dC 0x4020203,dC 0x4010204010301,dC 0x4020206040402010204,dC 0x7010104020202010204,dC 0x301021c,dC 0x3010208,dC 0x6040202010202010105,dC 0x1f,dC 0x401020201020f,dC 0x504020201020201010a,dC 0x2010202010105,dC 0x201020201010a,dC 0x7010404020202010204,dC 0x4010202010101,dC 0x2010102,dC 0x6030104020202010204,dC 0x4020202010207,dC 0x6030102010205,dC 0x503010201020a,dC 0x2010109,dC 0x4010202010301,dC 0x4020202010203,dC 0x6030404020202010204,dC 0x6030402010205,dC 0x503040201020a,dC 0x2010309,dC 0x2010302,dC 0x6040404020202010204,dC 0x7060402010204020304,dC 0x2010204020304,dC 0x2010104010301,dC 0x7030102010204020304,dC 0x2010304010301,dC 0x2010204020303,dC 0x7030402010204020304,dC 0x5020202010204,dC 0x2010206010405020204,dC 0x2010206010405020205,dC 0x5020207,dC 0x5020203,dC 0x5020202010205,dC 0x2010206010205020404,dC 0x2010206010205020405,dC 0x2010205020404,dC 0x6040205010401,dC 0x6040202010205020404,dC 0x6040205020407,dC 0x6040205020403,dC 0x5020402010205,dC 0x2010205020405,dC 0x5020407,dC 0x5020403,dC 0x2010101,dC 0x6030102010204,dC 0x6040202010101,dC 0x6040202010102,dC 0x402020c,dC 0x402021c,dC 0x5030202010108,dC 0x20,dC 0x2010202010101,dC 0x2010202010102,dC 0x21,dC 0x4020121,dC 0x402011d,dC 0x6030206030102010204,dC 0x6030206030102010205,dC 0x4010202010102,dC 0x6040202010207,dC 0x6040206030102010204,dC 0x6030102010206,dC 0x6050102010104010201,dC 0x6050102010104010202,dC 0x5040102010103010208,dC 0x6050106030102010205,dC 0x2010104010302,dC 0x6030106040402010204,dC 0x6030106050402010206,dC 0x6050102010207,dC 0x6050102010203,dC 0x603010201020b,dC 0x5010102010101,dC 0x5010102010102,dC 0x6050106030102010204,dC 0x2010115,dC 0x22,dC 0x6040302010203,dC 0x6050402010207,dC 0x6050402010203,dC 0x6050302010207,dC 0x6050202010203,dC 0x6030106050302010204,dC 0x7060302010205040203,dC 0x7060102010205040203,dC 0x6030202010204,dC 0x6030202010205,dC 0x2010205010301,dC 0x2010205010302,dC 0x603020201020b,dC 0x6030206050402010204,dC 0x6030405010302010201,dC 0x6030406050402010207,dC 0x503020201020a,dC 0x4010315,dC 0x6040405010302010202,dC 0x6040406050402010207,dC 0x5030404010302010208,dC 0x6030402010201,dC 0x6040402010202,dC 0x5030402010208,dC 0x6050102010201,dC 0x6050102010202,dC 0x5040102010208,dC 0x6050402010201,dC 0x6050402010202,dC 0x5040402010208,dC 0x2010301,dC 0x6030402010204,dC 0x6040202010301,dC 0x6040202010302,dC 0x402030c,dC 0x402031c,dC 0x5030202010308,dC 0x2010223,dC 0x6030306030402010204,dC 0x6030306030402010205,dC 0x4010202010302,dC 0x6040202010203,dC 0x6040206030402010204,dC 0x6030402010206,dC 0x603040201020b,dC 0x2010306050404010201,dC 0x2010306050404010202,dC 0x2010305040403010208,dC 0x6030406050402010205,dC 0x6030406040402010204,dC 0x6030406050402010206,dC 0x5010202010301,dC 0x5010202010302,dC 0x6050206030402010204,dC 0x2010315,dC 0x2010306040405010202,dC 0x2010305030404010208,dC 0x2010305010301,dC 0x2010305010302,dC 0x6030406050402010204,dC 0x3010112,dC 0x7060302010205040207,dC 0x7060102010205040207,dC 0x6030302010204,dC 0x6030302010206,dC 0x6050106030302010204,dC 0x6040202010204,dC 0x6040206040402010204,dC 0x6050104010304010201,dC 0x6050104010304010202,dC 0x5040103010303010208,dC 0x6050402010206,dC 0x6050104010201,dC 0x6050104010202,dC 0x6050102010205,dC 0x5040103010208,dC 0x6050404010201,dC 0x6050404010202,dC 0x6050402010205,dC 0x5040403010208,dC 0x6010404020204,dC 0x4010204010402,dC 0x7010406040202010204,dC 0x6050104010404010202,dC 0x6050102010402010205,dC 0x6010405020206,dC 0x6020404010204,dC 0x4010204010401,dC 0x7020406040202010204,dC 0x6020104010201,dC 0x6020104010202,dC 0x7030106040202010204,dC 0x6050106020104010201,dC 0x6050106020104010202,dC 0x5040105020103010208,dC 0x6020404010201,dC 0x6020404010202,dC 0x7030406040202010204,dC 0x6020406050404010201,dC 0x6020406050404010202,dC 0x5020405040403010208,dC 0x7050106040202010204,dC 0x6050202010206,dC 0x605020201020b,dC 0x7050406040202010204,dC 0x6040402010204,dC 0x7040402010204030304,dC 0x7040402010205040404,dC 0x4030306040402010204,dC 0x5040404010301,dC 0x5040404010302,dC 0x5040406040402010204,dC 0x5010101,dC 0x5010102,dC 0x6050102010204,dC 0x6040205010101,dC 0x6040205010102,dC 0x5030204010108,dC 0x5010205010101,dC 0x5010205010102,dC 0x6050206050102010204,dC 0x6050206050102010205,dC 0x502030c,dC 0x502031c,dC 0x7050102010205030304,dC 0x7050102010205030305,dC 0x5010105020301,dC 0x5010105020302,dC 0x6050202010204,dC 0x6050202010205,dC 0x6040405010201,dC 0x6040405010202,dC 0x5030404010208,dC 0x5010301,dC 0x5010302,dC 0x6050402010204,dC 0x6050306050402010204,dC 0x6050306050402010205,dC 0x5020105010301,dC 0x5020105010302,dC 0x502010c,dC 0x6050405030102010204,dC 0x502011c,dC 0x6050302010204,dC 0x4030202010204,dC 0x6010104020201,dC 0x6010104020202,dC 0x7060102010204030204,dC 0x6030302010205,dC 0x503030201020a,dC 0x6010204020301,dC 0x5010203020308,dC 0x6010304020301,dC 0x6010304020302,dC 0x7060402010204030304,dC 0x24,dC 0x2010204030304,dC 0x6010205020102,dC 0x6010202010205030104,dC 0x5030102010204,dC 0x6010205020101,dC 0x6020202010205030104,dC 0x5030102010205,dC 0x5010204020108,dC 0x6010305020102,dC 0x6010305020101,dC 0x7060402010205030104,dC 0x7060402010205030105,dC 0x5010304020108,dC 0x6030206030402010207,dC 0x6030202010207,dC 0x3010209,dC 0x6040202010206,dC 0x2010225,dC 0x6030402010207,dC 0x3010309,dC 0x6040402010206,dC 0x3020206030402010207,dC 0x3010202010207,dC 0x2010203010307,dC 0x6040205020101,dC 0x6040205020102,dC 0x6040202010205030104,dC 0x7060102010205030105,dC 0x5030202010204,dC 0x6010105020201,dC 0x6010105020202,dC 0x502020c,dC 0x7060102010205030204,dC 0x502021c,dC 0x5010104020208,dC 0x6010205020301,dC 0x5010204020308,dC 0x6030202010206,dC 0x6010305020301,dC 0x6010305020302,dC 0x7060402010205030304,dC 0x5010304020308,dC 0x2010226,dC 0x2010205030304,dC 0x6010205020401,dC 0x6050202010207,dC 0x5010204020408,dC 0x6010305020401,dC 0x6010305020402,dC 0x502040c,dC 0x7060402010205030404,dC 0x502041c,dC 0x7060402010205030405,dC 0x5010304020408,dC 0x2010205030404,dC 0x6040205020401,dC 0x6040205020402,dC 0x6040202010205030404,dC 0x5030402010205,dC 0x2010205030405,dC 0x5040202010204,dC 0x504020c,dC 0x7060102010205040204,dC 0x27,dC 0x6050302010205,dC 0x6050302010206,dC 0x2010205040404,dC 0x2010304,dC 0x6040202010303,dC 0x6040203020202010304,dC 0x2010303020205,dC 0x4020107,dC 0x201030302020a,dC 0x6040203020402010304,dC 0x2010303020405,dC 0x302040e,dC 0x4020103,dC 0x201030302040a,dC 0x6040202010307,dC 0x6040202010304,dC 0x2010305,dC 0x4020206040202010304,dC 0x201030a,dC 0x2010303,dC 0x3020202010304,dC 0x3020202010305,dC 0x6010402010303020204,dC 0x6010402010303020205,dC 0x2010306,dC 0x201030b,dC 0x5040202010303,dC 0x5040202010201,dC 0x2010307,dC 0x2010209,dC 0x302020201030b,dC 0x2010205040401,dC 0x302020201030a,dC 0x3020202010306,dC 0x2010305040403,dC 0x3020402010304,dC 0x3020402010305,dC 0x6010202010303020404,dC 0x6010202010303020405,dC 0x5040202010401,dC 0x302040201030b,dC 0x5040202010307,dC 0x2010405040401,dC 0x302040201030a,dC 0x3020402010306,dC 0x2010402010305,dC 0x6010402010304020204,dC 0x4020202010304,dC 0x5020202010304,dC 0x6010402010305020205,dC 0x6010402010305020204,dC 0x6020405010204,dC 0x5020402010304,dC 0x6010202010305020404,dC 0x6010202010305020405,dC 0x4030202010304,dC 0x6010404020202,dC 0x6030302010305,dC 0x6010204020302,dC 0x2010304030304,dC 0x5030102010304,dC 0x6010202010305030104,dC 0x6010202010305030105,dC 0x5030202010304,dC 0x6010405020202,dC 0x6030302010306,dC 0x6010205020302,dC 0x2010305030304,dC 0x6010205020402,dC 0x2010305030404,dC 0x5040202010304,dC 0x6050302010306,dC 0x2010305040404,dC 0x2010404,dC 0x4010206040202010404,dC 0x2010405,dC 0x6040202010404,dC 0x201040a,dC 0x2010403,dC 0x3010202010404,dC 0x2010402010307,dC 0x2010406020403010204,dC 0x2010406020403010205,dC 0x2010406,dC 0x201040b,dC 0x2010407,dC 0x3010402010404,dC 0x6020202010403010404,dC 0x6020202010403010405,dC 0x4010202010404,dC 0x4020204010202010404,dC 0x201040f,dC 0x2010406020404010204,dC 0x5010202010404,dC 0x2010406020405010204,dC 0x2010406020405010205,dC 0x2010402010306,dC 0x6010405020204,dC 0x5010402010404,dC 0x6020202010405010404,dC 0x6020202010405010405,dC 0x4020202010404,dC 0x4030202010404,dC 0x6010404020201,dC 0x6030302010405,dC 0x2010423,dC 0x28,dC 0x503020201040a,dC 0x2010404030304,dC 0x5030102010404,dC 0x5030102010405,dC 0x6020202010405030104,dC 0x6040202010405030104,dC 0x5030202010404,dC 0x6010405020201,dC 0x5010404020208,dC 0x6030302010406,dC 0x29,dC 0x2010426,dC 0x2010405030304,dC 0x2010405030404,dC 0x6040202010405030404,dC 0x2010405030405,dC 0x5040202010404,dC 0x6010405040201,dC 0x5010404030208,dC 0x6050302010405,dC 0x6010402010405040204,dC 0x5010402010405,dC 0x2010405040404,dC 0x6020203010104,dC 0x6020203010105,dC 0x4020206020203010104,dC 0x502020301010a,dC 0x4020307,dC 0x6020204020303010104,dC 0x6020203010106,dC 0x5020206020203010104,dC 0x602020301010b,dC 0x5020307,dC 0x6020205020303010104,dC 0x6040402010102,dC 0x7040406020203010104,dC 0x3010308,dC 0x6050102010102,dC 0x5020107,dC 0x7050106020203010104,dC 0x6050402010102,dC 0x7050406020203010104,dC 0x7050406020203010105,dC 0x5040206020203010104,dC 0x5040202010102,dC 0x6020105040207,dC 0x5010104030208,dC 0x2010105040402,dC 0x6020205040403010104,dC 0x3010104,dC 0x6040203010104,dC 0x3010105,dC 0x4020206040203010104,dC 0x301010a,dC 0x4020407,dC 0x3010408,dC 0x503010201030a,dC 0x5040206040203010104,dC 0x6050203010106,dC 0x605020301010b,dC 0x4020203010104,dC 0x6020303010105,dC 0x3010104020304,dC 0x3010106,dC 0x4010108,dC 0x5020103010104,dC 0x5020203010104,dC 0x6020303010106,dC 0x4010208,dC 0x4010308,dC 0x3010105020304,dC 0x602030301010b,dC 0x4010408,dC 0x301010b,dC 0x3010105020404,dC 0x5040203010104,dC 0x6050303010105,dC 0x6050303010106,dC 0x3010105040404,dC 0x3010204,dC 0x3010205,dC 0x4010203010204,dC 0x4010204010307,dC 0x4010206040403010204,dC 0x301020a,dC 0x5010203010204,dC 0x3010205010404,dC 0x6040203010203020404,dC 0x3020403010205,dC 0x301020e,dC 0x301020d,dC 0x4020303,dC 0x3010203020404,dC 0x3010203020405,dC 0x5040203010203020404,dC 0x301020302040b,dC 0x403020d,dC 0x5040202010202,dC 0x403021b,dC 0x6010105040207,dC 0x6050103020403010205,dC 0x4030223,dC 0x403040d,dC 0x403041b,dC 0x3010203020405040404,dC 0x3010203020406,dC 0x2010205040402,dC 0x6020403010204,dC 0x6020403010205,dC 0x5030202010408,dC 0x3020323,dC 0x6040402010401,dC 0x502040301020a,dC 0x5040206020403010204,dC 0x6020403010206,dC 0x602040301020b,dC 0x2010305040407,dC 0x6020405040403010204,dC 0x4020203010204,dC 0x6010104020207,dC 0x6020103010205,dC 0x5020103010208,dC 0x3020223,dC 0x502010301020a,dC 0x6020304010301,dC 0x3010204020304,dC 0x6040404020303010204,dC 0x6010205020107,dC 0x3010206010205020104,dC 0x6010205020103,dC 0x3010205020104,dC 0x5020103,dC 0x6020305010101,dC 0x6010305020107,dC 0x5020304010108,dC 0x4020123,dC 0x5020203010204,dC 0x6020105010201,dC 0x6010105020207,dC 0x5020104010208,dC 0x4020223,dC 0x5020303,dC 0x6020305010301,dC 0x6010305020307,dC 0x4020323,dC 0x3010205020304,dC 0x6020305010401,dC 0x6010305020407,dC 0x5020304010408,dC 0x4020423,dC 0x3010205020404,dC 0x6040203010205020404,dC 0x5020403010205,dC 0x301011b,dC 0x5030204020423,dC 0x6050103010206,dC 0x3010205020405,dC 0x201021c,dC 0x2010204020302,dC 0x3010206020204030304,dC 0x4020403,dC 0x3010203020205,dC 0x3010204030304,dC 0x4010307,dC 0x6040403010204,dC 0x6050403010206,dC 0x5040406040403010204,dC 0x5040203010204,dC 0x6020405040203,dC 0x3010206020405040204,dC 0x2010205040202,dC 0x6020105040201,dC 0x602020301020b,dC 0x6050103010205,dC 0x3010205040404,dC 0x6020203010304,dC 0x4020206020203010304,dC 0x6020203010305,dC 0x6020204020303010304,dC 0x6040402010302,dC 0x502020301030a,dC 0x5040206020203010304,dC 0x5040202010302,dC 0x6020203010306,dC 0x602020301030b,dC 0x403021e,dC 0x2010305040402,dC 0x6020205040403010304,dC 0x3010304,dC 0x6040203010304,dC 0x3010305,dC 0x4020206040203010304,dC 0x503040201030a,dC 0x301030a,dC 0x4020203010304,dC 0x6040302010302,dC 0x6020303010305,dC 0x3010304020304,dC 0x5020103010304,dC 0x6010203010305020104,dC 0x5020203010304,dC 0x6050302010302,dC 0x6020303010306,dC 0x3010305020304,dC 0x3010306,dC 0x602030301030b,dC 0x6010205020407,dC 0x5020403010304,dC 0x5040203010304,dC 0x301030b,dC 0x6010405040207,dC 0x6050303010306,dC 0x3010305040404,dC 0x6020203010404,dC 0x6020203010405,dC 0x6040202010201,dC 0x5030202010208,dC 0x2a,dC 0x502020301040a,dC 0x5040206020203010404,dC 0x5040202010402,dC 0x602020301040b,dC 0x6020203010406,dC 0x6020205040403010404,dC 0x3010404,dC 0x4010206040203010404,dC 0x3010405,dC 0x4010303,dC 0x6040203010404,dC 0x6040202010402,dC 0x301040a,dC 0x4010203010404,dC 0x5010203010404,dC 0x5010403010404,dC 0x3020203010404,dC 0x301030d,dC 0x3010406040403020204,dC 0x301040e,dC 0x3010403020205,dC 0x3020203010405,dC 0x5040203020203010404,dC 0x302020301040b,dC 0x3020203010405040404,dC 0x3020203010406,dC 0x2010405040402,dC 0x4020203010404,dC 0x2b,dC 0x502030301040a,dC 0x6020204010301,dC 0x6010304020303,dC 0x5020203010308,dC 0x3010404020304,dC 0x6020205010101,dC 0x6010305020103,dC 0x5020204010108,dC 0x5020103010404,dC 0x5020203010404,dC 0x6020405010201,dC 0x6010105020203,dC 0x5020404010208,dC 0x3010426,dC 0x6020205010301,dC 0x6010305020303,dC 0x5020204010308,dC 0x3010405020304,dC 0x6020205010401,dC 0x6010305020403,dC 0x6050202010402,dC 0x602030301040b,dC 0x5020204010408,dC 0x3010405020404,dC 0x6040203010405020404,dC 0x5020403010405,dC 0x3010405020405,dC 0x4030203010404,dC 0x201041c,dC 0x3010403020405,dC 0x3010406020404030204,dC 0x5040203010404,dC 0x6020405040201,dC 0x6010105040203,dC 0x5020404030208,dC 0x6050303010405,dC 0x6020405040207,dC 0x3010406020405040204,dC 0x2010405040202,dC 0x3010405040404,dC 0x4,dC 0x4010204,dC 0x4010206040205010404,dC 0x5010206,dC 0x5010405,dC 0x501020b,dC 0x4010205010404,dC 0x6010203020105,dC 0x4010206010203020104,dC 0x501020302010a,dC 0x3020105,dC 0x4010203020104,dC 0x6040204010203020104,dC 0x302010a,dC 0x6040302010101,dC 0x6010303020105,dC 0x5030302010108,dC 0x501030302010a,dC 0x3020106,dC 0x3020205,dC 0x4010203020204,dC 0x6040102010201,dC 0x5030102010208,dC 0x3010223,dC 0x501010302020a,dC 0x6040402010402,dC 0x501040302020a,dC 0x302020a,dC 0x6050104010203,dC 0x5010203020206,dC 0x706030501020302020b,dC 0x2010210,dC 0x4010203020304,dC 0x3020305,dC 0x4010206040203020304,dC 0x6010203020305,dC 0x6040302010301,dC 0x6010303020305,dC 0x5030302010308,dC 0x302030a,dC 0x3020306,dC 0x4010203020404,dC 0x3020405,dC 0x6040202010202,dC 0x6010203020405,dC 0x6040302010401,dC 0x6010303020405,dC 0x5030302010408,dC 0x2c,dC 0x501030302040a,dC 0x302040a,dC 0x6050104010207,dC 0x706020501020302040b,dC 0x5010203020406,dC 0x2010410,dC 0x4010204010102,dC 0x401021c,dC 0x7010104020204010204,dC 0x7010404020204010204,dC 0x4010204010101,dC 0x6020104020204010204,dC 0x6020404020204010204,dC 0x4020204010204,dC 0x4010204020101,dC 0x4020204010207,dC 0x6030104020204010204,dC 0x4010204020401,dC 0x301041b,dC 0x4020204010203,dC 0x6030404020204010204,dC 0x6020104010204,dC 0x6020206020104010204,dC 0x6020204010204,dC 0x6020206030104010204,dC 0x2010203010105,dC 0x201020301010a,dC 0x6050104020104010201,dC 0x5040103020103010208,dC 0x6030105010206,dC 0x6020206030404010204,dC 0x2010203010305,dC 0x5030202010223,dC 0x6040402010407,dC 0x201020301030a,dC 0x6020304010204,dC 0x2010302010405,dC 0x6020406020304010204,dC 0x6030106020304010204,dC 0x3010102010405,dC 0x301010201040a,dC 0x5020104010401,dC 0x5030102010305,dC 0x401010d,dC 0x6020404010207,dC 0x5030106020404010204,dC 0x6020405010206,dC 0x6020404010203,dC 0x401040d,dC 0x6020405030404010204,dC 0x6010205020105,dC 0x4010206010205020104,dC 0x5020105,dC 0x4010205020104,dC 0x6040204010205020104,dC 0x6040205020103,dC 0x6040305010101,dC 0x6010305020105,dC 0x5030304010108,dC 0x3020210,dC 0x201020d,dC 0x4030205010206,dC 0x5020404010226,dC 0x3020310,dC 0x201030d,dC 0x4010205020404,dC 0x5020405,dC 0x6050204010202,dC 0x5030204010408,dC 0x6040305010401,dC 0x6010305020405,dC 0x5030304010408,dC 0x2d,dC 0x201020c,dC 0x6010204020101,dC 0x5010203020108,dC 0x6030104010204,dC 0x4020204020101,dC 0x6030206030104010204,dC 0x3010203010105,dC 0x6030204010204,dC 0x6050104020201,dC 0x5040103020208,dC 0x6030304010204,dC 0x3010303010405,dC 0x6030406030304010204,dC 0x6010204020401,dC 0x201040c,dC 0x5010203020408,dC 0x6030404010204,dC 0x4010206010205030104,dC 0x6010205030105,dC 0x6020205030105,dC 0x4010206020205030104,dC 0x4010205030104,dC 0x6040204010205030104,dC 0x5030204020108,dC 0x6040305020101,dC 0x6010305030105,dC 0x5030304020108,dC 0x3010210,dC 0x402020f,dC 0x3020204010207,dC 0x5040403010223,dC 0x5030404010226,dC 0x402030f,dC 0x3010310,dC 0x6020205030405,dC 0x4010206020205030404,dC 0x4010205030404,dC 0x6050204010207,dC 0x6010205030405,dC 0x5030204020408,dC 0x6040305020401,dC 0x6050404010207,dC 0x5030304020408,dC 0x5010105,dC 0x6050104010204,dC 0x6010205040101,dC 0x6020205010105,dC 0x501020c,dC 0x5010204030108,dC 0x6050304010204,dC 0x6020104010302,dC 0x6020204010307,dC 0x6020204010303,dC 0x7030106020204010304,dC 0x6020205010306,dC 0x6020404010302,dC 0x7030406020204010304,dC 0x6020204010304,dC 0x6050104010302,dC 0x602020501030b,dC 0x7050106020204010304,dC 0x5020104010302,dC 0x5030106020204010304,dC 0x4010305020402,dC 0x6020205030404010304,dC 0x4010304,dC 0x2010108,dC 0x3020104010304,dC 0x6010204010303020104,dC 0x5010306,dC 0x6020304010302,dC 0x6020304010307,dC 0x2010208,dC 0x6010403020205,dC 0x3020204010304,dC 0x6040404010303020204,dC 0x2010308,dC 0x3020304010304,dC 0x6020304010303,dC 0x6020204010302,dC 0x2010408,dC 0x3020404010304,dC 0x6010204010305020104,dC 0x5020104010304,dC 0x602030501030b,dC 0x5020404010304,dC 0x5030104010304,dC 0x6010204010305030104,dC 0x5030404010304,dC 0x6020205010107,dC 0x3020206020205010104,dC 0x6020205010103,dC 0x6020203020305010104,dC 0x6020203020305010105,dC 0x6040405010102,dC 0x6020205010104,dC 0x4020206020205010104,dC 0x5020206,dC 0x6020204020305010104,dC 0x5020306,dC 0x6010304020401,dC 0x6020105010102,dC 0x7030106020205010105,dC 0x6020405010102,dC 0x6020204020305010103,dC 0x7030106020205010104,dC 0x7040406020205010103,dC 0x201022e,dC 0x7030406020205010104,dC 0x7030406020205010105,dC 0x7040406020205010107,dC 0x3010313,dC 0x7040406020205010104,dC 0x4030206020205010104,dC 0x4020205010102,dC 0x5010104020302,dC 0x6020204030305010104,dC 0x5010104,dC 0x6040205010107,dC 0x6040203020105010104,dC 0x5010103020105,dC 0x2010110,dC 0x6040203020205010104,dC 0x6040205010103,dC 0x5010103020205,dC 0x6040203020305010104,dC 0x5010103020305,dC 0x2010310,dC 0x6040203020405010104,dC 0x5010103020405,dC 0x6040205010104,dC 0x4020206040205010104,dC 0x6050102010305,dC 0x5020406,dC 0x4030206040205010104,dC 0x5010107,dC 0x401011f,dC 0x3020105010104,dC 0x3020105010105,dC 0x5010103,dC 0x6020305010107,dC 0x6020305010102,dC 0x3020205010104,dC 0x3020205010105,dC 0x501020302030a,dC 0x5010103020304,dC 0x6020305010103,dC 0x6020205010102,dC 0x5010103020404,dC 0x4020205010104,dC 0x6020305010105,dC 0x5010102010405,dC 0x5010106010404020204,dC 0x5010104020304,dC 0x4030205010104,dC 0x5010104030304,dC 0x5010204,dC 0x6010203020106,dC 0x5010206010203020104,dC 0x601020302010b,dC 0x5010203020104,dC 0x6050302010101,dC 0x6010303020106,dC 0x5040302010108,dC 0x3020126,dC 0x5010203020204,dC 0x5010203020205,dC 0x4010223,dC 0x5010203020304,dC 0x6050302010301,dC 0x6010303020306,dC 0x5040302010308,dC 0x5010203020404,dC 0x6050302010401,dC 0x6010303020406,dC 0x5040302010408,dC 0x3020426,dC 0x5010205020404,dC 0x6010205020404,dC 0x6020405010205,dC 0x6020205010304,dC 0x5010304,dC 0x5010307,dC 0x3020105010304,dC 0x6010205010303020104,dC 0x5010303,dC 0x6020305010302,dC 0x6020305010307,dC 0x3020205010304,dC 0x3020305010304,dC 0x6020305010303,dC 0x6020205010302,dC 0x6010203020406,dC 0x3020405010304,dC 0x6020205010404,dC 0x6020205010405,dC 0x6050204010201,dC 0x5040203010208,dC 0x4020205010201,dC 0x4020205010402,dC 0x6020205010407,dC 0x6020205010403,dC 0x4030206020205010404,dC 0x5010204020301,dC 0x6020204030305010404,dC 0x5010404,dC 0x501030b,dC 0x6040205010403,dC 0x6040205010407,dC 0x6040203020205010404,dC 0x6040203020405010404,dC 0x5010403020405,dC 0x6040205010404,dC 0x302010b,dC 0x6050202010101,dC 0x601030302010b,dC 0x5040202010108,dC 0x3020105010404,dC 0x601010302020b,dC 0x6020305010402,dC 0x6020305010407,dC 0x4010423,dC 0x3020205010404,dC 0x3020205010405,dC 0x5040205010403,dC 0x5040203020205010404,dC 0x5040205010407,dC 0x6050202010301,dC 0x601030302030b,dC 0x5040202010308,dC 0x5010403020304,dC 0x6050202010401,dC 0x601030302040b,dC 0x6020205010402,dC 0x6020305010403,dC 0x5040202010408,dC 0x2f,dC 0x5010403020404,dC 0x5040205010403020404,dC 0x502020b,dC 0x4020205010404,dC 0x6020305010405,dC 0x5010404010402,dC 0x5010406010404020204,dC 0x6050204010301,dC 0x601030502030b,dC 0x5040203010308,dC 0x5010404020304,dC 0x5020205010404,dC 0x5020205010405,dC 0x503020b,dC 0x4030205010404,dC 0x6050404020201,dC 0x601010503020b,dC 0x5040403020208,dC 0x6030305010405,dC 0x501041c,dC 0x6020405030206,dC 0x5010406020404030204,dC 0x6050204020301,dC 0x601030503030b,dC 0x5040203020308,dC 0x6020205030306,dC 0x602020503030b,dC 0x4020305010402,dC 0x6020205010404030304,dC 0x5010404030304,dC 0x503030b,dC 0x5040205010404,dC 0x5010406020405040204,dC 0x5010405020405,dC 0x6010203020104,dC 0x6040402010101,dC 0x5030402010108,dC 0x6050102010101,dC 0x7050106010203020104,dC 0x6050402010101,dC 0x7050406010203020104,dC 0x7050406010203020105,dC 0x5040206010203020104,dC 0x5040202010101,dC 0x5010203020126,dC 0x2010105040401,dC 0x504040c,dC 0x6010205040403020104,dC 0x3020104,dC 0x6040203020104,dC 0x4010407,dC 0x503010201040a,dC 0x5040206040203020104,dC 0x6050203020106,dC 0x605020302010b,dC 0x5040203020104,dC 0x5020404030223,dC 0x6050303020105,dC 0x3020105040404,dC 0x6010403020204,dC 0x3010323,dC 0x5040206010403020204,dC 0x601040302020b,dC 0x6010403020206,dC 0x6010405040403020204,dC 0x3020204,dC 0x4020203020204,dC 0x4020206040403020204,dC 0x5020203020204,dC 0x5020203020205,dC 0x3020205020404,dC 0x6040203020205020404,dC 0x5020403020205,dC 0x2e,dC 0x3020205020405,dC 0x4010403,dC 0x3010423,dC 0x6040403020204,dC 0x5040203020204,dC 0x6010405040203,dC 0x3020206010405040204,dC 0x6020105040202,dC 0x601020302020b,dC 0x6050103020205,dC 0x3020205040404,dC 0x6010203020304,dC 0x6040402010301,dC 0x5030402010308,dC 0x5040206010203020304,dC 0x5040202010301,dC 0x6010203020306,dC 0x601020302030b,dC 0x4030213,dC 0x2010305040401,dC 0x6010205040403020304,dC 0x3020304,dC 0x6040203020304,dC 0x6040205040403020304,dC 0x6050203020306,dC 0x5040203020304,dC 0x302030b,dC 0x6050303020305,dC 0x3020305040404,dC 0x6010203020404,dC 0x5030402010408,dC 0x5040206010203020404,dC 0x601020302040b,dC 0x501020302040a,dC 0x6010205040403020404,dC 0x3020404,dC 0x6040203020404,dC 0x4020206040203020404,dC 0x4020203020404,dC 0x5020203020404,dC 0x5020403020404,dC 0x5020403020405,dC 0x6040203020405020404,dC 0x5040203020404,dC 0x6020405040202,dC 0x5020104030223,dC 0x6050303020405,dC 0x6010403020405040204,dC 0x3020405040404,dC 0x4020204,dC 0x4010102,dC 0x6020204010102,dC 0x6020304010102,dC 0x6010104020204,dC 0x6030204010102,dC 0x401020f,dC 0x6050304010102,dC 0x6010206010104020204,dC 0x6050104010104010202,dC 0x6050102010102010205,dC 0x6010105020206,dC 0x6010204020204,dC 0x6010406010304020204,dC 0x6010304020204,dC 0x30,dC 0x4020206040205020404,dC 0x4020205020404,dC 0x6030104020204,dC 0x4020204020102,dC 0x6030206030104020204,dC 0x3020203020105,dC 0x6030204020204,dC 0x6030304020204,dC 0x3020303020405,dC 0x6030406030304020204,dC 0x6030404020204,dC 0x4020206020205030104,dC 0x4020205030104,dC 0x6040204020205030104,dC 0x4020205030404,dC 0x6050204020207,dC 0x6040305020402,dC 0x6050404020207,dC 0x6050104020204,dC 0x6050304020204,dC 0x6010204020304,dC 0x4020304,dC 0x6030205020102,dC 0x6030204020307,dC 0x5040203020323,dC 0x5030104020304,dC 0x6020204020305030104,dC 0x5030404020304,dC 0x6010205020104,dC 0x6050104010301,dC 0x5040103010308,dC 0x5020104,dC 0x5010406,dC 0x6040205020104,dC 0x6040205020107,dC 0x4030206040205020104,dC 0x4030205020104,dC 0x5030304020123,dC 0x5020104030304,dC 0x5020204,dC 0x5020205,dC 0x6010405020205,dC 0x6010205020304,dC 0x6010205020305,dC 0x5020304,dC 0x6010205020405,dC 0x6050304010201,dC 0x5040303010208,dC 0x5020404,dC 0x6040205020404,dC 0x7030106040205020404,dC 0x7030406040205020404,dC 0x4030205020404,dC 0x6030305020405,dC 0x5030304020423,dC 0x5020404030304,dC 0x4030204,dC 0x6020204010407,dC 0x6010404030204,dC 0x6010204020407,dC 0x5010403020208,dC 0x6020404030204,dC 0x6010204030304,dC 0x6020204030304,dC 0x7050106020204030304,dC 0x4030304,dC 0x6010205030104,dC 0x6050102010401,dC 0x5040102010408,dC 0x6050104020301,dC 0x5030104,dC 0x6020205030104,dC 0x7040406020205030104,dC 0x6050104020302,dC 0x6040205030104,dC 0x6050103020405,dC 0x5030204,dC 0x5030205,dC 0x6050202010201,dC 0x5040202010208,dC 0x6010405030204,dC 0x6010405030205,dC 0x6020405030204,dC 0x6020405030205,dC 0x6010205030304,dC 0x6050402010401,dC 0x5040402010408,dC 0x6010205030305,dC 0x6020205030304,dC 0x5030304,dC 0x6050302010201,dC 0x5040302010208,dC 0x6010205030404,dC 0x6050304020201,dC 0x6040405010207,dC 0x6020205030404,dC 0x6050304020202,dC 0x5030404,dC 0x6040205030404,dC 0x6050303020205,dC 0x5040204,dC 0x6010405040204,dC 0x6020405040204,dC 0x5040404]
def ptopP : List (Nat × Nat) := [(2,3),(1,3),(3,6),(16,17),(24,25),(36,37),(3,5),(8,10),(20,22),(36,38),(18,22),(8,12),(33,37),(18,26),(2,10),(33,41),(1,17),(18,50),(33,49),(3,9),(4,12),(40,41),(24,28),(48,52),(36,52),(5,21),(9,41),(5,37),(1,21),(36,44),(12,40),(40,44),(20,52),(20,21),(1,37),(40,42),(1,49),(18,19),(5,17),(17,33),(20,28),(24,26),(48,49),(48,50),(6,10),(0,12),(9,25),(3,34),(9,10),(6,7),(9,11),(9,13),(6,22),(33,35),(34,50),(5,7),(10,24),(4,22),(6,38),(34,35),(34,38),(1,7),(0,17),(5,13),(9,12),(8,44),(32,37),(32,38),(8,13),(16,22),(0,3),(17,48),(25,56),(26,56),(4,37),(4,38),(16,50),(5,12),(4,7),(16,19),(34,42),(2,35),(6,14),(3,18),(41,56),(2,22),(0,10),(2,19),(8,28)]
noncomputable def ptopK : List CutV := ptopC.map (mkCut ptopZ)
theorem ptopW : ∀ c ∈ ptopK, CutP ptopR ptopT c := cutsGood ptopY (by decide +kernel)
theorem ptopQ : ptopP.all (sepOK ptopT) = true := by decide +kernel
def ptopD4 : List StD := []
theorem ptopI4 : LevelN ptopR ptopT 4 ptopD4 := by intro s h; cases h
set_option maxHeartbeats 0 in
noncomputable def ptopD5 : List StD := [
mkSt [w1,w0,w808,w38,w122,w5] 0x107b9aa52d8b51d2741c3c683824b028201094149c4034301c0d40800,
mkSt [w809,w1,w0,w38,w122,w5] 0x103bdcd62d0b5a9294a044385c2c6414242010689c3428041c0d40800,
mkSt [w123,w1,w2,w810,w4,w5] 0x1183dcd62d4949c00000483cb8d440c8ec9500c07c34d00400cc2940880,
mkSt [w123,w1,w2,w3,w811,w5] 0x107b9ad62d4949c00000483c350cc8ec9500c05c40380400cc2940800]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC5x0 : levelOK ptopT ptopK ptopP 4 (ptopD4.map Prod.fst) ((ptopD5.drop (0*64)).take 64) = true := by decide +kernel
theorem ptopI5 : LevelN ptopR ptopT 5 ptopD5 := levelStep ptopB ptopW ptopQ ptopI4 (chunks 64 ptopD5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC5x0
  ))
set_option maxHeartbeats 0 in
noncomputable def ptopD6 : List StD := [
mkSt [w1,w2,w812,w0,w38,w122,w5] 0x173584c760c04a012443b0e0c10000180000a09c3034502c24200094b0281c0c17817c17417118684,
mkSt [w1,w2,w0,w38,w122,w813,w5] 0xdbcc911e1be70d19ae10a15a8448d3a046706c346864a05c28505824201014949c40b02c1c0c18818418150a03,
mkSt [w814,w1,w2,w0,w38,w122,w5] 0x32516414f4210771ced62d4941c9c38b42410946c50642820142c3440681c0d40900,
mkSt [w815,w1,w2,w0,w38,w122,w5] 0x324a6460f4210e3b9cd62d4941c9cb4642414946834b82c1c1050286c40200d40900,
mkSt [w816,w123,w1,w2,w3,w4,w5] 0x2d4a4cd4892a309bdcd62d4941cd060c06c2c200844483cd4ec3078280400403540980,
mkSt [w123,w1,w2,w3,w4,w5,w817] 0x66b2c4af695693946107358b54c6c34b8dc40c8c4689500c028785c7c8c245414fcd00430440140c80,
mkSt [w818,w123,w1,w2,w3,w4,w5] 0x2d4a4d5549aa51abdc862d4941cd0e860c1045c7c8c244440340400286c30d4c4483d40a80,
mkSt [w123,w1,w2,w819,w3,w4,w5] 0x4a44288e204878d181258a12243838a182838686c3440d0c90c950108c10430cc4428040050850550902,
mkSt [w820,w152,w1,w2,w0,w3,w4] 0x2d8b949318a22e73dcd62d4941d2520c02c680c607428dcc46c78444034040140900,
mkSt [w152,w1,w2,w0,w821,w3,w4] 0x36cd842b46ce126c60f7358b9c4402d24d494ecccc0803c447820248414486c0400283540b00,
mkSt [w822,w152,w1,w2,w0,w3,w4] 0x32349ce516266d63d4e6b16a4a03124dc60c104844034280400446c142cc4483cd540a00,
mkSt [w152,w1,w2,w823,w0,w3,w4] 0x38b400101e3a68c182c1c580320c6101c301840502d24c92d2128c1046c68280034044450807950882,
mkSt [w153,w1,w2,w0,w237,w4,w5] 0x92280c50871e75c6906da118580512404874a0a424143c3428040040802c50381c1080548901,
mkSt [w153,w99,w2,w0,w9,w4,w5] 0x314c825287a10e629286b14941c5cd05444603c00280534106814402c2540800,
mkSt [w153,w1,w2,w0,w8,w4,w5] 0x3211824cc7b92d3b5a462d4941ca080a4041468383c2c4c0050281c34441082540881,
mkSt [w99,w2,w0,w9,w8,w4,w5] 0x3e2e539504c12f735496316a4a0805c6840045534002c1c3c4c44d010142940880,
mkSt [w824,w1,w2,w0,w133,w3,w5] 0x46307a52e435a761ce852d4941c4434f0242010b860cc0414683840281c0d40880]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC6x0 : levelOK ptopT ptopK ptopP 5 (ptopD5.map Prod.fst) ((ptopD6.drop (0*64)).take 64) = true := by decide +kernel
theorem ptopI6 : LevelN ptopR ptopT 6 ptopD6 := levelStep ptopB ptopW ptopQ ptopI5 (chunks 64 ptopD6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC6x0
  ))
set_option maxHeartbeats 0 in
noncomputable def ptopD7p0 : List StD := [
mkSt [w118,w2,w0,w31,w4,w5] 0x5d3fb73dda63c6d364ec9c378d0346c40002410141c4460500c200ac0dc0d80d00d40cc0c918687,
mkSt [w118,w2,w0,w3,w38,w5] 0x273e6f3dba23d9b164142c57ad46c60342410141c4400500c201141100d010c0f40cc0d518607,
mkSt [w1,w2,w0,w38,w122,w5] 0x1f2320df1c1ad91684d6931446d24289cb8682c40241c10140c5028346c64209411c10816c16958884,
mkSt [w47,w26,w1,w2,w0,w20,w3,w5] 0x2a810806aa280488262402a20220021e08c01cda18ca88ca1cc08a800502c0418108468f060ec4490b8640048403c28200c35033034434d58a84,
mkSt [w1,w2,w107,w0,w20,w3,w4,w5] 0x1986459a78f4e261ac0001a8e40221d800c41c2040d9940581a18c480483c8050403828044494c40c003438c38400833838803837438037d20709,
mkSt [w1,w2,w6,w0,w133,w3,w4,w5] 0x85962475a692282692202020608081a614594490388060502cd4dc1cec3494c40c0428c06840003c39038037548983,
mkSt [w47,w26,w17,w1,w2,w0,w3,w5] 0x1eaa8a86b1a7a212aa2692281e70a68a61648051244f480502c20846834f0ec90b8006448042860443c0c4034d48b01,
mkSt [w17,w1,w2,w107,w0,w3,w4,w5] 0xc15b18241500d2c4dc0d2c494a628109015e1c68500045000443494280c0460dc1c8050003843743e038033918605,
mkSt [w6,w0,w337,w4,w13,w5] 0x67b9ad86ab3033d66a559d36a46068346c4cd80014501044d042442042c41c42841918606,
mkSt [w123,w1,w2,w3,w4,w5] 0x1d22c7208914de5d06da981714d29043cd4ec60c03064fc040044286c4034dcc426050025424158884,
mkSt [w1,w2,w32,w0,w3,w4,w87] 0x1623036843d9cb087b39400d86339562b1540992a834184c3c6c64fcaca4dca810c400044440340c1c52052853050052c24052425560888,
mkSt [w47,w26,w1,w2,w32,w0,w3,w5] 0x336800e0005cf1c384811a30300033606b942408d111e24a0fc3cdc2c84046044641c0048400cd43453c45026150803,
mkSt [w1,w2,w32,w0,w3,w4,w322,w5] 0x100098f400fc1406cfc1406cb15058080f1cb4364b42448204448fc3428aca41cdca810c4000c0452056055c45053055918786,
mkSt [w1,w2,w0,w782,w3,w4,w5] 0x1d63035f9d630f994f0014975b14ced05d5300cec68746c4460505ca42410142c00040c1c403457026050056c25424158886,
mkSt [w783,w1,w2,w6,w0,w3,w4,w5] 0x5065149654b962a502532048883a64078e1a3058a13024070806050ccd0dc1c3cc40cc044483428d4942c6c0400643854857950b82,
mkSt [w1,w2,w32,w107,w0,w3,w4,w5] 0x1f501162235d1f615c01c1855d1a000819501508550a0f500d0a4d080584044fc2848d4dcec3494c4001c04d83c2483885303841f057c54958887,
mkSt [w1,w2,w0,w784,w3,w4,w5] 0x1f7a2501f7a433bb21dacbd2d4392f6a493648483ccca42410143000044034281c0c26050054025424118785,
mkSt [w98,w154,w1,w2,w0,w4,w5] 0x15f2cf829e2babef45316e159ab015e6c174cc306040280400343c482c241426059856859c59424050118607,
mkSt [w98,w319,w1,w2,w0,w3,w5] 0x2a24d6209620dc6a1cc8986a04c4ac402a24e09c5846034280400403c302414485005b05ac5a85a456825426120588,
mkSt [w184,w40,w1,w2,w0,w3,w4] 0x2a2e294e1164d6116088ee2940a4e0861d5858c498440340400686c605020144462061861450061c25424061120588,
mkSt [w47,w26,w40,w1,w2,w0,w3,w5] 0xa0ec1aca2021c103b00a1c00a0c690380840649290500460440064484084342062846826110583,
mkSt [w323,w40,w1,w2,w0,w3,w5] 0x12322d0e1128a6112448b22d0028a45a2118449858444340400b8d0406c5020146061062863c63850064025426120608,
mkSt [w1,w2,w6,w0,w785,w3,w4,w5] 0x120584205e221b9e1c01a01e1c019a135805495754121804001a0c0a0748060502c40dc1c4494c414c0040034d861065065463800050958886,
mkSt [w40,w1,w2,w107,w0,w3,w4,w5] 0x2002121e141216141201081c120e0846141a0c06581614121000080609c2cd83cc044483428040080dcc4605028000865861158804,
mkSt [w47,w1,w2,w0,w3,w87] 0x1288c419f10638b618cb40a2a12c82391883c4450aca4a8108448b8400400603464200c67c6745006782406700f425560908,
mkSt [w79,w2,w0,w3,w4,w87] 0x1fe1c75fdd5b19d55b1493cd510e4003c444050aca420a810840c14643404006b46ac6b050068c25424158807,
mkSt [w1,w2,w320,w0,w3,w4,w87] 0x6210b67c3a190f87432000a8493193098440d0ec68340903c6c6440a034ac20a8108400040c1c4455c6d45006d82406d053025560808,
mkSt [w184,w321,w1,w2,w0,w3,w4] 0x15ecd7369e5da4f089d9ae0a5c262fd8b314c460340400686c40502014445006f06ec6e825424046918587,
mkSt [w152,w1,w2,w0,w3,w4] 0xd1f22cf16e09f0cdc5a9916d41290450dc60c4c0483c6c0400403428442cd4ec26050025424158884,
mkSt [w786,w1,w2,w0,w3,w5] 0x21475edd5a84d95650c29553070f0d0442c24a41410484028040068b830200c67c0f42d825424158805,
mkSt [w99,w1,w2,w0,w3,w237,w4,w5] 0x296a631ee4b80b6a389328cc3216a00128b0505cd0344440280424003c1480602c80108781,
mkSt [w1,w2,w0,w3,w237,w4,w5] 0x1d67651756a2215260529d5800169255509450928a88060505c2444a4d03c14cc000434101c2868408101a080c80080958985,
mkSt [w153,w99,w1,w2,w0,w3,w4,w5] 0x246f59c0a734e34b0a65a4073554941cd500b8d0c850804440342804140068602c80108781,
mkSt [w153,w1,w2,w0,w3,w4,w5] 0x1987a05f8909199c0e530790505b045997541300104b85cd0084440342800501c042c6810608201a081881481c80158806,
mkSt [w99,w2,w0,w3,w9,w4,w5] 0x24190d25230020969717121e191d169a1a19111680868b85cd0c054142c04443c280010402480608007f482807958904,
mkSt [w74,w99,w2,w0,w3,w4,w5] 0x1d2319090504df211896df1d1896c10f1d108ace4ac68d0444054502804943c00101480342c6007882c8007f558884,
mkSt [w99,w1,w2,w0,w3,w8,w4,w5] 0x14306909e007091c0660d010049095182860c305008a24040068385cd0446c40281cc800341480602c8148007f150803,
mkSt [w1,w2,w787,w6,w0,w3,w4,w5] 0x28013004898024388c0143a00d0028600000c3c112203824805044406028d4dcec34c45494c02c0068043c83c1f150982,
mkSt [w1,w2,w788,w6,w0,w3,w4,w5] 0x28b5d275b4eb1a4e510360b7b9ac42d4941c80504460382848dc1cd4ec34c41494c02c6cd804003c35d40b01,
mkSt [w1,w2,w107,w0,w789,w3,w4,w5] 0x2702120100e4011c2200211e02009c561a12051801140e120910010c09c385044602848dcd4ec34c494048000d81c3c5901f03848cd58984,
mkSt [w790,w1,w2,w107,w0,w3,w4,w5] 0x26142ebd42458a0bcb111d81c1241bb8304582f509100238609c28d8d4ec3c941c8060502cdcc434004804448cc00838550983,
mkSt [w22,w1,w2,w0,w133,w3,w4,w5] 0x2ee06021d3039c380800000ba81a83a4020000018503c38f044951840cc040c1c28003465037510702,
mkSt [w1,w2,w344,w75,w0,w3,w4,w5] 0x1d0a6819e3c80e1a3c80e1a3c04b9c34780001470d101838b0442c403c18dc5410c49400680cd83428af838150802,
mkSt [w1,w2,w344,w0,w3,w4,w5] 0xadf4945050562a0df5b22a0df5b00c28ac9551250444d834dc285410c494000468403c1c2c0cb34b301f0af838158885,
mkSt [w17,w1,w2,w225,w3,w4,w5] 0x19972c47d5e66e6b346666b03589cce64e0b24d8d44404302c483c60342814001cbf801cc10c0cbfcc0918706,
mkSt [w1,w2,w0,w791,w3,w4,w5] 0x1f5ab4ea11e4dd930e65b032c0c2b41a408900e880488c20843000343c04442c141cce8ce4be0bfcce118785,
mkSt [w1,w2,w0,w225,w792,w3,w4,w5] 0x390814082680582d828143441828118a068dc28662800084a04450d03c48302cd48400206014341f08cc338d2d18704,
mkSt [w793,w1,w2,w0,w3,w4,w15,w5] 0x2c54a0a2628b52090641122281501e385039a3204b142440706848d038f024a8014c94446434282084e830400cac3cf68f7150b02,
mkSt [w1,w2,w0,w3,w4,w15,w794,w5] 0x2db00aaaa268a28ac6a468482071e71a610594490706c48603cf034aca41c30a8014c108494e828400c5004fc8fc548b02,
mkSt [w795,w1,w0,w3,w4,w5] 0xb2307211edcdb18d6d45304d0ce8e83c446434a8c01084241c200c6c405004940fcde00d024158884,
mkSt [w1,w2,w131,w0,w3,w4,w87] 0x1fe3e0dfdcdadfdcdac119c2c2d61615ced2d1110f03c386c64a0ac20a81084000444400c341d03102d028240de06d4ce158887,
mkSt [w1,w2,w796,w0,w3,w4,w5] 0x1d615941011f1d411880174b54cac7135350810086c3c506c4038aca454108494040c2034440fd0406c903c24158805,
mkSt [w86,w1,w2,w0,w3,w129,w5] 0x26ccea0225da5321de5d3b73ebb4a64304185c081c68403c580c600044d034281f1074de106c0f506518706,
mkSt [w233,w1,w2,w0,w3,w42,w4,w5] 0x4c7201cd41e0f101a0f06960c031600048000000c0004c000000d08c64346828b020a050582c040cece8d81d0b50b10ad0a958804,
mkSt [w45,w233,w1,w2,w0,w3,w4,w5] 0x34b14b28f3a316700d8001c036000330b2892070000b4e8d80c6c405028042c34ec2064690bd0b910782,
mkSt [w797,w1,w2,w3,w4,w5] 0x459af4695663569a671423a66003c6c381c08843404440fc2c00d0f5424118485,
mkSt [w234,w1,w2,w0,w3,w8,w4,w5] 0x16014021002217000b0b47401e070720029a1b02d81712c0000d4002c3c68044c10c84440603438282ca41c0c1515d15915515114d58885,
mkSt [w27,w234,w1,w2,w0,w3,w4,w5] 0x22efbdf3c204ec200300014028e804e7800708614003c7c2d5840144434040c1c60289516116506910703,
mkSt [w345,w1,w2,w108,w0,w3,w4,w5] 0x28e2438a1b0a24830a24800f18e3461cc2892008060683ccc446cd0342c0400280c8060511ac7f510782,
mkSt [w345,w1,w2,w0,w3,w4,w5] 0x150a4c38b21dca92e12449af121b9525ac00c43c0844d0342c0400280c8050605084688011ac7f518685,
mkSt [w1,w798,w2,w108,w0,w3,w4,w5] 0x1c69a99812072461671a32281c69800d50e48038e385c508c6c44d0342804a8108400d42c80603c0d1b148981,
mkSt [w151,w50,w1,w63,w0,w3,w4,w5] 0x113014f033c432223c70d190600b0b08509062138283181a58e450202cbc0c3c4428a4e84824d44000383063925950902,
mkSt [w52,w1,w235,w63,w0,w3,w4,w5] 0x6a402a21e9a065da19f86415a1816140564900000060e020b0c0b0803c44502c41482820ec10c4d004d400e80c3825527924d27055927558906,
mkSt [w52,w236,w1,w63,w0,w3,w4,w5] 0x164c90b89061b1203868c260a12b4906509048c4010d1c10683c3440502114ec104428a4d024d42c48e8003928127d50982]
set_option maxHeartbeats 0 in
noncomputable def ptopD7p1 : List StD := [
mkSt [w151,w1,w2,w235,w0,w3,w4,w5] 0x43361c03ebe01f58636617660a4c85da74d6f780fc200324ce9482c10c468483834d400a40c4455825448124d28d28927918707,
mkSt [w151,w236,w1,w2,w0,w3,w4,w5] 0x2068310c29ba043453e6235e5a70c29bb1552cd70d42114600bc3ccc28d4e84448382c0034200c63924529d29929518705,
mkSt [w1,w2,w799,w63,w0,w3,w4,w5] 0x223060e9b0670d203c70d183c04e1a305c0002868c091838b060502844403cd4ec108494002c0c80d03524c7a550882,
mkSt [w1,w2,w800,w63,w0,w3,w4,w5] 0x34c303acfb8d3cb38d3cb02e34c2c000934c1e618a05044403c2cd4ec1084000c2880d8352447c110782,
mkSt [w1,w2,w336,w0,w3,w4,w801,w5] 0x64000f263c88e2438880a0bc70a143460b1424306101c386038d0e8483c30a41c18d4bc10c4002c3444040d3012c455d50983,
mkSt [w1,w2,w802,w0,w3,w4,w5] 0x1cd2243b54e83a731e92d6532d9674d21d004c44a4dcd4603cc4300004342c1c48c0954426135c37d18705,
mkSt [w1,w2,w0,w133,w803,w3,w4,w5] 0x1b84380da4076d0e02604162f06a101c4e0d6083070009306038446840f02c241c203494602804143d5dcc048cd50803,
mkSt [w804,w1,w2,w0,w133,w3,w4,w5] 0x248df0a67fb2d82ee3a2ddaba68b3694ba688069440f020146844403c34cc040060281c8ccc0465110703,
mkSt [w805,w2,w0,w3,w4,w5] 0x2eec77765b95a69484d82bc66003c44d034acc02010146cd850a4000fc0f441c24c2542a518706,
mkSt [w148,w2,w0,w3,w4,w87] 0x6efd93b6cc57aa15ab39a4272d43c44d834ac20a810840c14d0501c016ac2556a96a468c68118786,
mkSt [w806,w1,w2,w3,w4,w5] 0x457af62b57494aa2451423a0684683c1820543400440fc40840450024d18405,
mkSt [w1,w2,w0,w3,w807,w4,w5] 0x1162c18b0403f468d1ba24c99174a74ead466844b878247420103814cc00c8281c68400d71d71807950883]
noncomputable def ptopD7 : List StD := ptopD7p0 ++ ptopD7p1
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC7x0 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC7x1 : levelOK ptopT ptopK ptopP 6 (ptopD6.map Prod.fst) ((ptopD7.drop (1*64)).take 64) = true := by decide +kernel
theorem ptopI7 : LevelN ptopR ptopT 7 ptopD7 := levelStep ptopB ptopW ptopQ ptopI6 (chunks 64 ptopD7 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC7x0
  · exact ptopC7x1
  ))
set_option maxHeartbeats 0 in
noncomputable def ptopD8p0 : List StD := [
mkSt [w1,w2,w68,w3,w4,w5,w29] 0x181fedbd535cc87aecaa53a2c452e57355828443c38302c24201c14100c3428180801002001c02401801518786,
mkSt [w26,w1,w2,w68,w3,w4,w5] 0x195f456cb5e1ebb1158eaaf19920b39f363c3844200c48343c30281824081402401003403002c02918606,
mkSt [w89,w1,w2,w3,w4,w5,w29] 0x181f6cbb4f32b43aaa9433a6aa7911f151890443c38241c103028040014342c2004004804404c01801518706,
mkSt [w26,w89,w1,w2,w3,w4,w5] 0x1b5f455d9621ebaf118e2b5098a0b39f2e3c3844200c2c48343c04240014283004c04005402c02805118686,
mkSt [w1,w2,w0,w31,w4,w49,w5] 0x21dfc19ddb5957c1131551c4cf0544e1ccc91d48c4868643c38345c5828242054100c144c6007806c07406007006806558807,
mkSt [w58,w1,w2,w0,w31,w4,w5] 0x17e7bf1f5de274eb118f3f309431e15e06464844703c4c502c1c240c146c07808807008408007c06d18587,
mkSt [w1,w2,w69,w0,w31,w4,w5] 0x1966cdba566552b320b53a719b34b9560a146c40786c74302024100c4c601407809409008c06d18605,
mkSt [w1,w2,w0,w31,w4,w5,w117] 0x1edae713271822a65a104c6558504cc4e4db90c44c803c383440785c7c302420100c144c0ac0a006c0880a40a809c09807120789,
mkSt [w106,w1,w2,w0,w31,w4,w5] 0x1b5ee5ba35e254ab11952b5094b8a35e3146484834883c4c6c50281c200c84640880b80b40b006d18685,
mkSt [w76,w1,w2,w0,w31,w4,w5] 0x175ebdaa35e254a9119d1af094b8a35e31464840884c443c301c8c0c54480780c40c00bc07118585,
mkSt [w1,w2,w0,w31,w4,w5,w29] 0x1f7af38727e3b75e613271ca4206cdbbc6248402c80483420100c4460504c1406007006c0d40ac01801518687,
mkSt [w26,w1,w2,w0,w31,w4,w5] 0x1f026d09d3684c8f5d8469759539310204081090403420104c68481c0c44645024140e008802c0280a118785,
mkSt [w1,w2,w0,w3,w38,w49,w5] 0x25e5c121df5f5bd8971551cecf0f4ec7ca87094282c68643c38605c2c985828241c205410140c940fc0ec0f80f40680f006558907,
mkSt [w58,w1,w2,w0,w3,w38,w5] 0x19efbf1f5de274eb11972f309431e1de064648443c701094502c1c240c146c0fc1040f01000800ec07d18607,
mkSt [w1,w2,w0,w3,w38,w5,w29] 0x42000f81a0e068e26c30968931424d289300060e4843884c689c2c806034241c10140c44485020941140f00ec11c1180180f401560808,
mkSt [w26,w1,w2,w0,w3,w38,w5] 0x90e9dd98aebc26f5db409558cb881020426108064341094681c0c444050241412010402c0f402918685,
mkSt [w1,w2,w576,w0,w3,w38,w5] 0x1db3662dbb2160b92cc68d321c37c79a2a542c4898a028241c201410840c4080941340f013012c1280ed18706,
mkSt [w1,w2,w0,w3,w38,w577,w5] 0x25e5c1a1df5f5bd8571551cecf0f4ec7ca47094242c68643c38605c2c985828241c205410140c940fc0ec1380f40680640f158907,
mkSt [w578,w1,w2,w0,w3,w38,w5] 0x19af3e1d59e264cb11962d309431c15e314648443c701094502c1c240c146c0fc0f013c08007c0ed18606,
mkSt [w579,w1,w2,w0,w3,w38,w5] 0x19a3462d7a22e5cb15a63d5054b2c1623956286070109434281ca41464440c1340ec1481441400f118606,
mkSt [w1,w2,w69,w0,w3,w38,w5] 0x1b6ad5ca36a5d1b524b56af19b34a95622444c40786c7430201c2410140c94600fc14c09008c0ed18685,
mkSt [w1,w2,w0,w3,w38,w5,w117] 0x1a31186231590075aaa128632a960c8630885630440884c40806c3c3834785c7c30241c2010140c9413411c0ec11415009c0980f160888,
mkSt [w106,w1,w2,w0,w3,w38,w5] 0x1d9f6ecc39e264cb11de1d5094b8c39e0546484834886810946c50281c200c84641340fc1540b40b00ed18706,
mkSt [w76,w1,w2,w0,w3,w38,w5] 0x175ebdaa35e254a911952a5094b8a35e314648408894443c301c8c0c54480fc1580c00bc0f118585,
mkSt [w1,w2,w0,w3,w580,w38,w5] 0x25e321df1bc6df1dc91ad905d916d6910bd512d04289c4448684034ac1ca810140c6c645c5020941080ec0f011c16416015d58907,
mkSt [w1,w2,w0,w3,w38,w5,w581] 0x4200ef81a0e068e26c30968931424d289300060e4843884c689c2c806034241c10140c444850209411411c0f00ec18c0180f401560808,
mkSt [w582,w1,w2,w0,w3,w38,w5] 0x1d021d09b328478f5d84697595393102040810906034109444401c14684850200c1980fc19419011518705,
mkSt [w583,w1,w2,w0,w3,w38,w5] 0x1d0e84d8132bc08f5db4157595399042040828908034109468481c0c404450241419c13402c0280f518705,
mkSt [w217,w1,w2,w0,w3,w4,w49] 0x19e450ab5e23cb11193aaf0992bf3dfb73e3c20686460343c5c28042400141c81bc1b81c41c006806518607,
mkSt [w58,w217,w1,w2,w0,w3,w4] 0x1bf3adbf54e4f6a4e23f6a28e0b0cb439c26283428201c0c00443c502c24146c1b81c01d008007c1cc1bd18687,
mkSt [w584,w1,w2,w0,w3,w4,w5] 0x1be2670f7ce532e71dc91f107330e1ce06761864342824143c0400986038200c1e41d41e00740681dc06518687,
mkSt [w585,w1,w2,w0,w3,w4,w5] 0x1e31e0f2cf2c28b89a14f185bc0e00f03280c703cc0341c0c5024141f40841ec0801e81f007d18487,
mkSt [w1,w2,w0,w586,w3,w4,w5] 0x1beedf09bef548f141bc6ed41ab187d283164860347478282c241c20100cc0140782000941fc1e809008d18687,
mkSt [w587,w1,w2,w0,w3,w4,w5] 0x139b368c39aa64cd559e1cf4d9a0c39a83060c48783c3404200014401040a81dc1d409c09918486,
mkSt [w588,w1,w2,w0,w3,w4,w5] 0x18eb5b618e9458b49d6a3345c47418e83280c88143cc06c341c0c5020842140b80b41e82100b118586,
mkSt [w589,w1,w2,w0,w3,w4,w5] 0x1bb364bc18e3ea6509b662706cb8c18e05261480348820c0441c0c286c3c8c5421c1d40c40c01dc0bd18686,
mkSt [w590,w1,w2,w0,w3,w4,w5] 0x1ce4db241ed8a58cd98c645e5a054c1dc8d8098c248050243c144004004438200c22c2301b80d40080380181f001520609,
mkSt [w118,w28,w2,w0,w3,w4,w5] 0x1d526df9d758c1b0e11c0a0f0da00029ca84e86c4034000410141c94446050c40c2023822c2340d001518785,
mkSt [w109,w1,w6,w0,w3,w4,w5] 0x326d4e650a615c9e4545000000000195d5d5c1c0000483c3830ccac04c84034281c26025c0d024425824825424025120609,
mkSt [w1,w90,w6,w0,w3,w4,w5] 0x36716e690e4964a649451dddddc1c00000000001800483c343024c8040c00402850202602880d027c28428025424027920689,
mkSt [w1,w6,w0,w3,w15,w13,w5] 0x1d5100fcb9774dacb35a014874a000020000e8686c6434ace020000cd850d00444a42a824c2b02ac10c2a518786,
mkSt [w86,w1,w6,w0,w3,w4,w5] 0xb8f65edb3296b856900000004aec11eb308006c4034e4240cd4c8044464501cdc1342bc2b82542402b518706,
mkSt [w47,w1,w2,w0,w3,w15,w5] 0x4a23036843c9ccd8293196a00510000000240010c7412000e83c442c34aca4200048b840e4606c5064040fc2d82d424c0f42d02402cd60908,
mkSt [w218,w1,w6,w0,w3,w4,w5] 0xe096a312e29452e0564800000002081959595800006c60342014c804dc4440501c2602e80d02e42742542402e120608,
mkSt [w1,w146,w6,w0,w3,w4,w5] 0x363d7239363145360568819d9d9d8000000000188003c446034ac24c8dc040c006c40508c2603000d02fc2702542402f920788,
mkSt [w110,w2,w6,w0,w3,w4,w5] 0x3e388e31320d2c6e288925a58ce4c1605e0c84c4c4c483c3828541004ec94c44030340c0026031825427824827c31424120788,
mkSt [w47,w1,w2,w0,w20,w3,w4,w5] 0x312f5f6c412b4c551f414d655f42954d111f4505254d211f41150951460683c204034f0280044dc0c33c3343302d80f43402cc32432833834834432d2060d,
mkSt [w147,w1,w2,w6,w0,w3,w4,w5] 0x159d90eec312e98324e2c202020201d5871cc6c202158010e30003088448050583cc46c382c009437024836435c08035807836c3603681f024d2058c,
mkSt [w1,w2,w6,w0,w20,w3,w4,w5,w29] 0xfc14e9cdccc1d679351e159ccd8001f0ed28c0dd8114240c201c5805d4d00cc0dcc004440483c806050d8042820449434c40027028038c37804437433801401920789,
mkSt [w26,w1,w2,w6,w0,w20,w3,w4,w5] 0x3df4dd81b83431b19e008181ac01c20000002800a408e19dc1f1c080941034c1b1818008c44403c285004209434c46848dcec0039833834405002839402c34d20788,
mkSt [w83,w2,w6,w0,w3,w4,w5] 0x3a34ce3152296cae28c965a58d2500209e0cc109848483c308450dcec940c40283414002603a025428024439c24025120708,
mkSt [w1,w2,w6,w0,w3,w4,w183,w5] 0x2ae1808ecd8da6c1595926c1a15cd90000000000022ad1914cc9000186880605058ec943cc4000783b42ac3a83601f03b02803ac24c0692050b,
mkSt [w47,w17,w1,w2,w0,w3,w4,w5] 0x28729ead99a6812901010c485e99852d29268021010c411e999104410686c605020342804a444000c3c43c03bc3c82d82cc2543cc3b43392060a,
mkSt [w17,w1,w2,w6,w0,w3,w4,w5,w29] 0x7082d9728cb9b0350d209b00e0e013518740e80e1460b14c24b26cc0004000401c280c048044485034dcc0600001c3d43dc3d837401433918707,
mkSt [w26,w17,w1,w2,w6,w0,w3,w4,w5] 0x3a2ad54a92d000140774c1404c12ad2ca901c0060a02064018c10554803a940044341c9428000c046450dc6848c00300283ec3383e83e434d18707,
mkSt [w79,w2,w6,w0,w3,w4,w5] 0x27e4c9e321dec25dccda638b899781464788d041c784868444050f814d404ec94c40c54dc340064803fc3f82a44003f407824158987,
mkSt [w47,w1,w2,w0,w3,w13,w5] 0x1fe357a01f54030800011e92551c019c00559c00103c445004a8f81084d8d0000c606c380fc33840c41024c0f425432920788,
mkSt [w148,w6,w0,w3,w4,w13,w5] 0x1dda5e301dba141dd9b18419989165493d1810e8c860686cc0d8342014ec0494000c5054c444d04244304344142ac2a425558907,
mkSt [w79,w6,w0,w3,w4,w13,w5] 0x3871412e123e3834716e1c5d5d6a287841c15220414346cdcd85054ecc42000043c1444d04382a410c3fc3f82ac40024d20788,
mkSt [w1,w32,w6,w0,w3,w4,w13,w5] 0x1a9290410868496ab1452b58a02612f4723558a295a80d4a90322246475041d4d880a4502c6cdcfc20ec94c404c0343cd00044c44045445044825410c44443d60909,
mkSt [w40,w1,w6,w0,w3,w4,w13,w5] 0x15fe42954de25049c66179f6764d71d82dea655c429049c66140c21c4d080202cc0943c3400c468445004d847046444825446c46046810c45845d2078a,
mkSt [w47,w1,w6,w0,w3,w13,w5] 0x30d72b98ab0e12f303965c71461ae548944201c92840399c6c50ac20ec043cc40cd00094a438d8446047435c2a010c2b01f02542ac40d60889,
mkSt [w1,w591,w6,w0,w3,w4,w5] 0x997a3219f1c8586c4dad980d6cb8140c0c0c0c1414346c405024d438dcecc400940444601c3c1340042b80d047836158886,
mkSt [w52,w1,w32,w6,w0,w3,w4,w5] 0x2333354ba030d890c6606f874061b0006448452a34c0192c5603a0cd07134118688060502c6cfc20ec34c4c81cdc0400d4946444c3642544404804544844500d160989]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p1 : List StD := [
mkSt [w52,w40,w1,w6,w0,w3,w4,w5] 0x2dbaa6a8c5a6b4ada2b0a8ada2888028c5a680824850421e90d88890c68802c60443450c824dc04d4004049036425448846446c46848c0d04712070a,
mkSt [w219,w2,w6,w0,w3,w4,w5] 0x3a0e0d7e39748a1170ac64e5cce5c184d14c9844c4c6c4050108404dcec94c44460340c002742542f826049c30449824120788,
mkSt [w220,w2,w6,w0,w3,w4,w5] 0x3a20a287aba1a635740cd64f44b0912c000222046721b0483c446050a81404dc94c40c6c405434002604b02542702dc4ac2402e160808,
mkSt [w1,w2,w6,w0,w3,w4,w97,w5] 0x11f008b2ed9372aceecd302f12ce8800000000002a722dd08d48002c4460502cec944834c480303c002701f04b82482801344c44c04c84bc24c0192068c,
mkSt [w1,w2,w6,w0,w3,w4,w592,w5] 0x3b40017b71c03740002df74282b1ed6b4c8025dd42001096800000c086880502cd4c834dc2894c404c0000784502ac44c4e84e04f44f02804ec4e41f02612070d,
mkSt [w1,w2,w32,w134,w3,w4,w5] 0x52668498946629037c8d000070381da20751264288239844483c382c3028c81cdc04ec940cc4004034cc5d002605100d04fc4f850c28024025560a09,
mkSt [w1,w2,w32,w0,w3,w4,w59,w5] 0x19479bcaa34da794082eea7902c2eea003d96c161d2994c414891d1472390d8486068502c6cfc34ac1cdc5410c400040ca4a86421c46451c43c52044c25451445445051824160a0c,
mkSt [w47,w1,w2,w32,w0,w3,w4,w5] 0x370b636c731f6c432b42d4171764644d4f235d41554542e35d41570f060586cfcdc342c04a4000c684453844c2404800f452032c4542604502545342d92068d,
mkSt [w1,w2,w32,w119,w6,w0,w3,w4,w5] 0x2343522c08202debe9e7e4234340018148201e0100195c12161a19560f49d3cc100f4c0bc8060502c4448fc28401cd4dc94340cecc400d004c03c24054852054427424854158b07,
mkSt [w1,w2,w32,w119,w0,w3,w4,w5] 0x22eeb85bdda2cb018ddd60703b45960303a9d6c1b48a9d22772322cc2773090080b85c3c64fca4d4dc10ecc4040c48001c55427424845452053055025424054c5416088b,
mkSt [w98,w1,w2,w32,w6,w0,w3,w4,w5] 0x10cece2a1a242bdbe9e7c1a02422014ce00e1c1e1c0adbcfd6181615d210cec001000ccac80502cfc28d08cdc6054c4c0444034040048d4ec3c24027056852054824856558a87,
mkSt [w221,w1,w2,w32,w0,w3,w4,w5] 0x1726fa78ea4edb7200bcb521ba7396a43509db65a90d002624346c64fc682044840c8060745c8c5452026057425456c24118786,
mkSt [w1,w2,w32,w6,w0,w3,w4,w5,w29] 0x12c2320909124a4a9a181ebe927e5c18141219e00c6869b101798178a8a9311cd8e0d8bc408060502c44fc28d4481cdcec94340cc4003c04c0d82603dc27044c3785481f158b07,
mkSt [w26,w1,w2,w32,w6,w0,w3,w4,w5] 0x2b5898a6882400c82967400824220104a0181c1e1c029a9954161413500e18a680c00482844502cfc28401cdc94340cc4c06848d4ecd03c04002603985204503ed58a85,
mkSt [w98,w1,w2,w0,w134,w3,w4,w5] 0x225d5e42c281591a5d7510e2716cd108aa5d644904c0225d401910c882c3c8c605440342830042400142705a026056458c5885945682545902412068b,
mkSt [w154,w1,w2,w6,w0,w4,w5] 0x29790574a95530c55101eca94d24a0de1a010000c003080d4ec6010c03cb82c040034405005b421426024825424058120708,
mkSt [w319,w1,w2,w6,w0,w3,w5] 0x336d0b684f4902424241c2c2c2c2265da35d058242c3c3080c0b8400400945058605005bc24c1f02545b83582605842480780d02412060d,
mkSt [w1,w2,w6,w0,w593,w3,w4] 0x42d56f775a5daacb5ba8d2a0a0502814080000000000485c343c28306050802cc8d4dcecc40400c02600d05c45c05005c824854027024c2416080b,
mkSt [w594,w1,w2,w6,w0,w3,w4] 0x3f333dbb35b102828281c242424222571d9914d0c243460505cc8dcc4c068448004d400ec2605640d024c5d05cc5005d42482742542412078c,
mkSt [w1,w2,w6,w0,w3,w4,w595,w5] 0x21c0002bf990007700000886f02c16c85aab8e4004c0d412002116c0000018086c684480502cd4c834dc2894c40400c00784682ac4645e85e05f45f05182485ec5e41f02616080e,
mkSt [w40,w155,w1,w2,w3,w4,w5] 0x2ba90ba4e3a11e5d9b1ad6578514d24e87910ec2800483c38d514c8ec9510c05c2014cc30403404282c002605fc5f825424824158a86,
mkSt [w40,w1,w2,w0,w3,w4,w59,w5] 0x339b5ae5a5e60b0859e6d69455a556064499a4c896082859e40154c848602c682414443450042000844021460c44c60860045846425446c4686042412070c,
mkSt [w47,w40,w1,w2,w0,w3,w4,w5] 0x2126d6cc6912e5e11ed84d4556d1494c4316c258414d4256d149050145868603c04342c4420840f462448824060c46c2d826046446825432d2050c,
mkSt [w40,w1,w2,w119,w6,w0,w3,w4,w5] 0x1957562b480229d9e7e5e2215740019b5e160c1c1b5359c3ca141351c148020e01000c0a05c80502c4448d020d4603c84ecc028040040dcc43424061060c54027428054558a87,
mkSt [w40,w1,w2,w0,w3,w4,w5,w222] 0x36415e55165970a25d592cd25d5510e84a65550884c0225d590010c88802c208460444034500424001461063062c46426063425457024120689,
mkSt [w98,w40,w1,w2,w6,w0,w3,w4,w5] 0x10cece20c80225dbe3e1ccde0e061c0adbcfc41817c18802140146041210cec0010ccac0080502cd0246014c028444034040048d4ec3c24027056460c61028056958907,
mkSt [w98,w40,w1,w2,w0,w3,w4,w5] 0xa4606648a4610a25a104c9e5a0c54028a4601104c410a4600108c8002cd0603c140400403427046864c2806482542406446105692048a,
mkSt [w40,w1,w2,w6,w0,w3,w4,w5,w29] 0x1241508c8d122d69290811512092306c6e1100c9e04c4d2090a9a1900d692908e000c8a8402cd8203c14c04480483428040050dcc4602606103783dd58904,
mkSt [w26,w40,w1,w2,w6,w0,w3,w4,w5] 0x214686a0080600c81f5d449a1404180296874212116008060e0104020c0a069c80c48280044502cd020943c14c0286848403404002603ec60c46839958805,
mkSt [w155,w1,w2,w119,w0,w3,w4,w5] 0x1765ecd172501bb2dc66b92dca6c97259909db25c94e00262434483c308c28540c8060502c208426066454025466024118706,
mkSt [w47,w1,w2,w0,w3,w59,w5] 0x4e09124a44c649188111104f870b5182122c0114893419cc446050ace4a8f8108448b84004002c6c3c64200c0fc2d040c2d866c0f425424160a08,
mkSt [w1,w2,w6,w0,w3,w4,w87] 0xe7e71ba74f18e40d5906e48d5a481c0000000021983c446434d4c8dcc400c0502c80400427068468050068c21468824c24120789,
mkSt [w184,w1,w2,w6,w0,w3,w4] 0x429e70a7996882332d3480c08040200eb8122a92824420203460c8dcc4c068440400ec502c4080d450069c24c69469021c2746982542416080a,
mkSt [w79,w2,w0,w3,w4,w59,w5] 0x9e5e9e7c69ce5e25fdc9bd955575553c18cd08e4d4f83c4414406434ad18a420a810840c6c545004000fc2a42546a43fc6a824158a07,
mkSt [w86,w1,w0,w3,w4,w59,w5] 0x23e5e9e7c91d65e29fdd1bd88d571493c19f510ecd4e43c4424406434a9181084aca4040c6c5020001c0fc29c2b86c02542406bd58a07,
mkSt [w1,w2,w320,w0,w3,w4,w59,w5] 0x173b064ae26c67dc09ccd37d825ccd3012ed4a164a8542a8b39098c65229054443c502c6c64a034ac1ca4a854108400040c202d80fc4506046c421c44c2546c86cc2405196098c,
mkSt [w321,w1,w2,w0,w3,w4,w59,w5] 0x2e2f6eed51962f09d592ee8cd5510e2e485550884e2c25d590090c88602c68241444403450042000840fc4685186e06dc2144646e42542406052068b,
mkSt [w1,w2,w0,w3,w4,w87,w59] 0x281249194a5a71184ba5a4c55ca554a95002242672308543c2c6c4064341caca420a81084004450040c2b00fc6f86802142546846886f42416090a,
mkSt [w184,w1,w2,w0,w3,w4,w59] 0x4c8930990c4a12f512ba5aac1092e54215000c932823a988602c403424a420141084686c0400645044aca87006fc69021c2546946882b024160989,
mkSt [w47,w58,w1,w2,w6,w0,w3,w5] 0x3aa73fb4e4fcb7278000000420094e02144450000003065c283c80d4c804580c0094406c50dc602d82a00787085ec2601f118707,
mkSt [w47,w26,w1,w2,w6,w0,w3,w5] 0x336cccb3312597900000000520008204081190000002857ac84450c80c0094406080dc3c2cd470c2a02b034c2601f118686,
mkSt [w47,w58,w1,w2,w0,w3,w5] 0x21c9c75fdd5a49d950d6c9c7545250c9cf400c90c003c443458100c2c60c4b8d8286c50dc400fc2547100081f00f42d958807,
mkSt [w47,w26,w1,w2,w0,w3,w5] 0xba09f8e8b9c095b99495480000000069390400006880502010840068b864443c340c40280471c1f07147182b00f558806,
mkSt [w1,w2,w6,w0,w3,w4,w322,w5] 0x60b1ee008638800f72e02c16f770b70240063a8014004122c00000180844502cd4c834dc2894c4c08030003c0427068872c2482804f47342143747301f02616080c,
mkSt [w1,w2,w119,w0,w3,w4,w222] 0x5688b3aa8d2a6a008d49625047d395a8c458d294a914105080603468441d24c8dcd40d20c4ec002c40506c051c26074473868854074025473c27024160a8a,
mkSt [w106,w1,w2,w119,w6,w0,w3,w4] 0x2944a5bce96f218d05cca0a2541d22041d3a96e81030a98c4a5b814f0a548a0434605c44c8d494ecc0506cdcc48030d06404003c2b075424075075c27075874c74854160a0a,
mkSt [w323,w1,w2,w6,w0,w3,w5] 0xfb7b2138e0842c2c2c243030302aae3a6214542c304434c4c0b84004009480502c6027467c24c25476c76850077021c2607641f00d02412068e,
mkSt [w98,w221,w1,w2,w0,w3,w4] 0x23e5e30bc71ecbc71a60cbc71654d245cf108ec8800403530dc94c4c08024146c6804600074445c26078456478025427424158907,
mkSt [w98,w1,w2,w6,w69,w0,w3,w4] 0x1f62b8bb6e8e029dc9e28d92dbde28da02c2deee46c8194c5b4b8918000000007460502c9434c4806c04d468004440d0c0ec283c2b025424079879478c78856479027427160a0b,
mkSt [w1,w2,w324,w6,w0,w3,w4,w5] 0x18e1453865ee398c31e08f97431d48f704ba18ea42c800127843a90f2053c9d480502844d460dc34c49400ec04c03cd06824845044c4ec7a87ac0784e87a560889,
mkSt [w1,w2,w324,w0,w3,w4,w5] 0x35de0e08e5ce1db5f225c9adea24c0d161da18d8d946038d01c2894685404003444645f444c0782607a82484507a520688,
mkSt [w596,w1,w2,w0,w3,w4,w5] 0x1bb3cfcbb679418ddec11cde2bc2239bad06644068302834001c502c200c80605007b02482540787b424118687,
mkSt [w1,w2,w597,w0,w3,w4,w5] 0x38f6aaadb1aaac40eaa5ac84ea9d8100000000105c848682880a02cc824041c0c0014405007bc7b80082805a007858424c2412070a,
mkSt [w1,w2,w325,w6,w0,w3,w4,w5] 0x18e3433865eee9943ddc919843ddc91704c218e645c80012885399132054ca148028446050d440dc94c400ec3404c03cd86c2804684645ec7c47c80785e87c160909,
mkSt [w1,w2,w325,w0,w3,w4,w5] 0xde3c70edf3d76f9efd69f1c3804a5e3870e60502c44d8342460040014403c7cc0782607c44687c028118607,
mkSt [w2,w6,w0,w149,w3,w4,w5] 0x2e1e19822199360d910cb22da90010a62199154d41c30146050d4d03c34002c2804c027008c2600d07d87d424028120688,
mkSt [w1,w6,w0,w120,w3,w4,w5] 0x41950a8833c950e6388a04466393600062632d550451281c68407850ec943c284460243404c0cc007e409027024c7e007825428160808,
mkSt [w1,w2,w0,w598,w3,w4,w5] 0x3ebab5b281ad6aa5a160c2424258824000000c40148443c34805030282cc81c24040c00142700d07e01a02605007ec28024c2412078a,
mkSt [w99,w1,w2,w6,w0,w3,w4,w5] 0xeed8341dc22583b858505143c18d04102bddc0d8608116a771b1a0a20003000d0ec943cc40004c04480342c284050607f82700787f47f07fc79028160808,
mkSt [w99,w1,w2,w0,w3,w4,w5] 0x1e1f654385939763610f9e1c1a1990174b4d1381878b8d0c868943ccc44042c00283440501460802800788007f07f446958906,
mkSt [w1,w2,w6,w0,w3,w4,w129,w5] 0xe07028a446078481c0e15848200ef372b64c20741ad400a948a5c46150118480502cd4dc28ec9434c404c000443ccc2701e47e88302802548388341f160809,
mkSt [w1,w2,w326,w6,w0,w3,w4,w5] 0x248944a3e1d0288249226f88239126f802111c8932400888745224cf0053a1d46050802c40dcd4ec9434c4006c3004c03cd02485408548482b085084484d60908,
mkSt [w1,w2,w326,w0,w3,w4,w5] 0x1dab56dc38ef6bd575e6bd565835c5a2b306e0802ce8d034f01000306c043c0c402b05f485824884884518706,
mkSt [w599,w1,w2,w0,w3,w4,w5] 0xd934dad566365a921b65a91dba6cb521b24242834040c8060502c201427426050024825424118506]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p2 : List StD := [
mkSt [w1,w2,w600,w0,w3,w4,w5] 0x3e7a79b66da9726da964d659a958d0800000000c5884034288060742cd4c820041c0c008427486485c26050086028024c24120789,
mkSt [w1,w2,w327,w6,w0,w3,w4,w5] 0x2313131dc3dde1231edde11b1eddc1091b12d9c0990f1512d1c1510f46080502c40dcec9434c400443004c03cd028074c86c2b087086874958887,
mkSt [w1,w2,w327,w0,w3,w4,w5] 0x99f3ec95b274adb31dcacf25836898e13070080502c44d0f000346804403c30842b087487828086c86918706,
mkSt [w1,w2,w601,w0,w3,w4,w5] 0x366531784bdd6ce96bb19689953b18e8620cb5c2c14188483c3430288060502cac8cdc041c94c40c005427088026050088824888425424160909,
mkSt [w1,w2,w328,w6,w0,w3,w4,w5] 0x2302613529f42a8c4de4d0a8c21ccd0a01361ee662d011b4a8639989405551145c6050802c40dcd494c4ec6c4828340400c03cd02485642708a089889088c89c07889560a0a,
mkSt [w1,w2,w328,w0,w3,w4,w5] 0x1e17d7e14349cc1e17dd5a1817d541501209cb415005c482ce8d0342894000480cc3c546c405f48a424888c89045007958807,
mkSt [w1,w2,w6,w0,w3,w4,w223,w5] 0x1008028aa26081d020101595024111382be8c20841b1400ba50aa046450118480502cd4d8dc28ec944834c404c000443ccc2701f48b83dc8ac2482548b48b01f16090a,
mkSt [w1,w2,w107,w6,w0,w3,w4,w5] 0xf2a754cde33219bc6650480446602fa038ddd2a1680146e6744aa13003339a0805060382848dcd4ec34c4944400c02c043cd82486882602748c438028037c3748c96098a,
mkSt [w1,w2,w107,w0,w3,w4,w5] 0x259e1e3da0fa25a0f61665b0de2c018d88d229c18dc805038d8dcc444603404283c00481c8cc87826027400803868837c38120789,
mkSt [w602,w1,w2,w0,w3,w4,w5] 0xe3231ba35b0ce0984e88e0984e0508e0984c01c984444034d4dcecc4200c001c8060742748d48d003800850025424120708,
mkSt [w1,w2,w0,w20,w3,w4,w185,w5] 0x216fa00395769a7182c34d57232d54950100c540301a0d440b0502c160b05800e848683cf05028341ca81084000c20400d08e83408ec3488f08e48e025429c2796080b,
mkSt [w17,w1,w2,w0,w3,w4,w185,w5] 0x2daa8024d59e9b030717024282424241828181818258818694c250818e8486840346c50208400649088fc8f829c3c89000d03cc9048f42542512058c,
mkSt [w1,w2,w0,w3,w185,w13,w5] 0xb9d816388c9219e5d1ac15841414153868550ce8143c4464d0341c20a4a810840c6c504000d80fc29c0f49142a425558886,
mkSt [w22,w110,w2,w0,w3,w4,w5] 0x219f1f9cdd830187830181878300d2818781818a8884834282024ec940054100c041440303c33892c92891c24c27958806,
mkSt [w22,w1,w2,w0,w20,w3,w4,w5,w29] 0x170a5b3242081d0600d41040041692584e0d2fa48e10050d41d2470801a202040383c2044d8341d38004828dc0c94894037494493c33893918707,
mkSt [w26,w22,w1,w2,w0,w20,w3,w4,w5] 0x36d2a40da64850aa05b56aac88a298600a31c0561802855080c10a40e15a1414443c20341c293840dc0c68480033895895495094d18685,
mkSt [w22,w83,w2,w0,w3,w4,w5] 0x239d219edf9d0187830181878300d0818781818a888483428508ca41cec94008414040c40303c33896896494024c25158886,
mkSt [w22,w17,w1,w2,w0,w3,w4,w5,w29] 0x15884d162a0d39f360708daa0400018000298596ed982400000030000101000411880446050342048040c9743d897037433896d18586,
mkSt [w26,w22,w17,w1,w2,w0,w3,w4,w5] 0x3a0a158b148d5a86643440204b00e848090020420102386011420158b51a061044a42918645020040c684800403433898097c97918704,
mkSt [w22,w79,w2,w0,w3,w4,w5] 0x15af44acfa20576142850a142830a1428544683c446434405414040c6c500780d098898424c2a518586,
mkSt [w22,w219,w2,w0,w3,w4,w5] 0x54da5a2e15f8cc5499a80c549968682c35592508e8346c6050ac2494c4100c0414688c3c00408499891899493424c2f958906,
mkSt [w22,w220,w2,w0,w3,w4,w5] 0x1f8323a0df9d0187830180c7830192818781818a888346c6050201c94c400a85414040c40683c3389a89a493024c2e158886,
mkSt [w1,w2,w603,w0,w3,w4,w5] 0x211fc7dac719c1800180169513c2c2c000000000c28483440305824201cc49454003cb828040741dc9b09b491c0d006558807,
mkSt [w604,w1,w2,w0,w3,w4,w5] 0x192dc4ad3a33a182df00000003208009807818483c2864502400143040341c9409b81f00840d007d18606,
mkSt [w1,w2,w0,w605,w3,w4,w5] 0x1b72dc0014e55965004574f218b000000300c8683c383028241c140044342c202000949400d008d18685,
mkSt [w22,w2,w0,w149,w3,w4,w5] 0x21ddd940dad957d4874005c2d344c2c0c0c0d0c0c1848403c943430281c0c144438002c24209302409c49c80d094008d58807,
mkSt [w1,w2,w606,w0,w3,w4,w5] 0x4a071047c38da80003018001859290261300000000001848803c38cc5c7c24201cec10c40c00683430049349d41dc9d00a891c0d009960908,
mkSt [w607,w1,w2,w0,w3,w4,w5] 0x150a434d3a30c742df000000032001098078184430502000846c5c341c9409d82100b80d00b118506,
mkSt [w608,w1,w2,w0,w3,w4,w5] 0x1bb35cad2e63e84305800000032000c1807618683c38302c208c00548034281c9309e00c41dc0d00bd18686,
mkSt [w1,w2,w609,w0,w3,w4,w5] 0x7cb94df8ee00000c18f173210b00000000e286c6034241c20c49400444050049349ec0cc0d41f00d001518687,
mkSt [w1,w2,w0,w3,w329,w15,w5] 0x218b8025870763a09f5d1b82d6d916c0148000000003c44d86434aca4041410840c946c405020d00fc0f49f829c2402a558906,
mkSt [w109,w10,w1,w0,w3,w4,w5] 0x3e394a31062d4000000000000000284181818198948483c3830cc00c804dc0c2118403428260a180d0a14a08a1024c24120788,
mkSt [w10,w1,w90,w0,w3,w4,w5] 0x322d4a25220559999981800000000000c0c0c114d08483c383028c8dc1c004034cc260a300d0a2ca2424c24027920608,
mkSt [w10,w1,w0,w3,w15,w13,w5] 0x1d4d00fc99374daab30000100000b55e850ac8686c6434141ce0a42094d850d00444a3824ca04a3c10c2a518786,
mkSt [w86,w10,w1,w0,w3,w4,w5] 0x98b64edb318000000000000059ec365c20aa86c403400d4c8040d1820446450dc1342b4984a4024c24118706,
mkSt [w218,w10,w1,w0,w3,w4,w5] 0xa062d76316cc0000000000000002841818181989486c603400c804dc0c2518444050a20a500d0260a4ca4824c24120688,
mkSt [w10,w1,w146,w0,w3,w4,w5] 0x2a3225ae29a501d9d9d9c0000000000200c0c0d4d083c446034c8dc041c006c4050a1c0d0260a60a5c24c2402f920608,
mkSt [w1,w610,w2,w0,w3,w4,w5] 0x1af31eb44cf050a165050a1690072adb0a1a28643cf058042c14100c60342800a743d8a6ca70a0824d18686,
mkSt [w611,w1,w2,w0,w3,w4,w5] 0x1a07e7b1427840810211329dcc4121138468e444b86cd050041424483c400c68a787bc7b8080a7c07824d18687,
mkSt [w1,w2,w0,w612,w3,w4,w5] 0x3c0a3600c4f22d694e0000c0c0c140d8d8f2214d5cc4834b83cf0281014040c2444cc6840a787ec7e0a2407824ca7c09120788,
mkSt [w10,w1,w0,w120,w3,w4,w5] 0x22219f80dadd990d0d810acad784c500c0c0c080c14483c38c804f0101c24b8282c0c44681440a8c254a2424c07809158886,
mkSt [w10,w1,w2,w0,w3,w4,w129,w5] 0x1706079ee5cae7a5cc5ec8324363e13e782d92f001921b04403c385c2c5410044434280014a1ca8824ca90a241f083518607,
mkSt [w1,w613,w2,w0,w3,w4,w5] 0x360e2d4a288d418181a4818181a8800614594485848443c347c042c14100c6c382800a20aa03d8a74a9ca98a0824d20688,
mkSt [w614,w1,w2,w0,w3,w4,w5] 0x18aeddaf5cf86000000a9255bbe0c000000ec84434281410048420687c3c0ca240b4aa886085caa424d18607,
mkSt [w615,w1,w2,w0,w3,w4,w5] 0x19efc4af2e1860c1833762d05be0c0c18608cc6c3cf0283404548c442c500ca1c0c0880a743d888824d18607,
mkSt [w10,w1,w2,w0,w3,w4,w223,w5] 0x372e079ae5c6d4d5a46ce9524373a54a882dd3600a921b0440683c382c14100444d83428000ca1c24cab4a081f08b118686,
mkSt [w1,w616,w2,w0,w3,w4,w5] 0x9ca97c57eaca0c183620c1830014bdeb11c28804850046810140c44603400ac8aa4aa8ac4ac0a2024d18607,
mkSt [w10,w118,w2,w0,w3,w4,w5] 0xd0994d592dae3c5ab4a384e4c614709b90a286c6050040d3cc444dc14d834000cc014ad0acca2024118686,
mkSt [w1,w75,w0,w3,w4,w13,w5] 0x24a321259f8b9b5b5d5ba48107079764548f13914e868d0403c282cac205410c40cdc345ca400d8ae0404adcae42542a558906,
mkSt [w52,w1,w75,w0,w3,w4,w5] 0x3a260a060e35262e2900e62e211cc006014918c1908442c20403c681008dc0c006438e8078ae4108254aecae84402cd20708,
mkSt [w1,w75,w0,w3,w4,w5,w80] 0x2b69e9e11b5bd4d557d5269351cd0ec48345c906c486840dc44e8503c38345c282d24ac248c5410c40c00ae4af0af8af44a02f825558a87,
mkSt [w130,w1,w75,w0,w3,w4,w5] 0x1d8b16cc3b666bd501a65d321807c38a330a88482c6c403c100844dc0c006834d0ae4200b00afc44077518706,
mkSt [w1,w2,w0,w3,w4,w617,w5] 0x4622f0774395ced859b116aa849190ca732c14848e5198886840343c5c282cac04dc20a45410840c000fc0f44e441cadc4042542a560888,
mkSt [w330,w1,w2,w75,w0,w3,w4,w5] 0x1f258d651b9b6417151a641714d802644ace9854566415dd5808009c2c683c10086c443834f028dc000c078ae41f0ae8254b04b08adc2cd20709,
mkSt [w330,w1,w2,w0,w3,w4,w5] 0x22061996152daa109991220885a51062015995108882cac086c6438f0dc0c003c0fcae4b0c254ae8b040f42cd20588,
mkSt [w1,w2,w618,w75,w0,w3,w4,w5] 0x3a296a311e1d6cfe295d00fa357101ace2295d00000cbe155108cc88c40d940f0683c34dc2c2810c4ec0c00078b10af8b18b14254af072120788,
mkSt [w619,w1,w2,w75,w0,w3,w4,w5] 0x392121151914f6061e1612061e120009091cec8a0a0225211901920d04868d0084464343c282cdc000c40254b24af0b1cae4b20afc77520708,
mkSt [w1,w2,w75,w0,w3,w4,w5,w29] 0x1a1dd9fc5c597d7d99741ddc78358dbdbc9855ac00dcdcf9350cc5a4403880dc282c5410c40c0044d848343c254af8adcb28374044b2c01558808,
mkSt [w26,w1,w2,w75,w0,w3,w4,w5] 0x3e851e14f770a94bee0a747c606172bfbcce1d19a142850a14902c280cc46848dc54004440d03c34b3c050ae434c028b38af118787,
mkSt [w1,w2,w0,w3,w224,w13,w5] 0x4d66a6599c560ab27a915e73803b6050c898a940e93411e068d83c382cace020285410840c645cd034a40024cb484e40f4b50b4c4042a560988,
mkSt [w620,w1,w2,w0,w3,w4,w5] 0x162b561a7630b365a28a355a6ab166cb4500ac443c085820000cd864a06c4e4b58b54b5c2542b40fd18587,
mkSt [w1,w2,w0,w3,w224,w5,w29] 0x25cd23e107d91705d716df1ddb18d68303c312d08e4689c380444d83c2c5410840c648048342800b68b6424c0f4b6004401558907,
mkSt [w621,w1,w2,w0,w3,w4,w5] 0x18eedda851a86c675a29867560e0d8ceb40638643430200c402c14d83c280042441c404b7024c2a518606,
mkSt [w622,w1,w2,w0,w3,w4,w5] 0x15a2119a15ad2a018d24da09a11cc49a158d40c00002c44183c086c6434380c00078ae4adc1f0b0cae84402cd20588]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p3 : List StD := [
mkSt [w1,w2,w623,w0,w3,w4,w5] 0x1df6cfc97e684bf381c47ef5983397e6a2062c483c5c6434fd241c201008ec0c00078200b7cb78440b1472118707,
mkSt [w624,w1,w2,w0,w3,w4,w5] 0x179b564c9964e1cd15963d11d1b0c39a2b061848346c3c08502c280c0040b50b88b8c24c4a02f918586,
mkSt [w625,w1,w2,w0,w3,w4,w5] 0xb8e9eaabaa4d8c7258e2c9198a0cb8e8300002cdcac1808643c340c00b50210b90afc44077518506,
mkSt [w1,w626,w2,w0,w3,w4,w5] 0x176b567aee7250a789c50a789805ac4f0b5ab444342c682810006c3c3014b9caa4b984d024c2e118586,
mkSt [w627,w1,w2,w0,w3,w4,w5] 0x1ce4d0a48c93241e52cc645e520d841dc8d08d08244428543c0840006c04382c0cba0bb0bac2540040d40441f001520609,
mkSt [w186,w1,w2,w0,w3,w15,w5] 0x3e3a35f22da9e21d1dc580148000003e000dc8c5000e83c3830d85828241c201448b840040fcbc82c4bc40d00f424007d20788,
mkSt [w1,w2,w24,w3,w4,w183,w5] 0x3a6640209260f60e0e22312cca68aa1e5e64d2419e4cc5c8c201c64340860303c5804141f0be8be00383a8be4bdcbd824d20709,
mkSt [w17,w1,w2,w24,w3,w4,w5,w29] 0xf0873be09047043218e4544221aeb55906030a74a80112783c09cea60010c4403844d8281c483c04cc2c3034146008c00bf8bf0c04bf4bfc96c01c04560809,
mkSt [w26,w17,w1,w2,w24,w3,w4,w5] 0x212a71ca5d12363bbe4e67613ba546003415db2436301842095ca9d2e771395c44a484642c483cf0288c0430cc341408bf0c24c20030c18978c1cc1405160809,
mkSt [w1,w2,w0,w3,w4,w628,w5] 0x46612077cb944ab96124dca890018cea72248e42655090c4e8483c3840f03058288c1c20101400b80c0fc9082543a8c34c30c2cbe80d160889,
mkSt [w629,w1,w2,w0,w3,w4,w5] 0x2616161e0214de2214e08a061585899e1a14d08c498441c68403c2c0414000fcc3c24cc38c2c50040825520488,
mkSt [w109,w1,w2,w0,w3,w4,w5,w29] 0x202657098996d1111590327231b130707215b130f0327231b13020f038cc8044483c34302814d800338bfc374c4426096c254c2c01c974c40c492060c,
mkSt [w26,w109,w1,w2,w0,w3,w4,w5] 0x35012a0111aa012d2a31812d2a05a4012d2a118165c15d01010101010901cd034146848442c28403c00c50c4c030260c3c978c14c4520688,
mkSt [w1,w2,w0,w630,w3,w4,w5] 0x3e3aaeb709f339c9eea5e31e0e81cdd19a169315d30d06880a034302c8c208454c41cd814424c58c64c60c5c408c6807824c0d06c42612078c,
mkSt [w1,w2,w0,w631,w3,w4,w5] 0x1f7b8fd5947ef2f3c3e97a3c3b744b47a24e88486844d0cc30508c201c8400144034c34c6cc2c078c3c0d024518787,
mkSt [w52,w186,w1,w2,w0,w3,w5] 0x116aac1ab310d598cdd58b35a9d1ab09213648280844403c2ce43804c4d8e80fcc740d0be85b918605,
mkSt [w2,w150,w0,w24,w3,w4,w5] 0x3a210857c39506b862a100e184aa0de474340d4a652220883cecd8cc403050843408d41c0420c414268720c78260c80c7c24424160808,
mkSt [w632,w1,w2,w0,w3,w4,w5] 0x1662451a551cda5510ccca5504c8c89a5504c0c0c883c5044d81c04ec34268c3cc94c90c8c338c980d024520409,
mkSt [w1,w2,w0,w633,w3,w4,w5] 0x364dce417671e96e4dc1616661e0c8c5465dc544d40403c582ca41c1030c44834d40cbccca4cacca826c24c4a40d0ca120689,
mkSt [w1,w2,w0,w634,w3,w4,w5] 0x179b360c599cead2c1c68ccc1a35cf99aa56a84828cca4843400d414d030bcccb8cb4cbc0d024518586,
mkSt [w1,w635,w2,w0,w3,w4,w5] 0x2980359270aca589818269802580211d9d948005c8c20501c845408c43430041421424ccc8cd0ccc0d0cc4aa426920689,
mkSt [w1,w2,w0,w24,w3,w4,w97,w5] 0x396640debe617a8242605ab6655c41f2ad6d4888484692695e421a5243844ccac208448343c3008c4041c142681f04c04b8c00cdcbfc24ccd84c52078a,
mkSt [w1,w2,w187,w24,w3,w4,w5] 0x3630b22cd614e84cd094e45a1094c1dc621081e05c448345ccc24840840583c301814d00038cf4cf07b8cfccf824d20688,
mkSt [w1,w2,w636,w0,w3,w4,w5] 0x409f2b97bb5d921103ae40e11512e48e037b0d8d2371b0d8d068302834a0e4c8241c1014040cd8805007bccfc24c7b85a00fc58425560809,
mkSt [w186,w26,w1,w2,w0,w3,w5] 0x94da60bdb494cd72e530a142940af82b228143c28109468d890b8d04834301440d14bcc1f0d100f403118706,
mkSt [w188,w1,w2,w0,w24,w3,w4,w5] 0x2629aa25ae28e59a14c0219a14c010859a14dc1048419a14c01081884d834440400483c302014c4cecac026cd24aa4d20d1c24d20588,
mkSt [w1,w2,w0,w225,w3,w4,w5] 0x2e1615c0e9c8da0df0c22e29d4e550de21d4de1cdc03044d82084002c3404483c1426cd302543388ccc10d2826120608,
mkSt [w1,w116,w0,w3,w4,w13,w5] 0x1d2e8394536e65d78b540a7661c72f22921c10d4345cd8ac5084142804d0203c00408d40254470d3c2a518706,
mkSt [w52,w1,w116,w0,w3,w4,w5] 0x322d3e38f20d35f20dc0dc6a0d04c02481a108c1448345cac405084d4c8142820603c0400d403d8254108d44be84702cd20788,
mkSt [w1,w2,w0,w3,w4,w637,w5] 0x4e25118843d82cd8622d58ca8490550c64241086b06120c86c48603c50405c2c28ac1ca4200410140c00b80fc5e441cd404085182542a560988,
mkSt [w638,w1,w2,w0,w3,w4,w5] 0x222219961519a61059912208458910a201599510484ac684038f0040c003c0fcd4cb0c254be8d482cc0f520488,
mkSt [w1,w2,w116,w0,w3,w4,w5,w29] 0x281b2baeaea9edee68542f2feb8e562e2eea8e14012d2da84d1506046050d480d83428042c84140044483cd5cd402543d8d60d5801c374d50d540152078b,
mkSt [w26,w1,w2,w116,w0,w3,w4,w5] 0x21415f8143c5c15d5b99c157558dc0c1434589c8ccd251414141414149034645028d0c86848d4041400443c40030d68d4c34c028d64d5958807,
mkSt [w1,w2,w0,w3,w331,w13,w5] 0x25230d20e11f1c9b1b08d9c197c5c5d0510192c28fc48d83c385c2cace02010140c40d03428a49424cd745e40f4d784082a558907,
mkSt [w639,w1,w2,w0,w3,w4,w5] 0x14074e1a55f0c2919e8b27192a4184e33d048c48b83c5804000c4440685e4b58cfc2542b40fcd7d18507,
mkSt [w1,w2,w0,w640,w3,w4,w5] 0x1d376e0e90f63297ad87493824352f0f0f67084034302caca404845414483c28c442441cd88d8c40824c2a518707,
mkSt [w641,w1,w2,w0,w3,w4,w5] 0x159a115a154d26218d20da155d04c49a154d80c000044043c684034381400078d4c1f0d40b0cbe84702cd20488,
mkSt [w1,w2,w642,w0,w3,w4,w5] 0x1d92a6db79265bc9764d7d0de032b7911c062c485c444034d41c0420843cec14c4078200c88470b7c72118706,
mkSt [w54,w2,w150,w0,w3,w4,w5] 0x1bc68fe7bf29b2e36dd38f36d00365c68676c86c6050f0d41c0400ec142068403c078240d98c7820047072118707,
mkSt [w1,w2,w0,w643,w3,w4,w5] 0x1df7ef0e3f23f7f529b79f119b32e7f20734cc48343c5c2cac8c280414100cc440d80da4da0b8c24c4a42f918707,
mkSt [w644,w1,w2,w0,w3,w4,w5] 0xb8e9e9ab8e3d8c71d8e5cd058a0cb8e83000028ac043c4050341400d80210b90cb047077518486,
mkSt [w645,w1,w2,w0,w3,w4,w5] 0x1353c72accfa50a7d9ad527d9ba4a14fb300b44434043084683c2814b9cdb4aa4db04d424c2e118487,
mkSt [w1,w2,w0,w646,w3,w4,w5] 0x166a494255494e4d490d726d68916506554882451c444d8342884146840042c3c00dc0dc82540041f001cdc40d401520609,
mkSt [w1,w2,w0,w3,w4,w647,w5] 0x42610f86cb5db0c96128d4e894898dae722c9542637128546840343c302858042420a4540010840c0fc0f4500ddc24cdd8dd440425560809,
mkSt [w648,w1,w2,w0,w3,w4,w5] 0xfe7ac4e8e21f34b0dbf24b11927ec562334483c50e86038f024000c0fcde4358de0ae80d00f518487,
mkSt [w1,w2,w90,w0,w3,w4,w5,w29] 0xd286c40964b88924931030436190b84c0a050f85c0a000480c120d0582412040cc50244480d8343c28305410c40048200c33893c260dec254de8df004560908,
mkSt [w26,w1,w2,w90,w0,w3,w4,w5] 0x22a056c015cd0802bd5b0e6029d5b076038158a685b19cce074a8140a05028149050d028340cc4684824205444402c3c00df8260050de434c94cc14df560888,
mkSt [w1,w2,w0,w3,w332,w15,w5] 0x22a140191f1956cad6df1d9b8985838014800000000d04850241c3c300010840c9460044034280d00f4e002c024006558886,
mkSt [w649,w1,w2,w0,w3,w4,w5] 0x180bdf1a7638a34be294695e6b414757c506d0d034100858200c5000606880e10500a6cb5424c0fc2547b518608,
mkSt [w147,w18,w1,w2,w3,w4,w5] 0x27591b90275b0466d9c588269a881e441d1825c4c4243c54105830340028cc38f0180ce34e30008e2c35824ce28ae81f120709,
mkSt [w18,w1,w2,w20,w3,w4,w5,w29] 0x150a750a050ca7c3e174a53c06034c5000e0708a52a08e008241284a500880840cc44d834483c300c18f02c28005020e381dce40c04bfce3c93cdec01c0456080a,
mkSt [w26,w18,w1,w2,w20,w3,w4,w5] 0x2323754a5e12843bbe5480013ba448253415c92d4629c40a095c8dd2e771395c4440200c502c483430cc2418f0283c5400e38e4ce4894c030e44c14c1805160889,
mkSt [w1,w650,w2,w0,w3,w4,w5] 0x1a37e70c18314699c3110d9ef068324f8e830468342c28100060d020243c4414e544046dc0780d0e581dd18687,
mkSt [w651,w1,w2,w0,w3,w4,w5] 0x39328aa6262620c516948080809e18c080808202000483c6840cc3024c400a40c34b820e54e64ae8e5cde4e60dd427c1dc0d12070a,
mkSt [w1,w2,w652,w0,w3,w4,w5] 0x46612f5341a0d0030180c10c952ac426080180c067300148483c3438cc241c205410f030000c68b804290b14e6ce70338e741dc0d027d60889,
mkSt [w1,w653,w2,w0,w3,w4,w5] 0x308e6e5c81c1e4a52a41c001c1c001c498625dd844844348c20102c0030e838d40ce8ce8821ce84e800d024c2941dd20609,
mkSt [w654,w1,w2,w0,w3,w4,w5] 0x19efd73f1239766dda040810e3b081021c6800803c3430cc008c0c68282038e8ce98e901dc27ce940d118607,
mkSt [w655,w1,w2,w0,w3,w4,w5] 0x2c4edaecd55968659ad15d614edd5140d55ac0d15d4e824d00c143440043c0044e54eb0eacea4ea00781dce584d0ea82912058b,
mkSt [w18,w1,w2,w0,w3,w4,w97,w5] 0x1591c0b28dcdd681d18cee8989a8c866a1e1a1ddd9d681d18cc0884203cac1c541030048060502000290e304c41f0ebc1dcdeceb824c4c12060a,
mkSt [w226,w18,w1,w2,w3,w4,w5] 0x24e38da08adf9c90db909846c786969480d59290868643c8c1c5410f008cc180c28346004583000ed0a6cec8ecc24cb5558906,
mkSt [w1,w656,w2,w0,w3,w4,w5] 0xa21a20881c1e8a62181c881c1c001c4961d99d440080483410c40cd03c4400ee421ce8cee0edced82941dd20508,
mkSt [w188,w18,w1,w2,w0,w3,w4,w5] 0x261dae25a21ce59610e8858610e888a5a21cc08018259610c00188800343080605014483c20000cef0ec0ec82940181dceec24cee920589,
mkSt [w1,w2,w0,w3,w189,w15,w5] 0x98b8025850563a09f5d1b98d75916c0148000000003c44606434241c040010840c946cd8405020f040f4f000d024001558906,
mkSt [w2,w21,w0,w3,w4,w15,w5] 0x2a68e6e5a585ab4961499c4002db996a9294d3874e8e8486038405830a810848ca41c04943cc42cdcb80cf182c0f1cf1429c24158a86]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p4 : List StD := [
mkSt [w1,w2,w0,w3,w15,w227,w5] 0x2e2105879921f08203ba1c701039e0e68282aa00e95429d4e8382c8ca8414c10281c48d03c300c040f4f204e00d0f2cf282c029d60808,
mkSt [w1,w2,w0,w3,w4,w657,w5] 0x29ed3695459f4ea61b518cba512114c833d184284619888603c3840b830282c8c1c0420a800c41084940c0fc4e01a4124de04f0f142c029c2416098a,
mkSt [w658,w1,w2,w0,w3,w4,w5] 0x425d2d33cb14ea19519856a074181caa52038000e750b80c443c68345824a4180c2c1cc4b8383004134f3c108f302c0f38f340d029d60809,
mkSt [w1,w2,w0,w659,w3,w4,w5] 0x3a7275ba4035a668b1800a5c99889856549184848c84434387c282c24201c541094dc0c134f58f4cf54f500d024c1082c520709,
mkSt [w660,w1,w2,w0,w3,w4,w5] 0x17e79faf5ce972f3610f7e759311e0ceaa228444303c0454942c003824e80fcf60f54f5c24c2c424118587,
mkSt [w1,w2,w0,w20,w3,w4,w228,w15,w5] 0x1c001e926291d201d1b81c1810cdce524174cdac01f1580159a18164f1001c3da02d605848d0f06450243c340428201800a8414c1084940cf64f742c0f6cf6824c0d158a07,
mkSt [w1,w2,w0,w3,w229,w15,w5] 0x42210042c390a8486a110a6c86201d66a24c01cec66130d8e848382c243428a84150103c30dc0c200fcf7c0d05e00f4f802c429d60808,
mkSt [w1,w2,w0,w3,w4,w661,w5] 0x566933994c582cf971b524cc9612114c933c9844856118c8e848603c5040302c28241ca40420a8141084000cb80fc5185e0f545f0f842c429c24160a89,
mkSt [w1,w2,w0,w662,w3,w4,w5] 0x3d3a1201c1c1f0cd1230eca92605e4c1d501c114d84483cb82c24201ca810000c344030dcf54108f90f88f8c2c429c0d120788,
mkSt [w1,w2,w0,w3,w4,w663,w5] 0x4a5ce048cc1dd2c9699d56ea948a152e831c9442a4719884e83c3840b82c30588c1c202804001014940c0fc3a8de0c30fa824c2c0fa424160909,
mkSt [w1,w2,w664,w0,w3,w4,w5] 0x32aaae02023632802e3486a61e220616891a020106028443438a4241c1014942c0c04134fbcfb8fb40d024cfb0fac1082c12068a,
mkSt [w17,w1,w2,w0,w3,w4,w228,w15,w5] 0x2830bcbc72d4cf52cab50340618a662b8ae98d0a146ab213028401018203040d0483caca42804644050342c20840c2c4fc0fd00d0fccfc518786,
mkSt [w148,w2,w0,w3,w15,w13,w5] 0x1db0009c01c8b2803c05eae80335c6ac75c29d2485391983c45505434acd020a8400010840c6c50a494140fc4240e8fdcfd8fd42a40f560988,
mkSt [w79,w2,w0,w3,w15,w13,w5] 0x1a250328c10c870878b89a6c8038c966b1540180e934085ce83c44645434aca4a81084946c405014200c0fc9fc2a4fd810cfe00f424d60908,
mkSt [w1,w230,w0,w3,w15,w13,w5] 0x1600e03941140f188081dcad861add4aa34c09c0c853b9983c4424e034ac04d0a4a81084946c5020400c0fc1080e8fe810c29cfe40f560908,
mkSt [w86,w1,w0,w3,w15,w13,w5] 0x1a612119c84ca72988c11e6e96a02186b1548200a43409e03c4424d034a8401084ac04200c6c50a494d81c0fc910fd86bc29c0f4fec10c24d60989,
mkSt [w1,w2,w131,w0,w3,w15,w13,w5] 0x2340b3dd2a8c0b8d40a42e68d409f6e600328100b4b088448a3d820ac4b240ec3c382c6c64d0a034acd8e0a4a84150108494200c1080fcb50b48ff4ffc10c6c8ce0ff80f560a0b,
mkSt [w190,w1,w2,w0,w3,w15,w13,w5] 0x3682e2f6b9998aa082d9b68242d59472a2c2698ee6caa0821d81544ec3c68a9501094403438a4200c44841080fcd80ff900100c10c6e10040f50092070b,
mkSt [w1,w230,w0,w3,w4,w59,w5] 0x25a7aba988df27a4619edd80071ad897944510ce4c8603c4424406434aca404a814c01084946c50200c1c0fcfe443101429c24158a86,
mkSt [w1,w2,w131,w0,w3,w4,w59,w5] 0x1b3b064ae26c67dc09ccd37d825ccd3002ec1a164c060308b388981a0d2b034443c502c6c64a034ac1ca4a854108400040c201342d80fd0243d80d0ff5020ce06c901c5182416098d,
mkSt [w190,w1,w2,w0,w3,w4,w59,w5] 0x322beaeb8d9a2b49d94cf030d96d2e2a84583030322801d98c012c9860502c1c3c14944440343804200c841340d00fd0450002150390046e10346042412078c,
mkSt [w1,w2,w0,w3,w4,w15,w87] 0x4240c087cb186ce9690198cb9510194c94448000c7631148e83c442c50ac1c20a81084946c340c04f04680214de068c24c68424068960809,
mkSt [w231,w86,w1,w0,w3,w4,w5] 0x25675f25615f1d44db185752d512928f514f0e4c4003c44406434a81084aca420d01c006c50040c240fd05104c0d024158985,
mkSt [w231,w1,w2,w131,w0,w3,w4,w5] 0x33df9a7cfccae1e6006ef521b76dc3a43515db75e90d002624443c6ca01420e8d838f01c000fd05d0590546c904024118607,
mkSt [w86,w1,w2,w69,w0,w3,w4,w5] 0x1881000100126c81ea4101002661e09900165dc10d19001651c1008d06c741c2408443c580c006907106106c0d10681347980fd06520589,
mkSt [w76,w86,w1,w2,w0,w3,w4,w5] 0x24870f043ae0e1d322ae5d711735e7ae821dcb712b80a20000e8d0580c443c8c6c00480fd0800d107c89d07813518507,
mkSt [w2,w150,w0,w3,w4,w15,w5] 0xda7a4e3871d23a05edd1b8002d916559284d3108e84860682c4034a81084d41c0494ec6c6450200cf04c8108908429c24158986,
mkSt [w1,w2,w0,w3,w15,w232,w5] 0x9cbc027c74765e2cca15fc2ca915c5bd8d695529083c446434ac20a94c0010841c402cd86c500c04f0509909472c0f40d029d58987,
mkSt [w1,w2,w0,w3,w4,w665,w5] 0x4e0b1238c38dc708003cdc6d8612cd86b24c285268338988e8603c446450ac1c0400ec1084946c40200c34f0473472c008038de029c24160988,
mkSt [w233,w1,w2,w0,w3,w4,w5] 0x1ff7f4df92c5798ee58688183330c003064c1048b868402c24200c1cec64046c5034f0410909d0a029d0a40d118787,
mkSt [w1,w2,w0,w3,w4,w666,w5] 0x465d20384b51a8f900391a8c95885168a03ca44e88438984e83c446050ac1c20001014946c400c3404f050cc4b8008038de024d0c824160889,
mkSt [w1,w667,w2,w0,w3,w4,w5] 0x24f600e600f22e00de2a24e200c0c0c8c0da108600c3c50242044401c10940c3414050dd0d80d024d0d00fc1090d520688,
mkSt [w1,w2,w0,w668,w3,w4,w15,w5] 0x27cc03ac272f84244eef569496ac0800e400001400000c000024016448687c343c2ca8108494dc0c202840a790e81090e50e0ae42c0348adc0d024d2078b,
mkSt [w1,w2,w131,w3,w4,w333,w5] 0x1a41a199030916c006df1ddbc189c7d45241910ecbcd85804f03c30a8001084082434280c2c0d00f50f10f42c10f824158807,
mkSt [w1,w2,w0,w3,w4,w15,w669] 0x4a6320784bd9acc9319cdecb9422910c742c808244609a10e8483c3840b8302420041c282ca81084940cf04fc5100f551040d02c4d3024160909,
mkSt [w334,w190,w1,w2,w3,w4,w5] 0x26e109254b495e46dd0d5684d905449052d10d4e4004804403ca81094583000602c142554340c28f00d111110c2c424158985,
mkSt [w1,w2,w670,w0,w3,w4,w15,w5] 0x172204334162d8a02d68cd8382deeed0001c76070381c080b0101c160b0596c48446c6450ac3c282ca8108494040ca43440f5511c1086e111911424cfd8d4c2c43ccd400d16090d,
mkSt [w2,w0,w149,w3,w4,w15,w5] 0x219d9b0d98cb1781070ad5848304c293914f4b4f4341440486038a830241c203c34940c2c28f040d11291242402c158806,
mkSt [w1,w2,w0,w120,w3,w4,w15,w5] 0x3b6e011b3062c18344ed58354a678f06880cdbe0401a215684e84438782c403ca810849424680c0fc1091302c112c24d18706,
mkSt [w1,w2,w0,w3,w15,w129,w5] 0x218f801d9ce4e39a9a9ae19e5e5cda998c5654d2904385c681c3c2ca80010849460414c4434280cf0424c8311382c01f158906,
mkSt [w1,w2,w0,w3,w4,w671,w5] 0x4a02d16843d9ccd8411d10cc849ad12c732418448562124ce8d03c3840302420041c2c28001014940cb8f04830de113d1280d02c024160908,
mkSt [w234,w1,w2,w0,w3,w4,w5] 0x56aa5ba6e0d59b3a08d66f06342a0121c9a0c78681c2c1094343c2844151480fc1091451402c118586,
mkSt [w1,w2,w335,w0,w3,w4,w15,w5] 0x3e0d003972020d2e28ed750202316cc506020544c0e100801d48d4504e83c68502c4004a8108494d4440c8c0fc88010916cf042c516824d20788,
mkSt [w1,w2,w0,w3,w4,w672,w5] 0x52673248cc19ccd939a120cc9492d12c832c984284609a48e848603c3840b8302420041c282c00541084940cf051748acf5517d1782c40d024160a09,
mkSt [w1,w2,w673,w0,w3,w4,w5] 0x188f80b600fd20600052013e18064c9b8b64a4807c6c3428845494e83c2c0cf551891851802c40fc10918607,
mkSt [w1,w2,w0,w3,w4,w15,w674,w5] 0x408044cc86005d3a8102a883c411037500010680000000000400c00000022048b8e8402c50a8103c8494d40cac4464303428a791a010919d1942c42c11980d024d6098a,
mkSt [w1,w675,w2,w108,w0,w3,w4,w5] 0x2abd7aac869174eab16cd4ea914cc014869140c24c545ea1489e9cc88683480502c60a8100c006cfcdcc4d044d1b11a855d1b91b44502551ac4d92078a,
mkSt [w676,w1,w2,w108,w0,w3,w4,w5] 0x36a55eacc69d70aa916ca4aa914c80244aa148ca8894c69d40824c58cd0802c60681034004450040cd84651ad1bc2151b91c04691b02545d92068a,
mkSt [w1,w2,w677,w108,w0,w3,w4,w5] 0x188eb1d931e71b0630e3702013d1d6d40508986bb51000187431a6d02630e18880502cd83c3060c8dc1084ec0cd02834d4002b11d11cd1c821455d1ad1b11b86882547216090c,
mkSt [w1,w2,w108,w69,w0,w3,w4,w5] 0x171081b8ac2ad78c2d60e0b7dad5ced2013216aa74902800882a9dcc4002aa446c7444502cd460c8dca810080c003428d02b03282551b91d82607e91d47991ac08d6088b,
mkSt [w76,w1,w2,w108,w0,w3,w4,w5] 0x68ab9f685c9b2a5eda8daa5e194c01291c98cd1d44245c99cc0d8d0c348880502c60c830d404a8003cd91b91ac2548bd1e021d1dd1b089c0bd2070a,
mkSt [w1,w678,w2,w0,w3,w4,w5] 0x35e525f0c5d12c85e528ce05e600c00219c20202000606c041834a8100cc42c443cd0260f14124f1d1e8d083284d920688,
mkSt [w77,w2,w21,w0,w3,w4,w5] 0x1ce34b6103095edcdb40d896d5450000d0c0c0cec0c3c30a8d0108ca41c044000c4342c0cdc611f0d082603284d958885,
mkSt [w1,w2,w0,w679,w3,w4,w5] 0x41deaf70411c6ae413b5408c253ad410140415c100404020483430cc24c8205410840c94403c28042612051f9200e091fc24c27960808,
mkSt [w77,w147,w1,w2,w0,w3,w5] 0x21648762e164dc5b4a84d90757051512514284ce4285c243c18a810d02d5c48b800280c6038dc4120c0f424ce0835958905,
mkSt [w680,w1,w2,w0,w3,w4,w5] 0x19ae0eaa7864a8c30a876c1c3870efc6050000d03c302420400c0060580434260f84e092101dc3285d918607,
mkSt [w681,w1,w2,w0,w3,w4,w5] 0x312ced261226209104ce01d901c1c1c1d104c1c1c206434d8cc8c400c146030043cd0826121d218fa922024c25120608,
mkSt [w1,w2,w682,w0,w3,w4,w5] 0x7215d611edd40dac5411902d7548000cec0c0c000c68d83440d41c041084ec0c946c605020b7c20026032872158805,
mkSt [w77,w2,w150,w0,w3,w4,w5] 0x3615f215cdf00dcdb18d744d5128000d0c0c0cec0c6834d81084d41c044000ec6c500c20611f522826032872158805,
mkSt [w683,w1,w2,w0,w3,w4,w5] 0x34f4ebb4e71d1719d03160c183062c18306146c60341c200c1450680448b9d1f523026024c2e118586,
mkSt [w1,w2,w0,w684,w3,w4,w5] 0x172a95076ea6c1734064b75424a06ec180060c3068603c2c10140c9444d03428094200260d0808d18685,
mkSt [w77,w2,w0,w149,w3,w4,w5] 0x176aa4016926d2710065b55254300e803200003068603c942c400044340c28d11f523cd0826008d18685,
mkSt [w685,w1,w2,w0,w3,w4,w5] 0x3629caa2ca559711d03160c183062c183061468d03c280c54e8342c491f40c42601dc0bd18505,
mkSt [w1,w63,w0,w20,w3,w4,w5] 0x461f0d334409e64872b540ec8610cc00b5541c526720a9c8e8403c28342418ec10840cd444f05020003407241f124d24524825427960888]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p5 : List StD := [
mkSt [w50,w1,w63,w0,w3,w4,w5] 0x419ecc42d3a854066ab1174a630a5094003b048480304108443c5840502cbc1084d40c30002034d924d2444d81f0f992552502547245d96080a,
mkSt [w1,w63,w0,w3,w4,w13,w5] 0xd9da4e3871b219e9cdb1980c4c516958c8ed3104e8403c442cd834ac20ec10840cd480d050a40126524d2611982542a558906,
mkSt [w52,w1,w63,w0,w3,w4,w5] 0x3e271278c41dc6087bb8dacc843acd42004c0184692020c83c34446048502cbc1084d40c804020a40038f126d19825524c1092687242cd60988,
mkSt [w1,w2,w235,w63,w0,w3,w4,w5] 0x212397b125c42624a91ac2424b096c04042654836120001089289d8c4543115044345850d14840d4ec10c40ce83c2c00f4124c1f12852742552792444d960809,
mkSt [w236,w1,w2,w63,w0,w3,w4,w5] 0x1e76599e70d99e6d49a95645499540264c618cc14d5e44d981421450c3c58402cbc104434d4000c5048f992441f129025529524d27c5d920689,
mkSt [w1,w2,w0,w3,w4,w686,w5] 0x27dfe523c6dd21c09f1cd9da9f04d695d28d22ce4c868403c44483404d420a81410840c80d050a40126400803919841c2542a558987,
mkSt [w151,w1,w2,w63,w0,w3,w4,w5] 0x232423e4238d641f9f5ce41f1d1c02e44a8e445c5d641ca1200801a044502c3cbc1084482800e830d4380d26c1f025524524d2592a11982cd20789,
mkSt [w151,w1,w2,w0,w3,w4,w5] 0x121a0dfa34f1c604cded2a08d9e48492010dc0c488844605020a884480c3c40e83800d526cb0c0380082540f42cd1c920708,
mkSt [w1,w2,w63,w0,w3,w4,w49,w5] 0x249fd85c571b9c1a5a579c209b56469e84db168411251159d51166904044503428d458ec10840c00d0603c2b01e41c91992a40644ed2a924d20789,
mkSt [w58,w1,w2,w63,w0,w3,w4,w5] 0x12fa0eea36c56a16c548e212cd74c0322eed5cd8606a028542c0c0dcc3c28bc10e82cd4c40040d834585119924c7241cc1f42552b05ed2452ac07d2070b,
mkSt [w1,w12,w2,w0,w3,w4,w121,w5] 0x22f1801421e8f75c38dce145c345ae1461ae012070a28d22883399ce84321108443c3458a418e82820a8100c00c42c0548108f412c00f52c52bd2b84d873160889,
mkSt [w1,w2,w0,w20,w3,w4,w121,w5] 0x27e402e74cc83433cacfa79898d82f25050acc169a64354a0d59586848f050243c18a81084000c203428dcf641087302783400f4f752cd2b83312c92d024d2078d,
mkSt [w50,w1,w2,w0,w3,w4,w121,w5] 0x10c8801421e8164438dac14443058c1459aa08c464a10ca488048182873309483c38304820f4a810442804000c2c2434108f992dd2d80f52d52cc5d873160809,
mkSt [w17,w1,w2,w0,w3,w4,w121,w5] 0x1d1dc0bdf0f11de86904defaf6c6eee5d51520d48addc24104c2821483ca44834f428a810802c8400f0045024c7301092cc3c8fd00f52e52e02512b92078b,
mkSt [w1,w2,w0,w3,w121,w13,w5] 0xdc9c027c74765e2a09f5ddb19055715cc8293504f03c442cd034ac04e020a810840c4880d850a4012652cd2ec24c7300f42a558987,
mkSt [w687,w1,w2,w0,w3,w4,w5] 0x120a39b631acea1188e8a60588e044960188c09c8183444d05024a88420008048043c0d2f47312f0038008b582542b520708,
mkSt [w1,w2,w0,w3,w121,w49,w5] 0xdc9cc99d8e50be2a104dfdc9b18d695c28312c28e4382c988004d03c28a810840c4844603458001c92b824c0f52f92cc06558907,
mkSt [w1,w2,w336,w0,w3,w4,w5] 0x48890588bc1cd0037a9200e23718e18e03592049097019cce8305848a40418bc10c40c002c343c1c44411e92fc0f4f1c55c724f404d960908,
mkSt [w688,w1,w2,w0,w3,w4,w5] 0x32526d1e69d1ce60911dce545105d48e489101c001c443428502030840c3c68400034131530c0f5311200f6024c27920609,
mkSt [w1,w689,w2,w0,w3,w4,w5] 0x3e3a29b631298a2ca98902056981002618799514800e83c30582034ec10840c004438d448f980f52101dd30d3207245d920788,
mkSt [w1,w690,w2,w0,w3,w4,w5] 0x13cbc43ef4a050a50e850a50e801ec4a2d5ab46c3428100044303c143c932c3d922132824c25118487,
mkSt [w691,w1,w2,w0,w3,w4,w5] 0x15b34cbd4a60584142ae759158d0b4828500343c444834201040146cd0500126442441c2a533824d18606,
mkSt [w79,w88,w2,w0,w3,w4,w5] 0x9255f62e11f44c91d5a98c917564494d09350810e83c446434a4206854bc1084a880504814d40134133c6b424c2a558905,
mkSt [w1,w692,w2,w0,w3,w4,w5] 0x7ff96efaf35fb65a90736581809e6ff3914003c446050d4a4ec10840c802048380126cb0c0380081f07242cd18787,
mkSt [w693,w1,w2,w0,w3,w4,w5] 0x196e93018806dc56c055156e22c0188044002868483c541030402c0044d0340c1c80640741e41dd18685,
mkSt [w1,w694,w2,w0,w3,w4,w5] 0x2a802a48ddd014e50088009001b129aa58a86c3c28482c1000443430141cc07c0841f41f118585,
mkSt [w2,w21,w0,w3,w4,w5,w81] 0x2927e5dd5d5dd6d71bd7401513d142ca870dcb46c4844d040683c383458302cbca8548ca41c04dcec1426135535935c2ec2dc24158a07,
mkSt [w695,w1,w2,w0,w3,w4,w5] 0x2322e09192a24a0d6191200808090c20080808210c3c382c8c2014281cc434300537136d3693642ec2dc2000d120608,
mkSt [w1,w2,w0,w696,w3,w4,w5] 0x3631ae023631a8a22d820a1a15961446061184848c8607434f02c2824201c10ecdc0cf645c137c5c824c0d02002f120688,
mkSt [w1,w2,w0,w697,w3,w4,w5] 0x415f0e8228140a25618e186b5512602a93228140a6131984683c382c2824201c94540014443430dd37d38d3842013882f02dc0d160808,
mkSt [w1,w2,w698,w0,w3,w4,w5] 0x20236426cee40c2020242252264c21e1c5a44c4d44386c2c8c201c8454ec342804153a021d39d3993940d02ec24c20120689,
mkSt [w1,w699,w2,w0,w3,w4,w5] 0xf96b6ab5964e9cd21867cb41801a9960b140058a4184034fca85414c4f2caa51e93b87784d918506,
mkSt [w132,w2,w21,w0,w3,w4,w5] 0x158b4ebd58a5ead301be8cf19805c38a230a88e86034a41c1868c444fc40f1c7253c13b87784d918586,
mkSt [w1,w2,w0,w700,w3,w4,w5] 0x1ffbf70e3f6c78f742377f340343e7f68428c848343cf0cc24c828200410140cec40f653c92013c53cc24c27918787,
mkSt [w701,w1,w2,w0,w3,w4,w5] 0x1393268c392b67c959961cb49920c392830000482c20043c34140040f952101dd3c47785d918486,
mkSt [w702,w1,w2,w0,w3,w4,w5] 0x320a290e214d0141490d5e1c6d15588141490d40154443c34f0288404546ccc50143d13e13dc3d92213d824c25120608,
mkSt [w1,w2,w0,w3,w4,w703,w5] 0x1cfff1c1c7720fab307b348387470d1b64e8c406cd85004208c140010840c4460343385013f53f024c91825518787,
mkSt [w704,w1,w2,w0,w3,w4,w5] 0x4cf03960e31306f9d13540c1ab26c418306a844508c60000c34e824de07707681340d00f518486,
mkSt [w1,w2,w146,w0,w3,w4,w49,w5] 0x2bd82ef2f333d80e1e33d82b66f2a4da679e72640dd9245db065252844acd0343c288c58ec10840024640d409400134338be53ec1c93f84ec2613fd4052078c,
mkSt [w58,w1,w2,w146,w0,w3,w4,w5] 0x2b37ff078b7ada4306ad993aebd5a4860d2674170dc0865c183428d8ac04440c6c6050248cc4400141033940c5ece2940013518787,
mkSt [w1,w2,w0,w20,w3,w4,w189,w5] 0x3eae816aa4e4fa80c0e8b694d4e481728ccce4c1d4de90d0d8c8c8ccc4468f024d83c3418a8102800dc0c20340334c0542093c0d00f433942541d2078a,
mkSt [w17,w1,w2,w0,w3,w4,w189,w5] 0x1e16c12ee8ea1ae0d6109ee4e608e0dece0e10ccccdac0d6108101ccc3c34a428446c6050841c003c83c08fd42d41c0f496c0d03394294212058b,
mkSt [w705,w1,w2,w0,w3,w4,w5] 0xe0a2cf630ec920cc8a85218e56159420cc8801c5946cd834dc1084200c04686074012f403800824cac08d050025520688,
mkSt [w1,w2,w706,w0,w3,w4,w5] 0x123dba1db21ccd8181b0c5ae2864c58d81819cc01886834385ca41c24102c000cb8e8300433943821143d44030c0d030520788,
mkSt [w707,w1,w2,w0,w3,w4,w5] 0x11516a8e84ea52562a05d190e891900c2d680e50907c208c540034283c0c242154545d54514485cc24c21034144c3112050b,
mkSt [w48,w1,w2,w0,w20,w3,w4,w29] 0xf76cbda33077b2a5ae0313225ae0a5125832b70904920761c91c003230818483c68d8346010280020e880187444dc0d46945c211464354c0493cbfd4603416088a,
mkSt [w708,w1,w2,w0,w3,w4,w5] 0x2d126a48dcd25919a664cd010101218d0101011901868348c005c200c38442c2545547540030546c2103114700d120589,
mkSt [w709,w1,w2,w0,w3,w4,w5] 0x2425ac252ed426ad964a24acd6094400ad9424260850d02414083404283c4000134fbc3c948948147d49148d48430c2112058b,
mkSt [w17,w48,w1,w2,w0,w3,w4,w29] 0x1527a2256110a7e39346e4631046c2a4e251d5d426256110081c45d4d834281000e8746c80f460504404843d142d460c043c949896cbfd46920789,
mkSt [w710,w1,w2,w0,w3,w4,w5] 0x1c1998199ae4189aa6905a4e6505061c1c18181858508c106844d0200034241549069d2640fc69024d4a40d021120589,
mkSt [w79,w48,w2,w0,w3,w4,w5] 0x1cd6edf7cf6db1796e02275688936ee6c1766c6c6434a4205410840c68501400d8ad4ad4a8a0424c24118785,
mkSt [w711,w1,w2,w0,w3,w4,w5] 0x2a0d0e2caa25189a2121c88080809dc8808080989dc6840508c00200c6034e8253ec3054b54b14914b82100d120588,
mkSt [w712,w1,w2,w0,w3,w4,w5] 0x1c1e6088a0d81ea25a09dd61984944001c1c881c0060345854100cd03c28014dc2154554d94d54d031021120508,
mkSt [w226,w48,w1,w2,w0,w3,w4,w5] 0x1bd5df2e7ed84dd6c3c43ee8b2409bd59709c006eb67832400346810745c8c1460502c20000d42d4e14e821031024d4e518687,
mkSt [w713,w1,w2,w0,w3,w4,w5] 0x4c1a7076e383a73e133169d929004c18306c860d8345810140c3c2840014914f54f14ec0fc30c21118587,
mkSt [w48,w1,w2,w187,w0,w3,w4,w5] 0x1651764cce51402e714e44ae5144c0e89e6560dc988096514cc004818343c406810080cdcd8745c002545d5014e14fd50421030c24d4f920689,
mkSt [w188,w48,w1,w2,w0,w3,w4] 0x21a3a0cd88de919cda908788ce46968184d492908686034dc1084e8146c200c44480474806801518ac14e151424d2f558886,
mkSt [w714,w1,w2,w0,w3,w4,w5] 0x1b201ad41ae2881a6215d959a155581810181819583c2c8c1c18a810c43430040cde1524260d082415203280f520608,
mkSt [w1,w2,w715,w21,w0,w3,w4,w5] 0x22195e0d221164e21d5100f6194d01a4b2056d04e8a4e21d51000004c48a418d44460343cc42c30041c26152935d52d2fc24135472520688,
mkSt [w716,w1,w2,w21,w0,w3,w4,w5] 0x37fd2fd27a5df3cbb4c37cad40ebe7975e017878ef5a0332003c30448ca4186040fcccc42c0434482615395353b935553077918787,
mkSt [w1,w2,w21,w0,w3,w4,w5,w29] 0x1796975191950908551022a261a120888b1492cca1e1e261a12000a04038a41844483cc434302c041c602615408c4f1553c04535c01920708,
mkSt [w26,w1,w2,w21,w0,w3,w4,w5] 0x20821242051e4216125d0204d25900c216124900c8c08e02020202020442c18403448c4d1550f1d54c0f554805002c26135520409,
mkSt [w717,w1,w2,w0,w3,w4,w5] 0x1df6e7bc3ab4b1f0cb071e1c3870e003870e144868b8302c8c1c600c3c342820d01f155c0fd5603f84f024118707,
mkSt [w1,w2,w0,w3,w227,w5,w29] 0x1d426dc8d565c4a72d8c1a309a2af5ebaf3e3c689c382c00444860343c28301c041f156956c0f556404401918707]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p6 : List StD := [
mkSt [w718,w1,w2,w0,w3,w4,w5] 0x1753f73754f97daff1d9aabe5b9071539b2e2434a418446014408c4810382c0401371575578000044338aa518707,
mkSt [w1,w2,w0,w3,w4,w719,w5] 0x241c1768241f0c248cea845c1e684c24001c24266434305824a4541084940c3c2805584260ddc0f4e10240dd8e0920424d2068a,
mkSt [w110,w1,w2,w0,w3,w4,w5,w29] 0x567d3972b8c9912b1c38cab1419f315688c867cc55a232084038cc4460342820480558cdec24d58801c33918506,
mkSt [w26,w110,w1,w2,w0,w3,w4,w5] 0x26007e019bf00b1f8c0111fb4580223f68b01843400000000044403428206848d005594e4cc18338030f6159118487,
mkSt [w147,w1,w2,w0,w3,w13,w5] 0x2462dee109071c9a8acb149496c312904906d10e828483c5c50ac242010140cd8e028a44038d0004095a024c0f558904,
mkSt [w1,w2,w0,w20,w3,w4,w97,w5] 0x17600a9b9a94201b570d5ad9568c10105410101c109918958c88891038483cf034041814102800dc0c203415b8aa55b40195b024c4c520708,
mkSt [w1,w720,w2,w0,w3,w4,w5] 0x209fddd54549d90297c3400140000000108000000c4483cb85824a428615c000c14344030055c45bd5c024c9b81f024158807,
mkSt [w118,w1,w2,w0,w20,w3,w4,w5] 0x269152a0e69d4cce9140048a91424c58969140ccc840169140ccc840840683c0060342820dd45cdc50e00ccc055d41f15d03540d12048a,
mkSt [w1,w2,w0,w133,w3,w4,w5] 0x2df26a41edea5a19d2421e35ea4618722dea64204c0d868403414cc4428603c00041cc103555e0b302400008cd5d801d20689,
mkSt [w721,w1,w2,w0,w3,w4,w5] 0x1ae01a941922481a2095d959a055581810181819583c2c24a4a810003430040d5855f0260e082415ec3280f520588,
mkSt [w1,w182,w2,w0,w3,w4,w5,w29] 0x241ee769e9e52928650ca8a8e5cc882baa675918d9696aa5d918d8008050ec4494603c3430002c200449605600f841dd5fc2615f88c55f401c0192070b,
mkSt [w26,w1,w182,w2,w0,w3,w4,w5] 0x2c81da01c55a01e4da2941e5e20140c1ddda0948c0c091c1c1c1c1c1c4404d05094340c48ec004160d32154c03160802c2615fd20588,
mkSt [w722,w1,w2,w0,w3,w4,w5] 0x17335ea67134238f89843810204087020408a43cb8302c24a4600034d828215c45f01f15c03f824118606,
mkSt [w26,w1,w2,w0,w3,w229,w5] 0x17cf9d9e18ebf0cd560f14752230c4ce94262890403020243428003cd81561cf7d61803002c1f00f518587,
mkSt [w1,w2,w0,w723,w3,w4,w5] 0x29a22201b5a21525a21528ad922c8928a5a21c9510440582044483400302c1c600410c10ee962800001c338aa401920688,
mkSt [w724,w1,w2,w0,w3,w4,w5] 0x1a601a0c1a21c819a08c1948194d981814181819483c588c1c140c343004de1634260240c38d0824c0f520488,
mkSt [w1,w83,w2,w0,w3,w4,w5,w29] 0x679f5d7acbefdd542e5e194761e7c158e89876f0561a260840cc50444828843404141cd963c24c25163833804426118607,
mkSt [w26,w1,w83,w2,w0,w3,w4,w5] 0x2c81de01e0ea01e11a2501e1de00d901c9de08d900c091c1c1c1c1c1c445018d0341c004814844164564154c9783380502613e120588,
mkSt [w725,w1,w2,w0,w3,w4,w5] 0x2e31ae29c9e5e19e1d05c20a0202020201c2020201868b830588c1c0c3c342860201f155c0fc7b4c309b024c24120608,
mkSt [w1,w2,w0,w3,w183,w13,w5] 0x1ebb00dbb735b376ca8094000008911f0d880064d83c38f02804140008d0346058100f565024c40425406918786,
mkSt [w17,w1,w2,w0,w3,w4,w97,w5] 0x1959401111215a42565241c141c1c1c5051d5cca41d9011550c1cc4884834108060502014004c08fc018901660aa566424c25520489,
mkSt [w1,w2,w726,w0,w3,w4,w5] 0x98a964400022000028aac3650a84f9a8000a4a4dc6c603c044448341d6753a167166c21c3d918506,
mkSt [w17,w118,w1,w2,w0,w3,w4,w5] 0x271d7c95b1b1b595b29b18db2553a33b64a82a58c6c1100000a4446034288c6c50200542c3d01f16780d0dc518506,
mkSt [w1,w2,w727,w3,w4,w13,w5] 0x2388175c20df0c208edc200a0820215061cb5d8c60d03c302cac20a4845414d834280842441ccf16882a440801024d20708,
mkSt [w728,w1,w2,w3,w4,w13,w5] 0x234c171c20dc200d8c2151628f1d6248220c9c2048d03cac10302820a400d8342c1442441cec968c2a404040424d20688,
mkSt [w1,w2,w0,w337,w4,w13,w5] 0x268c1f202662d0268e60240d8c2426d4e4cd6154d4686cd834ac20a414501044d042441d6944182a408806169824d20609,
mkSt [w729,w1,w2,w0,w3,w4,w13] 0x14231c234f1c0d8c2021628e9d5160220e5e082048d834a4106844ac2000d0506c1442441d4e169c2a41b926424d20688,
mkSt [w148,w2,w0,w3,w4,w59,w5] 0x965696746dd25629f5cdb588504d493400d10ce4c8603c4414d8d034ac1cc020a810840c6c5450a4000fc4316a02542a558a05,
mkSt [w1,w2,w0,w3,w4,w13,w87] 0x1db1077c01c2ae803b4d8a0701a4c0e0703800866503908403c44d850ac20a4a80010840c6cd03526433868050068c68824c25560808,
mkSt [w338,w79,w2,w0,w3,w4,w5] 0x1d0aacd8132944696d1409565032911eb96400446c3420108440540450a40068156b40fc98424c2a518705,
mkSt [w1,w2,w0,w3,w97,w13,w5] 0x98e80dc50ae6b55660084000001c2dabc66003c4460d0340410008048d850152640f56c024c25401918686,
mkSt [w1,w2,w339,w3,w4,w340,w5] 0x2867a5a30b099e8007871a5843970294d4c58510c4c3098403c38f028ac04a454000818d82c345810216d56cd6d024c40425558a06,
mkSt [w341,w342,w1,w2,w3,w4,w5] 0x28e74b6248e15f1b1d5b1886c746850e52cf505f000d83470aca414100c5c280460242c3d60205800316e424d6e040825558a05,
mkSt [w1,w0,w120,w3,w4,w13,w5] 0x219d9b1999575581071351828503428f8ec90b48c2c24d0d8403c34aca4f01400100c2028cd2656ed12c24c25440558806,
mkSt [w1,w2,w0,w3,w13,w129,w5] 0x15b036df3e760baf666b216a4b7c65cc476243c5c2c44d03428101468e0a40c20012642096f44048341f118786,
mkSt [w1,w2,w0,w3,w4,w730,w5] 0x3e3df9f23171ee24e9255e20453144ce1489114cc886840343c5c282c0424a45410140c212640f483450112c40424c25520788,
mkSt [w731,w1,w2,w0,w3,w4,w5] 0x4b100b802a0a1524613010de1b24b00001400683028a41014d0602c0044244043380fc42518604,
mkSt [w1,w2,w0,w3,w4,w732,w5] 0x3a4236326dae2a514d518a6444ed895e5c94d59154868403c505c048c140010cc28d4212640f48b05004096fd16824c25520709,
mkSt [w1,w2,w733,w0,w3,w4,w5] 0x108f006600f42060002a54f95aa8401f3300a4803430d4683c2820c657057004080fc42518406,
mkSt [w1,w2,w0,w734,w3,w4,w5] 0x1cbd7200535643970252a52422464ea13a68283cb838782824a4100c1468202c6000ae972007809118784,
mkSt [w52,w1,w0,w120,w3,w4,w5] 0x1ab29d01ab2b3b7741d2853615364a8e844628603c2c14100c08e8d0243840017281e4ae807809118685,
mkSt [w735,w1,w2,w0,w3,w4,w5] 0xb21c4640000a190c052990c039340003306006c6034d4f0403ce82821168c3421c3d918504,
mkSt [w736,w1,w2,w0,w3,w4,w5] 0x1f601f201edaa01e5a09615dd99d5c1c101c1c1d5c3c4450ac1c201084ec6c34040d1f4260de17382417343280f520688,
mkSt [w737,w1,w2,w0,w3,w4,w5] 0x5b755cd6eace2715d03260c183064c18306a43c446450ac1c04600c6c34d8217404f47341f03f824118686,
mkSt [w1,w2,w0,w3,w232,w49,w5] 0x2199801d9b1b179492d10f8484c7048d82cacb02c4c68643c38605c2c9858ac1410281c04001c974974c1f109806958806,
mkSt [w738,w1,w2,w0,w3,w4,w5] 0x50e43004805c150c054950c039004800406008c8064340428f0683cd8201c8c981e43d918584,
mkSt [w1,w2,w739,w0,w3,w4,w5] 0x18ed83375429b000c2cb00842858e0ef85063c803c7024140034281c681004078338b157540fc1f408118607,
mkSt [w740,w1,w2,w0,w3,w4,w5] 0x1ee01ea01e52201d91c81d481c1d9c1c181c1c1d483c4450ac201c140c6c34051f4260241778de177c24c0f520588,
mkSt [w741,w1,w2,w0,w3,w4,w5] 0x5f3cebf5274768f98042810204085020408a43c444050ac1c040c6c3460217404f50cc1f00cc24c24118607,
mkSt [w1,w2,w742,w0,w3,w4,w97,w5] 0x20e0dc9b1b1316d8949316c154930090c4c4c50ecec2c8c88d0a8a86ce89c40382c806074ac20101400041c0c4c5788aa41f04c158805,
mkSt [w743,w1,w2,w0,w3,w4,w97,w5] 0x39f3c4b2e5c274992c970e1a4462c59a78285930ac96024668e89c64382c8004104834a40c44004c178caa41f04c518705,
mkSt [w1,w744,w2,w0,w3,w4,w5] 0x3c2450ddaa8ac54b000090a0111db252008c20686034301c483c2805794cd0214aa518584,
mkSt [w745,w1,w2,w0,w3,w4,w5] 0x6806a00332122564a004b546bd68680002400b8581c103428046c44004024300784d17980fcaa518685,
mkSt [w1,w2,w746,w0,w3,w4,w5] 0x39b68ead6dae820202020202020200d61d868546060483c40582420a494c40034b83054500ddc0d09b0dd491d7a4240dd82552070a,
mkSt [w1,w747,w2,w0,w3,w4,w5] 0x3d7a76708952690d46450101010105010101010500c483cb830588c0410140c003440281ca757b17aca6cfa824c254a0824120789,
mkSt [w748,w1,w2,w0,w3,w4,w5] 0x25224a58991a40c0c0c0d1d1d1d4d4c0c0c0c0c194c483c4058140034b83050163424c240c38c2c0d094025520489,
mkSt [w749,w1,w2,w0,w3,w4,w5] 0x316a665899625cc56e48c0c0c0c0c8c0c0c0c0c8c18483c68b858c8280034302440a787bc7b8255204f6024ca2424120609,
mkSt [w1,w2,w750,w187,w0,w3,w4,w5] 0x19512154df571c93511b40995714c182935102c0c2ca854d0ac88a8683428682cd874f0403c04101400dc0c254fd5e17c0b1424d4f958806,
mkSt [w751,w1,w2,w0,w3,w4,w5] 0x2a6661865c9980c0c0c0d6520994d4c0c0c0c0c114c683c34282c140044383093024d7cc5017d02400d094025520509,
mkSt [w752,w1,w2,w0,w3,w4,w5] 0x1f601f201e1ae01e9ac9615dd95d9c1c141c1c1d5c3c30241c042c1094144434280d1f4260de02417d40d0d080f520688,
mkSt [w753,w1,w2,w0,w3,w4,w5] 0x326e6962455cc2020214c0000000148000000014818443c3438302cc8240068b828a1c0d07e02542607eca2424c24120609,
mkSt [w343,w1,w2,w0,w120,w3,w4,w5] 0x12ed39f41ec2aefa726a0f60265945dc53894cd01101ba06a4682c3c141008e8382824004434f00d26d7e112cae824d18785,
mkSt [w343,w1,w2,w0,w3,w4,w5] 0xbeb964e96f1f3358ecf151a6b25e0cb253a282c3c1410080ce8f024380126cde0ae97e42541f00f518587,
mkSt [w754,w1,w2,w0,w3,w4,w5] 0x76ed49a721bd68c85843810204087020408a444b8302c241c0c686028217401f155c0d024118585]
set_option maxHeartbeats 0 in
noncomputable def ptopD8p7 : List StD := [
mkSt [w755,w1,w2,w0,w3,w4,w5] 0x11d3ddae74e4f8a90dbf1ad1d8a0e1521b2228345c68601410087458200d2f48357ec500b5424c25518587,
mkSt [w1,w2,w756,w0,w3,w4,w5] 0x3ecef5f2f16dc24242424242424240c6d65dc546464443c34287c208cec10c4006838300c934df40d09d05017fc91d4002417f82552078b,
mkSt [w1,w757,w2,w0,w3,w4,w5] 0x127a75c645f19e69dd1d8101010101810101011d00c68347cd4a484541c1400b8380428a20a98260a08db424c254a9c24120709,
mkSt [w758,w1,w2,w0,w3,w4,w5] 0x2a8aa19e9c9980c0c0c0d2920994d4c0c0c0c0c114c443c34287c8400683830934c4424d8145018182400d09402552050a,
mkSt [w759,w1,w2,w0,w3,w4,w5] 0x122a258a09a0860599454141414145414141414001068347cd4c800b8382820a2085c26024c254860a2424120508,
mkSt [w760,w1,w2,w0,w3,w4,w5] 0x2e2a258a209d81c1c1c1d619d585d5c1c1c1c1c115c683c34282c9454443830009300d050182c24182891c25520588,
mkSt [w761,w1,w2,w0,w3,w4,w5] 0x1f241d241cdae41e9a09655d585d9c1c141c1c1d5c3c241c042884945444342c0d1f58382615842418340d0e080f520609,
mkSt [w762,w1,w2,w0,w3,w4,w5] 0x36322da609a0861db14541414141454141414140010443c3438302cac040068b8288ca1c88026024c254888a0824120688,
mkSt [w763,w1,w2,w0,w3,w4,w5] 0xbe7a63e753172258ac714f86b25e0d31d2a283c14100ce838f08c0126cc34be98402541f00f518487,
mkSt [w764,w1,w2,w0,w3,w4,w5] 0x772dcaa725c538e89843810204087020408a444b8302c241c600c68d828217401f15c00d024118605,
mkSt [w765,w1,w2,w0,w3,w4,w5] 0xdd3cd8e74e3f6a90daf1a9058a0e1521b222834442448143c58200d2f48b184c500cfc24c25518487,
mkSt [w1,w2,w766,w0,w3,w4,w5] 0x2685c6a8a6a1c0c0c0c0c0c0c0c0c214d656564018c6c4050c53c00204460353ec24c2405013f40cd3f00d09342552050a,
mkSt [w1,w767,w2,w0,w3,w4,w5] 0x7fb8fdf8afef385e60408102140810204280c3c6c6050d4dc10140c0044401c34aa8ac4ac024c25577424118707]
noncomputable def ptopD8 : List StD := ptopD8p0 ++ ptopD8p1 ++ ptopD8p2 ++ ptopD8p3 ++ ptopD8p4 ++ ptopD8p5 ++ ptopD8p6 ++ ptopD8p7
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x0 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x1 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (1*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x2 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (2*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x3 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (3*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x4 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (4*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x5 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (5*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x6 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (6*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC8x7 : levelOK ptopT ptopK ptopP 7 (ptopD7.map Prod.fst) ((ptopD8.drop (7*64)).take 64) = true := by decide +kernel
theorem ptopI8 : LevelN ptopR ptopT 8 ptopD8 := levelStep ptopB ptopW ptopQ ptopI7 (chunks 64 ptopD8 8 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  · exact ptopC8x1
  · exact ptopC8x2
  · exact ptopC8x3
  · exact ptopC8x4
  · exact ptopC8x5
  · exact ptopC8x6
  · exact ptopC8x7
  ))
set_option maxHeartbeats 0 in
noncomputable def ptopD9p0 : List StD := [
mkSt [w1,w2,w68,w3,w4,w5] 0x22214b5f091d5ad8d7571490935106c483c302c24201c14100c3844342808184000c00800400001158885,
mkSt [w89,w1,w2,w3,w4,w5] 0x201f4b5cc8db52989952d7150549070483c241c103028003804443420142c4003c03800400004158805,
mkSt [w1,w2,w0,w31,w4,w5] 0x38f9b3830d98ed9cb72a57c946c3c30342420100c6c442814504c604005c00400006118784,
mkSt [w1,w2,w0,w3,w4,w38,w5] 0x6c5c0362e2e1542b1ee0511d1e6251481cde21c8d0682834241c10140c6c209450441240080f40e40e80381040041080000fd2068b,
mkSt [w1,w2,w0,w3,w38,w5] 0x208eee03c76d993364a54af52283c302834241c10140c6c4460405020942c0e400400150883,
mkSt [w1,w2,w0,w3,w4,w768] 0x654b776e5b674ecb94d5ac372486c6034241c10140c445020bc401b01ac1a800400118685,
mkSt [w217,w1,w2,w0,w3,w4] 0x75f1d75e5876aeba7732acc28302834201c10684404006040506c24141b41240040001b918785,
mkSt [w28,w1,w2,w0,w3,w4,w49,w5] 0x3a2a36322d256a014165221cde1d1cfa18d15510cc8200c14100c884468403c384434241c54100cc004001040781b00380e81d81d406806520709,
mkSt [w58,w28,w1,w2,w0,w3,w4,w5] 0x32ad5155429109496908d566a504a0c14281001cd85542110248c4800443c1c10c004006c502c24140e81041d41b00080781f80801e807d2060a,
mkSt [w28,w1,w2,w69,w0,w3,w4,w5] 0x2a65657169652d69652099595d18d8c65555048490c2414100000cc84786c6074301c2410c00400141fc1a42080080782040901e808d20609,
mkSt [w28,w1,w2,w0,w3,w4,w5,w117] 0x378fcf327cfb55c7cc76fe3bc76a97af68a91800e1c20036444448287834201c100cc004004010412403820c09c1d409918687,
mkSt [w106,w28,w1,w2,w0,w3,w4,w5] 0x3bafdf9c7ac3e7ee1b2e5ea12961c384010dcb71eb111b24004834881c10c004006c50282084641041240082180b41e80b118707,
mkSt [w76,w28,w1,w2,w0,w3,w4,w5] 0x16515169555109494908c6554504a4c241410020dc5955510c88c480088c0040044483c308c541fc1a42240380782200c01d40bd20509,
mkSt [w28,w1,w2,w0,w3,w4,w5,w29] 0x1a1cb87c7d99fdddb98d7c5c596d681d3d394d25081c1c180c00e8c4402c8048341c100cc0040044605020141d41e812422c0e804401c2280180155880a,
mkSt [w26,w28,w1,w2,w0,w3,w4,w5] 0x20c0ddc0deddc0c51bdb0016d9d6550000c1c013104e8cc0c0c0c00009040341c100cc004006848446450201423c05003002c1041fc02958807,
mkSt [w1,w2,w6,w0,w24,w3,w4,w5] 0x14f0d66bc9cecd6a21d9a005929c7a04022550e7d01050000000000c400018003c44d830348060d440c80014cc50d00426427427026c26803826000424c2482442400016080d,
mkSt [w18,w1,w2,w6,w0,w3,w4,w5] 0x23b1efa90b8dd08b8dc1256385d900000000000140108b8dc001008203c34ccd4d0c43018805060c826029429000827027424828c00427c28024c2400012060e,
mkSt [w1,w2,w6,w0,w3,w4,w15,w5] 0x204f7003b8bcbe6b1098ebe1901c0e5e2129404274f210000003800000001800e84868446434d4c8dc000c502c8040042c82702482802c42c00042a02b007824c29c2400016080e,
mkSt [w1,w2,w6,w0,w3,w4,w5,w81] 0x90b95d7b5ccbb9135c383b115cc80878929e540028000000000c006c3460d4c8dc00146850402cd0042742482801242702f02ec2f400424c2602dc2400012070e,
mkSt [w48,w1,w2,w6,w0,w3,w4,w5] 0x138defb573adc1538dc4a967a1dd0000000000010000138dc48140820684034d4d0c8dcec6c6074045c2601a431030c28024827430800427030424c2400012068e,
mkSt [w1,w2,w6,w0,w20,w3,w4,w5] 0x29273730a88f2ca88f0014c4e700c0c0c0c0e0c002dcd8cf00c8c00843468f0405004ec9480283c006031c27827427035434003800032024c2480052068c,
mkSt [w17,w1,w2,w6,w0,w3,w4,w5] 0x260dd96c54aa3d208447a05070381c0e063cdc6dd628381c81088f41c05030004034f0f4ec943c080c04c06c2cdc28805000600043a42503d03c800827027424828000024c3b82556098e,
mkSt [w1,w2,w6,w0,w3,w4,w13,w5] 0x2ee80a902f6b142eea9044282a92440028080000182d05a82c2c09083444d8502c04ec94c400d03c803382a04084040002a42b03f007800424d2068b,
mkSt [w1,w6,w0,w3,w4,w13,w5] 0x1a22a065b9dd0f34944560e64029560ef070041aa876001844dcd85020ec94c468acc0343c80d02ca404003383f00042a02b00782a426160988,
mkSt [w52,w1,w6,w0,w3,w4,w5] 0x29218dabe9278fcb27a42203219e015d5b59975553444405020ec3cc4d4d0c8dc1c00ac8034602c04a4942b047c0042a02cc0780d158a87,
mkSt [w1,w2,w6,w0,w3,w4,w5,w80] 0xaf2f28eb3710732f28c3030728d0644080000002830b1f0cd84088834e8405004ec94c4442c3c00602b04a82f82482804a44a012400049400424d2068c,
mkSt [w64,w1,w2,w6,w0,w3,w4,w5] 0x24a3e9f4962d0e02c461cf10783c1e0f06b55863e5983c1e0f088f8820503800b84460502cdcbc94c40c04c068d4e8303c00480044b42e01a44d44d028024827407827000024c4cc2556098f,
mkSt [w1,w2,w32,w6,w0,w3,w4,w5] 0x248a552d267309364ae2a792c8661200053d9cca56c809b2c05829532034ca0c5c586050fcd440dcec9434c4c02c806c043c00d021c2602482802702742544dc44c4404d824160a0c,
mkSt [w1,w2,w6,w0,w134,w3,w4,w5] 0x21cb3170001c037a9384ae5688f986040283018b30003014911f08c00150597040302c80503cdcec94c404c0286034002605840d02442782742702a02142482805802542416080e,
mkSt [w40,w1,w2,w6,w0,w3,w4,w5] 0x20c6b25cd64a4b8e419f67572358d695013016c6b4280d46550a92c000a4aa145c58806050d4d0ec94c004002c3c4434dcc4402145dc2802602702744642482544705d82416098c,
mkSt [w155,w1,w2,w6,w0,w3,w4,w5] 0x212f474b0c7224088e44803690e448c359284722421a4504111c890e60800000403c34d4301cec0cc02c04002860508026024821c27027465c28025424160809,
mkSt [w1,w2,w6,w0,w3,w4,w59,w5] 0x12b8dad1c83b80345f6e40882c16e468868142a5d2a810410022c6871049a848604464502cd43cdcec94c4c004003440802a025429c2a42702482806680782b02416090b,
mkSt [w1,w2,w0,w3,w4,w59,w5] 0x3a792c8c160d9077ebb0d0d505af190b4528283898402e04860686c2c40aca420a810840034504464040c1240082a06b86a01a46682b00380fc25429c2a42416098e,
mkSt [w47,w1,w2,w6,w0,w3,w4,w5] 0x32e3537d72fb7cc2fb74ca72d36e410cced368c00cc4c29354c2c2c2c80502c60dcc400683cc028349404447041f02a02402542702482800782cc2602b03292078d,
mkSt [w47,w1,w2,w0,w3,w4,w5] 0x3dc348a843ddd4686b929a02413b2968a435a5d14590381c6c60502010840040343c442838040c681247040080fc2a00380f42602b03282cd6080b,
mkSt [w1,w2,w119,w6,w0,w3,w4,w5] 0x2544a22ca8ef059545e0afc00228945a05b686c6573009b4aa6399560035524c8060502cdcd494c4ecc0484034303c04d0002142742702802486882547280787247202416090c,
mkSt [w1,w2,w6,w0,w3,w4,w5,w222] 0x21c067734c5c2620bf9ccd3068386cd320800180c6183014000f0d84681059b0806c40503cdcec94c404c0442c6034002742700d02dc2f82a024828026076421c7602542416080e,
mkSt [w98,w1,w2,w6,w0,w3,w4,w5] 0xb4361d40d74f681ae9eceb39b694cc50118d74a64801108002d0d886093998c80502cd0dc603cc4c00400402834d4ec21c2b027028024877c2547782747742416080b,
mkSt [w221,w1,w2,w6,w0,w3,w4,w5] 0xb2d474c15f2e4028e448116a8e448c259154722450a4504751c8902203000006c403468dc1cc40cc08004440060745c26021428024827079c27425424160809,
mkSt [w1,w2,w6,w0,w3,w4,w49,w5] 0x10af78ba2874aa2a800ee3a83015eeea6a9584ac7551d406904aadd5495022504080605058d09434006828c044ec3c04647a02702542a00782480680642b02616088a,
mkSt [w58,w1,w2,w6,w0,w3,w4,w5] 0x36d1b2c562d1be4ad1b95e76f1a140242ed5a9412505429180814d6948058d83494c4002844c03c50dc406c2a02480782702547d02800802b026007d2078b,
mkSt [w1,w2,w6,w69,w0,w3,w4,w5] 0x1b44c26529883c9d41259142d415f8e4023698a6c4201000ba52930680401a4c786c743060502c44d0ec940428c034683ccc00407dc1a42700042540002407e828009007808d60a0c,
mkSt [w1,w2,w6,w0,w3,w4,w5,w117] 0x25c3d3d111d1e2a1c3c7009fd3dd1a8899d7d11480048dd3c70a80c8c44287880505ce8d0f06034c06c30043c00402b025424084009c24809958907,
mkSt [w106,w1,w2,w6,w0,w3,w4,w5] 0xf028744a03024641e16912843e1c8d20032030b44100ca6a80c091240229208885c44d034f0683c6c28c460c0dc003050642b012425424087c0b42800b160908,
mkSt [w76,w1,w2,w6,w0,w3,w4,w5] 0x2543a434e826369545e0cf37535d0cc300269603629810c809098d9460331a4c888060502ce8d0289430ec34c0d4cc6c3c00482702802540788a82400c02488bc0bd6098a,
mkSt [w1,w2,w6,w0,w3,w4,w5,w29] 0x12732bdd2e9473c5e0af403c5e0af47585cced54a30004572ba9528800194c408060502cd8dcec9434c4c044003c28480401c2482802542740442a08c00180142616090b,
mkSt [w26,w1,w2,w6,w0,w3,w4,w5] 0x22c065b819cd070311a0ef8033996ed4018198cb75001068024b0180c060301890502cd0dc9434c448ec44c02840003c040308d82b005002c02826027160888,
mkSt [w1,w2,w0,w3,w4,w185,w5] 0x4b230048536894f51dba1b4256432094c07a1d0f0aa4a150e848686c405020a81084240c64003428441c12410890c6689100080380fc0000f429c9196090c,
mkSt [w22,w1,w2,w0,w20,w3,w4,w5] 0x200eb758cc262b799cc560442111d6d43a305622b0198cc831088ac06035201048f0341cec94dc0c2428004420683c409209349301f034035403800491c9242796080b,
mkSt [w22,w17,w1,w2,w0,w3,w4,w5] 0x2a0dba5cd50adb911c857158098456f57114884db62ac80031088ac0aa2488144434f08d0cec0918502c20040c28a4946c60683c4095c9309341f03c83d094000896025425160a8b,
mkSt [w22,w1,w2,w0,w3,w4,w13,w5] 0x232417664e4f2420264c201e95cc2000215c000114001c1c000018143c44d8d034aca42094000c6c500782549103f000466898c3382a520689,
mkSt [w22,w1,w2,w0,w3,w4,w5,w80] 0xdddddbdbe3e1dfddda99c8d7d4d4c1cdc3c4924cc1c1c3c48a50c0c342ce860501cac8cc4d40c003044243c4091c9409184a04a41240049902f958889,
mkSt [w22,w64,w1,w2,w0,w3,w4,w5] 0x1562415cce5714818ec48f2718ec48d1612cd56240924800031d8902282388004460512c20bc0118684824040ce81cc4403c3007894091c1a44d04d499c9a09302542e16098b,
mkSt [w22,w1,w2,w0,w3,w4,w49,w5] 0xaeac246c5254ac161452ad112e4a10add19449d1c4ac11944810200c44342800640c1d18683c07891894024825403891091c0689ac0652050b,
mkSt [w58,w22,w1,w2,w0,w3,w4,w5] 0x325e4e4a764d326e69248a625d14944a625d000280ca41cd0204948007044d83428403c2cc518506c2428007891891c0082549bc08094007d2068a,
mkSt [w22,w1,w2,w69,w0,w3,w4,w5] 0x1fc7c7e3c5c521dfdd1a99d7d5129089c3c704800e49c3c704800180c786c60743044d0342824000d18683ccc400782802549c009094008d58887,
mkSt [w22,w1,w2,w0,w3,w4,w5,w117] 0xe1881a8d46a37c3a0303869b0d66a24c1cc8613190a0e2032184c6428030104828781ce8d034f0c4000d186c3c304091c94024825409c9189cc09960808,
mkSt [w106,w22,w1,w2,w0,w3,w4,w5] 0x3b16cdf8f14edbb25a6c7aa326298f54941c1c63c51d0a64008844d034f03c306c28c518686450202809182549dc0b49400b118787,
mkSt [w76,w22,w1,w2,w0,w3,w4,w5] 0x33366dd8b34dd9ae529c59a224338b34841c1be2cd150a440088e8d034286ccc443c30ed18488c2480782549e40c091c0bd18707,
mkSt [w22,w1,w2,w0,w3,w4,w5,w29] 0xd274b39d8ec68bc1dece323a5dacc34019cce3611ac4c207038d8461106008402c806050d834c40c44291800201c483c308c091c94025412493491004401c9e80180156090c,
mkSt [w26,w22,w1,w2,w0,w3,w4,w5] 0x226037400de70801bcdd0d4000cc50c13080066280881c08a24980c0603000009050d03428c40c6848451800201c403c309f08d805003002c91893002960888,
mkSt [w1,w2,w0,w3,w4,w329,w5] 0xf35c1ba72725942f5f24d81c9aa5da005c5e6601d868d834aca41014206c500444d00c1240080f4a006689fc004a040382a40fc2612070c,
mkSt [w10,w1,w2,w0,w24,w3,w4,w5] 0x2db1058cad8528e5850022cac6c2d6c000001c80000c898502c0c01883cd8cc40d40cc4043044d034244a20a1c26826c260038a0ca082400012060b,
mkSt [w10,w18,w1,w2,w0,w3,w4,w5] 0x295350d48c54c5890a82b03788a82ae36910454c559801423115054069240800483ccc04185509185028141c0030d40c8044d034260a1ca20290294a28008a2427c24160a0a]
set_option maxHeartbeats 0 in
noncomputable def ptopD9p1 : List StD := [
mkSt [w10,w1,w2,w0,w3,w4,w15,w5] 0x38b70031210f2d68a7210743574f5f4003000000000483030d0880188e848686c2c40500494dc6434284429c9fca1ca08a246682c02c4078a34a042400012070d,
mkSt [w10,w1,w2,w0,w3,w4,w5,w81] 0xd0d48c94904ad6924c2d2cecae2dc800000000002c14d08c4801886c4050040cec68dcd034282dca08a242ec2f0124a20260a442400012058b,
mkSt [w10,w48,w1,w2,w0,w3,w4,w5] 0x196b415d0e76b4918ec4912818ec48f17134d96b42080142031d8902292408006840d405288518446074141c006cdc0c5cd03428260a24a081a430c310a54a58a1c30424160a0b,
mkSt [w10,w1,w0,w3,w4,w13,w5] 0xdf6013ef2f2e1f9b632c9ca0a2edd45029a26e502468dcd83410aca46c1420d050040c44a640e83f09fca0424c2600040784242a52078b,
mkSt [w10,w1,w2,w0,w3,w4,w49,w5] 0x36fa81f532de8ac29a9ec862c69d1ae592eea926e04842c69d1ac0c2460683864100c0434281c551844d0a089fc248a1ca24064260a68078a040692070b,
mkSt [w58,w10,w1,w2,w0,w3,w4,w5] 0x2ef1ded49ad1e046ddcca96ee9c8a46046ddd880c2948251c10c88800684011184434286c50dc14d89fc280a08a1ca80078a0426007ca240812060b,
mkSt [w10,w1,w2,w69,w0,w3,w4,w5] 0x20cb95cc9848a98b411f2e41b0843254023598ab952251023610864a80401020786c60743068403ccc14041d18280c44d034a84280240a1c08ca24a8807809160909,
mkSt [w10,w1,w2,w0,w3,w4,w5,w117] 0x1ea3cccccccfa362a0e1cd0c4cc8a30ece8e4a21c40d0c4cc8a010184828780c6c403c30041d18e834f0d0a08a24248240098a04a9409d20788,
mkSt [w106,w10,w1,w2,w0,w3,w4,w5] 0x3b16adf8f146d7aa32ec7b662629af54940c3c63c51d32140088683c30d034f06c28dd1844645084280a04240aac0b0a240b518787,
mkSt [w76,w10,w1,w2,w0,w3,w4,w5] 0x3e8ea1ba888d96a46194b6b10dac946aa4619c810242088d98948480080886c0ccce8d0342830d5183c4854a1c248a24240ab00780bcab8a080c12078a,
mkSt [w10,w1,w2,w0,w3,w4,w5,w29] 0xf182bb607037843e1ced3341608e336082050b751a50c2082c11c661101030402c806050dc4810141d180444d8340c288c0a08a24000a209fc04401c260abc0140196088c,
mkSt [w26,w10,w1,w2,w0,w3,w4,w5] 0x208041c811a8f90211072e20235192b72901088391100c1007420100804020109050dc4010141c6848451804d034280cad48d8260050030a0402802ca1d60809,
mkSt [w1,w2,w75,w0,w3,w4,w5] 0x400ce277b1598e787019cacd07019dac045a2114e961a350485c40dc2c5410c40c683c28440034d01a4ad8038124000adc44025560808,
mkSt [w1,w2,w0,w3,w4,w224,w5] 0x3ab98085f1c9fd41996df93619b1ed44819da5e15c86c44043c2c5410840c6428002034681240f4004b44b48038b501080000fd2078a,
mkSt [w53,w1,w2,w0,w3,w4,w13,w5] 0x1636322e11121628ea111601655124d62099511cd8960001510cc008444403c2c2054080c6cfc301400078b50004b48b6c40424c2a520688,
mkSt [w52,w53,w1,w2,w0,w3,w4,w5] 0x3b6e4c7aacc6c1521bbd56663157aacc8601cb65c90d851400443c086c64fc3014e8d038f00400b50078b48b74ae84402cd18707,
mkSt [w53,w1,w100,w2,w0,w3,w4,w5] 0x32dd5ad46acea76e1bdb96e5394d46ac8669d351ab119a00452444d940f02408ec6cfc30dc1464078b80b1444072118705,
mkSt [w53,w1,w2,w0,w3,w4,w5,w80] 0x21c3dfc909dddad9c3c91695c3c912d1cfc3c90cca81c1c3c906c00446848342c280524240c0008d4fc301464b50124004b844a024c2f958807,
mkSt [w130,w53,w1,w2,w0,w3,w4,w5] 0x3aad5a952ccda356232b566632576acc8601cb51ab119a2400492c086c64fc30144434280400d0b50b94afc44077518705,
mkSt [w64,w53,w1,w2,w0,w3,w4,w5] 0x114d0d48e96532120e0a0491452cde00296520de1854914d08c1c48012c0864fc30dc1468483c5c5424cba01a4078ba44d0b782e120608,
mkSt [w53,w1,w2,w0,w3,w4,w5,w29] 0x2fe6a58b65bcb96931ddb6e3b49934d274a4860c149c212e4404448342c080c3014802800d8fcdc24c440124ba0b48018ba804401518789,
mkSt [w26,w53,w1,w2,w0,w3,w4,w5] 0x20c0dd80c70580dedd9b0006c599164006c5950252508ec0c0c0c000090d0342c080c3014684844280064fcdcbb402c050b50b7802958806,
mkSt [w1,w2,w0,w24,w3,w4,w15,w5] 0x3cba0036f2eaec82022aecc0c626c02d595e1ad9554002000001c0000e84868384434cc24201c0430140c40bc0268038bbc2c00780d0bcc2c42400012078b,
mkSt [w1,w2,w0,w24,w3,w4,w5,w81] 0x3166e9eae9c2c2ed69c0e2e561c01512d955d511028000000240000d0d83440cc24201c0430845426c2682ec124bd00382600d02f02400012060b,
mkSt [w48,w1,w2,w0,w24,w3,w4,w5] 0x124e65c275e57269e5400a61dd5cd90000001480000011cd424108c48d830cc4034201c0400607424142681a4260038bd43100d024000120689,
mkSt [w17,w1,w2,w24,w3,w4,w5] 0x45170b88341970f070361ac80602e00a375289550960321440288ca41c8434cc2c144430f03c046008bec244008038bf024c2500d160888,
mkSt [w109,w1,w2,w0,w3,w4,w5] 0x381a1a35b596302c0e0da0281605a00264161181a1c48288ca484401444343c301cd0001a4c28038008124250c2c0d024d20709,
mkSt [w1,w2,w0,w24,w3,w4,w13,w5] 0x20cee021c46c3e86835da3d869b5da7d04c18149e1b2b55a46232386c0b2e91844ccd850ace0a420843c3008c434d014bbc4082444042602a426803833824c0d0bcc078c556080e,
mkSt [w52,w1,w2,w0,w24,w3,w4,w5] 0x16f0a7d3880e5a72ad4b40938a9cb4a5528c82e5a492146471339680a05038c868344430cc40a40008e8d03804c41460c702cc268bbc038be8078bcc0d02456080a,
mkSt [w1,w100,w2,w0,w24,w3,w4,w5] 0x22ded142e150f6e1510272e150ed2926e15cc1011846e150c28d0880031241c0444d94024843408c414268b147201a4038000338c88c840d02452068b,
mkSt [w1,w2,w0,w24,w3,w4,w5,w80] 0x5198cbe4b25904ba6325484ba4329300021d2d96230c66a93caa52807419d8d8cc5044ac8c24843c30c5243408d41440bcc2684a024424cc9c4a40d02f960889,
mkSt [w130,w1,w2,w0,w24,w3,w4,w5] 0x361616023615322e1501ea061524e4ce0615209ccc9a06150000d04c8d868412c8c0008443404c414d0bcc774124038cc0cb00d024520688,
mkSt [w64,w1,w2,w0,w24,w3,w4,w5] 0x348eaab5796a91554e80f4b1aead45489c2a82e56200148e815142488d844201c3408c4852c48303c14044d0cd426c24407824c4d4cec2e02680d12070b,
mkSt [w58,w1,w2,w24,w3,w4,w5] 0x39b2727dd5f27e39b275c409b2416c2941ea65dd51444d82834c4cc2c04243058143c4084d04078008bbc03833807c260bcd20789,
mkSt [w186,w1,w2,w0,w3,w4,w5] 0x21c54d46a2a691b1e56e8909e54aa912c2a541d649c2028943cd8301c0444340c68124008004d08bbc0fcd0c2600f4bcc07d2060b,
mkSt [w1,w2,w0,w24,w3,w4,w5,w29] 0xc1f27e969642b6ae553ab68a51009ab6ae5528585e9ea65102205c038cc4480d81c8430c404343c08481426cbbc044268018338d1826001401d2078a,
mkSt [w26,w1,w2,w0,w24,w3,w4,w5] 0x390129410d29410d8980c1352971ad810d294215a400a10101010101090d01c0434c44814443008403c8405002c030d34bcc02826026920708,
mkSt [w1,w2,w116,w0,w3,w4,w5] 0x3d31f9f66a4a7e1131da6c0c25ce40dce0c9d654ccc44345c50d440c88414280060043cd00083d8d381a4124d4000047025520789,
mkSt [w1,w2,w0,w3,w4,w331,w5] 0xee0c021c3e030355b194b0e46c99990b5190188ca822a084838441c3c2810140c6c402c946820341240f4004d702c0d74008d801080000fd6080b,
mkSt [w54,w1,w2,w0,w3,w4,w13,w5] 0x17dfae9d2275f2e7a45e142a496bd94548ed92f001521b004444402c850814683c3000c4d80078004d74d8440824c2a518588,
mkSt [w52,w54,w1,w2,w0,w3,w4,w5] 0x374e4c7aaa46c1521bbd56663157aacc8601cb65c90d851400450868403c3000e8d038f004c4d80078d74d90be84702cd18687,
mkSt [w54,w1,w100,w2,w0,w3,w4,w5] 0x2ead5ad46acda76a1bcb76a4b84d46ac76680351ab119a00452444d940f02508683c30040040078d94c8847072118685,
mkSt [w54,w1,w2,w0,w3,w4,w5,w80] 0x3f0eedb3366b75872c951872c36f9f0e58ccd060c396233444684850342c28052485083c30d40040d80124d9c4a424c2f918786,
mkSt [w130,w54,w1,w2,w0,w3,w4,w5] 0x3ead5a952acea356232b76a6b2596ed49709cb51ab119a2400492d0868403c30d40044342804c4d0d80da8cb047077518785,
mkSt [w54,w64,w1,w2,w0,w3,w4,w5] 0x27a54f117a5c65d29464bd2dc274a7a588ed9005e94e1312012d0868485c2414403c3004000781a4db84d424cdac2e118607,
mkSt [w54,w1,w2,w0,w3,w4,w5,w29] 0x1618d5f99994b8b8744c39d9b58d689898744d49241818744d0824e4403844d8342908143000802cc4483c0424c470124dc0d74018dbc01c01558809,
mkSt [w26,w54,w1,w2,w0,w3,w4,w5] 0x20c0dd80c70580dedd9b0006c599164006c5950252508ec0c0c0c000090d03429081430006848442cc4403c04dcc02c030d80dac02958806,
mkSt [w1,w2,w90,w0,w3,w4,w5] 0x3962e2ddddf6c31552ddf03022c9c1ed252ad9e6a4044502054100c342830403c6024001a4dd000824c91c038124dd40d027c2782552070c,
mkSt [w1,w2,w0,w3,w4,w332,w5] 0x3edac0514160b0c5030d610f474b58d0c5580582ca84aa00504420603054108400043c3428d0680c1240f4004e0ce08e04038e140fc0642616080b,
mkSt [w18,w1,w2,w0,w3,w4,w15,w5] 0x34b2802d95a686c2cad6e0dcd29d92c00280000000048282958010c1ce848684034441c0450208464802c0e042900082c4e18078e140d02400012068b,
mkSt [w18,w1,w2,w0,w3,w4,w5,w81] 0x31658d0da1426e524e48c9895d0a5480000000000241914d0008c48d06c6840341c0400605020142ec008124294260e1c0d024000120609,
mkSt [w18,w48,w1,w2,w0,w3,w4,w5] 0x162239b615911e09b108ee15912888e615a1001cd84215910c88c442034301d45104474245460502820842901a4260008e200d030c24120708,
mkSt [w18,w1,w2,w20,w3,w4,w5] 0x44190e8830d990f0103a008d55ab616c974215090a61201848cc2434543c0c2c18f044302850402000e242780080d0038e3827c24d60888,
mkSt [w18,w1,w2,w0,w3,w4,w13,w5] 0x1572c2aca566d4414ad0a942cee54d55615ad15d5954414ad0824d420d868443455080c805020d000e0427c24c408290008338078e14e504052060b,
mkSt [w52,w18,w1,w2,w0,w3,w4,w5] 0x39f6725885ea5861d2609905d26d091885ea41609d1855d24001c90004068350850282014e8d038040060e68290e040080780d0e14ae827d20709,
mkSt [w18,w1,w100,w2,w0,w3,w4,w5] 0x7d7e8bc623df72992cf7298094be22478d1a2f188cc920018352444d940244108ec8050282060290c88008338e7827cb1518707,
mkSt [w18,w1,w2,w0,w3,w4,w5,w80] 0x6a6531108d067b1582c4404b99acc410ad86cb64a204ee062b05888021082034cd24ac8c0c403c30d508e8500024602904a42f8e140d0e7c27c24c4a160809,
mkSt [w130,w18,w1,w2,w0,w3,w4,w5] 0x37264d5874ccc3923a2c3925b275874c84e99ae1c900192600492d08805028241444340400d0e14008e9c0d0afc27d18686,
mkSt [w64,w18,w1,w2,w0,w3,w4,w5] 0x20a6a7d0d5248a529d9d4720ab4034c25c295248a019c81600229a86a090a81444b81c0d0800e86050203d2c483004544d4eb429427c07824c290ec02e04d00d16080b,
mkSt [w18,w1,w2,w3,w4,w49,w5] 0x4962c0474965d3073abd9d21062899b2c85a2946c994a014cc6044d03410005c2c582404303c5428640cec4260078e04008038e1406433960909,
mkSt [w18,w1,w2,w0,w3,w4,w5,w29] 0xd173b0dc6ec6839dc8c347bb9dacc410a1c2eb65224512073b91868021082040cc0444d834481030008029086050200c26001c294e04018ed433801404560889,
mkSt [w26,w18,w1,w2,w0,w3,w4,w5] 0x3d013a01110e01353a2c8135322ca981110e00c881c19d010101010109034401030002868484508d050200cef403026002ce1402805029120788,
mkSt [w48,w1,w2,w0,w3,w4,w15,w5] 0x271400a00e22940e4e215051d1a1500018000000000024180c0c501c486c684034201c04a86450241b0f10f0cf08f040d013424000120609,
mkSt [w1,w12,w2,w0,w3,w4,w15,w5] 0x252404c68750a72bd5ca3a20b48883a6284400041d2d54252021511475310004068342c581c182820a81084940ca54848e8f244d8f40f040002c0f20f2c0d029d6090a]
set_option maxHeartbeats 0 in
noncomputable def ptopD9p2 : List StD := [
mkSt [w1,w2,w0,w20,w3,w4,w15,w5] 0x22b07018adf64b12010cecb123906e4b00054f8d765829688503a1d568442270e84838f0203c1810940c2440a8342868dc29cf482c0f04108f44340f642c427824c0d16088c,
mkSt [w50,w1,w2,w0,w3,w4,w15,w5] 0x3cba4235714a6d2d12494c688e496514825649551884400249611c588e84868382c24f42804940c40203444f7c5d8f98f04f782c4f940d029d20789,
mkSt [w17,w1,w2,w0,w3,w4,w15,w5] 0x2491b01418cc9b39bcc76660abb1b6d639940165b6328d7823018eccc000528ce84868f01ca410948434f428500c44646c0429cfa02c4f041083c8f9c24cfc02c02500d16090c,
mkSt [w1,w2,w0,w3,w15,w13,w5] 0x16aaa2ba4c6632859d4823300038ac72e0681580eb950260e86864d850ace020a9501084946c2c344044a4d00c004338ff029c1a00001b02a40fc24c0d160a8b,
mkSt [w1,w230,w2,w0,w3,w4,w15,w5] 0x1b04043ec1a3b71835a8cb0d168083b5d06818041d8a8120d021901a0d3d1d048686c40501ca81084940c24643428441086b901029c2403600002c02c40e80fc1040d16080d,
mkSt [w1,w2,w0,w3,w4,w15,w59,w5] 0x193c01c700009960d46ad58e406020c6ab31760b4da95368c05008247530a6ce83c442c406434ac1ca420a81084946c50040c0fc0d09fc2a41b02c42c101824c29c2a02416098c,
mkSt [w231,w1,w2,w0,w3,w4,w15,w5] 0xeaab2ae88caaa8446a4ce801108e08e811508dc508e820288c458820603c445004841c0c20e838f00fca042a03d82c02c49fd04829c2412060a,
mkSt [w86,w1,w2,w0,w3,w4,w15,w5] 0xf0416e80e2a900e46288c0c0de9cc0c21600c0d8c0c24200c0c19a048686c40341c0c94502444646b829c91024c2402b49180d00fc1092060a,
mkSt [w86,w1,w2,w0,w3,w4,w5] 0x3d666679b17655b1566c09a16668201a8d664201e14486c50d02484340c28441c3c4000681246b80086689189100382b42540d12078a,
mkSt [w1,w100,w2,w0,w3,w4,w15,w5] 0x1944050ec773b8e28a08fb0e348283b60acc00041da84188302090f662290004834686c4051241c0444f024a810849465400c201b1090720c88b142c02c400108cf040d029d60a0c,
mkSt [w64,w1,w2,w0,w3,w4,w15,w5] 0x2068401135da4881be0f0ed19b6050dd6298c08145ea813200042109a730618ce82c501c201084944830a92c3c44040d0c0f0c4d44d029c0fc2c02c424d0c4f042e00d16080d,
mkSt [w1,w2,w131,w0,w3,w4,w15,w5] 0x2aeac18ecd4d3ac174f13ac2b4f101eac948e520487ac0c4d9155551448686c64a024441cf0a810849434200c1342c40fcb502401281090ecb480d02c12080b,
mkSt [w1,w2,w0,w3,w4,w15,w333,w5] 0x2fac2428001e6f535211af0c0dce12ee96942a15d56c200849104e94e8382c241c3c342830a81084940c0fc0f42c0e040641b00d10fc2c4bbc2412070b,
mkSt [w334,w1,w2,w0,w3,w4,w15,w5] 0x134e8cf8e1e4c0d69c1c28734169828538ac5260e18e13141c44d83c1c28e8502c24e14bbc0fce051082c00d024118488,
mkSt [w190,w1,w2,w0,w3,w4,w15,w5] 0x1b1a410e4f0d5a43154cda4b316ce87b014560d31f1a42d54cc288530486824201cf0a8109444400c3404841082c02401343d80fcd80d741411200d02c52078c,
mkSt [w1,w2,w69,w0,w3,w4,w15,w5] 0x1d4e90382a30090530812c89080013180502862096c30862b604864f06200144786c743068443c2ca800414c1084942824340c1b020913408cf0409029c0002c00796098a,
mkSt [w76,w1,w2,w0,w3,w4,w15,w5] 0x1ea5c149a389a08c81c99e8481dd9a4e81c3c9829492800a8990444e84038886c3428014c944430a82c483ce88c0c2251700bc0c029c0782c558907,
mkSt [w1,w2,w0,w3,w4,w228,w15,w5] 0x160805c1c090705829f20005829c2006c82c14b1002a5260b0102c04793516840483c3050e8ac1c20a81084942834040c1b0109190240f042c02c415c0d118c0fd6088b,
mkSt [w769,w1,w2,w0,w3,w4,w15,w5] 0x366d8542550c12d5576125c57618132081022c04002040808d06c4034201c040ce844645024f051a41340d01b024118686,
mkSt [w1,w2,w108,w0,w3,w4,w5] 0x3da526943c5a12477b42470277b3a5a00391a5972a32988c68d85060c8dca810840c44d43400802c04d11c40082b02a012403800032825560909,
mkSt [w77,w1,w12,w2,w0,w3,w4,w5] 0x20eb57bb8c2eb56105d6ad36105d6aa3490210e080408800083402010220001c60342c18e94828200c6840003c3004d0338f211f51ecf2cd083284d960808,
mkSt [w77,w1,w2,w0,w20,w3,w4,w5] 0x3a75764482557132556d10aa5564a11c5e555d1d10845a55410110824d034282c2004180c403cdc006068f451f4340039208e08f6424c27920709,
mkSt [w77,w50,w1,w2,w0,w3,w4,w5] 0x3ded6df8c5d17085ed74c221c20208b085ed68e4a0821a02020881c00d02cf444342804946840003c30dcd8338f7d1f5214f94e083285d920788,
mkSt [w77,w17,w1,w2,w0,w3,w4,w5] 0x3e6d7a74866d51064d7120624d608914866d68a520905e4d400902400d03428f4502c208440006c683c0460fa11f43c800922424cfc0d0825120789,
mkSt [w77,w1,w100,w2,w0,w3,w4,w5] 0x7c5e321dedd1bc6c51897c6c50a9480d2c0c0c28000d0c0c0c2800e43468605124204424f840006cf00cd940051f4d08e0922c33832872158887,
mkSt [w77,w64,w1,w2,w0,w3,w4,w5] 0xe493642b26d028e4928c296492444e08e49108294829e491044c240034d8502084684000a830603c041b10c4d08e084d04d523424d1f42e12068a,
mkSt [w77,w1,w2,w69,w0,w3,w4,w5] 0x1b028624a168138c35206f27435186b2510e0c8230900122384208c240028810786c743044603428240c40009404d0683ccd1f432824c090209238d0808d60908,
mkSt [w77,w76,w1,w2,w0,w3,w4,w5] 0x9028724608853843d1c6d21c190465260ae0882351248c4384208ca4110200088e86034289444308c4000a8ccd86c3c051f432824c0c0225240e080bd60888,
mkSt [w1,w2,w63,w0,w3,w4,w5] 0x41cee267bb55cc576ab98d0c76a9d980035ba0d4c9319b0c48805040d4ec10840c3c2c44280034d000812525d19803800072425560808,
mkSt [w1,w2,w0,w3,w4,w121,w5] 0x123600323d4d7a0275bd7a19f5b15c2e01a1a9646045080483ca810840c2820044434002c00812400518d2e80380f410800120789,
mkSt [w88,w1,w12,w2,w0,w3,w4,w5] 0x27c9e547e31945e0995f1dda99571493d04947048e8dc2494704800a4443458a418e8d1482820bc0cc468143c30d448f401f13052fd3087244d958987,
mkSt [w88,w1,w2,w0,w20,w3,w4,w5] 0x1f42a8282824257d3904ad4652c84aa24a228e2253a190a44a088940804000c43444282c24200418bc0c00dc68143c483401a41f003800531930d31c24c2796080a,
mkSt [w50,w88,w1,w2,w0,w3,w4,w5] 0xfc7cd4fe10d4fde8d5d1bd847450497d4475300104fc28d4b08848005820f4bc0c68483014443428043c00d8f981f132530d2d87245d958807,
mkSt [w17,w88,w1,w2,w0,w3,w4,w5] 0x15617d15788d16764e726d6461089e696461001e5855448d1082088003428a4f4bc68483cd414802c50846024d30c0081f03c93312e52fc25120789,
mkSt [w88,w1,w2,w0,w3,w4,w13,w5] 0x16ca8d090490a65849d4d461828b424590ec648a1224504730002848110002c403444d8508020bc840c6814a4d0003c301b118d30d2fc40440800533526424c2a56088b,
mkSt [w52,w88,w1,w2,w0,w3,w4,w5] 0x92b99a4a629032c99066f27491166d10932488b3508012259420cc44040900034446050a4bc84683c3014d00420e84838f00126cae8be92fd30d18d3447242cd60989,
mkSt [w88,w1,w2,w0,w3,w4,w49,w5] 0x2b27e49092e74c256493684b26d289290a24910a05cc002490004428408044603428bc0c68145800d03cd41b118c24c7240380693481c930c0652078a,
mkSt [w58,w88,w1,w2,w0,w3,w4,w5] 0x94a47d150d4338a429e6e26a129461260ad094a3002450254048cc14220900080d83458bc0c683cd4142c28e8485024c518d30c00808072424c1cd34d2fc07d6088a,
mkSt [w1,w12,w2,w0,w3,w4,w5,w81] 0x1c67e65267a74f64665326e466528c242466520dc421a565108cc80048342c1c0419482820bca854ec14d0f2cf404d81240013602ec0d02dd20789,
mkSt [w1,w2,w0,w20,w3,w4,w5,w81] 0x51a851a9546a052a834c45d2a9746401b6874da620216207552690881389d8d048f024203c2868a854ec3418bcdc1440f653782ec3402dc24d3740d02782f16088a,
mkSt [w50,w1,w2,w0,w3,w4,w5,w81] 0x36fced1bb7b77c7b4af5c7b49709f8f686cd070e3da2b4268d0402c20f400bc342804ec14d8f945d81253802f00d02dd18687,
mkSt [w17,w1,w2,w0,w3,w4,w5,w81] 0xf6361e1e322e12061d3a0e36392c426a260918618212061d0081d841cd03428bca8ec5014f46c0454603c8fc02f02dc24d3902500d02ed20709,
mkSt [w64,w1,w2,w0,w3,w4,w81] 0x3d9a3a3d6dba3171b630012daa1c09e54d9621015d0e8341c206054806c145068444804bd3a42dc1b01a41242e024c0d120788,
mkSt [w218,w1,w2,w0,w3,w4,w5] 0xad5d6ed22e9cd26cde40522d1dc1c1922d1c2411e06c5020401468343c1cd0001b13ac00893099d3a80381a42e00d024d2058b,
mkSt [w1,w2,w770,w0,w3,w4,w5] 0x350e0e3d2d3a15353201c92d2a2400d1211e18d0c8c8050483c40c8dc94541444003404d13b0008038aa41b000077825520788,
mkSt [w132,w1,w12,w2,w0,w3,w4,w5] 0x3eadea96ea43b76a6bcb76a4b84f46ac46680351ab119a0044483418e8d14828212868fccc040040f2d3bd3b87784d918785,
mkSt [w132,w1,w2,w0,w20,w3,w4,w5] 0x3ba7be1c7ecce3ee533e3d24a86fc7a466ccd2f1e900033444483c28342c0419285468fcdc0040f641240393d13c424c27918707,
mkSt [w132,w50,w1,w2,w0,w3,w4,w5] 0x2eadaa946a43b76a73da356233596ed49709d351ab119a2200f52844d8342804ec68fcccdc0040f953d53c47785d918705,
mkSt [w132,w17,w1,w2,w0,w3,w4,w5] 0x2726dd5a7243c39263bc39232375a72484ed92e1c9001b220034f52880602c201468fc040040fc00093e424d3b825118686,
mkSt [w1,w2,w146,w0,w3,w4,w5] 0x418f84c833ddd9062b9f016266b8b180065b21d589444a00442850ac24ec10840c3c6c4034608c013e800824c934a553ec1240380d03042f82556080c,
mkSt [w1,w2,w0,w3,w4,w189,w5] 0x14b40a8d1188d0a1db94ecfa64b95acc05d0542aa6482003c6c24601c20a81084005044d83428040c0081240054180f5430f080383380142616088b,
mkSt [w48,w1,w12,w2,w0,w3,w4,w5] 0x7a4ee6cfa4259ca6b019ee53951dfa73eddba91e90d9200183418d14828212840c444745c8c603394341a544430c304f4118707,
mkSt [w48,w1,w2,w0,w20,w3,w4,w5] 0xc44a652960afa1ab95940309341940b5aa890c9a42894ee00311280a3509024403c2820341868100cdc612874f0002430d4583540fc2780d031145c30434024d6080b,
mkSt [w50,w48,w1,w2,w0,w3,w4,w5] 0x17cd4f117a574bd2e4b6bd28c17497cd88e99805e94e111600f52844745c2414d8342804003381a54783100d0f9830518607,
mkSt [w17,w48,w1,w2,w0,w3,w4,w5] 0x96abe957892a175a2a4b14c2e8c9a00c96aa56142d5489280024c8143428a5281074f08cf4006c508460043d14943103040fc24c3c942c25030c0d12078b,
mkSt [w48,w1,w2,w0,w3,w4,w13,w5] 0x394c1438ef6c3935536c380c4f2ef438b4922df5b408014ced0474286c34a421286810840cd85c7400ac1b03382a54a149c0002604044083040fcf0824d2652070e,
mkSt [w52,w48,w1,w2,w0,w3,w4,w5] 0xe613642b2610296492c428e4928c4e48e61109482829e49104244c00344020844474d004acf06038001b0f08ae8be830c3114bc0d126c3052068a,
mkSt [w48,w1,w2,w0,w3,w4,w80] 0x164cce9823e5cc036cb1920a454ad94a97420e48c73098106c6034ac8c1084d480e86840744400241b14c42f94c00d01a412430424d60809,
mkSt [w48,w1,w2,w0,w3,w4,w49,w5] 0x14298c82a0cd90502472d6053cdd2d661828e6994304ce802018a48c3328820403804d0342928686410004424745c600c1b0f094c80694cc3382603100641c96088a,
mkSt [w58,w48,w1,w2,w0,w3,w4,w5] 0xa9db682da9182eab5b042eaa58461010a9d988c8242c21180cc4440034292840100c745c6c5024d8c41b0f0950c31008150833807c2601cc30d2068b,
mkSt [w48,w1,w2,w0,w3,w4,w29] 0xcf9da3215d891f5d9a1507599615d3054b90d0c106c60d83420108400e8806828740448440c261510f081a412401433958887,
mkSt [w1,w2,w21,w0,w3,w4,w5] 0x1d2dede5bda5de4e2dd5b8f4e1f190e8282de980e8c588ca41834c42c1c44683004603c401a426151c038124f140044d824120789,
mkSt [w1,w2,w0,w3,w4,w227,w5] 0x325dc0322a0e25a595b61c41d5e225b16d55ea19ac42c68003c281c4414d00434300c125558f200380fc000f2c1f000520689,
mkSt [w1,w12,w2,w0,w3,w4,w5,w29] 0x241aa76a2a25e9ea65cce8ebe54f882828274f0ac46aaa660dc94444a4194828204460342c301c3c0448c5434f201244d8f400143395700440192078a]
set_option maxHeartbeats 0 in
noncomputable def ptopD9p3 : List StD := [
mkSt [w26,w1,w12,w2,w0,w3,w4,w5] 0x2280178019158018d3a10018df9d1ac018979512c2d04e800000000009019482820d0342c1c6848443004403cc557c02805002cf2cf4158886,
mkSt [w110,w1,w2,w0,w3,w4,w5] 0x31a2222d5962281da2056415a6155c0251a2195dc14443024543420280c603c40041a558003920400812427c24c24120609,
mkSt [w1,w2,w0,w20,w3,w4,w13,w5] 0x2cb2c02da992ec82c2e9acc0cad1800002c00001c02d5d56d9954d400d0683cf02414100c340028d8f4434126403840559c24cf644082540052060b,
mkSt [w1,w2,w0,w20,w3,w4,w5,w80] 0x6b2ad62a2828286a940ca8aa1401c8000000200110e9295510d00048503cf0342014100c002840f655a84a01240395a424c4a42540052060a,
mkSt [w64,w1,w2,w0,w20,w3,w4,w5] 0x2e8aa9828449a6a109824242425c424e98899895024244498281104c84434f028040c0024143c483400041a40fd5ac0384d55bc24c2552058a,
mkSt [w147,w1,w2,w0,w3,w4,w5] 0x35ed9992a28e9155e5b29d61ed86a91ec28db295c6448283cdca4406c342044380c001f4124008000ae8f455c80fc0801f00f4f652068c,
mkSt [w1,w2,w0,w20,w3,w4,w5,w29] 0x2c16ef72726c3031accc32322ccc08b2f32e4c2a0532f2ae4d46050038d84460342818480c003cdc20354f440441240382542783400155cc01801d2068c,
mkSt [w26,w1,w2,w0,w20,w3,w4,w5] 0x3900ce01a1f0170f8301ab386b80356759710519400000000090d0342868484418400c003cdc215e405002803002cf6434118707,
mkSt [w1,w182,w2,w0,w3,w4,w5] 0x39a22235f5ce3115221dc251ae19dd2825a205c501044582450ec9434043020603c40001a55e8008f841240041dc5d824120709,
mkSt [w1,w2,w0,w3,w4,w229,w5] 0x2e9980ee2a0a2d61516a18c190ca216d1651aa255cc683c3028dc4414d820340c124001614404f7c0080fc004f941f12058a,
mkSt [w50,w1,w2,w0,w3,w4,w5,w29] 0x37f7ddcb969efcf134efcf13d43dfe6b72a0877e789b252244038f4483c302c20442804dcd834005d9624f7c01433962001c01918788,
mkSt [w26,w50,w1,w2,w0,w3,w4,w5] 0x20c0c580c7058016c59f00dcdb99164000c5951242508ec0c0c000c0090f4d03c302028046848442cdc40340162c028030f94f9802d58806,
mkSt [w1,w83,w2,w0,w3,w4,w5] 0x40d30987b199d0d562a216c0b20261ec8a502813026428184830508ca4dc84341c442840d03c14041a4008a09630250038244124fa824024d6080b,
mkSt [w1,w2,w0,w3,w4,w183,w5] 0x1eb1815e1a263d61457a2935b5a6355d1671ae115406c50206410443428683c0014041c6012400164cbe8fa00380fc068fc01f12078a,
mkSt [w17,w1,w2,w0,w3,w4,w13,w5] 0x106d42a90d2126c2e6cec28142828298c8dd5d0ac29041414d028188cd06828341000206c5014d84040043c8009264408fa165424cfc02552058b,
mkSt [w17,w1,w2,w0,w3,w4,w5,w80] 0x1e52510d121022e06121c41c1c1c1d8951918ca01c2010510c1cc488e8444034041000502414604a0004008124fc165824c25520588,
mkSt [w17,w64,w1,w2,w0,w3,w4,w5] 0x212797b3a5a43664ac46ca214a50ec24122242276001844809088d8a441120244434e82930a4f40c683c8c2c205014603c81a40fd65c00824d6604d025560809,
mkSt [w17,w1,w2,w0,w3,w4,w5,w29] 0xb06228984cd5031186a232b3d9cad350a592cc559a852006230d44602050444044d834483c28002cf4041c8060501401c0082542503d0fa00156680180456080a,
mkSt [w26,w17,w1,w2,w0,w3,w4,w5] 0x20c0dfc006c5c0dcdfd840dcdbd8570006c5c101825290c0c000c0c009034d03c28002c684844f4041c64501567c03002802cfc03c805158807,
mkSt [w148,w1,w2,w0,w3,w4,w13,w5] 0x3a98286d2e6ed03a9a6c3819d9ec38443819ad84383430182c0018246cd83420a454005014d0684241b06a16916842544044080e80040fc10424c2a52058e,
mkSt [w1,w2,w0,w3,w4,w13,w59,w5] 0x160a0442c152a8d85014c485bc414db62028120349828140a390006654050c8403c442cd8d034ac20a4a8140010840c6c500fc3389102a41b04084056b02a024c2556090b,
mkSt [w338,w1,w2,w0,w3,w4,w13,w5] 0x1e6e7b81cccc0eb4c0709b03060c02e060d1030a0c1830a64603c44d8d0341c20e0000c146c500fc2a16b83382542a518706,
mkSt [w79,w1,w2,w0,w3,w4,w13,w5] 0x1e0c14641de6501e0de41c0d4c1c1c441c0da5855c1c200c1c1d4c186cd83454205014d0686a02a44242543f8a049fc0fc24d20489,
mkSt [w79,w1,w2,w0,w3,w4,w5] 0x35a28eb1e9aea1d99e98202996a41822d19e8259820486c504014683c2054d03404441246a00086680789fc0383f8a0424024d2068b,
mkSt [w64,w1,w2,w0,w3,w4,w13,w5] 0x2317889c029c1002ca9e20161400018c01cddd8c014820140000180040e844d8353020100068acd050141b16c549d0c526424d6bc25520708,
mkSt [w1,w2,w339,w0,w3,w4,w13,w5] 0x3a7a417270b0ba0226323a41e63081ae40e46086060e4e525896160e4683480d8a0ac04d0a41410840c00e0216bc40440825412c0fcf2d6c833920809,
mkSt [w1,w2,w0,w3,w4,w13,w340,w5] 0x21309023e4120774b99ccd664ad40a95532241003119d8ea493110866561a8c868d03c345c2c5828aca45410140c20d80fcfa00696d8408404f4424c25560809,
mkSt [w341,w1,w2,w0,w3,w4,w13,w5] 0x1226221e0d0e1200c20d1201594d18c604955504c49201820d08c184844403c20106c502c140fcfc0f44fa16dc40424c25520488,
mkSt [w342,w1,w2,w0,w3,w4,w13,w5] 0x1bb7b4bd5ab6e0092b6e1650b147cfbf5668fb708495861468d06068e0140c44342800d8a56bc0fcf944056e833840918607,
mkSt [w1,w2,w69,w0,w3,w4,w13,w5] 0xc45c08d9d81e2e0c1dd9e4001dd9ac441c1d592c00e4e49d18ecec24782c6c7430d0e03428101468a40c2044002096f000425440409007958887,
mkSt [w76,w1,w2,w0,w3,w4,w13,w5] 0x209f80c949495c9a818946818197545090938342908e800c894a444286c80882ce034280c0044d8303ce8ac542256f82540c007840958806,
mkSt [w1,w2,w0,w3,w4,w771,w13,w5] 0x140804b980ee68980e44038500de203692cc140a0d2090253299cc46622890540686c5cd83404acd0e0a4a810140c5000201b149c2541612644044080fd7083396090a,
mkSt [w772,w1,w2,w0,w3,w4,w13,w5] 0x34ec8542450c125450c09d0408ac2336aac22404002040410408044d83420100068d0501526570d6bc24c1b025518606,
mkSt [w1,w773,w2,w0,w3,w4,w5] 0x25ca627625f26995a26daae5e242ad8c25e25c0d8186c5004446034c4ec203c0068401240097100782a00040381f02cc2b02412068b,
mkSt [w52,w1,w2,w69,w0,w3,w4,w5] 0x27c63c165c6a52e3050a14f3b0035ab656ac50744781800a286c6074201014d038040126d7241b0008ae807809118507,
mkSt [w52,w76,w1,w2,w0,w3,w4,w5] 0x3dd55bccdad27ad6c2778de8b176cdd59509d9366b402116004088e40c443c30ac54d0380448e80172c038078be80c118785,
mkSt [w1,w2,w150,w0,w3,w4,w5] 0x3dca2a39dab61dd82a1671ed222d0d25d82a2401250806c50d42034ec1c68602830043c400780097301240382000050847202412078a,
mkSt [w1,w2,w0,w3,w4,w232,w5] 0x125a40fa6dadb642316daa4158dda4e255d955a00cc3c442834ac20141cd8106c04500012400800174508c0380043381f120709,
mkSt [w1,w100,w2,w0,w3,w4,w49,w5] 0x31dea4b56ad961832d84e832d76c80065a0d09a1678e8b14286880405d24044540241014ed08d750038c8807806918606,
mkSt [w58,w1,w100,w2,w0,w3,w4,w5] 0x39565c4b52ec892b24b472b00990a1461491e1264b81a4082840712445402410ec6050dcd86c15758008080338078b1518706,
mkSt [w219,w1,w2,w0,w3,w4,w5] 0x12dddef122edc52addd80d0edde4181522ddc25a0106c50ac8460342444400c3c041b1764008a1ca553e80381a430424c2412060b,
mkSt [w1,w774,w2,w0,w3,w4,w5] 0x1aa1e2b5daad29f2a128d5d2ad0228c5e6a11c04c0c6cac50049434c4406860243c001b176c0081a40382117680047742412068a,
mkSt [w1,w220,w2,w0,w3,w4,w5] 0x39ceeaf9db36f1ed5eed15d16ac29e49e562e01c01c4450d42034a8541c406cd03c14040793a8008a2099c1240397742dc24c2e02412070c,
mkSt [w1,w2,w0,w3,w4,w97,w5] 0x191010d34f199ba29b4c981adb0ec05a1e9a4e01c02c503420481014042830603c1c000080001b00381257840181f120708,
mkSt [w64,w1,w2,w0,w3,w4,w49,w5] 0x1042810206e37040201037042c8109742020c8781b990c403021086e2403048402c992c4404d034280c0068603c5c141b17914c82544d40680781c960808,
mkSt [w58,w64,w1,w2,w0,w3,w4,w5] 0x1513878ea1078e9f1d9a431913831700d5139081c30e8d078a444300070d834280c00483c5ce8602d2c50dc1550d79c2540780801cc4d158807,
mkSt [w775,w1,w2,w0,w3,w4,w5] 0x198e1e2d595e2d39b6297295921172ae559e2945c14d01c0044283038344060546804201dc1257a8004e040080780d0e142412070a,
mkSt [w226,w1,w2,w0,w3,w4,w5] 0x39b62a2121a618fd9a251d79b605301e7daa258105cd0643c04403458286c1c004460500c1257b4000fa0fc00083d824c25520789,
mkSt [w1,w776,w2,w0,w3,w4,w5] 0x25d2223959f62da5e2316ee5e201ea5c25e2055c0146c5020441cd834c42804683c40141241f00057b8bbc0780380d0bcc07c2412070b,
mkSt [w1,w2,w187,w0,w3,w4,w5] 0x418f0787aa15d0d9230e1eab0431e02a0569919906513ac04828506810dc6c44d0341400403c0c241257bc000f4403824cf6408025560809,
mkSt [w1,w2,w0,w149,w3,w4,w5] 0x21c9e9bdd669b9dd6db975f2699a3165e4298165640683024202c341444281cd060403c051280041257c80383380d008c24120789,
mkSt [w1,w2,w0,w120,w3,w4,w5] 0x3a1221ba1d51b62919a92624218125321d6d85f12404478141028243440cc683c00d00c1240017dd12c03824c09025520708,
mkSt [w1,w2,w0,w3,w4,w129,w5] 0x15ddc091d0e1b9c19d8cf5f231a0eca5c61da8e49805c4420281014346000683ccc040c1e41242080040017e80381f120708,
mkSt [w777,w1,w2,w0,w3,w4,w5] 0x2a0d07844260e9087c1d1c4582c35124c5842a0c8920b008e8d0f0100044605c6834500c304004201b18040041dd8000d000824160808,
mkSt [w778,w1,w2,w0,w3,w4,w5] 0x2a12121616250e3e0d20fa362520f17a2a2520c0dd8a46c0c0468483c30144428341c40001b180c0003d980800824c25520788,
mkSt [w1,w779,w2,w0,w3,w4,w5] 0x1e65a67d9a7975b2656ce99a6554cdc5866544e000c6c5044d0f06834c4406030041c3c841b181c0041a58100d00380b024120789,
mkSt [w1,w2,w780,w0,w3,w4,w5] 0x1ddfc7dfbfef76e7760f1f146047edf2dc2d405044281014dc6434684030003c0c201b000182003824c0b425518787,
mkSt [w1,w781,w2,w0,w3,w4,w5] 0x41892c95b35492f675325aa863a3256a280b28032154801480e820283430a8ec686004d03c401c543398300041dc1240091780d00bc2416080a,
mkSt [w1,w2,w335,w0,w3,w4,w5] 0x3e071067c3150cf874b598a18580582a05541112c85139c03444485028ac1410ccd46c00403c0c8c3d812400183c00916824c0c025560809,
mkSt [w1,w2,w0,w3,w4,w223,w5] 0x39d1808dbcf1f981d1dcf9b625f0eca98625e0dc9803844203428144810cc006cd83c040c1f42241240040018480081f120788,
mkSt [w118,w1,w2,w0,w3,w4,w5] 0x1a4d8e791a759d324dac111661a8d01e5665ae05c106c50d828c4383c44406000340420f080080058540381a41f00d024120709,
mkSt [w188,w1,w2,w0,w3,w4,w5] 0x19d595fd75f99975c5b0094dd1ac2819f5d182416204450d0dc140440003080343c480c1c0080010c58581a403824c254aa520789]
noncomputable def ptopD9 : List StD := ptopD9p0 ++ ptopD9p1 ++ ptopD9p2 ++ ptopD9p3
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x0 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (0*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x1 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (1*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x2 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (2*64)).take 64) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC9x3 : levelOK ptopT ptopK ptopP 8 (ptopD8.map Prod.fst) ((ptopD9.drop (3*64)).take 64) = true := by decide +kernel
theorem ptopI9 : LevelN ptopR ptopT 9 ptopD9 := levelStep ptopB ptopW ptopQ ptopI8 (chunks 64 ptopD9 4 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC9x0
  · exact ptopC9x1
  · exact ptopC9x2
  · exact ptopC9x3
  ))
set_option maxHeartbeats 0 in
noncomputable def ptopD10 : List StD := [
mkSt [w28,w1,w2,w0,w3,w4,w5] 0x1c253098818212f329a6526d168ba5a2c300000120059a843c303424100cc004001c6c442820145060400581241a41a00380080040e800160909,
mkSt [w1,w2,w6,w0,w3,w4,w5] 0x4d94ea7a03da4f489b49e21007b29dc00068318aeb0011808060502cd4d0dcec94c434c04428043c306800401a42982a012400803800400160a08,
mkSt [w22,w1,w2,w0,w3,w4,w5] 0x501f2f9984025310803e4c0e3698e586932184c722304008486c5024d034ec94c40d18004420281c683c30408dc2981241a403800800000491160a09,
mkSt [w10,w1,w2,w0,w3,w4,w5] 0x48152598830212f311965c6d0602a500731988cb21301020486c50d4dc68401c3d18300414340c44d0289f42981241a40380080040009fd60909,
mkSt [w53,w1,w2,w0,w3,w4,w5] 0x2827dfe4cec7e2201fdcda9687d8d6888487d4c2928483c5c2420342c54080c3014d02800446cfc64dcb401241a4004038000b4958a07,
mkSt [w1,w2,w0,w24,w3,w4,w5] 0x44146a32c46151081c12000f07028db0985830086074c2c0d8cc24201c84c4343008d068443c4004140080381a4124004bb8bbc00160888,
mkSt [w54,w1,w2,w0,w3,w4,w5] 0x261fdfe4dcc7e2201fdcd69a87d8d6888487d4c2928485c242034288508143000d02cc444683c4004d6c1241a4004008000d7558987,
mkSt [w18,w1,w2,w0,w3,w4,w5] 0x381b1089988c91208842126f07036126c02988c90020981ccc24d03454403c0429083044680080500c6020dfc0081241a4004038000e0560988,
mkSt [w1,w2,w0,w3,w4,w15,w5] 0x51e7000693c9b12788421e48770321a4c02382090b250240e8486c2c64501c34201084944440283c0c3004681a01b0124008038004efc00160a08,
mkSt [w77,w1,w2,w0,w3,w4,w5] 0x3a1a6d89046206f07434d80723c14d64a209260a662110006cd85044603420840c400094303cd02804681a01240380080051e40001b160908,
mkSt [w88,w1,w2,w0,w3,w4,w5] 0x11c7dce1de22e1de1cce1bd686d89695c286c8849285080d034bc840c681444200028303cd4481240380080052b400118d58887,
mkSt [w1,w2,w0,w3,w4,w5,w81] 0x374e8d1a33efd3b9666dba1600ed8b2ab1606c50d020ecbc603428683c300440141241b000803800535000118787,
mkSt [w132,w1,w2,w0,w3,w4,w5] 0x21899b9f9d9a9f9d9a98178588945453858886425044844d03421281468008028ecfccc40041b00380080053b400158806,
mkSt [w48,w1,w2,w0,w3,w4,w5] 0xcc911899bc1d0a39046200a3783a1a060010cc90131181c6c203428403c30452868d08400040c7460245d4141a4038008004124000f0960988,
mkSt [w1,w12,w2,w0,w3,w4,w5] 0xe17d7d4ecd5eaa893e6e4a2a1dedc9a1817d4d2828588ca418e8d1482820140c342c1c68443004403c60c55541241a4000038004f2158b07,
mkSt [w1,w2,w0,w20,w3,w4,w5] 0x1c190c8419ccb1033996000f0703200e63682c190b331a80f024d014340cdc186840283c446000215980381a4124000008f4400560808,
mkSt [w50,w1,w2,w0,w3,w4,w5] 0xe1bdbd8e4c7e29687e0de1c1bd8d6888487d4d28285824f4140c3c3020280468402cdc4434d8016101241a4000008004f7d58907,
mkSt [w17,w1,w2,w0,w3,w4,w5] 0x201d10899a8c71208842146d0783a146d03188c70020384cf08cd0340c3c002cf428a440046c1c445060156480081241a4000038004fa160988,
mkSt [w1,w2,w0,w3,w4,w13,w5] 0x25fa002cacae3ddc3a3495c2162cb025e8222ca81406cd850a43414680c30d0203c0044281a01b012400803800168000520788,
mkSt [w52,w1,w2,w0,w3,w4,w5] 0x360e71880361e6824410dc4706c30d6082112a0865200048342850a4603c14d004206830f03840e8001a01240380080017140041b160888,
mkSt [w1,w100,w2,w0,w3,w4,w5] 0x1bc9d6dbce2ae9e692e6a5e2a0de9c9bd816d41282851242044d940f024800c34141c684030043c6028ec12403800800173c00508d58a87,
mkSt [w1,w2,w0,w3,w4,w5,w80] 0x18ec77badd6f1783b1de40843b9d64606ba1d8eb2501002ce850d00c403415244430283c00d424601241b176000803800175c00560888,
mkSt [w130,w1,w2,w0,w3,w4,w5] 0x1d87879d9ba09f8986945d9b9896145389868450424512c68403c1424440430d480d03428001b003800800177000558806,
mkSt [w64,w1,w2,w0,w3,w4,w5] 0x28c90e891a0230a3803a120a3783a1a0d00108c90630384ce850d00c3400692c44206004301c3c2848157801a40380080001240050c560908,
mkSt [w1,w2,w0,w3,w4,w49,w5] 0x2caa00e511261c801e312c04b62530ac20aa251ca00d058686034002804643c440c1c1a01240040017a00380081b120688,
mkSt [w58,w1,w2,w0,w3,w4,w5] 0x2e10fa20a210f02e38f4b02e24e09c0481d0c0188c8345844402c3c280024045014d86c1a00081240040017c40381b120708,
mkSt [w1,w2,w69,w0,w3,w4,w5] 0x1d8b98e99688e782a4e29da018d69e9d9a18d694920786c74302024444034281400d004683ccc0c1c601240040017d803820958a06,
mkSt [w1,w2,w0,w3,w4,w5,w117] 0x157d7d495d5e261cdc8825fddd49a4459d7d4925002878e8d0f06c40343000805c043c600c1c1b17f40380040017f000958887,
mkSt [w106,w1,w2,w0,w3,w4,w5] 0x1b47616549469d63609e5d5b589654134946904442488d034f068603c5c006c28443004645020841b000400182403958905,
mkSt [w76,w1,w2,w0,w3,w4,w5] 0x1fc9dae5cc88e3e01ad89fdc1ad896018688d48482888e820800c34cc0030d06c6028043c488c5412403800400184400822558907,
mkSt [w1,w2,w0,w3,w4,w5,w29] 0x1c0487842e16f187c31e02187c39d62d04c2218eb1502402c5080d82060341400440448303c280c1c1a41a000803800400012585160888,
mkSt [w26,w1,w2,w0,w3,w4,w5] 0x11803700ea18074dde0074dd82c52980000000905020d03414006848440440303c280c1d85c1b012550883]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC10x0 : levelOK ptopT ptopK ptopP 9 (ptopD9.map Prod.fst) ((ptopD10.drop (0*64)).take 64) = true := by decide +kernel
theorem ptopI10 : LevelN ptopR ptopT 10 ptopD10 := levelStep ptopB ptopW ptopQ ptopI9 (chunks 64 ptopD10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC10x0
  ))
set_option maxHeartbeats 0 in
noncomputable def ptopD11 : List StD := [
mkSt [w1,w2,w0,w3,w4,w5] 0x386cda4388d01e3678c1c3660b06c50242040341400d00468303c4428600c1cef81a150902]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem ptopC11x0 : levelOK ptopT ptopK ptopP 10 (ptopD10.map Prod.fst) ((ptopD11.drop (0*64)).take 64) = true := by decide +kernel
theorem ptopI11 : LevelN ptopR ptopT 11 ptopD11 := levelStep ptopB ptopW ptopQ ptopI10 (chunks 64 ptopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC11x0
  ))
theorem ptopL : LowN ptopR ptopT 12 := lowSearch ptopB ptopI11 (by decide +kernel)

def sixInputs : List Sig := rootsW [0,1,2,3,4,5]
def graph : Sig := W ptopT
theorem graph_proper : proper graph := (baseOK_ok ptopB).prop
def sample (r : Row) (i : Fin 6) : Bool := bit r (sixInputs.getD i.val zero)
theorem sixList : List.ofFn (fun i : Fin 6 => sixInputs.getD i.val zero) = sixInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = sixInputs.map (bit r) := by
  rw [←sixList,List.map_ofFn]
  rfl
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sixTable : ∀ r : Row, bit r graph = target (sample r) := by decide +kernel
theorem sixEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sixInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sixInputs.toFinset := by
  have b := baseOK_ok ptopB
  have goalEq : (execute C.gates sixInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sixEval C legal C.output r).trans ((computes (sample r)).trans (sixTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sixInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W ptopT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sixInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sixInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = sixInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run sixInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes : Impossible true graph 11 sixInputs.toFinset := by
  intro k small run
  have steps := list_run run sixInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (sixInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega
theorem replaceShort (s : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize 6 target s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  classical
  by_cases big : 13 ≤ s
  · exact ⟨smallCircuit,witnessMonotone,(by rw [witnessSize]; exact big),witnessCorrect⟩
  obtain ⟨C,legal,hs,correct⟩ := h
  by_cases mono : ∀ g ∈ C.gates, g.op ≠ GateOp.not
  · refine ⟨C,?_,hs,correct⟩
    intro g hg
    obtain ⟨ho,hl⟩ := legal g hg
    refine ⟨?_,hl⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ho ⊢
    rcases ho with a | a | a
    · exact Or.inl a
    · exact Or.inr a
    · exact (mono g hg a).elim
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : C.gates.countP (fun q => !isNot q) < C.gates.length := by
    rcases Nat.lt_or_ge (C.gates.countP (fun q => !isNot q)) C.gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  obtain ⟨k,hk,run⟩ := physicalSigned C legal correct
  have hs' : C.gates.length ≤ s := hs
  exact (excludes k (by omega) run).elim

end PEqualNP.Outside.L_meta_46668

theorem PEqualNP.Outside.L_meta_46668 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124264 * 2 ^ 32 + 4276812936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124264 * 2 ^ 32 + 4276812936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  exact PEqualNP.Outside.L_meta_46668.replaceShort s h
