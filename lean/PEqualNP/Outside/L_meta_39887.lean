import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39887_aux
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
def full : Nat := ((0xffffffff * 2 ^ 32 + 0xffffffff) * 2 ^ 64 + (0xffffffff * 2 ^ 32 + 0xffffffff))
def xN : Nat → Nat
  | 0 => ((0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa) * 2 ^ 64 + (0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa))
  | 1 => ((0xcccccccc * 2 ^ 32 + 0xcccccccc) * 2 ^ 64 + (0xcccccccc * 2 ^ 32 + 0xcccccccc))
  | 2 => ((0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0) * 2 ^ 64 + (0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0))
  | 3 => ((0xff00ff00 * 2 ^ 32 + 0xff00ff00) * 2 ^ 64 + (0xff00ff00 * 2 ^ 32 + 0xff00ff00))
  | 4 => ((0xffff0000 * 2 ^ 32 + 0xffff0000) * 2 ^ 64 + (0xffff0000 * 2 ^ 32 + 0xffff0000))
  | 5 => ((0xffffffff * 2 ^ 32 + 0x0) * 2 ^ 64 + (0xffffffff * 2 ^ 32 + 0x0))
  | _ => ((0xffffffff * 2 ^ 32 + 0xffffffff) * 2 ^ 64 + 0x0)
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

def w0 : Nat := ((0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa) * 2 ^ 64 + (0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa))
def w1 : Nat := ((0xcccccccc * 2 ^ 32 + 0xcccccccc) * 2 ^ 64 + (0xcccccccc * 2 ^ 32 + 0xcccccccc))
def w2 : Nat := ((0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0) * 2 ^ 64 + (0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0))
def w3 : Nat := ((0xff00ff00 * 2 ^ 32 + 0xff00ff00) * 2 ^ 64 + (0xff00ff00 * 2 ^ 32 + 0xff00ff00))
def w4 : Nat := ((0x88888888 * 2 ^ 32 + 0x88888888) * 2 ^ 64 + (0x88888888 * 2 ^ 32 + 0x88888888))
def w5 : Nat := ((0xa0a0a0a0 * 2 ^ 32 + 0xa0a0a0a0) * 2 ^ 64 + (0xa0a0a0a0 * 2 ^ 32 + 0xa0a0a0a0))
def w6 : Nat := ((0xaa00aa00 * 2 ^ 32 + 0xaa00aa00) * 2 ^ 64 + (0xaa00aa00 * 2 ^ 32 + 0xaa00aa00))
def w7 : Nat := ((0xc0c0c0c0 * 2 ^ 32 + 0xc0c0c0c0) * 2 ^ 64 + (0xc0c0c0c0 * 2 ^ 32 + 0xc0c0c0c0))
def w8 : Nat := ((0xcc00cc00 * 2 ^ 32 + 0xcc00cc00) * 2 ^ 64 + (0xcc00cc00 * 2 ^ 32 + 0xcc00cc00))
def w9 : Nat := ((0xf000f000 * 2 ^ 32 + 0xf000f000) * 2 ^ 64 + (0xf000f000 * 2 ^ 32 + 0xf000f000))
def w10 : Nat := ((0x80808080 * 2 ^ 32 + 0x80808080) * 2 ^ 64 + (0x80808080 * 2 ^ 32 + 0x80808080))
def w11 : Nat := ((0x70707070 * 2 ^ 32 + 0x70707070) * 2 ^ 64 + (0x70707070 * 2 ^ 32 + 0x70707070))
def w12 : Nat := ((0x88008800 * 2 ^ 32 + 0x88008800) * 2 ^ 64 + (0x88008800 * 2 ^ 32 + 0x88008800))
def w13 : Nat := ((0x77007700 * 2 ^ 32 + 0x77007700) * 2 ^ 64 + (0x77007700 * 2 ^ 32 + 0x77007700))
def w14 : Nat := ((0x4c4c4c4c * 2 ^ 32 + 0x4c4c4c4c) * 2 ^ 64 + (0x4c4c4c4c * 2 ^ 32 + 0x4c4c4c4c))
def w15 : Nat := ((0xa000a000 * 2 ^ 32 + 0xa000a000) * 2 ^ 64 + (0xa000a000 * 2 ^ 32 + 0xa000a000))
def w16 : Nat := ((0x5f005f00 * 2 ^ 32 + 0x5f005f00) * 2 ^ 64 + (0x5f005f00 * 2 ^ 32 + 0x5f005f00))
def w17 : Nat := ((0x44cc44cc * 2 ^ 32 + 0x44cc44cc) * 2 ^ 64 + (0x44cc44cc * 2 ^ 32 + 0x44cc44cc))
def w18 : Nat := ((0x50f050f0 * 2 ^ 32 + 0x50f050f0) * 2 ^ 64 + (0x50f050f0 * 2 ^ 32 + 0x50f050f0))
def w19 : Nat := ((0x2a2a2a2a * 2 ^ 32 + 0x2a2a2a2a) * 2 ^ 64 + (0x2a2a2a2a * 2 ^ 32 + 0x2a2a2a2a))
def w20 : Nat := ((0xc000c000 * 2 ^ 32 + 0xc000c000) * 2 ^ 64 + (0xc000c000 * 2 ^ 32 + 0xc000c000))
def w21 : Nat := ((0x3f003f00 * 2 ^ 32 + 0x3f003f00) * 2 ^ 64 + (0x3f003f00 * 2 ^ 32 + 0x3f003f00))
def w22 : Nat := ((0x22aa22aa * 2 ^ 32 + 0x22aa22aa) * 2 ^ 64 + (0x22aa22aa * 2 ^ 32 + 0x22aa22aa))
def w23 : Nat := ((0x30f030f0 * 2 ^ 32 + 0x30f030f0) * 2 ^ 64 + (0x30f030f0 * 2 ^ 32 + 0x30f030f0))
def w24 : Nat := (0xaaa0aaa0aaa0aaa * 2 ^ 64 + 0xaaa0aaa0aaa0aaa)
def w25 : Nat := (0xccc0ccc0ccc0ccc * 2 ^ 64 + 0xccc0ccc0ccc0ccc)
def w26 : Nat := ((0x7f007f00 * 2 ^ 32 + 0x7f007f00) * 2 ^ 64 + (0x7f007f00 * 2 ^ 32 + 0x7f007f00))
def w27 : Nat := ((0x70f070f0 * 2 ^ 32 + 0x70f070f0) * 2 ^ 64 + (0x70f070f0 * 2 ^ 32 + 0x70f070f0))
def w28 : Nat := ((0x4ccc4ccc * 2 ^ 32 + 0x4ccc4ccc) * 2 ^ 64 + (0x4ccc4ccc * 2 ^ 32 + 0x4ccc4ccc))
def w29 : Nat := ((0x2aaa2aaa * 2 ^ 32 + 0x2aaa2aaa) * 2 ^ 64 + (0x2aaa2aaa * 2 ^ 32 + 0x2aaa2aaa))
def w30 : Nat := ((0xeeeeeeee * 2 ^ 32 + 0xeeeeeeee) * 2 ^ 64 + (0xeeeeeeee * 2 ^ 32 + 0xeeeeeeee))
def w31 : Nat := ((0xfafafafa * 2 ^ 32 + 0xfafafafa) * 2 ^ 64 + (0xfafafafa * 2 ^ 32 + 0xfafafafa))
def w32 : Nat := ((0xffaaffaa * 2 ^ 32 + 0xffaaffaa) * 2 ^ 64 + (0xffaaffaa * 2 ^ 32 + 0xffaaffaa))
def w33 : Nat := ((0xfcfcfcfc * 2 ^ 32 + 0xfcfcfcfc) * 2 ^ 64 + (0xfcfcfcfc * 2 ^ 32 + 0xfcfcfcfc))
def w34 : Nat := ((0xffccffcc * 2 ^ 32 + 0xffccffcc) * 2 ^ 64 + (0xffccffcc * 2 ^ 32 + 0xffccffcc))
def w35 : Nat := ((0xfff0fff0 * 2 ^ 32 + 0xfff0fff0) * 2 ^ 64 + (0xfff0fff0 * 2 ^ 32 + 0xfff0fff0))
def w36 : Nat := ((0xfefefefe * 2 ^ 32 + 0xfefefefe) * 2 ^ 64 + (0xfefefefe * 2 ^ 32 + 0xfefefefe))
def w37 : Nat := (0xe0e0e0e0e0e0e0e * 2 ^ 64 + 0xe0e0e0e0e0e0e0e)
def w38 : Nat := ((0xffeeffee * 2 ^ 32 + 0xffeeffee) * 2 ^ 64 + (0xffeeffee * 2 ^ 32 + 0xffeeffee))
def w39 : Nat := (0xee00ee00ee00ee0 * 2 ^ 60 + 0xee00ee00ee00ee)
def w40 : Nat := ((0x32323232 * 2 ^ 32 + 0x32323232) * 2 ^ 64 + (0x32323232 * 2 ^ 32 + 0x32323232))
def w41 : Nat := ((0xfffafffa * 2 ^ 32 + 0xfffafffa) * 2 ^ 64 + (0xfffafffa * 2 ^ 32 + 0xfffafffa))
def w42 : Nat := (0xfa00fa00fa00fa0 * 2 ^ 60 + 0xfa00fa00fa00fa)
def w43 : Nat := ((0x33223322 * 2 ^ 32 + 0x33223322) * 2 ^ 64 + (0x33223322 * 2 ^ 32 + 0x33223322))
def w44 : Nat := (0xf0a0f0a0f0a0f0a * 2 ^ 64 + 0xf0a0f0a0f0a0f0a)
def w45 : Nat := ((0x54545454 * 2 ^ 32 + 0x54545454) * 2 ^ 64 + (0x54545454 * 2 ^ 32 + 0x54545454))
def w46 : Nat := ((0xfffcfffc * 2 ^ 32 + 0xfffcfffc) * 2 ^ 64 + (0xfffcfffc * 2 ^ 32 + 0xfffcfffc))
def w47 : Nat := (0xfc00fc00fc00fc0 * 2 ^ 60 + 0xfc00fc00fc00fc)
def w48 : Nat := ((0x55445544 * 2 ^ 32 + 0x55445544) * 2 ^ 64 + (0x55445544 * 2 ^ 32 + 0x55445544))
def w49 : Nat := (0xf0c0f0c0f0c0f0c * 2 ^ 64 + 0xf0c0f0c0f0c0f0c)
def w50 : Nat := ((0x55505550 * 2 ^ 32 + 0x55505550) * 2 ^ 64 + (0x55505550 * 2 ^ 32 + 0x55505550))
def w51 : Nat := ((0x33303330 * 2 ^ 32 + 0x33303330) * 2 ^ 64 + (0x33303330 * 2 ^ 32 + 0x33303330))
def w52 : Nat := (0xfe00fe00fe00fe0 * 2 ^ 60 + 0xfe00fe00fe00fe)
def w53 : Nat := (0xf0e0f0e0f0e0f0e * 2 ^ 64 + 0xf0e0f0e0f0e0f0e)
def w54 : Nat := ((0x33323332 * 2 ^ 32 + 0x33323332) * 2 ^ 64 + (0x33323332 * 2 ^ 32 + 0x33323332))
def w55 : Nat := ((0x55545554 * 2 ^ 32 + 0x55545554) * 2 ^ 64 + (0x55545554 * 2 ^ 32 + 0x55545554))
def w56 : Nat := ((0x22222222 * 2 ^ 32 + 0x22222222) * 2 ^ 64 + (0x22222222 * 2 ^ 32 + 0x22222222))
def w57 : Nat := ((0x44444444 * 2 ^ 32 + 0x44444444) * 2 ^ 64 + (0x44444444 * 2 ^ 32 + 0x44444444))
def w58 : Nat := (0xa0a0a0a0a0a0a0a * 2 ^ 64 + 0xa0a0a0a0a0a0a0a)
def w59 : Nat := ((0x50505050 * 2 ^ 32 + 0x50505050) * 2 ^ 64 + (0x50505050 * 2 ^ 32 + 0x50505050))
def w60 : Nat := (0xaa00aa00aa00aa0 * 2 ^ 60 + 0xaa00aa00aa00aa)
def w61 : Nat := ((0x55005500 * 2 ^ 32 + 0x55005500) * 2 ^ 64 + (0x55005500 * 2 ^ 32 + 0x55005500))
def w62 : Nat := (0xc0c0c0c0c0c0c0c * 2 ^ 64 + 0xc0c0c0c0c0c0c0c)
def w63 : Nat := ((0x30303030 * 2 ^ 32 + 0x30303030) * 2 ^ 64 + (0x30303030 * 2 ^ 32 + 0x30303030))
def w64 : Nat := (0xcc00cc00cc00cc0 * 2 ^ 60 + 0xcc00cc00cc00cc)
def w65 : Nat := ((0x33003300 * 2 ^ 32 + 0x33003300) * 2 ^ 64 + (0x33003300 * 2 ^ 32 + 0x33003300))
def w66 : Nat := (0xf000f000f000f00 * 2 ^ 60 + 0xf000f000f000f0)
def w67 : Nat := (0xf000f000f000f00 * 2 ^ 64 + 0xf000f000f000f00)
def w68 : Nat := ((0xf8f8f8f8 * 2 ^ 32 + 0xf8f8f8f8) * 2 ^ 64 + (0xf8f8f8f8 * 2 ^ 32 + 0xf8f8f8f8))
def w69 : Nat := ((0xff88ff88 * 2 ^ 32 + 0xff88ff88) * 2 ^ 64 + (0xff88ff88 * 2 ^ 32 + 0xff88ff88))
def w70 : Nat := ((0xe0e0e0e0 * 2 ^ 32 + 0xe0e0e0e0) * 2 ^ 64 + (0xe0e0e0e0 * 2 ^ 32 + 0xe0e0e0e0))
def w71 : Nat := ((0xee00ee00 * 2 ^ 32 + 0xee00ee00) * 2 ^ 64 + (0xee00ee00 * 2 ^ 32 + 0xee00ee00))
def w72 : Nat := ((0xecececec * 2 ^ 32 + 0xecececec) * 2 ^ 64 + (0xecececec * 2 ^ 32 + 0xecececec))
def w73 : Nat := ((0xffa0ffa0 * 2 ^ 32 + 0xffa0ffa0) * 2 ^ 64 + (0xffa0ffa0 * 2 ^ 32 + 0xffa0ffa0))
def w74 : Nat := ((0xc8c8c8c8 * 2 ^ 32 + 0xc8c8c8c8) * 2 ^ 64 + (0xc8c8c8c8 * 2 ^ 32 + 0xc8c8c8c8))
def w75 : Nat := ((0xfa00fa00 * 2 ^ 32 + 0xfa00fa00) * 2 ^ 64 + (0xfa00fa00 * 2 ^ 32 + 0xfa00fa00))
def w76 : Nat := ((0xeecceecc * 2 ^ 32 + 0xeecceecc) * 2 ^ 64 + (0xeecceecc * 2 ^ 32 + 0xeecceecc))
def w77 : Nat := ((0xfaf0faf0 * 2 ^ 32 + 0xfaf0faf0) * 2 ^ 64 + (0xfaf0faf0 * 2 ^ 32 + 0xfaf0faf0))
def w78 : Nat := ((0xcc88cc88 * 2 ^ 32 + 0xcc88cc88) * 2 ^ 64 + (0xcc88cc88 * 2 ^ 32 + 0xcc88cc88))
def w79 : Nat := ((0xf0a0f0a0 * 2 ^ 32 + 0xf0a0f0a0) * 2 ^ 64 + (0xf0a0f0a0 * 2 ^ 32 + 0xf0a0f0a0))
def w80 : Nat := ((0xff0cff0c * 2 ^ 32 + 0xff0cff0c) * 2 ^ 64 + (0xff0cff0c * 2 ^ 32 + 0xff0cff0c))
def w81 : Nat := ((0xf300f300 * 2 ^ 32 + 0xf300f300) * 2 ^ 64 + (0xf300f300 * 2 ^ 32 + 0xf300f300))
def w82 : Nat := ((0xff30ff30 * 2 ^ 32 + 0xff30ff30) * 2 ^ 64 + (0xff30ff30 * 2 ^ 32 + 0xff30ff30))
def w83 : Nat := ((0xcf00cf00 * 2 ^ 32 + 0xcf00cf00) * 2 ^ 64 + (0xcf00cf00 * 2 ^ 32 + 0xcf00cf00))
def w84 : Nat := ((0xf0fcf0fc * 2 ^ 32 + 0xf0fcf0fc) * 2 ^ 64 + (0xf0fcf0fc * 2 ^ 32 + 0xf0fcf0fc))
def w85 : Nat := ((0xf030f030 * 2 ^ 32 + 0xf030f030) * 2 ^ 64 + (0xf030f030 * 2 ^ 32 + 0xf030f030))
def w86 : Nat := ((0xf3f0f3f0 * 2 ^ 32 + 0xf3f0f3f0) * 2 ^ 64 + (0xf3f0f3f0 * 2 ^ 32 + 0xf3f0f3f0))
def w87 : Nat := ((0xc0f0c0f0 * 2 ^ 32 + 0xc0f0c0f0) * 2 ^ 64 + (0xc0f0c0f0 * 2 ^ 32 + 0xc0f0c0f0))
def w88 : Nat := ((0xccfcccfc * 2 ^ 32 + 0xccfcccfc) * 2 ^ 64 + (0xccfcccfc * 2 ^ 32 + 0xccfcccfc))
def w89 : Nat := ((0xcc0ccc0c * 2 ^ 32 + 0xcc0ccc0c) * 2 ^ 64 + (0xcc0ccc0c * 2 ^ 32 + 0xcc0ccc0c))
def w90 : Nat := ((0xcfcccfcc * 2 ^ 32 + 0xcfcccfcc) * 2 ^ 64 + (0xcfcccfcc * 2 ^ 32 + 0xcfcccfcc))
def w91 : Nat := ((0xc0ccc0cc * 2 ^ 32 + 0xc0ccc0cc) * 2 ^ 64 + (0xc0ccc0cc * 2 ^ 32 + 0xc0ccc0cc))
def w92 : Nat := ((0xffff0000 * 2 ^ 32 + 0xffff0000) * 2 ^ 64 + (0xffff0000 * 2 ^ 32 + 0xffff0000))
def w93 : Nat := ((0xcccc0000 * 2 ^ 32 + 0xcccc0000) * 2 ^ 64 + (0xcccc0000 * 2 ^ 32 + 0xcccc0000))
def w94 : Nat := ((0xf0f00000 * 2 ^ 32 + 0xf0f00000) * 2 ^ 64 + (0xf0f00000 * 2 ^ 32 + 0xf0f00000))
def w95 : Nat := ((0xff000000 * 2 ^ 32 + 0xff000000) * 2 ^ 64 + (0xff000000 * 2 ^ 32 + 0xff000000))
def w96 : Nat := ((0xffc0c0c0 * 2 ^ 32 + 0xffc0c0c0) * 2 ^ 64 + (0xffc0c0c0 * 2 ^ 32 + 0xffc0c0c0))
def w97 : Nat := ((0xfcf0cc00 * 2 ^ 32 + 0xfcf0cc00) * 2 ^ 64 + (0xfcf0cc00 * 2 ^ 32 + 0xfcf0cc00))
def w98 : Nat := ((0xfcccf000 * 2 ^ 32 + 0xfcccf000) * 2 ^ 64 + (0xfcccf000 * 2 ^ 32 + 0xfcccf000))
def w99 : Nat := ((0xffffffff * 2 ^ 32 + 0x0) * 2 ^ 64 + (0xffffffff * 2 ^ 32 + 0x0))
def w100 : Nat := ((0xaaaa0000 * 2 ^ 32 + 0xaaaa0000) * 2 ^ 64 + (0xaaaa0000 * 2 ^ 32 + 0xaaaa0000))
def w101 : Nat := (0xff000000ff00000 * 2 ^ 60 + 0xff000000ff0000)
def w102 : Nat := (0xff00ff000000000 * 2 ^ 60 + 0xff00ff00000000)
def w103 : Nat := ((0xf8f88888 * 2 ^ 32 + 0xf8f88888) * 2 ^ 64 + (0xf8f88888 * 2 ^ 32 + 0xf8f88888))
def w104 : Nat := ((0xececa0a0 * 2 ^ 32 + 0xececa0a0) * 2 ^ 64 + (0xececa0a0 * 2 ^ 32 + 0xececa0a0))
def w105 : Nat := ((0xeaeac0c0 * 2 ^ 32 + 0xeaeac0c0) * 2 ^ 64 + (0xeaeac0c0 * 2 ^ 32 + 0xeaeac0c0))
def p1_T : Nat := ((0x88888888 * 2 ^ 32 + 0x88888888) * 2 ^ 64 + (0x88888888 * 2 ^ 32 + 0x88888888))
def p1_R : List Nat := [0, 1]
def p1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
theorem p1_B : baseOK p1_T p1_R p1_E = true := by decide +kernel
theorem p1_L : LowN p1_R p1_T 1 := lowCount p1_B (by decide +kernel)

def p2_T : Nat := ((0xeeeeeeee * 2 ^ 32 + 0xeeeeeeee) * 2 ^ 64 + (0xeeeeeeee * 2 ^ 32 + 0xeeeeeeee))
def p2_R : List Nat := [0, 1]
def p2_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
theorem p2_L : LowN p2_R p2_T 1 := lowCount p2_B (by decide +kernel)

def p3_T : Nat := ((0xe8e8e8e8 * 2 ^ 32 + 0xe8e8e8e8) * 2 ^ 64 + (0xe8e8e8e8 * 2 ^ 32 + 0xe8e8e8e8))
def p3_R : List Nat := [0, 1, 2]
def p3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
theorem p3_S0 : SliceN p3_R p3_T (((0x33333333 * 2 ^ 32 + 0x33333333) * 2 ^ 64 + (0x33333333 * 2 ^ 32 + 0x33333333)),1,[0, 2]) := mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel)
theorem p3_S1 : SliceN p3_R p3_T (((0x55555555 * 2 ^ 32 + 0x55555555) * 2 ^ 64 + (0x55555555 * 2 ^ 32 + 0x55555555)),1,[1, 2]) := mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel)
theorem p3_S2 : SliceN p3_R p3_T (((0xcccccccc * 2 ^ 32 + 0xcccccccc) * 2 ^ 64 + (0xcccccccc * 2 ^ 32 + 0xcccccccc)),1,[0, 2]) := mkSlice (w:=2) p3_B p2_B p2_L (by decide +kernel)
theorem p3_S3 : SliceN p3_R p3_T (((0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa) * 2 ^ 64 + (0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa)),1,[1, 2]) := mkSlice (w:=1) p3_B p2_B p2_L (by decide +kernel)
theorem p3_S4 : SliceN p3_R p3_T ((0xf0f0f0f0f0f0f0f * 2 ^ 64 + 0xf0f0f0f0f0f0f0f),1,[0, 1]) := mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel)
theorem p3_S5 : SliceN p3_R p3_T (((0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0) * 2 ^ 64 + (0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0)),1,[0, 1]) := mkSlice (w:=4) p3_B p2_B p2_L (by decide +kernel)
def p3_Z : List SliceD := [(((0x33333333 * 2 ^ 32 + 0x33333333) * 2 ^ 64 + (0x33333333 * 2 ^ 32 + 0x33333333)),1,[0, 2]),(((0x55555555 * 2 ^ 32 + 0x55555555) * 2 ^ 64 + (0x55555555 * 2 ^ 32 + 0x55555555)),1,[1, 2]),(((0xcccccccc * 2 ^ 32 + 0xcccccccc) * 2 ^ 64 + (0xcccccccc * 2 ^ 32 + 0xcccccccc)),1,[0, 2]),(((0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa) * 2 ^ 64 + (0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa)),1,[1, 2]),((0xf0f0f0f0f0f0f0f * 2 ^ 64 + 0xf0f0f0f0f0f0f0f),1,[0, 1]),(((0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0) * 2 ^ 64 + (0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0)),1,[0, 1])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨p3_S0,p3_S1,p3_S2,p3_S3,p3_S4,p3_S5,by simp⟩
def p3_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def p3_P : List (Nat × Nat) := [(4,5),(1,3),(0,3),(2,3),(2,6),(1,5)]
def p3_K : List CutV := p3_C.map (mkCut p3_Z)
theorem p3_W : ∀ c ∈ p3_K, CutP p3_R p3_T c := cutsGood p3_Y (by decide +kernel)
theorem p3_Q : p3_P.all (sepOK p3_T) = true := by decide +kernel
noncomputable def p3_D3 : List StD := [
([w0,w1,w2],[0,1,2,3,4,5],[0,1,2,3,4,5],[[0,1,100,2,3,101,102],[4,1,103,5,3,100],[4,0,101,5,2,104,105]])]
def p3_D2 : List StD := []
theorem p3_I2 : LevelN p3_R p3_T 2 p3_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p3_C3x0 : levelOK p3_T p3_K p3_P 2 (p3_D2.map Prod.fst) ((p3_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem p3_I3 : LevelN p3_R p3_T 3 p3_D3 := levelStep p3_B p3_W p3_Q p3_I2 (chunks 16 p3_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C3x0
  ))
theorem p3_L : LowN p3_R p3_T 4 := lowSearch p3_B p3_I3 (by decide +kernel)

def p4_T : Nat := ((0x80808080 * 2 ^ 32 + 0x80808080) * 2 ^ 64 + (0x80808080 * 2 ^ 32 + 0x80808080))
def p4_R : List Nat := [0, 1, 2]
def p4_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
theorem p4_L : LowN p4_R p4_T 2 := lowCount p4_B (by decide +kernel)

def p5_T : Nat := ((0xe880e880 * 2 ^ 32 + 0xe880e880) * 2 ^ 64 + (0xe880e880 * 2 ^ 32 + 0xe880e880))
def p5_R : List Nat := [0, 1, 2, 3]
def p5_E : List (Nat × Nat × Nat) := [(0,6,7),(1,5,7),(2,3,7),(3,3,11)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
theorem p5_S0 : SliceN p5_R p5_T (((0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa) * 2 ^ 64 + (0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa)),4,[1, 2, 3]) := mkSlice (w:=1) p5_B p3_B p3_L (by decide +kernel)
theorem p5_S1 : SliceN p5_R p5_T (((0xcccccccc * 2 ^ 32 + 0xcccccccc) * 2 ^ 64 + (0xcccccccc * 2 ^ 32 + 0xcccccccc)),4,[0, 2, 3]) := mkSlice (w:=2) p5_B p3_B p3_L (by decide +kernel)
theorem p5_S2 : SliceN p5_R p5_T (((0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0) * 2 ^ 64 + (0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0)),4,[0, 1, 3]) := mkSlice (w:=4) p5_B p3_B p3_L (by decide +kernel)
theorem p5_S3 : SliceN p5_R p5_T (((0xff00ff00 * 2 ^ 32 + 0xff00ff00) * 2 ^ 64 + (0xff00ff00 * 2 ^ 32 + 0xff00ff00)),4,[0, 1, 2]) := mkSlice (w:=8) p5_B p3_B p3_L (by decide +kernel)
theorem p5_S4 : SliceN p5_R p5_T (((0x55555555 * 2 ^ 32 + 0x55555555) * 2 ^ 64 + (0x55555555 * 2 ^ 32 + 0x55555555)),2,[1, 2, 3]) := mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S5 : SliceN p5_R p5_T (((0x88888888 * 2 ^ 32 + 0x88888888) * 2 ^ 64 + (0x88888888 * 2 ^ 32 + 0x88888888)),1,[2, 3]) := mkSlice (w:=3) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S6 : SliceN p5_R p5_T (((0xa0a0a0a0 * 2 ^ 32 + 0xa0a0a0a0) * 2 ^ 64 + (0xa0a0a0a0 * 2 ^ 32 + 0xa0a0a0a0)),1,[1, 3]) := mkSlice (w:=5) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S7 : SliceN p5_R p5_T (((0xaa00aa00 * 2 ^ 32 + 0xaa00aa00) * 2 ^ 64 + (0xaa00aa00 * 2 ^ 32 + 0xaa00aa00)),1,[1, 2]) := mkSlice (w:=9) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S8 : SliceN p5_R p5_T (((0x33333333 * 2 ^ 32 + 0x33333333) * 2 ^ 64 + (0x33333333 * 2 ^ 32 + 0x33333333)),2,[0, 2, 3]) := mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S9 : SliceN p5_R p5_T (((0xc0c0c0c0 * 2 ^ 32 + 0xc0c0c0c0) * 2 ^ 64 + (0xc0c0c0c0 * 2 ^ 32 + 0xc0c0c0c0)),1,[0, 3]) := mkSlice (w:=6) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S10 : SliceN p5_R p5_T (((0xcc00cc00 * 2 ^ 32 + 0xcc00cc00) * 2 ^ 64 + (0xcc00cc00 * 2 ^ 32 + 0xcc00cc00)),1,[0, 2]) := mkSlice (w:=10) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S11 : SliceN p5_R p5_T ((0xf0f0f0f0f0f0f0f * 2 ^ 64 + 0xf0f0f0f0f0f0f0f),2,[0, 1, 3]) := mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S12 : SliceN p5_R p5_T (((0xf000f000 * 2 ^ 32 + 0xf000f000) * 2 ^ 64 + (0xf000f000 * 2 ^ 32 + 0xf000f000)),1,[0, 1]) := mkSlice (w:=12) p5_B p2_B p2_L (by decide +kernel)
theorem p5_S13 : SliceN p5_R p5_T (((0x50505050 * 2 ^ 32 + 0x50505050) * 2 ^ 64 + (0x50505050 * 2 ^ 32 + 0x50505050)),1,[1, 3]) := mkSlice (w:=4) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S14 : SliceN p5_R p5_T (((0x30303030 * 2 ^ 32 + 0x30303030) * 2 ^ 64 + (0x30303030 * 2 ^ 32 + 0x30303030)),1,[0, 3]) := mkSlice (w:=4) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S15 : SliceN p5_R p5_T ((0xff00ff00ff00ff0 * 2 ^ 60 + 0xff00ff00ff00ff),2,[0, 1, 2]) := mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel)
theorem p5_S16 : SliceN p5_R p5_T (((0x55005500 * 2 ^ 32 + 0x55005500) * 2 ^ 64 + (0x55005500 * 2 ^ 32 + 0x55005500)),1,[1, 2]) := mkSlice (w:=8) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S17 : SliceN p5_R p5_T (((0x33003300 * 2 ^ 32 + 0x33003300) * 2 ^ 64 + (0x33003300 * 2 ^ 32 + 0x33003300)),1,[0, 2]) := mkSlice (w:=8) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S18 : SliceN p5_R p5_T ((0xc0c0c0c0c0c0c0c * 2 ^ 64 + 0xc0c0c0c0c0c0c0c),1,[0, 3]) := mkSlice (w:=2) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S19 : SliceN p5_R p5_T ((0xcc00cc00cc00cc0 * 2 ^ 60 + 0xcc00cc00cc00cc),1,[0, 2]) := mkSlice (w:=2) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S20 : SliceN p5_R p5_T ((0xa0a0a0a0a0a0a0a * 2 ^ 64 + 0xa0a0a0a0a0a0a0a),1,[1, 3]) := mkSlice (w:=1) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S21 : SliceN p5_R p5_T ((0xaa00aa00aa00aa0 * 2 ^ 60 + 0xaa00aa00aa00aa),1,[1, 2]) := mkSlice (w:=1) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S22 : SliceN p5_R p5_T (((0x44444444 * 2 ^ 32 + 0x44444444) * 2 ^ 64 + (0x44444444 * 2 ^ 32 + 0x44444444)),1,[2, 3]) := mkSlice (w:=2) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S23 : SliceN p5_R p5_T ((0xf000f000f000f00 * 2 ^ 64 + 0xf000f000f000f00),1,[0, 1]) := mkSlice (w:=8) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S24 : SliceN p5_R p5_T ((0xf000f000f000f00 * 2 ^ 60 + 0xf000f000f000f0),1,[0, 1]) := mkSlice (w:=4) p5_B p1_B p1_L (by decide +kernel)
theorem p5_S25 : SliceN p5_R p5_T (((0x22222222 * 2 ^ 32 + 0x22222222) * 2 ^ 64 + (0x22222222 * 2 ^ 32 + 0x22222222)),1,[2, 3]) := mkSlice (w:=1) p5_B p1_B p1_L (by decide +kernel)
def p5_Z : List SliceD := [(((0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa) * 2 ^ 64 + (0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa)),4,[1, 2, 3]),(((0xcccccccc * 2 ^ 32 + 0xcccccccc) * 2 ^ 64 + (0xcccccccc * 2 ^ 32 + 0xcccccccc)),4,[0, 2, 3]),(((0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0) * 2 ^ 64 + (0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0)),4,[0, 1, 3]),(((0xff00ff00 * 2 ^ 32 + 0xff00ff00) * 2 ^ 64 + (0xff00ff00 * 2 ^ 32 + 0xff00ff00)),4,[0, 1, 2]),(((0x55555555 * 2 ^ 32 + 0x55555555) * 2 ^ 64 + (0x55555555 * 2 ^ 32 + 0x55555555)),2,[1, 2, 3]),(((0x88888888 * 2 ^ 32 + 0x88888888) * 2 ^ 64 + (0x88888888 * 2 ^ 32 + 0x88888888)),1,[2, 3]),(((0xa0a0a0a0 * 2 ^ 32 + 0xa0a0a0a0) * 2 ^ 64 + (0xa0a0a0a0 * 2 ^ 32 + 0xa0a0a0a0)),1,[1, 3]),(((0xaa00aa00 * 2 ^ 32 + 0xaa00aa00) * 2 ^ 64 + (0xaa00aa00 * 2 ^ 32 + 0xaa00aa00)),1,[1, 2]),(((0x33333333 * 2 ^ 32 + 0x33333333) * 2 ^ 64 + (0x33333333 * 2 ^ 32 + 0x33333333)),2,[0, 2, 3]),(((0xc0c0c0c0 * 2 ^ 32 + 0xc0c0c0c0) * 2 ^ 64 + (0xc0c0c0c0 * 2 ^ 32 + 0xc0c0c0c0)),1,[0, 3]),(((0xcc00cc00 * 2 ^ 32 + 0xcc00cc00) * 2 ^ 64 + (0xcc00cc00 * 2 ^ 32 + 0xcc00cc00)),1,[0, 2]),((0xf0f0f0f0f0f0f0f * 2 ^ 64 + 0xf0f0f0f0f0f0f0f),2,[0, 1, 3]),(((0xf000f000 * 2 ^ 32 + 0xf000f000) * 2 ^ 64 + (0xf000f000 * 2 ^ 32 + 0xf000f000)),1,[0, 1]),(((0x50505050 * 2 ^ 32 + 0x50505050) * 2 ^ 64 + (0x50505050 * 2 ^ 32 + 0x50505050)),1,[1, 3]),(((0x30303030 * 2 ^ 32 + 0x30303030) * 2 ^ 64 + (0x30303030 * 2 ^ 32 + 0x30303030)),1,[0, 3]),((0xff00ff00ff00ff0 * 2 ^ 60 + 0xff00ff00ff00ff),2,[0, 1, 2]),(((0x55005500 * 2 ^ 32 + 0x55005500) * 2 ^ 64 + (0x55005500 * 2 ^ 32 + 0x55005500)),1,[1, 2]),(((0x33003300 * 2 ^ 32 + 0x33003300) * 2 ^ 64 + (0x33003300 * 2 ^ 32 + 0x33003300)),1,[0, 2]),((0xc0c0c0c0c0c0c0c * 2 ^ 64 + 0xc0c0c0c0c0c0c0c),1,[0, 3]),((0xcc00cc00cc00cc0 * 2 ^ 60 + 0xcc00cc00cc00cc),1,[0, 2]),((0xa0a0a0a0a0a0a0a * 2 ^ 64 + 0xa0a0a0a0a0a0a0a),1,[1, 3]),((0xaa00aa00aa00aa0 * 2 ^ 60 + 0xaa00aa00aa00aa),1,[1, 2]),(((0x44444444 * 2 ^ 32 + 0x44444444) * 2 ^ 64 + (0x44444444 * 2 ^ 32 + 0x44444444)),1,[2, 3]),((0xf000f000f000f00 * 2 ^ 64 + 0xf000f000f000f00),1,[0, 1]),((0xf000f000f000f00 * 2 ^ 60 + 0xf000f000f000f0),1,[0, 1]),(((0x22222222 * 2 ^ 32 + 0x22222222) * 2 ^ 64 + (0x22222222 * 2 ^ 32 + 0x22222222)),1,[2, 3])]
theorem p5_Y : ∀ s ∈ p5_Z, SliceN p5_R p5_T s := by
  unfold p5_Z
  simp only [List.forall_mem_cons]
  exact ⟨p5_S0,p5_S1,p5_S2,p5_S3,p5_S4,p5_S5,p5_S6,p5_S7,p5_S8,p5_S9,p5_S10,p5_S11,p5_S12,p5_S13,p5_S14,p5_S15,p5_S16,p5_S17,p5_S18,p5_S19,p5_S20,p5_S21,p5_S22,p5_S23,p5_S24,p5_S25,by simp⟩
def p5_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(2,[(0,0,1)]),(3,[(0,0,1)]),(6,[]),(1,[(0,0,1)]),(3,[(0,0,2)]),(7,[]),(1,[(0,0,2)]),(2,[(0,0,2)]),(8,[]),(9,[]),(0,[(0,0,1)]),(3,[(0,1,2)]),(10,[]),(0,[(0,0,2)]),(2,[(0,1,2)]),(1,[(0,1,2)]),(0,[(0,1,2)]),(11,[]),(12,[]),(1,[(2,0,1)]),(0,[(2,0,1)]),(0,[(3,0,1)]),(13,[]),(14,[]),(1,[(3,0,1)]),(1,[(2,0,2)]),(0,[(2,0,2)]),(0,[(3,0,2)]),(15,[]),(16,[]),(17,[]),(1,[(3,0,2)]),(2,[(2,0,1)]),(18,[]),(3,[(2,0,1)]),(19,[]),(20,[]),(21,[]),(2,[(3,0,1)]),(22,[]),(3,[(2,0,2)]),(0,[(2,1,2)]),(0,[(3,1,2)]),(23,[]),(2,[(3,0,2)]),(2,[(2,0,2)]),(24,[]),(25,[]),(3,[(3,0,1)]),(3,[(3,0,2)]),(3,[(2,1,2)]),(3,[(3,1,2)]),(1,[(3,1,2)]),(0,[(1,1,2)]),(2,[(3,1,2)]),(1,[(2,1,2)]),(0,[(1,0,1)]),(0,[(1,0,2)]),(3,[(0,0,2),(0,1,2)]),(3,[(0,0,1),(0,1,2)]),(3,[(0,0,1),(0,0,2)]),(2,[(0,0,1),(0,0,2)]),(3,[(0,0,2),(2,1,3)]),(1,[(0,0,1),(0,0,2)]),(0,[(0,0,2),(0,1,2)]),(0,[(0,0,1),(0,1,2)]),(0,[(0,0,1),(0,0,2)])]
def p5_P : List (Nat × Nat) := [(12,13),(12,14),(5,7),(10,11),(10,14),(6,7),(6,14),(9,11),(9,13),(5,13),(3,7),(3,11),(2,11),(4,13),(2,7),(8,13),(1,11),(4,14),(1,7),(8,14),(4,7),(8,11),(1,13),(2,14),(0,11),(0,13),(0,14),(0,7)]
def p5_K : List CutV := p5_C.map (mkCut p5_Z)
theorem p5_W : ∀ c ∈ p5_K, CutP p5_R p5_T c := cutsGood p5_Y (by decide +kernel)
theorem p5_Q : p5_P.all (sepOK p5_T) = true := by decide +kernel
noncomputable def p5_D6 : List StD := [
([w0,w1,w2,w3],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11],[[100,101,0,1,102],[103,104,0,2,100],[105,106,0,3,100],[107,108,1,2,101],[102,109,1,3,101],[110,111,2,3,104]])]
noncomputable def p5_D5 : List StD := [
([w4,w0,w1,w2,w3],[0,1,4,2,5,3,6,7],[8,10,9,11,4,6],[[0,1],[0],[2,100,3,4,101],[2,102,5,4,103],[0,1],[0,104,6],[0,105,7],[1,100,6],[1,102,7],[101,103,7,6,100]]),
([w5,w0,w1,w2,w3],[0,2,4,1,8,3,9,10],[7,2,11,9,1,6],[[0,1],[2,100,3,4,101],[0],[2,102,5,4,103],[0,104,6],[0,1],[0,105,7],[1,100,6],[101,103,7,6,100],[1,102,7]]),
([w6,w0,w1,w2,w3],[0,3,4,1,11,2,12,13],[2,7,10,8,1,4],[[0,1],[2,100,3,4,101],[2,102,5,4,103],[0],[0,104,6],[0,105,7],[0,1],[101,103,7,6,100],[1,100,6],[1,102,7]]),
([w0,w7,w1,w2,w3],[14,15,0,16,1,2,17,3],[3,5,0,6,11,9],[[0,100,1,2,101],[0,102,1,3,4],[5,100,3],[101,103,6,3,100],[4,5],[4],[0,104,6,1,7,103],[4,5],[0,105,4,6],[5,104,6]]),
([w0,w8,w1,w2,w3],[14,18,0,19,1,20,3,2],[5,3,0,4,10,8],[[0,100,1,2,101],[0,102,1,3,4],[101,103,5,3,100],[6,100,3],[4,6],[0,104,5,1,7,103],[4],[0,105,4,5],[4,6],[6,104,5]]),
([w0,w1,w9,w2,w3],[21,22,23,24,0,2,3,1],[0,1,2,5,3,7],[[100,101,0,1,102],[2,103,3,1,4,100],[2,104,3,1,5],[6,103,1],[2,102,3,0,7,101],[2,105,3,0,5],[6,102,0],[5,6],[5],[5,6]])]
noncomputable def p5_D4 : List StD := [
([w10,w0,w1,w2,w3],[25,26,27,23,3,6,16,9,4,14],[],[[0],[1],[2],[3,4],[5,6,7],[3,5],[8,6],[3,5],[9,7],[3,5]]),
([w11,w0,w1,w2,w3],[1,0,16,23,3,28,27,6,29,30],[],[[0,1],[1,0],[2],[3,4,5],[5,6],[3,6,7],[5,6],[3,5],[8,9],[3,5]]),
([w12,w0,w1,w2,w3],[31,32,14,2,33,19,12,4,34,7],[],[[0],[1],[2,3],[4],[2,5,6],[7,5],[6,5,7],[2,6],[2,6],[8,9]]),
([w13,w0,w1,w2,w3],[1,0,34,2,35,19,33,7,36,37],[],[[0,1],[1,0],[2,3,4],[5],[4,6],[4,6],[2,6,7],[8,9],[2,4],[2,4]]),
([w4,w5,w1,w2,w3],[6,38,0,9,23,4,10,14,7,29,39],[12,13],[[0,1],[2],[3,0,4],[5,6,100],[0,3,7],[2],[5,8,101],[0,3],[9,3],[10,0]]),
([w4,w6,w1,w2,w3],[7,40,0,4,13,34,1,14,6,36,12,41],[14,15],[[0,1],[2],[3,4,100],[3,0,5],[0,6,7],[3,8,101],[2],[9,10],[0,10],[11,0]]),
([w4,w0,w7,w2,w3],[38,16,23,14,17,4,6,28,27,7,42],[16,17],[[0],[1,0],[1,0,2],[3,4,100],[3,1,5],[1,6],[7,1],[8],[3,9,101],[10,6]]),
([w4,w0,w8,w2,w3],[40,19,14,20,34,4,35,7,6,33,43],[18,19],[[0],[1,0],[2,3,100],[1,0,4],[2,1,5],[6,1],[1,7],[2,8,101],[9],[10,6]]),
([w14,w0,w1,w2,w3],[2,0,16,14,3,39,26,44,45],[],[[0,1],[2],[1,0],[3,4,5],[3,5],[5,6,7],[8,6],[3,7,8],[3,5],[5,7]]),
([w15,w0,w1,w2,w3],[46,4,1,47,48,22,23,13,34,10],[],[[0],[1,2],[3],[4],[1,5],[1,5],[1,5],[6,7],[8,9],[5,7,6]]),
([w16,w0,w1,w2,w3],[46,10,34,1,35,22,48,49,50],[],[[0,1],[2,3,4],[2,0,1],[5],[4,6],[1,6,4],[2,1],[7,8],[2,1],[2,1]]),
([w5,w6,w1,w2,w3],[34,2,51,35,12,0,3,9,23,49,13,52],[20,21],[[0,1,2],[3,4,100],[5],[0,6],[3,7,101],[3,1,8],[5],[9,10],[11,3],[3,10]]),
([w5,w0,w7,w1,w3],[25,16,14,23,17,35,9,45,26,53],[22,23],[[0],[1,0],[1,0,2],[3,4,100],[3,1,5],[1,6],[7,1],[8],[3,5,101],[9,6]]),
([w5,w0,w1,w9,w3],[46,23,21,22,34,35,10,9,43,48],[18,19],[[0],[1,2,100],[3,0],[1,0,4],[5,3],[1,3,5],[3,6],[1,7,101],[8,5],[9]]),
([w17,w0,w1,w2,w3],[31,12,19,14,45,32,41,54],[],[[0,1],[2],[3,4],[2,0],[3,1],[4,5],[1,5,4],[3,1],[3,1],[6,7]]),
([w18,w0,w1,w2,w3],[23,0,3,1,52,22,28,47,55],[],[[0,1,2],[0,3,4],[5],[0,2,1],[6,7],[0,4],[4,7,6],[0,4],[4,8],[0,6]]),
([w6,w0,w8,w1,w2],[3,19,33,1,14,45,20,12,34,13,53],[22,23],[[0],[1,2],[1,3,4],[5,6,100],[5,1],[1,7],[5,1],[0],[8,9,101],[10,5]]),
([w6,w0,w1,w9,w2],[3,34,21,22,48,2,23,28,13,12,42],[16,17],[[0],[1,2,100],[3,4],[1,5,6],[7,3],[1,3,7],[3,8],[1,9,101],[10,7],[0]]),
([w19,w0,w1,w2,w3],[9,26,16,28,3,42,45,53],[],[[0],[1,2],[0,1],[3,4,5],[3,2],[6,2],[3,2],[2,3,5],[7,6],[5,3]]),
([w0,w20,w1,w2,w3],[23,0,14,21,53,20,34,17,56,57,58],[],[[0,1],[2,3],[0,4,5],[6,4,7],[8],[9],[10],[0,3,2],[2,3],[0,5]]),
([w21,w0,w1,w2,w3],[34,0,49,59,17,21,36,58,60],[],[[0,1,2],[0,2],[0,3,4],[5],[6,7],[2,8],[0,2],[2,7,6],[0,2],[0,4]]),
([w0,w7,w8,w2,w3],[49,19,36,16,20,52,1,3],[20,21],[[0,1,100],[2,3,101],[0,4],[5,0],[0,4],[6],[4,7,5],[0,4],[6],[2,4]]),
([w0,w7,w1,w9,w3],[49,22,36,21,16,41,56,58],[14,15],[[0,1,100],[2,3],[0,4,101],[5,0],[6],[2,3],[3,6,5],[0,3,2],[0,3],[7]]),
([w22,w0,w1,w2,w3],[12,32,19,45,2,53,28,43,40],[],[[0],[1,2],[3,4,5],[0,1],[6,2],[3,2],[3,2],[5,3],[2,3,5],[7,6,8]]),
([w23,w0,w1,w2,w3],[49,0,52,17,1,29,61,23],[],[[0,1,2],[0,2],[3],[4,3],[5,6],[0,2],[2,0],[0,2],[2,0],[7,5]]),
([w0,w8,w1,w9,w2],[52,22,29,21,19,39,3,2],[12,13],[[0,1,100],[2,3],[0,4,101],[5,0],[6],[2,3],[3,7,5],[0,3,2],[0,3],[6]]),
([w24,w0,w1,w2,w3],[10,28,1,43,0,22,45,42,46],[],[[0],[1,2,3],[0,3,4],[1,0,5],[1,3],[6,3],[1,5],[7,1],[3,6,8],[3,1,7]]),
([w25,w0,w1,w2,w3],[29,0,39,17,62,26,41,56,36],[],[[0,1,2],[3],[3,4,5],[0,2],[0,2],[2,0],[6,7],[8,6],[0,2],[2,0]])]
noncomputable def p5_D3 : List StD := [
([w26,w0,w1,w2],[52,0,36,63,29,39,41],[],[[0,1,2],[0,3,4],[5,2,4],[2,5],[5,0],[2,0,6]]),
([w27,w0,w1,w3],[39,0,52,36,27,41,29],[],[[0,1,2],[3,2,4],[0,3,5],[3,0],[2,3],[2,0,6]]),
([w4,w5,w7,w3],[16,1,52,29,64,39,65,66],[24,25,26],[[0,1,2],[0,2],[3,4,100],[0,1],[5,6,101],[3,7,102]]),
([w4,w6,w8,w2],[19,3,52,36,33,41,29,67],[27,25,26],[[0,1,2],[0,1],[3,2,100],[0,4],[5,6,101],[3,7,102]]),
([w28,w0,w2,w3],[29,0,41,36,63,52,68,39],[],[[0,1,2],[3,2],[0,4,5],[6,0,7],[2,3],[2,0,3]]),
([w5,w6,w1,w9],[22,3,52,28,41,39,69],[27,24,26],[[0,1,2],[3,4,100],[0,1],[2,5,101],[0,3],[2,6,102]]),
([w29,w1,w2,w3],[28,0,36,39,52,41,29],[],[[0,1,2],[3,1],[0,1,4],[2,0,5],[4,3,6],[3,0]]),
([w0,w7,w8,w9],[39,70,52,71,72,3,1,58],[27,24,25],[[0,1,100],[2,3,101],[0,4,102],[0,5,2],[2,5],[0,6,7]])]
def p5_D2 : List StD := []
theorem p5_I2 : LevelN p5_R p5_T 2 p5_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C3x0 : levelOK p5_T p5_K p5_P 2 (p5_D2.map Prod.fst) ((p5_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem p5_I3 : LevelN p5_R p5_T 3 p5_D3 := levelStep p5_B p5_W p5_Q p5_I2 (chunks 16 p5_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C4x0 : levelOK p5_T p5_K p5_P 3 (p5_D3.map Prod.fst) ((p5_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C4x1 : levelOK p5_T p5_K p5_P 3 (p5_D3.map Prod.fst) ((p5_D4.drop (1*16)).take 16) = true := by decide +kernel
theorem p5_I4 : LevelN p5_R p5_T 4 p5_D4 := levelStep p5_B p5_W p5_Q p5_I3 (chunks 16 p5_D4 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C4x0
  · exact p5_C4x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C5x0 : levelOK p5_T p5_K p5_P 4 (p5_D4.map Prod.fst) ((p5_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem p5_I5 : LevelN p5_R p5_T 5 p5_D5 := levelStep p5_B p5_W p5_Q p5_I4 (chunks 16 p5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p5_C6x0 : levelOK p5_T p5_K p5_P 5 (p5_D5.map Prod.fst) ((p5_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem p5_I6 : LevelN p5_R p5_T 6 p5_D6 := levelStep p5_B p5_W p5_Q p5_I5 (chunks 16 p5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C6x0
  ))
theorem p5_L : LowN p5_R p5_T 7 := lowSearch p5_B p5_I6 (by decide +kernel)

def p6_T : Nat := ((0xfefefefe * 2 ^ 32 + 0xfefefefe) * 2 ^ 64 + (0xfefefefe * 2 ^ 32 + 0xfefefefe))
def p6_R : List Nat := [0, 1, 2]
def p6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
theorem p6_L : LowN p6_R p6_T 2 := lowCount p6_B (by decide +kernel)

def p7_T : Nat := ((0xfee8fee8 * 2 ^ 32 + 0xfee8fee8) * 2 ^ 64 + (0xfee8fee8 * 2 ^ 32 + 0xfee8fee8))
def p7_R : List Nat := [0, 1, 2, 3]
def p7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
theorem p7_S0 : SliceN p7_R p7_T (((0x55555555 * 2 ^ 32 + 0x55555555) * 2 ^ 64 + (0x55555555 * 2 ^ 32 + 0x55555555)),4,[1, 2, 3]) := mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel)
theorem p7_S1 : SliceN p7_R p7_T (((0x33333333 * 2 ^ 32 + 0x33333333) * 2 ^ 64 + (0x33333333 * 2 ^ 32 + 0x33333333)),4,[0, 2, 3]) := mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel)
theorem p7_S2 : SliceN p7_R p7_T ((0xf0f0f0f0f0f0f0f * 2 ^ 64 + 0xf0f0f0f0f0f0f0f),4,[0, 1, 3]) := mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel)
theorem p7_S3 : SliceN p7_R p7_T ((0xff00ff00ff00ff0 * 2 ^ 60 + 0xff00ff00ff00ff),4,[0, 1, 2]) := mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel)
theorem p7_S4 : SliceN p7_R p7_T (((0x11111111 * 2 ^ 32 + 0x11111111) * 2 ^ 64 + (0x11111111 * 2 ^ 32 + 0x11111111)),1,[2, 3]) := mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel)
theorem p7_S5 : SliceN p7_R p7_T (((0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa) * 2 ^ 64 + (0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa)),2,[1, 2, 3]) := mkSlice (w:=1) p7_B p6_B p6_L (by decide +kernel)
theorem p7_S6 : SliceN p7_R p7_T ((0x505050505050505 * 2 ^ 64 + 0x505050505050505),1,[1, 3]) := mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel)
theorem p7_S7 : SliceN p7_R p7_T ((0x550055005500550 * 2 ^ 60 + 0x55005500550055),1,[1, 2]) := mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel)
theorem p7_S8 : SliceN p7_R p7_T ((0x303030303030303 * 2 ^ 64 + 0x303030303030303),1,[0, 3]) := mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel)
theorem p7_S9 : SliceN p7_R p7_T (((0xcccccccc * 2 ^ 32 + 0xcccccccc) * 2 ^ 64 + (0xcccccccc * 2 ^ 32 + 0xcccccccc)),2,[0, 2, 3]) := mkSlice (w:=2) p7_B p6_B p6_L (by decide +kernel)
theorem p7_S10 : SliceN p7_R p7_T ((0x330033003300330 * 2 ^ 60 + 0x33003300330033),1,[0, 2]) := mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel)
theorem p7_S11 : SliceN p7_R p7_T ((0xf000f000f000f0 * 2 ^ 60 + 0xf000f000f000f),1,[0, 1]) := mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel)
theorem p7_S12 : SliceN p7_R p7_T (((0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0) * 2 ^ 64 + (0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0)),2,[0, 1, 3]) := mkSlice (w:=4) p7_B p6_B p6_L (by decide +kernel)
theorem p7_S13 : SliceN p7_R p7_T ((0xc0c0c0c0c0c0c0c * 2 ^ 64 + 0xc0c0c0c0c0c0c0c),1,[0, 3]) := mkSlice (w:=2) p7_B p2_B p2_L (by decide +kernel)
theorem p7_S14 : SliceN p7_R p7_T (((0x30303030 * 2 ^ 32 + 0x30303030) * 2 ^ 64 + (0x30303030 * 2 ^ 32 + 0x30303030)),1,[0, 3]) := mkSlice (w:=4) p7_B p2_B p2_L (by decide +kernel)
theorem p7_S15 : SliceN p7_R p7_T ((0xcc00cc00cc00cc0 * 2 ^ 60 + 0xcc00cc00cc00cc),1,[0, 2]) := mkSlice (w:=2) p7_B p2_B p2_L (by decide +kernel)
theorem p7_S16 : SliceN p7_R p7_T (((0xff00ff00 * 2 ^ 32 + 0xff00ff00) * 2 ^ 64 + (0xff00ff00 * 2 ^ 32 + 0xff00ff00)),2,[0, 1, 2]) := mkSlice (w:=8) p7_B p6_B p6_L (by decide +kernel)
theorem p7_S17 : SliceN p7_R p7_T (((0x33003300 * 2 ^ 32 + 0x33003300) * 2 ^ 64 + (0x33003300 * 2 ^ 32 + 0x33003300)),1,[0, 2]) := mkSlice (w:=8) p7_B p2_B p2_L (by decide +kernel)
theorem p7_S18 : SliceN p7_R p7_T ((0xa0a0a0a0a0a0a0a * 2 ^ 64 + 0xa0a0a0a0a0a0a0a),1,[1, 3]) := mkSlice (w:=1) p7_B p2_B p2_L (by decide +kernel)
theorem p7_S19 : SliceN p7_R p7_T (((0x50505050 * 2 ^ 32 + 0x50505050) * 2 ^ 64 + (0x50505050 * 2 ^ 32 + 0x50505050)),1,[1, 3]) := mkSlice (w:=4) p7_B p2_B p2_L (by decide +kernel)
theorem p7_S20 : SliceN p7_R p7_T ((0xaa00aa00aa00aa0 * 2 ^ 60 + 0xaa00aa00aa00aa),1,[1, 2]) := mkSlice (w:=1) p7_B p2_B p2_L (by decide +kernel)
theorem p7_S21 : SliceN p7_R p7_T (((0x55005500 * 2 ^ 32 + 0x55005500) * 2 ^ 64 + (0x55005500 * 2 ^ 32 + 0x55005500)),1,[1, 2]) := mkSlice (w:=8) p7_B p2_B p2_L (by decide +kernel)
theorem p7_S22 : SliceN p7_R p7_T ((0xf000f000f000f00 * 2 ^ 60 + 0xf000f000f000f0),1,[0, 1]) := mkSlice (w:=4) p7_B p2_B p2_L (by decide +kernel)
theorem p7_S23 : SliceN p7_R p7_T ((0xf000f000f000f00 * 2 ^ 64 + 0xf000f000f000f00),1,[0, 1]) := mkSlice (w:=8) p7_B p2_B p2_L (by decide +kernel)
theorem p7_S24 : SliceN p7_R p7_T (((0x22222222 * 2 ^ 32 + 0x22222222) * 2 ^ 64 + (0x22222222 * 2 ^ 32 + 0x22222222)),1,[2, 3]) := mkSlice (w:=1) p7_B p2_B p2_L (by decide +kernel)
theorem p7_S25 : SliceN p7_R p7_T (((0x44444444 * 2 ^ 32 + 0x44444444) * 2 ^ 64 + (0x44444444 * 2 ^ 32 + 0x44444444)),1,[2, 3]) := mkSlice (w:=2) p7_B p2_B p2_L (by decide +kernel)
def p7_Z : List SliceD := [(((0x55555555 * 2 ^ 32 + 0x55555555) * 2 ^ 64 + (0x55555555 * 2 ^ 32 + 0x55555555)),4,[1, 2, 3]),(((0x33333333 * 2 ^ 32 + 0x33333333) * 2 ^ 64 + (0x33333333 * 2 ^ 32 + 0x33333333)),4,[0, 2, 3]),((0xf0f0f0f0f0f0f0f * 2 ^ 64 + 0xf0f0f0f0f0f0f0f),4,[0, 1, 3]),((0xff00ff00ff00ff0 * 2 ^ 60 + 0xff00ff00ff00ff),4,[0, 1, 2]),(((0x11111111 * 2 ^ 32 + 0x11111111) * 2 ^ 64 + (0x11111111 * 2 ^ 32 + 0x11111111)),1,[2, 3]),(((0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa) * 2 ^ 64 + (0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa)),2,[1, 2, 3]),((0x505050505050505 * 2 ^ 64 + 0x505050505050505),1,[1, 3]),((0x550055005500550 * 2 ^ 60 + 0x55005500550055),1,[1, 2]),((0x303030303030303 * 2 ^ 64 + 0x303030303030303),1,[0, 3]),(((0xcccccccc * 2 ^ 32 + 0xcccccccc) * 2 ^ 64 + (0xcccccccc * 2 ^ 32 + 0xcccccccc)),2,[0, 2, 3]),((0x330033003300330 * 2 ^ 60 + 0x33003300330033),1,[0, 2]),((0xf000f000f000f0 * 2 ^ 60 + 0xf000f000f000f),1,[0, 1]),(((0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0) * 2 ^ 64 + (0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0)),2,[0, 1, 3]),((0xc0c0c0c0c0c0c0c * 2 ^ 64 + 0xc0c0c0c0c0c0c0c),1,[0, 3]),(((0x30303030 * 2 ^ 32 + 0x30303030) * 2 ^ 64 + (0x30303030 * 2 ^ 32 + 0x30303030)),1,[0, 3]),((0xcc00cc00cc00cc0 * 2 ^ 60 + 0xcc00cc00cc00cc),1,[0, 2]),(((0xff00ff00 * 2 ^ 32 + 0xff00ff00) * 2 ^ 64 + (0xff00ff00 * 2 ^ 32 + 0xff00ff00)),2,[0, 1, 2]),(((0x33003300 * 2 ^ 32 + 0x33003300) * 2 ^ 64 + (0x33003300 * 2 ^ 32 + 0x33003300)),1,[0, 2]),((0xa0a0a0a0a0a0a0a * 2 ^ 64 + 0xa0a0a0a0a0a0a0a),1,[1, 3]),(((0x50505050 * 2 ^ 32 + 0x50505050) * 2 ^ 64 + (0x50505050 * 2 ^ 32 + 0x50505050)),1,[1, 3]),((0xaa00aa00aa00aa0 * 2 ^ 60 + 0xaa00aa00aa00aa),1,[1, 2]),(((0x55005500 * 2 ^ 32 + 0x55005500) * 2 ^ 64 + (0x55005500 * 2 ^ 32 + 0x55005500)),1,[1, 2]),((0xf000f000f000f00 * 2 ^ 60 + 0xf000f000f000f0),1,[0, 1]),((0xf000f000f000f00 * 2 ^ 64 + 0xf000f000f000f00),1,[0, 1]),(((0x22222222 * 2 ^ 32 + 0x22222222) * 2 ^ 64 + (0x22222222 * 2 ^ 32 + 0x22222222)),1,[2, 3]),(((0x44444444 * 2 ^ 32 + 0x44444444) * 2 ^ 64 + (0x44444444 * 2 ^ 32 + 0x44444444)),1,[2, 3])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨p7_S0,p7_S1,p7_S2,p7_S3,p7_S4,p7_S5,p7_S6,p7_S7,p7_S8,p7_S9,p7_S10,p7_S11,p7_S12,p7_S13,p7_S14,p7_S15,p7_S16,p7_S17,p7_S18,p7_S19,p7_S20,p7_S21,p7_S22,p7_S23,p7_S24,p7_S25,by simp⟩
def p7_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(2,[(1,0,1)]),(3,[(1,0,1)]),(4,[]),(5,[]),(1,[(1,0,1)]),(3,[(1,0,2)]),(6,[]),(1,[(1,0,2)]),(2,[(1,0,2)]),(7,[]),(0,[(1,0,1)]),(8,[]),(9,[]),(3,[(1,1,2)]),(0,[(1,0,2)]),(2,[(1,1,2)]),(10,[]),(1,[(1,1,2)]),(0,[(1,1,2)]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(18,[]),(19,[]),(20,[]),(21,[]),(2,[(3,0,1)]),(0,[(3,0,1)]),(0,[(2,0,1)]),(1,[(2,0,1)]),(3,[(3,0,1)]),(0,[(3,0,2)]),(0,[(2,0,2)]),(1,[(2,0,2)]),(22,[]),(23,[]),(1,[(3,0,1)]),(24,[]),(25,[]),(2,[(2,0,1)]),(2,[(3,0,2)]),(0,[(3,1,2)]),(0,[(2,1,2)]),(2,[(2,0,2)]),(1,[(3,0,2)]),(3,[(2,0,1)]),(3,[(2,0,2)]),(3,[(2,1,2)]),(2,[(2,1,2)]),(3,[(3,1,2)]),(2,[(3,1,2)]),(1,[(3,1,2)]),(0,[(0,0,2)]),(1,[(2,1,2)]),(3,[(3,0,2)]),(3,[(1,0,1),(1,1,2)]),(3,[(1,0,1),(1,0,2)]),(2,[(1,0,2),(1,1,2)]),(2,[(1,0,1),(1,1,2)]),(2,[(1,0,1),(1,0,2)]),(0,[(0,1,2)]),(2,[(1,0,1),(3,2,3)]),(0,[(0,0,1)]),(1,[(1,0,2),(3,1,3)]),(1,[(1,0,2),(1,1,2)]),(1,[(1,0,1),(1,1,2)]),(1,[(1,0,1),(1,0,2)]),(0,[(1,1,2),(3,0,3)]),(0,[(1,0,2),(1,1,2)]),(0,[(1,0,1),(1,1,2)]),(0,[(1,0,1),(1,0,2)])]
def p7_P : List (Nat × Nat) := [(4,5),(2,3),(1,3),(1,5),(8,9),(1,9),(4,6),(2,6),(8,10),(2,10),(8,12),(4,12),(4,11),(7,8)]
def p7_K : List CutV := p7_C.map (mkCut p7_Z)
theorem p7_W : ∀ c ∈ p7_K, CutP p7_R p7_T c := cutsGood p7_Y (by decide +kernel)
theorem p7_Q : p7_P.all (sepOK p7_T) = true := by decide +kernel
noncomputable def p7_D6 : List StD := [
([w0,w1,w2,w3],[0,1,2,3],[0,1,2,3,4,5,6,7,8,9,10,11],[[0,1,100,101,102],[0,2,101,100,103],[0,3,100,104,105],[1,2,102,106,107],[1,3,102,108,109],[2,3,103,110,111]])]
noncomputable def p7_D5 : List StD := [
([w0,w1,w30,w2,w3],[0,1,4,5,6,2,7,3],[3,5,7,9,10,11],[[0,1],[1],[0,100,2],[0,101,3],[0],[1,102,2],[1,103,3],[2,4,5,6,100,104],[3,4,7,6,101,105],[3,2,100,104,105]]),
([w0,w1,w2,w31,w3],[0,8,2,9,10,1,7,3],[2,5,6,8,9,11],[[0,100,1],[0,2],[2],[0,101,3],[2,102,1],[4,1,5,6,100,103],[3,1,100,103,104],[0],[2,105,3],[3,4,7,6,101,104]]),
([w0,w1,w2,w3,w32],[0,11,12,3,13,1,7,2],[2,3,6,7,8,10],[[0,100,1],[0,101,2],[0,3],[3],[2,1,100,102,103],[3,104,1],[4,1,5,6,100,102],[3,105,2],[4,2,7,6,101,103],[0]]),
([w0,w1,w2,w33,w3],[1,14,2,15,0,16,17,3],[1,0,4,5,9,11],[[0,100,1],[2,101,1],[3,1,4,5,100,102],[6,1,100,102,103],[0,2],[2],[0,104,6],[0],[2,105,6],[6,3,7,5,104,103]]),
([w0,w1,w2,w3,w34],[1,18,19,3,20,0,16,2],[1,0,3,4,7,10],[[0,100,1],[2,1,100,101,102],[3,103,1],[4,1,5,6,100,101],[0,104,2],[0,3],[3],[3,105,2],[4,2,7,6,104,102],[0]]),
([w0,w1,w2,w3,w35],[21,22,2,3,23,0,24,1],[0,1,2,4,6,8],[[0,1,100,101,102],[2,100,1],[3,103,1],[4,1,5,6,100,101],[2,104,0],[3,105,0],[4,0,7,6,104,102],[2,3],[3],[2]])]
noncomputable def p7_D4 : List StD := [
([w1,w30,w2,w31,w3],[0,8,4,16,25,24,9,26,5],[11,9],[[0],[1,2],[1,2,3],[1,4],[2,1,5],[1,2],[6,4,100],[0],[2,7],[8,7,101]]),
([w1,w30,w2,w3,w32],[0,11,27,5,12,28,29,4],[10,7],[[0],[1,2],[1,3],[1,2],[4,2,100],[3,1,5],[1,2],[2,6],[7,6,101],[0]]),
([w0,w30,w2,w33,w3],[1,14,4,7,30,24,17,31,5],[11,5],[[0],[1,2],[1,2,3],[1,4],[2,1,5],[1,2],[6,4,100],[0],[2,7],[8,7,101]]),
([w0,w30,w2,w3,w34],[1,18,32,5,19,28,33,4],[10,3],[[0],[1,2],[1,3],[1,2],[4,2,100],[3,1,5],[1,2],[2,6],[7,6,101],[0]]),
([w0,w1,w2,w36,w3],[14,4,8,34,7,35,16,36,24,3],[],[[0,1,2],[0,2,1],[3],[0,4],[1,0,2],[5],[2,6],[7],[1,8],[9,4]]),
([w37,w0,w1,w2,w3],[0,4,34,14,3,25,24,36,37,30],[],[[0,1,2],[1,0],[3],[4,5,6],[7,1,8],[1,6],[7,9],[1,6],[8,5],[1,6]]),
([w0,w1,w2,w3,w38],[18,5,11,7,38,16,39,28,2,40],[],[[0,1,2],[0,3],[0,2,1],[4],[2,5],[1,0,2],[6],[1,7],[8,3],[9]]),
([w39,w0,w1,w2,w3],[0,5,38,2,32,28,18,40,41,27],[],[[0,1,2],[1,0],[3,4,5],[6],[7,1,4],[7,4],[1,5],[8,9],[1,5],[1,5]]),
([w1,w2,w31,w3,w32],[12,42,11,43,8,0,9],[8,6],[[0,1],[2,1,100],[1,3],[4,3,101],[5],[0,6],[0,1],[6,0,3],[0,1],[5]]),
([w0,w1,w31,w33,w3],[14,8,44,32,45,27,35,46],[9,5],[[0,1],[2],[0,1,3],[0,4],[1,0,5],[6],[1,7],[0,1],[5,4,100],[3,7,101]]),
([w40,w0,w1,w2,w3],[0,8,44,14,3,45,16,35,47,26],[],[[0,1,2],[3],[1,0],[4,5,6],[1,6],[7,1,5],[7,5],[1,6],[1,6],[8,9]]),
([w0,w1,w31,w3,w35],[22,32,2,9,21,33,8],[8,2],[[0,1],[2],[0,3],[0,1],[4,1,100],[1,5],[6,5,101],[3,0,5],[0,1],[2]]),
([w0,w1,w2,w3,w41],[22,32,12,9,48,24,28,1,49,50],[],[[0,1],[0,1],[0,2,3],[4],[2,5],[1,6],[7,1],[1,0,2],[8],[9]]),
([w42,w0,w1,w2,w3],[0,2,1,32,28,22,50,9,51,42],[],[[0,1],[2,3,4],[1,0],[5],[6,3],[6,3],[6,4,7],[8,9],[3,4],[3,4]]),
([w0,w1,w2,w32,w34],[18,11,45,52,46,39,19,12],[7,3],[[0,1],[0,2],[3],[0,1,2],[1,4],[1,0,4],[5],[6,2,100],[7,4,101],[0,1]]),
([w43,w0,w1,w2,w3],[0,11,52,18,2,45,46,16,53,29],[],[[0,1,2],[3],[4,5,6],[1,0],[1,7],[6,5],[6,1,5],[1,6],[1,6],[8,9]]),
([w0,w1,w2,w32,w35],[22,30,12,48,31,21,11,49],[6,2],[[0,1],[0,2],[3],[0,1],[1,4],[5,1,100],[6,4,101],[2,0,4],[7],[0,1]]),
([w44,w0,w1,w2,w3],[0,12,48,1,30,31,22,24,54,43],[],[[0,1,2],[3,4,5],[6],[1,0],[5,4],[1,7],[5,1,4],[1,5],[8,9],[1,5]]),
([w45,w0,w1,w2,w3],[8,14,35,3,31,45,30,46],[],[[0],[0,1,2],[1,0],[3,4,5],[1,6],[1,5],[1,5],[5,1,6],[5,7],[6,4]]),
([w0,w2,w33,w3,w34],[46,42,19,18,43,14,55,17,56],[4,0],[[0,1,2],[3,1,100],[0,4,1],[5,4,101],[6],[2,7],[2,0,1],[6,0,4],[2,1],[8]]),
([w0,w1,w33,w3,w35],[21,27,22,29,14,57,17,2],[4,1],[[0,1],[2,1,100],[1,3],[4,3,101],[5],[0,6],[0,1],[5,0,3],[0,1],[7]]),
([w0,w1,w2,w3,w46],[21,27,19,42,43,0,58,59,56],[],[[0,1],[2,3],[1,4],[5,1],[0,1],[0,2,3],[6],[1,0,2],[7],[8]]),
([w47,w0,w1,w2,w3],[0,27,43,2,60,1,19,61,42,29],[],[[0,1,2],[2,3,4],[3,1,5],[6],[7,1],[2,8],[1,2],[2,1,7],[7,2,8],[1,9]]),
([w48,w0,w1,w2,w3],[11,18,39,2,46,45,30,33,38],[],[[0],[0,1,2],[3,4,5],[1,0],[1,6],[1,5],[1,5],[5,4],[5,1,4],[6,7,8]]),
([w0,w1,w2,w34,w35],[21,25,26,22,18,19,58,59],[0,1],[[0,1],[1,2],[3,1,100],[4,2,101],[0,5],[6],[0,1],[5,0,2],[7],[0,1]]),
([w49,w0,w1,w2,w3],[0,25,42,19,21,59,43,26],[],[[0,1,2],[2,3],[4],[3,4],[5,1],[1,2],[2,6],[3,2],[2,1,5],[1,7]]),
([w50,w0,w1,w2,w3],[42,1,33,30,0,49,22,45,31,62],[],[[0],[1,2,3],[4,2,5],[3,6],[2,3],[2,7],[6,3],[3,8],[7,2,9],[3,2,8]]),
([w51,w0,w1,w2,w3],[0,26,25,42,35,21,59,57,29,46],[],[[0,1,2],[3],[4,5,6],[2,1],[1,2],[2,1],[7,8],[5,9],[1,2],[2,1]])]
noncomputable def p7_D3 : List StD := [
([w30,w31,w33,w3],[1,14,44,35,42,45,63,64,26],[12,9,5],[[0,1,2],[1,3],[4,5,100],[0,1],[6,5,101],[7,8,102]]),
([w30,w2,w32,w34],[65,45,1,18,52,66,67,46],[13,7,3],[[0,1,100],[2,3,4],[3,1],[5,1,101],[6,7,102],[2,1,3]]),
([w52,w0,w1,w2],[0,45,46,50,26,68,69,25],[],[[0,1],[1,2],[3,4,5],[4,6,7],[2,1],[1,2]]),
([w53,w0,w1,w3],[0,25,26,36,46,70,71,45],[],[[0,1,2],[3,4,5],[2,1],[2,1],[4,6,7],[2,1]]),
([w1,w31,w32,w35],[72,42,73,30,74,2,0],[13,6,2],[[0,1,100],[2,3,101],[4,1,102],[5,1],[6,3],[5,1]]),
([w54,w0,w2,w3],[0,30,45,46,75,26],[],[[0,1],[1,2,3],[3,2],[3,2],[3,1],[1,4,5]]),
([w0,w33,w34,w35],[76,26,77,25,78,2,1],[13,0,1],[[0,1,100],[2,3,101],[4,1,102],[5,1],[6,3],[5,1]]),
([w55,w1,w2,w3],[0,25,26,46,45],[],[[0,1],[0,2],[0,3,4],[4,3],[2,1],[1,2]])]
def p7_D2 : List StD := []
theorem p7_I2 : LevelN p7_R p7_T 2 p7_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C3x0 : levelOK p7_T p7_K p7_P 2 (p7_D2.map Prod.fst) ((p7_D3.drop (0*16)).take 16) = true := by decide +kernel
theorem p7_I3 : LevelN p7_R p7_T 3 p7_D3 := levelStep p7_B p7_W p7_Q p7_I2 (chunks 16 p7_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C3x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C4x0 : levelOK p7_T p7_K p7_P 3 (p7_D3.map Prod.fst) ((p7_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C4x1 : levelOK p7_T p7_K p7_P 3 (p7_D3.map Prod.fst) ((p7_D4.drop (1*16)).take 16) = true := by decide +kernel
theorem p7_I4 : LevelN p7_R p7_T 4 p7_D4 := levelStep p7_B p7_W p7_Q p7_I3 (chunks 16 p7_D4 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C4x0
  · exact p7_C4x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C5x0 : levelOK p7_T p7_K p7_P 4 (p7_D4.map Prod.fst) ((p7_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem p7_I5 : LevelN p7_R p7_T 5 p7_D5 := levelStep p7_B p7_W p7_Q p7_I4 (chunks 16 p7_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C5x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p7_C6x0 : levelOK p7_T p7_K p7_P 5 (p7_D5.map Prod.fst) ((p7_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem p7_I6 : LevelN p7_R p7_T 6 p7_D6 := levelStep p7_B p7_W p7_Q p7_I5 (chunks 16 p7_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C6x0
  ))
theorem p7_L : LowN p7_R p7_T 7 := lowSearch p7_B p7_I6 (by decide +kernel)

def p8_T : Nat := ((0xe8a8e8a8 * 2 ^ 32 + 0xe8a8e8a8) * 2 ^ 64 + (0xe8a8e8a8 * 2 ^ 32 + 0xe8a8e8a8))
def p8_R : List Nat := [0, 1, 2, 3]
def p8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,6,14)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
theorem p8_S0 : SliceN p8_R p8_T (((0xff00ff00 * 2 ^ 32 + 0xff00ff00) * 2 ^ 64 + (0xff00ff00 * 2 ^ 32 + 0xff00ff00)),4,[0, 1, 2]) := mkSlice (w:=8) p8_B p3_B p3_L (by decide +kernel)
def p8_Z : List SliceD := [(((0xff00ff00 * 2 ^ 32 + 0xff00ff00) * 2 ^ 64 + (0xff00ff00 * 2 ^ 32 + 0xff00ff00)),4,[0, 1, 2])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨p8_S0,by simp⟩
def p8_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p8_P : List (Nat × Nat) := []
def p8_K : List CutV := p8_C.map (mkCut p8_Z)
theorem p8_W : ∀ c ∈ p8_K, CutP p8_R p8_T c := cutsGood p8_Y (by decide +kernel)
theorem p8_Q : p8_P.all (sepOK p8_T) = true := by decide +kernel
noncomputable def p8_D4 : List StD := [
([w0,w1,w2,w3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def p8_D3 : List StD := []
theorem p8_I3 : LevelN p8_R p8_T 3 p8_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p8_C4x0 : levelOK p8_T p8_K p8_P 3 (p8_D3.map Prod.fst) ((p8_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem p8_I4 : LevelN p8_R p8_T 4 p8_D4 := levelStep p8_B p8_W p8_Q p8_I3 (chunks 16 p8_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C4x0
  ))
theorem p8_L : LowN p8_R p8_T 5 := lowSearch p8_B p8_I4 (by decide +kernel)

def p9_T : Nat := ((0xfeeafeea * 2 ^ 32 + 0xfeeafeea) * 2 ^ 64 + (0xfeeafeea * 2 ^ 32 + 0xfeeafeea))
def p9_R : List Nat := [0, 1, 2, 3]
def p9_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
theorem p9_S0 : SliceN p9_R p9_T (((0x55555555 * 2 ^ 32 + 0x55555555) * 2 ^ 64 + (0x55555555 * 2 ^ 32 + 0x55555555)),4,[1, 2, 3]) := mkSlice (w:=0) p9_B p3_B p3_L (by decide +kernel)
def p9_Z : List SliceD := [(((0x55555555 * 2 ^ 32 + 0x55555555) * 2 ^ 64 + (0x55555555 * 2 ^ 32 + 0x55555555)),4,[1, 2, 3])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨p9_S0,by simp⟩
def p9_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[])]
def p9_P : List (Nat × Nat) := []
def p9_K : List CutV := p9_C.map (mkCut p9_Z)
theorem p9_W : ∀ c ∈ p9_K, CutP p9_R p9_T c := cutsGood p9_Y (by decide +kernel)
theorem p9_Q : p9_P.all (sepOK p9_T) = true := by decide +kernel
noncomputable def p9_D4 : List StD := [
([w0,w1,w2,w3],[0],[],[[0],[0],[0],[0],[0],[0]])]
def p9_D3 : List StD := []
theorem p9_I3 : LevelN p9_R p9_T 3 p9_D3 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p9_C4x0 : levelOK p9_T p9_K p9_P 3 (p9_D3.map Prod.fst) ((p9_D4.drop (0*16)).take 16) = true := by decide +kernel
theorem p9_I4 : LevelN p9_R p9_T 4 p9_D4 := levelStep p9_B p9_W p9_Q p9_I3 (chunks 16 p9_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C4x0
  ))
theorem p9_L : LowN p9_R p9_T 5 := lowSearch p9_B p9_I4 (by decide +kernel)

def p10_T : Nat := ((0xeaeaeaea * 2 ^ 32 + 0xeaeaeaea) * 2 ^ 64 + (0xeaeaeaea * 2 ^ 32 + 0xeaeaeaea))
def p10_R : List Nat := [0, 1, 2]
def p10_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
theorem p10_L : LowN p10_R p10_T 2 := lowCount p10_B (by decide +kernel)

def p11_T : Nat := ((0xa8a8a8a8 * 2 ^ 32 + 0xa8a8a8a8) * 2 ^ 64 + (0xa8a8a8a8 * 2 ^ 32 + 0xa8a8a8a8))
def p11_R : List Nat := [0, 1, 2]
def p11_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
theorem p11_L : LowN p11_R p11_T 2 := lowCount p11_B (by decide +kernel)

def p12_T : Nat := ((0xeaa8eaa8 * 2 ^ 32 + 0xeaa8eaa8) * 2 ^ 64 + (0xeaa8eaa8 * 2 ^ 32 + 0xeaa8eaa8))
def p12_R : List Nat := [0, 1, 2, 3]
def p12_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
theorem p12_S0 : SliceN p12_R p12_T (((0xcccccccc * 2 ^ 32 + 0xcccccccc) * 2 ^ 64 + (0xcccccccc * 2 ^ 32 + 0xcccccccc)),2,[0, 2, 3]) := mkSlice (w:=2) p12_B p10_B p10_L (by decide +kernel)
theorem p12_S1 : SliceN p12_R p12_T (((0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa) * 2 ^ 64 + (0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa)),2,[1, 2, 3]) := mkSlice (w:=1) p12_B p6_B p6_L (by decide +kernel)
theorem p12_S2 : SliceN p12_R p12_T (((0x55555555 * 2 ^ 32 + 0x55555555) * 2 ^ 64 + (0x55555555 * 2 ^ 32 + 0x55555555)),2,[1, 2, 3]) := mkSlice (w:=0) p12_B p4_B p4_L (by decide +kernel)
theorem p12_S3 : SliceN p12_R p12_T (((0x33333333 * 2 ^ 32 + 0x33333333) * 2 ^ 64 + (0x33333333 * 2 ^ 32 + 0x33333333)),2,[0, 2, 3]) := mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel)
theorem p12_S4 : SliceN p12_R p12_T (((0x22222222 * 2 ^ 32 + 0x22222222) * 2 ^ 64 + (0x22222222 * 2 ^ 32 + 0x22222222)),1,[2, 3]) := mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel)
theorem p12_S5 : SliceN p12_R p12_T (((0x44444444 * 2 ^ 32 + 0x44444444) * 2 ^ 64 + (0x44444444 * 2 ^ 32 + 0x44444444)),1,[2, 3]) := mkSlice (w:=2) p12_B p1_B p1_L (by decide +kernel)
theorem p12_S6 : SliceN p12_R p12_T ((0x303030303030303 * 2 ^ 64 + 0x303030303030303),1,[0, 3]) := mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel)
theorem p12_S7 : SliceN p12_R p12_T (((0x50505050 * 2 ^ 32 + 0x50505050) * 2 ^ 64 + (0x50505050 * 2 ^ 32 + 0x50505050)),1,[1, 3]) := mkSlice (w:=4) p12_B p1_B p1_L (by decide +kernel)
theorem p12_S8 : SliceN p12_R p12_T ((0xa0a0a0a0a0a0a0a * 2 ^ 64 + 0xa0a0a0a0a0a0a0a),1,[1, 3]) := mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel)
theorem p12_S9 : SliceN p12_R p12_T (((0xc0c0c0c0 * 2 ^ 32 + 0xc0c0c0c0) * 2 ^ 64 + (0xc0c0c0c0 * 2 ^ 32 + 0xc0c0c0c0)),1,[0, 3]) := mkSlice (w:=6) p12_B p2_B p2_L (by decide +kernel)
theorem p12_S10 : SliceN p12_R p12_T (((0x55005500 * 2 ^ 32 + 0x55005500) * 2 ^ 64 + (0x55005500 * 2 ^ 32 + 0x55005500)),1,[1, 2]) := mkSlice (w:=8) p12_B p1_B p1_L (by decide +kernel)
theorem p12_S11 : SliceN p12_R p12_T ((0xf0f0f0f0f0f0f0f * 2 ^ 64 + 0xf0f0f0f0f0f0f0f),2,[0, 1, 3]) := mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel)
theorem p12_S12 : SliceN p12_R p12_T (((0xff00ff00 * 2 ^ 32 + 0xff00ff00) * 2 ^ 64 + (0xff00ff00 * 2 ^ 32 + 0xff00ff00)),2,[0, 1, 2]) := mkSlice (w:=8) p12_B p10_B p10_L (by decide +kernel)
theorem p12_S13 : SliceN p12_R p12_T ((0xaa00aa00aa00aa0 * 2 ^ 60 + 0xaa00aa00aa00aa),1,[1, 2]) := mkSlice (w:=1) p12_B p2_B p2_L (by decide +kernel)
theorem p12_S14 : SliceN p12_R p12_T ((0xff00ff00ff00ff0 * 2 ^ 60 + 0xff00ff00ff00ff),2,[0, 1, 2]) := mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel)
theorem p12_S15 : SliceN p12_R p12_T ((0x330033003300330 * 2 ^ 60 + 0x33003300330033),1,[0, 2]) := mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel)
theorem p12_S16 : SliceN p12_R p12_T (((0xcc00cc00 * 2 ^ 32 + 0xcc00cc00) * 2 ^ 64 + (0xcc00cc00 * 2 ^ 32 + 0xcc00cc00)),1,[0, 2]) := mkSlice (w:=10) p12_B p2_B p2_L (by decide +kernel)
theorem p12_S17 : SliceN p12_R p12_T (((0xf000f000 * 2 ^ 32 + 0xf000f000) * 2 ^ 64 + (0xf000f000 * 2 ^ 32 + 0xf000f000)),1,[0, 1]) := mkSlice (w:=12) p12_B p2_B p2_L (by decide +kernel)
theorem p12_S18 : SliceN p12_R p12_T ((0xf000f000f000f0 * 2 ^ 60 + 0xf000f000f000f),1,[0, 1]) := mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel)
def p12_Z : List SliceD := [(((0xcccccccc * 2 ^ 32 + 0xcccccccc) * 2 ^ 64 + (0xcccccccc * 2 ^ 32 + 0xcccccccc)),2,[0, 2, 3]),(((0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa) * 2 ^ 64 + (0xaaaaaaaa * 2 ^ 32 + 0xaaaaaaaa)),2,[1, 2, 3]),(((0x55555555 * 2 ^ 32 + 0x55555555) * 2 ^ 64 + (0x55555555 * 2 ^ 32 + 0x55555555)),2,[1, 2, 3]),(((0x33333333 * 2 ^ 32 + 0x33333333) * 2 ^ 64 + (0x33333333 * 2 ^ 32 + 0x33333333)),2,[0, 2, 3]),(((0x22222222 * 2 ^ 32 + 0x22222222) * 2 ^ 64 + (0x22222222 * 2 ^ 32 + 0x22222222)),1,[2, 3]),(((0x44444444 * 2 ^ 32 + 0x44444444) * 2 ^ 64 + (0x44444444 * 2 ^ 32 + 0x44444444)),1,[2, 3]),((0x303030303030303 * 2 ^ 64 + 0x303030303030303),1,[0, 3]),(((0x50505050 * 2 ^ 32 + 0x50505050) * 2 ^ 64 + (0x50505050 * 2 ^ 32 + 0x50505050)),1,[1, 3]),((0xa0a0a0a0a0a0a0a * 2 ^ 64 + 0xa0a0a0a0a0a0a0a),1,[1, 3]),(((0xc0c0c0c0 * 2 ^ 32 + 0xc0c0c0c0) * 2 ^ 64 + (0xc0c0c0c0 * 2 ^ 32 + 0xc0c0c0c0)),1,[0, 3]),(((0x55005500 * 2 ^ 32 + 0x55005500) * 2 ^ 64 + (0x55005500 * 2 ^ 32 + 0x55005500)),1,[1, 2]),((0xf0f0f0f0f0f0f0f * 2 ^ 64 + 0xf0f0f0f0f0f0f0f),2,[0, 1, 3]),(((0xff00ff00 * 2 ^ 32 + 0xff00ff00) * 2 ^ 64 + (0xff00ff00 * 2 ^ 32 + 0xff00ff00)),2,[0, 1, 2]),((0xaa00aa00aa00aa0 * 2 ^ 60 + 0xaa00aa00aa00aa),1,[1, 2]),((0xff00ff00ff00ff0 * 2 ^ 60 + 0xff00ff00ff00ff),2,[0, 1, 2]),((0x330033003300330 * 2 ^ 60 + 0x33003300330033),1,[0, 2]),(((0xcc00cc00 * 2 ^ 32 + 0xcc00cc00) * 2 ^ 64 + (0xcc00cc00 * 2 ^ 32 + 0xcc00cc00)),1,[0, 2]),(((0xf000f000 * 2 ^ 32 + 0xf000f000) * 2 ^ 64 + (0xf000f000 * 2 ^ 32 + 0xf000f000)),1,[0, 1]),((0xf000f000f000f0 * 2 ^ 60 + 0xf000f000f000f),1,[0, 1])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨p12_S0,p12_S1,p12_S2,p12_S3,p12_S4,p12_S5,p12_S6,p12_S7,p12_S8,p12_S9,p12_S10,p12_S11,p12_S12,p12_S13,p12_S14,p12_S15,p12_S16,p12_S17,p12_S18,by simp⟩
def p12_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(10,[]),(11,[]),(12,[]),(13,[]),(14,[]),(15,[]),(16,[]),(17,[]),(18,[])]
def p12_P : List (Nat × Nat) := [(4,5),(12,14),(2,3),(1,3),(10,14),(1,5),(6,14),(8,9),(1,9),(5,6),(0,3),(3,6),(0,5),(3,10),(0,9),(1,7),(1,11),(1,13)]
def p12_K : List CutV := p12_C.map (mkCut p12_Z)
theorem p12_W : ∀ c ∈ p12_K, CutP p12_R p12_T c := cutsGood p12_Y (by decide +kernel)
theorem p12_Q : p12_P.all (sepOK p12_T) = true := by decide +kernel
noncomputable def p12_D5 : List StD := [
([w0,w1,w2,w3],[],[0,1,2,3,4,5,6,7,8],[[100,101,102,103],[102,104,100,105],[100,106,107,108],[103,105,101,104],[103,108,101,106],[105,108,104,106]])]
noncomputable def p12_D4 : List StD := [
([w4,w0,w1,w2,w3],[0,1,2,3,4,5,6,7],[9],[[0],[1],[2],[2],[100,2,3],[2,4],[2,4],[3,5],[3,5],[6,7]]),
([w0,w1,w30,w2,w3],[0,1,3,5,2,4,8,9],[9],[[100,0,1],[2],[3,1],[3,1],[4],[5,0],[5,0],[0],[0],[6,7]]),
([w56,w0,w1,w2,w3],[3,1,2,4,0,9,10],[10,5],[[0],[1],[2,3],[2,3],[2,4,100],[2,3],[2,3],[3,4],[3,4],[101,5,6]]),
([w57,w0,w1,w2,w3],[0,2,4,5,3,1,8],[10,6],[[0],[1],[2,3],[2,3],[4,5,100],[3,2],[3,2],[2,3],[2,3],[6,101]]),
([w5,w0,w1,w2,w3],[9,2,4,8,11,5,7,6],[11],[[0],[1],[2],[1],[1,3],[100,1,4],[1,3],[3,5,6],[7,5],[3,6]]),
([w0,w1,w2,w31,w3],[7,8,9,4,6,2],[11],[[0,1],[100,2,3],[4],[0,1],[1,0],[0],[3,2],[5],[1,0],[0]]),
([w58,w0,w1,w2,w3],[6,2,8,4,9,7,10],[12,3],[[0],[1,2],[3],[1,2],[1,2],[1,4,100],[1,2],[2,5],[101,4,6],[2,4]]),
([w59,w0,w1,w2,w3],[9,8,7,2,6,4],[12,6],[[0],[1,2],[3],[1,2],[2,1],[4,5,100],[2,1],[1,2],[4,101],[1,2]]),
([w6,w0,w1,w2,w3],[12,2,4,13,14,15,7,5,10],[13],[[0],[1],[1],[2],[1,3],[1,3],[100,1,4],[5,6,7],[3,7,8],[3,6,8]]),
([w0,w1,w2,w3,w32],[10,8,4,12,14,16,13,2],[13],[[0,1],[0,2],[100,3,1],[4],[1,5,2],[2,0,6],[0],[1,0,6],[0],[7]]),
([w60,w0,w1,w2,w3],[14,2,13,4,12,7],[14,3],[[0],[1,2],[1,2],[3],[1,2],[1,2],[1,4,100],[101,5],[2,4],[2,4]]),
([w61,w0,w1,w2,w3],[12,14,10,2,13,4],[14,4],[[0],[1,2],[1,2],[3],[2,4],[2,4],[1,5,100],[5,101],[1,2],[1,2]]),
([w0,w7,w1,w2,w3],[6,9,15,4,7,16,8],[14],[[0,1],[0,1],[0,1],[2,3,100],[4],[5],[0,1],[2,6],[0,1],[0,1]]),
([w0,w1,w2,w33,w3],[7,16,6,9,8,4],[2],[[0,1,2],[2,3],[2,1],[0,1,100],[0,1],[4],[2,3],[5],[2,0],[2,0]]),
([w62,w0,w1,w2,w3],[9,8,16,7,6,4],[2,15],[[0,100],[1],[2],[0],[3,0,4],[4,0],[3,5],[5,3,101],[4,0],[4,0]]),
([w63,w0,w1,w2,w3],[6,7,4,16,9,5,8],[0,15],[[0,100],[1],[2],[0],[0,3],[0,4],[5,3,6],[6,3,101],[0,4],[0,3,4]]),
([w0,w8,w1,w2,w3],[6,16,4,14,10,9],[12],[[0,1],[0,1],[0,2,100],[3,1],[4],[2,1],[5],[2,1],[0,3],[0,1,3]]),
([w0,w1,w2,w3,w34],[10,16,15,9,14,4],[2],[[0,1,2],[0,3,100],[2,1],[2,1],[2,1],[0,3],[4],[2,0],[2,0],[5]]),
([w64,w0,w1,w2,w3],[16,14,9,10,15,4],[2,16],[[0,100],[1],[0],[2],[3,0,4],[3,5],[4,0],[4,0],[5,3,101],[4,0]]),
([w65,w0,w1,w2,w3],[9,10,16,4,15,5,13],[7,16],[[0,100],[1],[2],[3],[4,0],[5,0,6],[4,2],[4,2],[6,0,101],[4,0,2]]),
([w0,w1,w9,w2,w3],[15,13,17,6,8,16,9],[10],[[0,1,100],[0,2],[3,1,2],[0,2],[1,2],[0,2,4],[1,2],[5],[6],[3,0]]),
([w0,w1,w2,w3,w35],[10,16,9,18,17,13,6],[10],[[0,1,100],[0,2,3],[3,1],[3,1],[3,1,4],[3,0],[3,0],[0,2],[5],[6]]),
([w66,w0,w1,w2,w3],[16,10,13,9,6,17,18],[0,17],[[0,100],[1],[2],[3],[1,0,4],[1,5,4],[6,0],[6,0,5],[4,1,6],[4,0,101]]),
([w67,w0,w1,w2,w3],[17,16,6,15,13,9,18],[7,17],[[0,100],[0],[1],[2],[3,4,5],[6,0],[3,0],[3,0,6],[4,0],[3,5,101]])]
noncomputable def p12_D3 : List StD := [
([w0,w1,w68,w3],[2,9,6,17,15,18],[],[[0,1,2],[0,1,2],[0,3,4],[4,3,5],[2,1],[2,1]]),
([w11,w0,w1,w3],[2,13,17,18,16,8,10],[],[[0,1],[1,2,3],[1,4],[0,5],[0,5],[3,6]]),
([w0,w1,w2,w69],[2,16,15,17,6,18],[],[[0,1,2],[0,3,4],[0,1,2],[2,1],[4,3,5],[2,1]]),
([w13,w0,w1,w2],[2,16,18,17,6,10,15,13,5],[],[[0,1,2],[2,3,4],[4,5,6],[0,7],[0,7],[2,8,6]]),
([w0,w1,w70,w3],[6,13,16,2,5,18,17],[],[[0,1,2],[0,1,3],[4,2,5],[5,2,6],[0,4],[0,2,1]]),
([w37,w0,w1,w3],[2,13,17,18,16,7,8],[],[[0,1],[2,0,3],[1,4],[5,1],[5,2,6],[1,2]]),
([w0,w1,w71,w2],[15,13,16,18,5,17],[],[[0,1,2],[0,2],[3,1,4],[1,4,5],[0,2],[0,2]]),
([w39,w0,w1,w2],[2,8,17,18,13,16,10],[],[[0,1],[2,0,3],[1,4,5],[6,1],[6,2,4],[1,2]]),
([w0,w72,w2,w3],[2,13,9,18,16,17,8],[],[[0,1],[0,2,3],[0,4,3],[1,4,5],[1,2,5],[6,2]]),
([w14,w0,w2,w3],[2,16,8,17,13,4,10,15],[],[[0,1,2],[2,1,3],[4,3],[0,5],[0,2],[2,6,7]]),
([w0,w1,w2,w73],[2,8,17,18,10,13],[],[[0,1],[0,2,3],[0,1],[1,2],[3,2],[1,4,5]]),
([w16,w0,w1,w2],[2,8,13,10,5,15],[],[[0,1],[2,3],[1,3,2],[0,1],[0,2],[1,4,5]]),
([w0,w74,w2,w3],[2,8,6,13,17,15,9],[],[[0,1],[2,3,4],[5,1,4],[1,0],[2,4,3],[1,6]]),
([w40,w0,w2,w3],[2,13,8,10,5,9],[],[[0,1],[2,0],[1,3],[4,1],[4,2],[1,5,2]]),
([w0,w1,w2,w75],[15,13,9,18,8,2,17],[],[[0,1,2],[3,1,2],[0,4,5],[0,6,3],[1,2,6],[0,2,4]]),
([w42,w0,w1,w2],[2,8,10,9,13,17],[],[[0,1],[2,3,4],[1,0],[2,1],[2,3,4],[1,5]]),
([w0,w76,w2,w3],[2,9,13,16,18,17],[],[[0,1,2],[0,1,2],[0,3,4],[4,3,5],[2,1,5],[2,1,3]]),
([w17,w0,w2,w3],[2,13,18,17,4,10],[],[[0,1],[2,3],[1,3],[0,1],[0,4],[1,5]]),
([w0,w1,w77,w3],[2,13,17,18,10],[],[[0,1],[0,1],[0,2,3],[3,2],[1,2],[1,4]]),
([w18,w0,w1,w3],[2,17,18,16,4,13,8,10],[],[[0,1,2],[2,3,4],[4,3],[0,5],[0,6],[2,7]]),
([w0,w78,w2,w3],[2,18,10,17,13,15],[],[[0,1],[2,3,4],[5,3],[1,3],[1,0],[4,2]]),
([w43,w0,w2,w3],[2,13,18,17,10,5,8],[],[[0,1],[2,3],[1,0],[4,1],[5,3,6],[1,4]]),
([w0,w1,w79,w3],[10,8,17,18,13],[],[[0,1],[0,2,3],[3,1,2],[1,2],[3,0],[1,0,4]]),
([w44,w0,w1,w3],[2,13,17,8,10,7],[],[[0,1],[2,3],[1,0],[4,1],[5,2,3],[1,2]]),
([w0,w7,w33,w3],[18,9,6,17],[15],[[0,1],[2,1],[0,3],[100],[2,1],[0,1,2]]),
([w0,w1,w2,w80],[10,9,6,2,17,8,15,16],[],[[0,1,2],[0,1,2],[3,4,5],[6,4,7],[2,0,1],[2,0,1]]),
([w0,w1,w2,w81],[15,9,6,17,18],[],[[0,1],[2,1],[0,3],[0,3,4],[2,1],[0,1,2]]),
([w0,w1,w2,w82],[10,9,6,2,17,18],[],[[0,1,2],[0,1,2],[3,4,5],[5,4],[2,0,1],[2,0,1]]),
([w0,w1,w83,w2],[6,9,2,8,16,15],[],[[0,1],[2,3],[0,1],[0,1],[3,4,5],[0,1]]),
([w0,w8,w2,w34],[6,16,9,15],[16],[[0,1],[0,2],[3,1],[3,1],[100],[0,1,3]]),
([w0,w1,w84,w3],[15,9,2,6,16],[],[[0,1],[2,1,3],[0,4],[0,4],[3,1],[0,1,3]]),
([w0,w1,w85,w3],[6,16,17,15,18],[],[[0,1],[0,2],[3,1],[3,1],[0,2,4],[0,1,3]]),
([w0,w1,w86,w3],[15,16,2,17,18],[],[[0,1],[2,3,4],[0,1],[0,1],[4,3],[0,1]]),
([w0,w87,w1,w3],[2,9,18,15,16,6],[],[[0,1,2],[3,1],[2,4],[2,4,3],[3,1,4],[2,1,5]]),
([w0,w1,w9,w35],[15,16,17,18],[17],[[0,1],[0,2],[3,1],[3,1,2],[0,2,3],[100]]),
([w0,w88,w2,w3],[2,16,6,17,18,9],[],[[0,1,2],[2,3],[4,1],[4,1,3],[2,3,4],[2,1,5]]),
([w0,w89,w2,w3],[2,16,6,17,18,15],[],[[0,1,2],[2,3],[4,1],[4,1,3],[2,3,4],[2,1,5]]),
([w0,w90,w2,w3],[2,16,15,18,17],[],[[0,1,2],[3,4],[2,1],[2,1],[3,4],[2,1]]),
([w0,w91,w2,w3],[2,9,15,18,17,6],[],[[0,1,2],[3,1],[2,4],[2,4,3],[3,1,4],[2,1,5]])]
def p12_D2 : List StD := []
theorem p12_I2 : LevelN p12_R p12_T 2 p12_D2 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C3x0 : levelOK p12_T p12_K p12_P 2 (p12_D2.map Prod.fst) ((p12_D3.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C3x1 : levelOK p12_T p12_K p12_P 2 (p12_D2.map Prod.fst) ((p12_D3.drop (1*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C3x2 : levelOK p12_T p12_K p12_P 2 (p12_D2.map Prod.fst) ((p12_D3.drop (2*16)).take 16) = true := by decide +kernel
theorem p12_I3 : LevelN p12_R p12_T 3 p12_D3 := levelStep p12_B p12_W p12_Q p12_I2 (chunks 16 p12_D3 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C3x0
  · exact p12_C3x1
  · exact p12_C3x2
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C4x0 : levelOK p12_T p12_K p12_P 3 (p12_D3.map Prod.fst) ((p12_D4.drop (0*16)).take 16) = true := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C4x1 : levelOK p12_T p12_K p12_P 3 (p12_D3.map Prod.fst) ((p12_D4.drop (1*16)).take 16) = true := by decide +kernel
theorem p12_I4 : LevelN p12_R p12_T 4 p12_D4 := levelStep p12_B p12_W p12_Q p12_I3 (chunks 16 p12_D4 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C4x0
  · exact p12_C4x1
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p12_C5x0 : levelOK p12_T p12_K p12_P 4 (p12_D4.map Prod.fst) ((p12_D5.drop (0*16)).take 16) = true := by decide +kernel
theorem p12_I5 : LevelN p12_R p12_T 5 p12_D5 := levelStep p12_B p12_W p12_Q p12_I4 (chunks 16 p12_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C5x0
  ))
theorem p12_L : LowN p12_R p12_T 6 := lowSearch p12_B p12_I5 (by decide +kernel)

def p13_T : Nat := ((0xfee8eaa8 * 2 ^ 32 + 0xfee8eaa8) * 2 ^ 64 + (0xfee8eaa8 * 2 ^ 32 + 0xfee8eaa8))
def p13_R : List Nat := [0, 1, 2, 3, 4]
def p13_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,6,22)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
theorem p13_S0 : SliceN p13_R p13_T (((0x55555555 * 2 ^ 32 + 0x55555555) * 2 ^ 64 + (0x55555555 * 2 ^ 32 + 0x55555555)),7,[1, 2, 3, 4]) := mkSlice (w:=0) p13_B p5_B p5_L (by decide +kernel)
theorem p13_S1 : SliceN p13_R p13_T (((0xffff0000 * 2 ^ 32 + 0xffff0000) * 2 ^ 64 + (0xffff0000 * 2 ^ 32 + 0xffff0000)),7,[0, 1, 2, 3]) := mkSlice (w:=16) p13_B p7_B p7_L (by decide +kernel)
theorem p13_S2 : SliceN p13_R p13_T (((0x33333333 * 2 ^ 32 + 0x33333333) * 2 ^ 64 + (0x33333333 * 2 ^ 32 + 0x33333333)),5,[0, 2, 3, 4]) := mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S3 : SliceN p13_R p13_T ((0xf0f0f0f0f0f0f0f * 2 ^ 64 + 0xf0f0f0f0f0f0f0f),5,[0, 1, 3, 4]) := mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S4 : SliceN p13_R p13_T (((0xff00ff00 * 2 ^ 32 + 0xff00ff00) * 2 ^ 64 + (0xff00ff00 * 2 ^ 32 + 0xff00ff00)),5,[0, 1, 2, 4]) := mkSlice (w:=8) p13_B p9_B p9_L (by decide +kernel)
theorem p13_S5 : SliceN p13_R p13_T ((0xff00ff00ff00ff0 * 2 ^ 60 + 0xff00ff00ff00ff),5,[0, 1, 2, 4]) := mkSlice (w:=0) p13_B p8_B p8_L (by decide +kernel)
theorem p13_S6 : SliceN p13_R p13_T ((0xffff0000ffff00 * 2 ^ 56 + 0xffff0000ffff),6,[0, 1, 2, 3]) := mkSlice (w:=0) p13_B p12_B p12_L (by decide +kernel)
theorem p13_S7 : SliceN p13_R p13_T (((0xcccccccc * 2 ^ 32 + 0xcccccccc) * 2 ^ 64 + (0xcccccccc * 2 ^ 32 + 0xcccccccc)),5,[0, 2, 3, 4]) := mkSlice (w:=2) p13_B p9_B p9_L (by decide +kernel)
theorem p13_S8 : SliceN p13_R p13_T (((0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0) * 2 ^ 64 + (0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0)),5,[0, 1, 3, 4]) := mkSlice (w:=4) p13_B p9_B p9_L (by decide +kernel)
def p13_Z : List SliceD := [(((0x55555555 * 2 ^ 32 + 0x55555555) * 2 ^ 64 + (0x55555555 * 2 ^ 32 + 0x55555555)),7,[1, 2, 3, 4]),(((0xffff0000 * 2 ^ 32 + 0xffff0000) * 2 ^ 64 + (0xffff0000 * 2 ^ 32 + 0xffff0000)),7,[0, 1, 2, 3]),(((0x33333333 * 2 ^ 32 + 0x33333333) * 2 ^ 64 + (0x33333333 * 2 ^ 32 + 0x33333333)),5,[0, 2, 3, 4]),((0xf0f0f0f0f0f0f0f * 2 ^ 64 + 0xf0f0f0f0f0f0f0f),5,[0, 1, 3, 4]),(((0xff00ff00 * 2 ^ 32 + 0xff00ff00) * 2 ^ 64 + (0xff00ff00 * 2 ^ 32 + 0xff00ff00)),5,[0, 1, 2, 4]),((0xff00ff00ff00ff0 * 2 ^ 60 + 0xff00ff00ff00ff),5,[0, 1, 2, 4]),((0xffff0000ffff00 * 2 ^ 56 + 0xffff0000ffff),6,[0, 1, 2, 3]),(((0xcccccccc * 2 ^ 32 + 0xcccccccc) * 2 ^ 64 + (0xcccccccc * 2 ^ 32 + 0xcccccccc)),5,[0, 2, 3, 4]),(((0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0) * 2 ^ 64 + (0xf0f0f0f0 * 2 ^ 32 + 0xf0f0f0f0)),5,[0, 1, 3, 4])]
theorem p13_Y : ∀ s ∈ p13_Z, SliceN p13_R p13_T s := by
  unfold p13_Z
  simp only [List.forall_mem_cons]
  exact ⟨p13_S0,p13_S1,p13_S2,p13_S3,p13_S4,p13_S5,p13_S6,p13_S7,p13_S8,by simp⟩
def p13_C : List (Nat × List (Nat × Nat × Nat)) := [(0,[]),(1,[]),(0,[(0,0,1)]),(2,[]),(3,[]),(1,[(0,1,2)]),(0,[(2,0,1)]),(0,[(3,0,1)]),(4,[]),(5,[]),(6,[]),(0,[(1,0,1)]),(7,[]),(8,[]),(1,[(1,1,2)]),(1,[(2,1,2)]),(1,[(3,1,2)]),(0,[(0,0,2)]),(1,[(0,1,3)]),(0,[(2,0,2)]),(0,[(1,0,2)]),(1,[(1,1,3)]),(0,[(3,0,2)]),(1,[(2,1,3)]),(1,[(3,1,3)]),(0,[(0,1,2)]),(1,[(0,2,3)]),(0,[(2,1,2)]),(0,[(1,1,2)]),(1,[(1,2,3)]),(0,[(3,1,2)]),(1,[(2,2,3)]),(1,[(3,2,3)]),(0,[(1,0,1),(0,0,1)]),(1,[(0,1,2),(1,1,2)]),(4,[(1,1,2)]),(5,[(1,1,2)]),(6,[(1,1,2)]),(5,[(0,1,2)]),(4,[(0,1,2)]),(6,[(0,1,2)]),(0,[(1,0,2),(0,0,2)]),(1,[(0,1,3),(1,1,3)]),(8,[(1,1,2)]),(3,[(1,1,2)]),(6,[(1,1,3)]),(3,[(0,1,2)]),(8,[(0,1,2)]),(6,[(0,1,3)]),(0,[(0,1,2),(1,1,2)]),(1,[(0,2,3),(1,2,3)]),(7,[(1,1,2)]),(2,[(1,1,2)]),(2,[(0,1,2)]),(7,[(0,1,2)]),(6,[(1,2,3)]),(6,[(0,2,3)])]
def p13_P : List (Nat × Nat) := [(2,3),(4,5),(8,9),(1,3),(1,5),(12,14),(10,14),(1,9),(6,14),(12,28),(6,22),(10,26),(6,7),(24,26),(24,28),(20,22),(18,22),(18,26),(1,7),(20,28),(10,11),(1,11),(12,13),(1,13),(3,6),(0,3),(3,10),(2,14),(5,12),(4,14)]
def p13_K : List CutV := p13_C.map (mkCut p13_Z)
theorem p13_W : ∀ c ∈ p13_K, CutP p13_R p13_T c := cutsGood p13_Y (by decide +kernel)
theorem p13_Q : p13_P.all (sepOK p13_T) = true := by decide +kernel
noncomputable def p13_D8 : List StD := [
([w0,w1,w2,w3,w92],[0,1],[0,1,2,3,4,5,6,7,8,9,10,11],[[0,100,101],[0,101,100],[0,102,100],[0,1,100],[103,104,105,106],[103,107,105,108],[1,109,110],[104,107,106,108],[1,111,109],[1,110,109]])]
noncomputable def p13_D7 : List StD := [
([w0,w7,w1,w2,w3,w92],[2,3,4,5,6,7,8,9,10],[12,2,8,13,3,14,4,10,11],[[0,1,100],[0,1,100],[0,2,100],[0,101,100],[0,3,100],[1,4],[1,2,5],[1,6,102,7],[1,3,8],[1,2],[1,103,104],[1,3,104],[2,105,106],[2,3,106],[3,107,108]]),
([w0,w1,w2,w33,w3,w92],[11,12,13,14,7,6,9,8,10],[1,0,2,15,5,16,6,7,10,11],[[0,1,100],[0,2,101],[0,1,102],[0,102,100],[0,3,100],[1,2],[1,4],[1,103,104],[1,3,104],[1,2,5],[2,105,106],[2,3,106],[1,6,107,7],[1,3,8],[3,108,109]]),
([w62,w0,w1,w2,w3,w92],[6,3,2,11,8,9,1,15,10,13],[0,17,2,18,5,15,4,14,10,11],[[0,1,100],[1,2],[1,3],[1,4,101,5],[1,6,7,8],[0,1,100],[0,9,100],[0,102,100],[0,7,100],[1,9,103],[1,104,105],[1,7,104],[9,106,107],[7,9,106],[7,108,109]]),
([w63,w0,w1,w2,w3,w92],[7,12,11,2,8,9,1,16,10,13,4],[1,19,2,18,3,13,6,16,10,11],[[0,1,100],[1,2],[1,3],[1,4,101,5],[1,6,7,8],[0,1,100],[0,9,100,10],[0,102,100],[0,7,100],[1,10,103],[1,104,105],[1,7,104],[10,106,107],[7,10,106],[7,108,109]]),
([w0,w8,w1,w2,w3,w92],[17,9,12,3,18,19,13,4,10],[20,1,6,15,3,19,7,11,10],[[0,1,100],[0,2,100,3],[0,101,100],[0,1,100],[0,4,100],[1,3,5],[1,6,102,7],[1,2],[1,4,8],[3,103,104],[1,2,3],[3,4,104],[1,105,106],[4,107,108],[1,4,106]]),
([w0,w1,w2,w3,w34,w92],[20,12,8,21,22,4,13,19,10],[1,0,13,5,17,8,4,11,10],[[0,1,100],[0,100,101],[0,2,100],[0,1,100],[0,3,100],[1,102,103],[1,2],[1,4],[1,3,103],[2,104,105],[1,5,106,6],[3,107,108],[1,2,7],[2,3,105],[1,3,8]]),
([w64,w0,w1,w2,w3,w92],[19,8,17,13,4,20,1,23,10,12,3],[0,16,1,5,13,21,7,19,11,10],[[0,1,100],[1,2],[1,3,101,4],[1,5],[1,6,7,8],[0,9,100,10],[0,102,100],[0,1,100],[0,7,100],[10,103,104],[1,10,105],[7,10,103],[1,106,107],[7,108,109],[1,7,106]]),
([w65,w0,w1,w2,w3,w92],[22,12,20,13,4,17,1,24,10,9],[2,14,1,3,15,21,8,17,11,10],[[0,1,100],[1,2],[1,3,101,4],[1,5],[1,6,7,8],[0,1,100],[0,102,100],[0,9,100],[0,7,100],[1,103,104],[1,9,105],[1,7,103],[9,106,107],[7,108,109],[7,9,106]]),
([w0,w1,w9,w2,w3,w92],[25,9,13,4,26,12,3,27,10],[0,1,22,5,16,4,17,7,9,10],[[0,100,101],[0,1,102],[0,2,101,3],[0,1,102],[0,4,100],[1,5,103,6],[3,104,105],[1,106,107],[4,108,109],[1,3,7],[1,2],[1,4,8],[1,2,3],[3,4,105],[1,4,107]]),
([w0,w1,w2,w3,w35,w92],[28,13,8,29,3,12,30,27,10],[0,1,14,6,19,8,3,9,10],[[0,100,101],[0,1,100],[0,2,100],[0,1,100],[0,3,100],[1,102,103],[2,104,105],[1,4,106,5],[3,107,108],[1,2],[1,6],[1,3,103],[1,2,7],[2,3,105],[1,3,8]]),
([w66,w0,w1,w2,w3,w92],[27,8,12,3,25,28,1,31,10,13,4],[1,15,0,6,14,7,17,9,10,23],[[0,1,100],[1,2,101,3],[1,4],[1,5],[1,6,7,8],[0,102,100],[0,9,100,10],[0,1,100],[0,7,100],[10,103,104],[1,105,106],[7,107,108],[1,10,109],[7,10,103],[1,7,105]]),
([w67,w0,w1,w2,w3,w92],[30,9,12,3,28,25,1,32,10,13],[2,13,0,4,16,8,19,9,10,23],[[0,1,100],[1,2,101,3],[1,4],[1,5],[1,6,7,8],[0,102,100],[0,9,100],[0,1,100],[0,7,100],[9,103,104],[1,105,106],[7,107,108],[1,9,109],[7,9,103],[1,7,105]])]
noncomputable def p13_D6 : List StD := [
([w0,w7,w33,w3,w92],[33,3,13,34,35,36,37,38,39,40],[24,25,2,0,18,8,3,7,10,11],[[0,1,100],[0,2,101],[0,102,103],[0,3,102],[1,2,104],[1,4,105,5],[1,3,6],[2,7,106,8,107],[2,3,9],[3,108,109]]),
([w0,w8,w2,w34,w92],[41,9,8,42,43,44,45,46,47,48],[26,1,0,8,27,21,3,4,11,10],[[0,1,100],[0,101,102],[0,2,101],[0,3,101],[1,4,103,5,104],[1,2,105],[1,3,6],[2,7,106,8,107],[3,108,109],[2,3,9]]),
([w0,w1,w9,w35,w92],[49,4,13,50,51,52,53,54,55,56],[0,1,28,8,29,3,9,10,23],[[0,100,101],[0,1,102],[0,2,100],[0,3,100],[1,4,103,5,104],[2,6,105,7],[3,106,107],[1,2,108],[1,3,8],[2,3,9]])]
def p13_D5 : List StD := []
theorem p13_I5 : LevelN p13_R p13_T 5 p13_D5 := by intro s h; cases h
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C6x0 : levelOK p13_T p13_K p13_P 5 (p13_D5.map Prod.fst) ((p13_D6.drop (0*16)).take 16) = true := by decide +kernel
theorem p13_I6 : LevelN p13_R p13_T 6 p13_D6 := levelStep p13_B p13_W p13_Q p13_I5 (chunks 16 p13_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C6x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C7x0 : levelOK p13_T p13_K p13_P 6 (p13_D6.map Prod.fst) ((p13_D7.drop (0*16)).take 16) = true := by decide +kernel
theorem p13_I7 : LevelN p13_R p13_T 7 p13_D7 := levelStep p13_B p13_W p13_Q p13_I6 (chunks 16 p13_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C7x0
  ))
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem p13_C8x0 : levelOK p13_T p13_K p13_P 7 (p13_D7.map Prod.fst) ((p13_D8.drop (0*16)).take 16) = true := by decide +kernel
theorem p13_I8 : LevelN p13_R p13_T 8 p13_D8 := levelStep p13_B p13_W p13_Q p13_I7 (chunks 16 p13_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C8x0
  ))
theorem p13_L : LowN p13_R p13_T 9 := lowSearch p13_B p13_I8 (by decide +kernel)

def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276677288 * 2 ^ 32 + 4007717536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def smallCircuit : Circuit := ⟨[⟨.and,[2,3]⟩, ⟨.and,[6,4]⟩, ⟨.and,[1,0]⟩, ⟨.or,[7,8]⟩, ⟨.and,[9,5]⟩, ⟨.or,[4,6]⟩, ⟨.and,[11,1]⟩, ⟨.or,[12,0]⟩, ⟨.or,[3,2]⟩, ⟨.and,[13,14]⟩, ⟨.or,[10,15]⟩],16⟩
theorem witnessMonotone : PEqualNP.MetaComplexity.Monotone2 smallCircuit := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by decide +kernel
theorem witnessSize : smallCircuit.size = 11 := rfl

def sevenInputs : List Sig := [W 0x26555555554, W 0x39199999998, W 0x19fe1e1e1e0, W 0x59fe01fe00, W 0x101fffe0000, W 0x1fffffffe]
def graph : Sig := W 0x155fdd1d550
theorem graph_proper : proper graph := by unfold proper; decide +kernel
def sampleSeven (r : Row) (i : Fin 6) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 6 => sevenInputs.getD i.val zero) = sevenInputs := rfl
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

def lowRow (i : Fin 6) : Row := Fin.ofNat 128 (([33, 35, 37, 37, 39, 41] : List Nat).getD i.val 0)
def highRow (i : Fin 6) : Row := Fin.ofNat 128 (([34, 36, 34, 38, 40, 4] : List Nat).getD i.val 0)
set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 6, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 6, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x)=target x) :
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
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 6, sevenInputs.getD i.val zero = a := by
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

def cutIndex (r : Row) : Row := Fin.ofNat 128 (1 + ((r.val / 1) % 2) * 1 + ((r.val / 2) % 2) * 2 + ((r.val / 4) % 2) * 4 + ((r.val / 8) % 2) * 8 + ((r.val / 16) % 2) * 16)
def reducedSig : List Sig := [W (xN 0), W (xN 1), W (xN 2), W (xN 3), W (xN 4), one]
theorem projectedGoal : restrictRows cutIndex (observe graph) = observe (W p13_T) := by
  funext r
  have h : ∀ r : Row, bit (cutIndex r) graph = bit r (W p13_T) := by decide +kernel
  exact h r
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem projectedRoots : (sevenInputs.map observe).map (restrictRows cutIndex) = reducedSig.map observe := by
  have h : sevenInputs.map (fun w => table (restrictRows cutIndex (observe w))) = reducedSig := by decide +kernel
  rw [←h]
  simp only [List.map_map,Function.comp_def,observe_table]
theorem projectedSupply : supply true ((rootsW p13_R).map observe) (reducedSig.map observe) := by
  intro w hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
  have all : reducedSig.all (fun v => v == zero || v == one || (rootsW p13_R).contains v) = true := by decide +kernel
  have good := List.all_eq_true.mp all v hv
  simp only [Bool.or_eq_true, beq_iff_eq,List.contains_iff_mem] at good
  rcases good with (rfl|rfl)|mem
  · exact Or.inr (Or.inl ⟨false,funext (fun i => bit_zero i)⟩)
  · exact Or.inr (Or.inl ⟨true,funext (fun i => bit_one i)⟩)
  · exact Or.inl (List.mem_map.mpr ⟨v,mem,rfl⟩)
theorem lostInputs : 1 ≤ mass (reducedSig.map observe) := by
  have z : Constant (observe zero) := ⟨false,funext (fun i => bit_zero i)⟩
  have o : Constant (observe one) := ⟨true,funext (fun i => bit_one i)⟩
  have cz : cost (observe zero) = 1 := by simp [cost,z]
  have co : cost (observe one) = 1 := by simp [cost,o]
  simp only [reducedSig,List.map_cons,List.map_nil,mass_cons,cz,co]
  omega
theorem binaryLower (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (correct : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x) :
    10 ≤ C.gates.countP (fun g => !isNot g) := by
  obtain ⟨b,hb,run⟩ := physicalSigned C legal correct
  have steps := list_run run sevenInputs (by decide +kernel) rfl
  have nc : ¬ Constant (restrictRows cutIndex (observe graph)) := by
    rw [projectedGoal]
    apply observe_proper
    unfold proper
    decide +kernel
  have sup : supply true ((rootsW p13_R).map observe) ((sevenInputs.map observe).map (restrictRows cutIndex)) := by
    rw [projectedRoots]
    exact projectedSupply
  have result := projected_bound cutIndex steps nc Reach.start sup (L := 9)
    (fun q bs built available => p13_L q bs built (projectedGoal ▸ available))
  rw [projectedRoots] at result
  have lost := lostInputs
  omega
theorem replaceShort (s : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize 6 target s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  classical
  by_cases big : 11 ≤ s
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
  have lower := binaryLower C legal correct
  have size : C.gates.length ≤ s := hs
  omega

end PEqualNP.Outside.L_meta_39887_aux

theorem PEqualNP.Outside.L_meta_39887 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 4007717536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 4007717536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s h
  exact PEqualNP.Outside.L_meta_39887_aux.replaceShort s h
