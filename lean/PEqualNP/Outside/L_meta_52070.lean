import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_52070.Certificate10560
open PEqualNP.CircuitLowerBounds
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffaffffffeefefeeca0fffffffffffffffaffffffeefefeeca0fffffffffffffffaffffffeefefeeca0fffffffffffffffaffffffeefefeeca0
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
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

abbrev Bits := BitVec 1695
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 1695 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 1695 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 1695 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 1695 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 1695) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 1695) (j : Fin 9) :
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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 4 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 1695) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 1695) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide)]
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
    if (rs ||| column d z.2) != BitVec.allOnes 1695 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1695) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1695 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 1695) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 1695) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 1695) &&
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
def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.and, [8, 0]⟩,
    ⟨.and, [11, 9]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.or, [15, 17]⟩,
    ⟨.or, [13, 18]⟩], 19⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 13 := rfl

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

def sevenInputs : List Sig := vars 127
def sampleSeven (r : Row) (i : Fin 7) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 7 => sevenInputs.getD i.val zero) = sevenInputs := rfl
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

def lowRow (i : Fin 7) : Row := Fin.ofNat 512 (1 <<< ([2, 3, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([2, 3, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 7, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
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
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 7, sevenInputs.getD i.val zero = a := by
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
    (lower : Impossible true graph 11 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
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

def repeatRows (k value : Nat) : Bits := BitVec.ofNat 1695 (value * ((2 ^ (k * ((1695 + k - 1) / k)) - 1) / (2 ^ k - 1)))

def g21Y : Array (Bits × Bits) := #[((repeatRows 16 0xbbbb), (repeatRows 16 0xf0)),
    (0x0, 0x0),
    ((repeatRows 16 0xdddd), (repeatRows 16 0xf00)),
    (0x0, 0x0),
    ((repeatRows 16 0xeeee), (repeatRows 16 0xf000)),
    (0x0, 0x0),
    (0x0, 0x0)]
def g21C : List ColumnInfo := []
def g21D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g21L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g21D3)
  | _ => emptyPacking
def g21I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g21 : Forest := ⟨21, 3, fun i => (g21Y[i]?).getD (0,0), g21C, [[], [66], [32], [32, 66], [64, 66], [64]], g21L, g21I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g21P3n0 : block g21 3 0 1 = true := by decide +kernel
theorem g21B3 : block g21 3 0 1 = true := g21P3n0
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
def K21 := extendKnown [] 4 [(21,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V21 : Known true K21 := extend_ok (m:=21) baseKnown low21 (by decide +kernel)

def g42Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 16 0xbbbb), (repeatRows 16 0xf0)),
    (0x0, 0x0),
    ((repeatRows 16 0xdddd), (repeatRows 16 0xf00)),
    (0x0, 0x0),
    ((repeatRows 16 0xeeee), (repeatRows 16 0xf000)),
    (0x0, 0x0)]
def g42C : List ColumnInfo := []
def g42D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g42L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g42D3)
  | _ => emptyPacking
def g42I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g42 : Forest := ⟨42, 3, fun i => (g42Y[i]?).getD (0,0), g42C, [[], [83], [49], [49, 83], [81, 83], [81]], g42L, g42I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g42P3n0 : block g42 3 0 1 = true := by decide +kernel
theorem g42B3 : block g42 3 0 1 = true := g42P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g42T : checkedTables g42 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g42 0 0 0 = true)
  · exact (rfl : block g42 1 0 0 = true)
  · exact (rfl : block g42 2 0 0 = true)
  · exact g42B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g42G : graphValid g42 (boundsBefore K21) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low42 : Lower true (varsX 42) (graphGoal 42) 4 := lower_forest (g:=g42) (i:=0) (hints:=1052720) (before_sound K21 V21) g42G g42T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K42 := extendKnown K21 4 [(42,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V42 : Known true K42 := extend_ok (m:=42) V21 low42 (by decide +kernel)

def g49Y : Array (Bits × Bits) := #[((repeatRows 16 0xbbbb), (repeatRows 16 0xf0)),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 16 0xdddd), (repeatRows 16 0xf00)),
    ((repeatRows 16 0xeeee), (repeatRows 16 0xf000)),
    (0x0, 0x0)]
def g49C : List ColumnInfo := []
def g49D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g49L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g49D3)
  | _ => emptyPacking
def g49I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g49 : Forest := ⟨49, 3, fun i => (g49Y[i]?).getD (0,0), g49C, [[], [84], [64], [64, 84], [80, 84], [80]], g49L, g49I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g49P3n0 : block g49 3 0 1 = true := by decide +kernel
theorem g49B3 : block g49 3 0 1 = true := g49P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g49T : checkedTables g49 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g49 0 0 0 = true)
  · exact (rfl : block g49 1 0 0 = true)
  · exact (rfl : block g49 2 0 0 = true)
  · exact g49B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g49G : graphValid g49 (boundsBefore K42) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low49 : Lower true (varsX 49) (graphGoal 49) 4 := lower_forest (g:=g49) (i:=0) (hints:=4) (before_sound K42 V42) g49G g49T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K49 := extendKnown K42 4 [(49,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V49 : Known true K49 := extend_ok (m:=49) V42 low49 (by decide +kernel)

def g50Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 16 0xbbbb), (repeatRows 16 0xf0)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 16 0xdddd), (repeatRows 16 0xf00)),
    ((repeatRows 16 0xeeee), (repeatRows 16 0xf000)),
    (0x0, 0x0)]
def g50C : List ColumnInfo := []
def g50D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g50L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g50D3)
  | _ => emptyPacking
def g50I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g50 : Forest := ⟨50, 3, fun i => (g50Y[i]?).getD (0,0), g50C, [[], [84], [65], [65, 84], [81, 84], [81]], g50L, g50I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g50P3n0 : block g50 3 0 1 = true := by decide +kernel
theorem g50B3 : block g50 3 0 1 = true := g50P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g50T : checkedTables g50 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g50 0 0 0 = true)
  · exact (rfl : block g50 1 0 0 = true)
  · exact (rfl : block g50 2 0 0 = true)
  · exact g50B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g50G : graphValid g50 (boundsBefore K49) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low50 : Lower true (varsX 50) (graphGoal 50) 4 := lower_forest (g:=g50) (i:=0) (hints:=1114176) (before_sound K49 V49) g50G g50T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K50 := extendKnown K49 4 [(50,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V50 : Known true K50 := extend_ok (m:=50) V49 low50 (by decide +kernel)

def g69Y : Array (Bits × Bits) := #[((repeatRows 16 0xbbbb), (repeatRows 16 0xf0)),
    (0x0, 0x0),
    ((repeatRows 16 0xdddd), (repeatRows 16 0xf00)),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 16 0xeeee), (repeatRows 16 0xf000))]
def g69C : List ColumnInfo := []
def g69D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g69L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g69D3)
  | _ => emptyPacking
def g69I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g69 : Forest := ⟨69, 3, fun i => (g69Y[i]?).getD (0,0), g69C, [[], [98], [32], [32, 98], [96, 98], [96]], g69L, g69I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g69P3n0 : block g69 3 0 1 = true := by decide +kernel
theorem g69B3 : block g69 3 0 1 = true := g69P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g69T : checkedTables g69 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g69 0 0 0 = true)
  · exact (rfl : block g69 1 0 0 = true)
  · exact (rfl : block g69 2 0 0 = true)
  · exact g69B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g69G : graphValid g69 (boundsBefore K50) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low69 : Lower true (varsX 69) (graphGoal 69) 4 := lower_forest (g:=g69) (i:=0) (hints:=2) (before_sound K50 V50) g69G g69T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K69 := extendKnown K50 4 [(69,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V69 : Known true K69 := extend_ok (m:=69) V50 low69 (by decide +kernel)

def g81Y : Array (Bits × Bits) := #[((repeatRows 16 0xbbbb), (repeatRows 16 0xf0)),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 16 0xdddd), (repeatRows 16 0xf00)),
    (0x0, 0x0),
    ((repeatRows 16 0xeeee), (repeatRows 16 0xf000))]
def g81C : List ColumnInfo := []
def g81D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g81L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g81D3)
  | _ => emptyPacking
def g81I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g81 : Forest := ⟨81, 3, fun i => (g81Y[i]?).getD (0,0), g81C, [[], [100], [64], [64, 100], [96, 100], [96]], g81L, g81I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81P3n0 : block g81 3 0 1 = true := by decide +kernel
theorem g81B3 : block g81 3 0 1 = true := g81P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81T : checkedTables g81 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g81 0 0 0 = true)
  · exact (rfl : block g81 1 0 0 = true)
  · exact (rfl : block g81 2 0 0 = true)
  · exact g81B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g81G : graphValid g81 (boundsBefore K69) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low81 : Lower true (varsX 81) (graphGoal 81) 4 := lower_forest (g:=g81) (i:=0) (hints:=4) (before_sound K69 V69) g81G g81T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K81 := extendKnown K69 4 [(81,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V81 : Known true K81 := extend_ok (m:=81) V69 low81 (by decide +kernel)

def g84Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 16 0xbbbb), (repeatRows 16 0xf0)),
    (0x0, 0x0),
    ((repeatRows 16 0xdddd), (repeatRows 16 0xf00)),
    (0x0, 0x0),
    ((repeatRows 16 0xeeee), (repeatRows 16 0xf000))]
def g84C : List ColumnInfo := []
def g84D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g84L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g84D3)
  | _ => emptyPacking
def g84I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g84 : Forest := ⟨84, 3, fun i => (g84Y[i]?).getD (0,0), g84C, [[], [100], [66], [66, 100], [98, 100], [98]], g84L, g84I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g84P3n0 : block g84 3 0 1 = true := by decide +kernel
theorem g84B3 : block g84 3 0 1 = true := g84P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g84T : checkedTables g84 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g84 0 0 0 = true)
  · exact (rfl : block g84 1 0 0 = true)
  · exact (rfl : block g84 2 0 0 = true)
  · exact g84B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g84G : graphValid g84 (boundsBefore K81) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low84 : Lower true (varsX 84) (graphGoal 84) 4 := lower_forest (g:=g84) (i:=0) (hints:=33686528) (before_sound K81 V81) g84G g84T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K84 := extendKnown K81 4 [(84,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V84 : Known true K84 := extend_ok (m:=84) V81 low84 (by decide +kernel)

def g97Y : Array (Bits × Bits) := #[((repeatRows 16 0xbbbb), (repeatRows 16 0xf0)),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 16 0xdddd), (repeatRows 16 0xf00)),
    ((repeatRows 16 0xeeee), (repeatRows 16 0xf000))]
def g97C : List ColumnInfo := []
def g97D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g97L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g97D3)
  | _ => emptyPacking
def g97I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g97 : Forest := ⟨97, 3, fun i => (g97Y[i]?).getD (0,0), g97C, [[], [101], [80], [80, 101], [96, 101], [96]], g97L, g97I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g97P3n0 : block g97 3 0 1 = true := by decide +kernel
theorem g97B3 : block g97 3 0 1 = true := g97P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g97T : checkedTables g97 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g97 0 0 0 = true)
  · exact (rfl : block g97 1 0 0 = true)
  · exact (rfl : block g97 2 0 0 = true)
  · exact g97B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g97G : graphValid g97 (boundsBefore K84) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low97 : Lower true (varsX 97) (graphGoal 97) 4 := lower_forest (g:=g97) (i:=0) (hints:=5) (before_sound K84 V84) g97G g97T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K97 := extendKnown K84 4 [(97,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V97 : Known true K97 := extend_ok (m:=97) V84 low97 (by decide +kernel)

def g104Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 16 0xbbbb), (repeatRows 16 0xf0)),
    (0x0, 0x0),
    ((repeatRows 16 0xdddd), (repeatRows 16 0xf00)),
    ((repeatRows 16 0xeeee), (repeatRows 16 0xf000))]
def g104C : List ColumnInfo := []
def g104D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g104L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g104D3)
  | _ => emptyPacking
def g104I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g104 : Forest := ⟨104, 3, fun i => (g104Y[i]?).getD (0,0), g104C, [[], [101], [83], [83, 101], [99, 101], [99]], g104L, g104I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g104P3n0 : block g104 3 0 1 = true := by decide +kernel
theorem g104B3 : block g104 3 0 1 = true := g104P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g104T : checkedTables g104 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g104 0 0 0 = true)
  · exact (rfl : block g104 1 0 0 = true)
  · exact (rfl : block g104 2 0 0 = true)
  · exact g104B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g104G : graphValid g104 (boundsBefore K97) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low104 : Lower true (varsX 104) (graphGoal 104) 4 := lower_forest (g:=g104) (i:=0) (hints:=53497856) (before_sound K97 V97) g104G g104T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K104 := extendKnown K97 4 [(104,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V104 : Known true K104 := extend_ok (m:=104) V97 low104 (by decide +kernel)

def g112Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 16 0xbbbb), (repeatRows 16 0xf0)),
    ((repeatRows 16 0xdddd), (repeatRows 16 0xf00)),
    ((repeatRows 16 0xeeee), (repeatRows 16 0xf000))]
def g112C : List ColumnInfo := []
def g112D3 (j : Nat) : Nat := if j = 0 then 0x7 else 0
def g112L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g112D3)
  | _ => emptyPacking
def g112I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g112 : Forest := ⟨112, 3, fun i => (g112Y[i]?).getD (0,0), g112C, [[], [101], [84], [84, 101], [100, 101], [100]], g112L, g112I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g112P3n0 : block g112 3 0 1 = true := by decide +kernel
theorem g112B3 : block g112 3 0 1 = true := g112P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g112T : checkedTables g112 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g112 0 0 0 = true)
  · exact (rfl : block g112 1 0 0 = true)
  · exact (rfl : block g112 2 0 0 = true)
  · exact g112B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g112G : graphValid g112 (boundsBefore K104) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low112 : Lower true (varsX 112) (graphGoal 112) 4 := lower_forest (g:=g112) (i:=0) (hints:=71630848) (before_sound K104 V104) g112G g112T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K112 := extendKnown K104 4 [(112,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V112 : Known true K112 := extend_ok (m:=112) V104 low112 (by decide +kernel)

def g23Y : Array (Bits × Bits) := #[((repeatRows 63 0x55eaf57abd5eaf57), (repeatRows 63 0xff803fe00)),
    ((repeatRows 63 0x66b359acd66b359a), (repeatRows 63 0x3fe00ffffc0000)),
    ((repeatRows 63 0x78fc7e3f1f8fc7e3), (repeatRows 63 0x3ffff000000000)),
    (0x0, 0x0),
    ((repeatRows 63 0x7f3f9fcfe7f3f9fc), (repeatRows 63 0x7fc0000000000000)),
    (0x0, 0x0),
    (0x0, 0x0)]
def g23C : List ColumnInfo := [(2,0,21,0,4)]
def g23D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g23L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g23D4)
  | _ => emptyPacking
def g23I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g23 : Forest := ⟨23, 4, fun i => (g23Y[i]?).getD (0,0), g23C, [[], [32]], g23L, g23I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23P4n0 : block g23 4 0 1 = true := by decide +kernel
theorem g23B4 : block g23 4 0 1 = true := g23P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23T : checkedTables g23 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g23 0 0 0 = true)
  · exact (rfl : block g23 1 0 0 = true)
  · exact (rfl : block g23 2 0 0 = true)
  · exact (rfl : block g23 3 0 0 = true)
  · exact g23B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23G : graphValid g23 (boundsBefore K112) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low23 : Lower true (varsX 23) (graphGoal 23) 5 := lower_forest (g:=g23) (i:=0) (hints:=66) (before_sound K112 V112) g23G g23T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K23 := extendKnown K112 5 [(23,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V23 : Known true K23 := extend_ok (m:=23) V112 low23 (by decide +kernel)

def g27Y : Array (Bits × Bits) := #[((repeatRows 64 0xb6b6b6b6b6b6b6b6), (repeatRows 64 0xff00ff00ff00)),
    ((repeatRows 64 0xdbdbdbdbdbdbdbdb), (repeatRows 64 0xffff0000)),
    (0x0, 0x0),
    ((repeatRows 64 0xe3e3e3e3e3e3e3e3), (repeatRows 64 0xff00ffff00000000)),
    ((repeatRows 64 0xfcfcfcfcfcfcfcfc), (repeatRows 64 0xffff000000000000)),
    (0x0, 0x0),
    (0x0, 0x0)]
def g27C : List ColumnInfo := []
def g27D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g27L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g27D3)
  | _ => emptyPacking
def g27I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g27 : Forest := ⟨27, 3, fun i => (g27Y[i]?).getD (0,0), g27C, [[], [48, 65]], g27L, g27I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P3n0 : block g27 3 0 1 = true := by decide +kernel
theorem g27B3 : block g27 3 0 1 = true := g27P3n0
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
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=4148) (before_sound K23 V23) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K23 4 [(27,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V23 low27 (by decide +kernel)

def g30Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 64 0xb7b7b7b7b7b7b7b7), (repeatRows 64 0xff00ff00)),
    ((repeatRows 64 0xdadadadadadadada), (repeatRows 64 0xff00ffff0000)),
    ((repeatRows 64 0xe3e3e3e3e3e3e3e3), (repeatRows 64 0xff00ffff00000000)),
    ((repeatRows 64 0xfcfcfcfcfcfcfcfc), (repeatRows 64 0xffff000000000000)),
    (0x0, 0x0),
    (0x0, 0x0)]
def g30C : List ColumnInfo := []
def g30D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g30L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g30D3)
  | _ => emptyPacking
def g30I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g30 : Forest := ⟨30, 3, fun i => (g30Y[i]?).getD (0,0), g30C, [[], [65, 50]], g30L, g30I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30P3n0 : block g30 3 0 1 = true := by decide +kernel
theorem g30B3 : block g30 3 0 1 = true := g30P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30T : checkedTables g30 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g30 0 0 0 = true)
  · exact (rfl : block g30 1 0 0 = true)
  · exact (rfl : block g30 2 0 0 = true)
  · exact g30B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30G : graphValid g30 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low30 : Lower true (varsX 30) (graphGoal 30) 4 := lower_forest (g:=g30) (i:=0) (hints:=70704) (before_sound K27 V27) g30G g30T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K30 := extendKnown K27 4 [(30,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V30 : Known true K30 := extend_ok (m:=30) V27 low30 (by decide +kernel)

def g39Y : Array (Bits × Bits) := #[((repeatRows 64 0xb7b7b7b7b7b7b7b7), (repeatRows 64 0xff00ff00)),
    ((repeatRows 64 0xdadadadadadadada), (repeatRows 64 0xff00ffff0000)),
    ((repeatRows 64 0xe3e3e3e3e3e3e3e3), (repeatRows 64 0xff00ffff00000000)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 64 0xfcfcfcfcfcfcfcfc), (repeatRows 64 0xffff000000000000)),
    (0x0, 0x0)]
def g39C : List ColumnInfo := []
def g39D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g39L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g39D3)
  | _ => emptyPacking
def g39I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g39 : Forest := ⟨39, 3, fun i => (g39Y[i]?).getD (0,0), g39C, [[], [80, 33]], g39L, g39I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39P3n0 : block g39 3 0 1 = true := by decide +kernel
theorem g39B3 : block g39 3 0 1 = true := g39P3n0
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
theorem g39G : graphValid g39 (boundsBefore K30) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low39 : Lower true (varsX 39) (graphGoal 39) 4 := lower_forest (g:=g39) (i:=0) (hints:=82) (before_sound K30 V30) g39G g39T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K39 := extendKnown K30 4 [(39,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V39 : Known true K39 := extend_ok (m:=39) V30 low39 (by decide +kernel)

def g43Y : Array (Bits × Bits) := #[((repeatRows 63 0x55aad56ab55aad56), (repeatRows 63 0x3fe00ff803fe00)),
    ((repeatRows 63 0x66f379bcde6f379b), (repeatRows 63 0xffffc0000)),
    (0x0, 0x0),
    ((repeatRows 63 0x78fc7e3f1f8fc7e3), (repeatRows 63 0x3ffff000000000)),
    (0x0, 0x0),
    ((repeatRows 63 0x7f3f9fcfe7f3f9fc), (repeatRows 63 0x7fc0000000000000)),
    (0x0, 0x0)]
def g43C : List ColumnInfo := [(1,0,42,0,4)]
def g43D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g43L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g43D4)
  | _ => emptyPacking
def g43I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g43 : Forest := ⟨43, 4, fun i => (g43Y[i]?).getD (0,0), g43C, [[], [49]], g43L, g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P4n0 : block g43 4 0 1 = true := by decide +kernel
theorem g43B4 : block g43 4 0 1 = true := g43P4n0
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
def K43 := extendKnown K39 5 [(43,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V39 low43 (by decide +kernel)

def g45Y : Array (Bits × Bits) := #[((repeatRows 64 0xafafafafafafafaf), (repeatRows 64 0xff0000ff00)),
    (0x0, 0x0),
    ((repeatRows 64 0xcbcbcbcbcbcbcbcb), (repeatRows 64 0xff00ff0000ff0000)),
    ((repeatRows 64 0xf2f2f2f2f2f2f2f2), (repeatRows 64 0xffffff000000)),
    (0x0, 0x0),
    ((repeatRows 64 0xfcfcfcfcfcfcfcfc), (repeatRows 64 0xffff000000000000)),
    (0x0, 0x0)]
def g45C : List ColumnInfo := []
def g45D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g45L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g45D3)
  | _ => emptyPacking
def g45I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g45 : Forest := ⟨45, 3, fun i => (g45Y[i]?).getD (0,0), g45C, [[], [80, 50]], g45L, g45I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P3n0 : block g45 3 0 1 = true := by decide +kernel
theorem g45B3 : block g45 3 0 1 = true := g45P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : checkedTables g45 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g45 0 0 0 = true)
  · exact (rfl : block g45 1 0 0 = true)
  · exact (rfl : block g45 2 0 0 = true)
  · exact g45B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (graphGoal 45) 4 := lower_forest (g:=g45) (i:=0) (hints:=20482) (before_sound K43 V43) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K43 4 [(45,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V43 low45 (by decide +kernel)

def g51Y : Array (Bits × Bits) := #[((repeatRows 60 0xab6adab6adab6ad), (repeatRows 60 0xffc00ffc00)),
    ((repeatRows 60 0xcdb36cdb36cdb36), (repeatRows 60 0xfffff00000)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 60 0xf1fc7f1fc7f1fc7), (repeatRows 60 0x3ff0000000000)),
    ((repeatRows 60 0xfe3f8fe3f8fe3f8), (repeatRows 60 0xffc000000000000)),
    (0x0, 0x0)]
def g51C : List ColumnInfo := [(1,0,50,0,4)]
def g51D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g51L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g51D4)
  | _ => emptyPacking
def g51I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g51 : Forest := ⟨51, 4, fun i => (g51Y[i]?).getD (0,0), g51C, [[], [84], [16], [16, 84]], g51L, g51I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51P4n0 : block g51 4 0 1 = true := by decide +kernel
theorem g51B4 : block g51 4 0 1 = true := g51P4n0
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
theorem g51G : graphValid g51 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 5 := lower_forest (g:=g51) (i:=0) (hints:=68) (before_sound K45 V45) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K45 5 [(51,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V45 low51 (by decide +kernel)

def g53Y : Array (Bits × Bits) := #[((repeatRows 60 0xaeebbaeebbaeebb), (repeatRows 60 0xffc00)),
    (0x0, 0x0),
    ((repeatRows 60 0xcb72dcb72dcb72d), (repeatRows 60 0xffc00003ff00000)),
    (0x0, 0x0),
    ((repeatRows 60 0xf3bcef3bcef3bce), (repeatRows 60 0xffc0000000)),
    ((repeatRows 60 0xfc3f0fc3f0fc3f0), (repeatRows 60 0xfffff0000000000)),
    (0x0, 0x0)]
def g53C : List ColumnInfo := [(4,0,49,0,4)]
def g53D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g53L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g53D4)
  | _ => emptyPacking
def g53I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g53 : Forest := ⟨53, 4, fun i => (g53Y[i]?).getD (0,0), g53C, [[], [82], [64], [64, 82]], g53L, g53I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53P4n0 : block g53 4 0 1 = true := by decide +kernel
theorem g53B4 : block g53 4 0 1 = true := g53P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53T : checkedTables g53 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g53 0 0 0 = true)
  · exact (rfl : block g53 1 0 0 = true)
  · exact (rfl : block g53 2 0 0 = true)
  · exact (rfl : block g53 3 0 0 = true)
  · exact g53B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g53G : graphValid g53 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low53 : Lower true (varsX 53) (graphGoal 53) 5 := lower_forest (g:=g53) (i:=0) (hints:=2) (before_sound K51 V51) g53G g53T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K53 := extendKnown K51 5 [(53,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V53 : Known true K53 := extend_ok (m:=53) V51 low53 (by decide +kernel)

def g54Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 63 0x576bb5daed76bb5d), (repeatRows 63 0xff803fe00)),
    ((repeatRows 63 0x65b2d96cb65b2d96), (repeatRows 63 0x7fc0000ffffc0000)),
    (0x0, 0x0),
    ((repeatRows 63 0x79fcfe7f3f9fcfe7), (repeatRows 63 0x1ff000000000)),
    ((repeatRows 63 0x7e3f1f8fc7e3f1f8), (repeatRows 63 0x7fffe00000000000)),
    (0x0, 0x0)]
def g54C : List ColumnInfo := [(4,0,50,0,4)]
def g54D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g54L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g54D4)
  | _ => emptyPacking
def g54I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g54 : Forest := ⟨54, 4, fun i => (g54Y[i]?).getD (0,0), g54C, [[], [81]], g54L, g54I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54P4n0 : block g54 4 0 1 = true := by decide +kernel
theorem g54B4 : block g54 4 0 1 = true := g54P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54T : checkedTables g54 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g54 0 0 0 = true)
  · exact (rfl : block g54 1 0 0 = true)
  · exact (rfl : block g54 2 0 0 = true)
  · exact (rfl : block g54 3 0 0 = true)
  · exact g54B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54G : graphValid g54 (boundsBefore K53) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low54 : Lower true (varsX 54) (graphGoal 54) 5 := lower_forest (g:=g54) (i:=0) (hints:=1115200) (before_sound K53 V53) g54G g54T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K54 := extendKnown K53 5 [(54,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V54 : Known true K54 := extend_ok (m:=54) V53 low54 (by decide +kernel)

def g57Y : Array (Bits × Bits) := #[((repeatRows 63 0x55eaf57abd5eaf57), (repeatRows 63 0xff803fe00)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 63 0x66b359acd66b359a), (repeatRows 63 0x3fe00ffffc0000)),
    ((repeatRows 63 0x78fc7e3f1f8fc7e3), (repeatRows 63 0x3ffff000000000)),
    ((repeatRows 63 0x7f3f9fcfe7f3f9fc), (repeatRows 63 0x7fc0000000000000)),
    (0x0, 0x0)]
def g57C : List ColumnInfo := [(8,0,49,0,4)]
def g57D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g57L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g57D4)
  | _ => emptyPacking
def g57I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g57 : Forest := ⟨57, 4, fun i => (g57Y[i]?).getD (0,0), g57C, [[], [64]], g57L, g57I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57P4n0 : block g57 4 0 1 = true := by decide +kernel
theorem g57B4 : block g57 4 0 1 = true := g57P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57T : checkedTables g57 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g57 0 0 0 = true)
  · exact (rfl : block g57 1 0 0 = true)
  · exact (rfl : block g57 2 0 0 = true)
  · exact (rfl : block g57 3 0 0 = true)
  · exact g57B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57G : graphValid g57 (boundsBefore K54) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low57 : Lower true (varsX 57) (graphGoal 57) 5 := lower_forest (g:=g57) (i:=0) (hints:=20484) (before_sound K54 V54) g57G g57T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K57 := extendKnown K54 5 [(57,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V57 : Known true K57 := extend_ok (m:=57) V54 low57 (by decide +kernel)

def g58Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 60 0xabeafabeafabeaf), (repeatRows 60 0xffc00)),
    (0x0, 0x0),
    ((repeatRows 60 0xcd735cd735cd735), (repeatRows 60 0x3ff003ff00000)),
    ((repeatRows 60 0xf1bc6f1bc6f1bc6), (repeatRows 60 0x3ffffc0000000)),
    ((repeatRows 60 0xfe3f8fe3f8fe3f8), (repeatRows 60 0xffc000000000000)),
    (0x0, 0x0)]
def g58C : List ColumnInfo := [(8,0,50,0,4)]
def g58D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g58L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g58D4)
  | _ => emptyPacking
def g58I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g58 : Forest := ⟨58, 4, fun i => (g58Y[i]?).getD (0,0), g58C, [[], [67], [81], [81, 67]], g58L, g58I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g58P4n0 : block g58 4 0 1 = true := by decide +kernel
theorem g58B4 : block g58 4 0 1 = true := g58P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g58T : checkedTables g58 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g58 0 0 0 = true)
  · exact (rfl : block g58 1 0 0 = true)
  · exact (rfl : block g58 2 0 0 = true)
  · exact (rfl : block g58 3 0 0 = true)
  · exact g58B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g58G : graphValid g58 (boundsBefore K57) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low58 : Lower true (varsX 58) (graphGoal 58) 5 := lower_forest (g:=g58) (i:=0) (hints:=1118256) (before_sound K57 V57) g58G g58T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K58 := extendKnown K57 5 [(58,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V58 : Known true K58 := extend_ok (m:=58) V57 low58 (by decide +kernel)

def g60Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 64 0xabababababababab), (repeatRows 64 0xff000000ff00ff00)),
    ((repeatRows 64 0xcececececececece), (repeatRows 64 0xff00ffff0000)),
    ((repeatRows 64 0xf3f3f3f3f3f3f3f3), (repeatRows 64 0xffff00000000)),
    ((repeatRows 64 0xfcfcfcfcfcfcfcfc), (repeatRows 64 0xffff000000000000)),
    (0x0, 0x0)]
def g60C : List ColumnInfo := []
def g60D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g60L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g60D3)
  | _ => emptyPacking
def g60I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g60 : Forest := ⟨60, 3, fun i => (g60Y[i]?).getD (0,0), g60C, [[], [50, 84]], g60L, g60I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g60P3n0 : block g60 3 0 1 = true := by decide +kernel
theorem g60B3 : block g60 3 0 1 = true := g60P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g60T : checkedTables g60 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g60 0 0 0 = true)
  · exact (rfl : block g60 1 0 0 = true)
  · exact (rfl : block g60 2 0 0 = true)
  · exact g60B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g60G : graphValid g60 (boundsBefore K58) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low60 : Lower true (varsX 60) (graphGoal 60) 4 := lower_forest (g:=g60) (i:=0) (hints:=3298304) (before_sound K58 V58) g60G g60T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K60 := extendKnown K58 4 [(60,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V60 : Known true K60 := extend_ok (m:=60) V58 low60 (by decide +kernel)

def g75Y : Array (Bits × Bits) := #[((repeatRows 64 0xaeaeaeaeaeaeaeae), (repeatRows 64 0xff00ff00ff00)),
    ((repeatRows 64 0xcbcbcbcbcbcbcbcb), (repeatRows 64 0xff000000ffff0000)),
    (0x0, 0x0),
    ((repeatRows 64 0xf3f3f3f3f3f3f3f3), (repeatRows 64 0xffff00000000)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 64 0xfcfcfcfcfcfcfcfc), (repeatRows 64 0xffff000000000000))]
def g75C : List ColumnInfo := []
def g75D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g75L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g75D3)
  | _ => emptyPacking
def g75I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g75 : Forest := ⟨75, 3, fun i => (g75Y[i]?).getD (0,0), g75C, [[], [16, 99]], g75L, g75I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75P3n0 : block g75 3 0 1 = true := by decide +kernel
theorem g75B3 : block g75 3 0 1 = true := g75P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75T : checkedTables g75 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g75 0 0 0 = true)
  · exact (rfl : block g75 1 0 0 = true)
  · exact (rfl : block g75 2 0 0 = true)
  · exact g75B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g75G : graphValid g75 (boundsBefore K60) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low75 : Lower true (varsX 75) (graphGoal 75) 4 := lower_forest (g:=g75) (i:=0) (hints:=4150) (before_sound K60 V60) g75G g75T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K75 := extendKnown K60 4 [(75,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V75 : Known true K75 := extend_ok (m:=75) V60 low75 (by decide +kernel)

def g77Y : Array (Bits × Bits) := #[((repeatRows 63 0x55eaf57abd5eaf57), (repeatRows 63 0x1ff00003fe00)),
    (0x0, 0x0),
    ((repeatRows 63 0x66f379bcde6f379b), (repeatRows 63 0x3fe00007fc0000)),
    ((repeatRows 63 0x78bc5e2f178bc5e2), (repeatRows 63 0x3ffffff8000000)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 63 0x7f3f9fcfe7f3f9fc), (repeatRows 63 0x7fc0000000000000))]
def g77C : List ColumnInfo := [(8,0,69,0,4)]
def g77D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g77L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g77D4)
  | _ => emptyPacking
def g77I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g77 : Forest := ⟨77, 4, fun i => (g77Y[i]?).getD (0,0), g77C, [[], [32]], g77L, g77I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g77P4n0 : block g77 4 0 1 = true := by decide +kernel
theorem g77B4 : block g77 4 0 1 = true := g77P4n0
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
theorem low77 : Lower true (varsX 77) (graphGoal 77) 5 := lower_forest (g:=g77) (i:=0) (hints:=24578) (before_sound K75 V75) g77G g77T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K77 := extendKnown K75 5 [(77,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V77 : Known true K77 := extend_ok (m:=77) V75 low77 (by decide +kernel)

def g78Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 64 0xabababababababab), (repeatRows 64 0xff000000ff00ff00)),
    ((repeatRows 64 0xcececececececece), (repeatRows 64 0xff00ffff0000)),
    ((repeatRows 64 0xf3f3f3f3f3f3f3f3), (repeatRows 64 0xffff00000000)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 64 0xfcfcfcfcfcfcfcfc), (repeatRows 64 0xffff000000000000))]
def g78C : List ColumnInfo := []
def g78D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g78L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g78D3)
  | _ => emptyPacking
def g78I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g78 : Forest := ⟨78, 3, fun i => (g78Y[i]?).getD (0,0), g78C, [[], [33, 99]], g78L, g78I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78P3n0 : block g78 3 0 1 = true := by decide +kernel
theorem g78B3 : block g78 3 0 1 = true := g78P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78T : checkedTables g78 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g78 0 0 0 = true)
  · exact (rfl : block g78 1 0 0 = true)
  · exact (rfl : block g78 2 0 0 = true)
  · exact g78B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g78G : graphValid g78 (boundsBefore K77) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low78 : Lower true (varsX 78) (graphGoal 78) 4 := lower_forest (g:=g78) (i:=0) (hints:=33560112) (before_sound K77 V77) g78G g78T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K78 := extendKnown K77 4 [(78,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V78 : Known true K78 := extend_ok (m:=78) V77 low78 (by decide +kernel)

def g83Y : Array (Bits × Bits) := #[((repeatRows 63 0x576bb5daed76bb5d), (repeatRows 63 0xff803fe00)),
    ((repeatRows 63 0x65b2d96cb65b2d96), (repeatRows 63 0x7fc0000ffffc0000)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 63 0x79fcfe7f3f9fcfe7), (repeatRows 63 0x1ff000000000)),
    (0x0, 0x0),
    ((repeatRows 63 0x7e3f1f8fc7e3f1f8), (repeatRows 63 0x7fffe00000000000))]
def g83C : List ColumnInfo := [(2,0,81,0,4)]
def g83D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g83L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g83D4)
  | _ => emptyPacking
def g83I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g83 : Forest := ⟨83, 4, fun i => (g83Y[i]?).getD (0,0), g83C, [[], [96]], g83L, g83I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83P4n0 : block g83 4 0 1 = true := by decide +kernel
theorem g83B4 : block g83 4 0 1 = true := g83P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83T : checkedTables g83 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g83 0 0 0 = true)
  · exact (rfl : block g83 1 0 0 = true)
  · exact (rfl : block g83 2 0 0 = true)
  · exact (rfl : block g83 3 0 0 = true)
  · exact g83B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83G : graphValid g83 (boundsBefore K78) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low83 : Lower true (varsX 83) (graphGoal 83) 5 := lower_forest (g:=g83) (i:=0) (hints:=68) (before_sound K78 V78) g83G g83T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K83 := extendKnown K78 5 [(83,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V83 : Known true K83 := extend_ok (m:=83) V78 low83 (by decide +kernel)

def g85Y : Array (Bits × Bits) := #[((repeatRows 55 0x55bab756eadd5b), (repeatRows 55 0x3ff800)),
    (0x0, 0x0),
    ((repeatRows 55 0x66dcdb9b736e6d), (repeatRows 55 0x1ffc00000)),
    (0x0, 0x0),
    ((repeatRows 55 0x78ef1de3bc778e), (repeatRows 55 0xffe00000000)),
    (0x0, 0x0),
    ((repeatRows 55 0x7f0fe1fc3f87f0), (repeatRows 55 0x7ff00000000000))]
def g85C : List ColumnInfo := [(1,0,84,0,4), (4,0,81,0,4), (16,0,69,0,4), (64,0,21,0,4)]
def g85D3 (j : Nat) : Nat := if j = 0 then 0x8028023ea6a1203e11240901 else 0
def g85D4 (j : Nat) : Nat := if j = 0 then 0x6090858702fd0901bd42407e40901 else 0
def g85D5 (j : Nat) : Nat := if j = 0 then 0x1a2047d01 else 0
def g85D6 (j : Nat) : Nat := if j = 0 then 0x7208f else 0
def g85L : Nat → Packing
  | 3 => (2, 3, 2, 0, 0, 5, 0, g85D3)
  | 4 => (3, 2, 2, 0, 0, 5, 0, g85D4)
  | 5 => (1, 1, 2, 0, 0, 1, 0, g85D5)
  | 6 => (1, 0, 2, 0, 0, 1, 0, g85D6)
  | _ => emptyPacking
def g85I : Nat → Nat → Option (Nat × Nat)
  | 4, tag => lookupShort 1 4 1 3 1 0 (fun j => if j=0 then 0xc08 else 0) tag
  | 5, tag => lookupShort 4 12 1 7 2 3 (fun j => if j=0 then 0x8a19e00f00216100100408 else 0) tag
  | 6, tag => lookupShort 3 9 1 8 1 5 (fun j => if j=0 then 0x6003106c00002d02000 else 0) tag
  | _, _ => none
def g85 : Forest := ⟨85, 6, fun i => (g85Y[i]?).getD (0,0), g85C, [[], [100], [66], [66, 100], [98, 100], [98], [32], [32, 100], [32, 66], [32, 66, 100], [32, 98, 100], [32, 98], [64, 66], [64, 66, 100], [64], [64, 100], [64, 98], [64, 98, 100], [96, 98, 100], [96, 98], [96, 100], [96], [96, 66, 100], [96, 66]], g85L, g85I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P3n0 : block g85 3 0 2 = true := by decide +kernel
theorem g85B3 : block g85 3 0 2 = true := g85P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P4n0 : block g85 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P4n2 : block g85 4 2 1 = true := by decide +kernel
theorem g85B4 : block g85 4 0 3 = true := (@block_merge g85 4 0 2 1 g85P4n0 g85P4n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P5n0 : block g85 5 0 1 = true := by decide +kernel
theorem g85B5 : block g85 5 0 1 = true := g85P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g85P6n0 : block g85 6 0 1 = true := by decide +kernel
theorem g85B6 : block g85 6 0 1 = true := g85P6n0
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
theorem g85G : graphValid g85 (boundsBefore K83) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low85 : Lower true (varsX 85) (graphGoal 85) 7 := lower_forest (g:=g85) (i:=0) (hints:=2) (before_sound K83 V83) g85G g85T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K85 := extendKnown K83 7 [(85,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V85 : Known true K85 := extend_ok (m:=85) V83 low85 (by decide +kernel)

def g86Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 63 0x556ab55aad56ab55), (repeatRows 63 0x7fc0000ff803fe00)),
    ((repeatRows 63 0x67b3d9ecf67b3d9e), (repeatRows 63 0xffffc0000)),
    (0x0, 0x0),
    ((repeatRows 63 0x79fcfe7f3f9fcfe7), (repeatRows 63 0x1ff000000000)),
    (0x0, 0x0),
    ((repeatRows 63 0x7e3f1f8fc7e3f1f8), (repeatRows 63 0x7fffe00000000000))]
def g86C : List ColumnInfo := [(2,0,84,0,4)]
def g86D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g86L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g86D4)
  | _ => emptyPacking
def g86I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g86 : Forest := ⟨86, 4, fun i => (g86Y[i]?).getD (0,0), g86C, [[], [98]], g86L, g86I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86P4n0 : block g86 4 0 1 = true := by decide +kernel
theorem g86B4 : block g86 4 0 1 = true := g86P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86T : checkedTables g86 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g86 0 0 0 = true)
  · exact (rfl : block g86 1 0 0 = true)
  · exact (rfl : block g86 2 0 0 = true)
  · exact (rfl : block g86 3 0 0 = true)
  · exact g86B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86G : graphValid g86 (boundsBefore K85) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low86 : Lower true (varsX 86) (graphGoal 86) 5 := lower_forest (g:=g86) (i:=0) (hints:=33621056) (before_sound K85 V85) g86G g86T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K86 := extendKnown K85 5 [(86,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V86 : Known true K86 := extend_ok (m:=86) V85 low86 (by decide +kernel)

def g89Y : Array (Bits × Bits) := #[((repeatRows 63 0x55eaf57abd5eaf57), (repeatRows 63 0xff803fe00)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 63 0x66b359acd66b359a), (repeatRows 63 0x3fe00ffffc0000)),
    ((repeatRows 63 0x78fc7e3f1f8fc7e3), (repeatRows 63 0x3ffff000000000)),
    (0x0, 0x0),
    ((repeatRows 63 0x7f3f9fcfe7f3f9fc), (repeatRows 63 0x7fc0000000000000))]
def g89C : List ColumnInfo := [(8,0,81,0,4)]
def g89D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g89L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g89D4)
  | _ => emptyPacking
def g89I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g89 : Forest := ⟨89, 4, fun i => (g89Y[i]?).getD (0,0), g89C, [[], [64]], g89L, g89I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89P4n0 : block g89 4 0 1 = true := by decide +kernel
theorem g89B4 : block g89 4 0 1 = true := g89P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89T : checkedTables g89 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g89 0 0 0 = true)
  · exact (rfl : block g89 1 0 0 = true)
  · exact (rfl : block g89 2 0 0 = true)
  · exact (rfl : block g89 3 0 0 = true)
  · exact g89B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89G : graphValid g89 (boundsBefore K86) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low89 : Lower true (varsX 89) (graphGoal 89) 5 := lower_forest (g:=g89) (i:=0) (hints:=24580) (before_sound K86 V86) g89G g89T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K89 := extendKnown K86 5 [(89,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V89 : Known true K89 := extend_ok (m:=89) V86 low89 (by decide +kernel)

def g92Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 63 0x55eaf57abd5eaf57), (repeatRows 63 0xff803fe00)),
    ((repeatRows 63 0x66b359acd66b359a), (repeatRows 63 0x3fe00ffffc0000)),
    ((repeatRows 63 0x78fc7e3f1f8fc7e3), (repeatRows 63 0x3ffff000000000)),
    (0x0, 0x0),
    ((repeatRows 63 0x7f3f9fcfe7f3f9fc), (repeatRows 63 0x7fc0000000000000))]
def g92C : List ColumnInfo := [(8,0,84,0,4)]
def g92D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g92L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g92D4)
  | _ => emptyPacking
def g92I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g92 : Forest := ⟨92, 4, fun i => (g92Y[i]?).getD (0,0), g92C, [[], [66]], g92L, g92I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g92P4n0 : block g92 4 0 1 = true := by decide +kernel
theorem g92B4 : block g92 4 0 1 = true := g92P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g92T : checkedTables g92 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g92 0 0 0 = true)
  · exact (rfl : block g92 1 0 0 = true)
  · exact (rfl : block g92 2 0 0 = true)
  · exact (rfl : block g92 3 0 0 = true)
  · exact g92B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g92G : graphValid g92 (boundsBefore K89) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low92 : Lower true (varsX 92) (graphGoal 92) 5 := lower_forest (g:=g92) (i:=0) (hints:=33711104) (before_sound K89 V89) g92G g92T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K92 := extendKnown K89 5 [(92,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V92 : Known true K92 := extend_ok (m:=92) V89 low92 (by decide +kernel)

def g99Y : Array (Bits × Bits) := #[((repeatRows 63 0x576bb5daed76bb5d), (repeatRows 63 0xff803fe00)),
    ((repeatRows 63 0x65b2d96cb65b2d96), (repeatRows 63 0x7fc0000ffffc0000)),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 63 0x79fcfe7f3f9fcfe7), (repeatRows 63 0x1ff000000000)),
    ((repeatRows 63 0x7e3f1f8fc7e3f1f8), (repeatRows 63 0x7fffe00000000000))]
def g99C : List ColumnInfo := [(2,0,97,0,4)]
def g99D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g99L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g99D4)
  | _ => emptyPacking
def g99I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g99 : Forest := ⟨99, 4, fun i => (g99Y[i]?).getD (0,0), g99C, [[], [96]], g99L, g99I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99P4n0 : block g99 4 0 1 = true := by decide +kernel
theorem g99B4 : block g99 4 0 1 = true := g99P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99T : checkedTables g99 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g99 0 0 0 = true)
  · exact (rfl : block g99 1 0 0 = true)
  · exact (rfl : block g99 2 0 0 = true)
  · exact (rfl : block g99 3 0 0 = true)
  · exact g99B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99G : graphValid g99 (boundsBefore K92) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low99 : Lower true (varsX 99) (graphGoal 99) 5 := lower_forest (g:=g99) (i:=0) (hints:=85) (before_sound K92 V92) g99G g99T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K99 := extendKnown K92 5 [(99,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V99 : Known true K99 := extend_ok (m:=99) V92 low99 (by decide +kernel)

def g101Y : Array (Bits × Bits) := #[((repeatRows 60 0xabeafabeafabeaf), (repeatRows 60 0xffc00)),
    (0x0, 0x0),
    ((repeatRows 60 0xcd735cd735cd735), (repeatRows 60 0x3ff003ff00000)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 60 0xf1bc6f1bc6f1bc6), (repeatRows 60 0x3ffffc0000000)),
    ((repeatRows 60 0xfe3f8fe3f8fe3f8), (repeatRows 60 0xffc000000000000))]
def g101C : List ColumnInfo := [(4,0,97,0,4)]
def g101D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g101L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g101D4)
  | _ => emptyPacking
def g101I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g101 : Forest := ⟨101, 4, fun i => (g101Y[i]?).getD (0,0), g101C, [[], [82], [96], [96, 82]], g101L, g101I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P4n0 : block g101 4 0 1 = true := by decide +kernel
theorem g101B4 : block g101 4 0 1 = true := g101P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101T : checkedTables g101 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g101 0 0 0 = true)
  · exact (rfl : block g101 1 0 0 = true)
  · exact (rfl : block g101 2 0 0 = true)
  · exact (rfl : block g101 3 0 0 = true)
  · exact g101B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101G : graphValid g101 (boundsBefore K99) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low101 : Lower true (varsX 101) (graphGoal 101) 5 := lower_forest (g:=g101) (i:=0) (hints:=2) (before_sound K99 V99) g101G g101T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K101 := extendKnown K99 5 [(101,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V101 : Known true K101 := extend_ok (m:=101) V99 low101 (by decide +kernel)

def g102Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 64 0xabababababababab), (repeatRows 64 0xff000000ff00ff00)),
    ((repeatRows 64 0xcececececececece), (repeatRows 64 0xff00ffff0000)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 64 0xf3f3f3f3f3f3f3f3), (repeatRows 64 0xffff00000000)),
    ((repeatRows 64 0xfcfcfcfcfcfcfcfc), (repeatRows 64 0xffff000000000000))]
def g102C : List ColumnInfo := []
def g102D3 (j : Nat) : Nat := if j = 0 then 0xf else 0
def g102L : Nat → Packing
  | 3 => (1, 0, 1, 0, 0, 1, 0, g102D3)
  | _ => emptyPacking
def g102I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g102 : Forest := ⟨102, 3, fun i => (g102Y[i]?).getD (0,0), g102C, [[], [33, 101]], g102L, g102I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g102P3n0 : block g102 3 0 1 = true := by decide +kernel
theorem g102B3 : block g102 3 0 1 = true := g102P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g102T : checkedTables g102 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g102 0 0 0 = true)
  · exact (rfl : block g102 1 0 0 = true)
  · exact (rfl : block g102 2 0 0 = true)
  · exact g102B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g102G : graphValid g102 (boundsBefore K101) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low102 : Lower true (varsX 102) (graphGoal 102) 4 := lower_forest (g:=g102) (i:=0) (hints:=34604624) (before_sound K101 V101) g102G g102T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K102 := extendKnown K101 4 [(102,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V102 : Known true K102 := extend_ok (m:=102) V101 low102 (by decide +kernel)

def g105Y : Array (Bits × Bits) := #[((repeatRows 60 0xab6adab6adab6ad), (repeatRows 60 0xffc00ffc00)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 60 0xcdb36cdb36cdb36), (repeatRows 60 0xfffff00000)),
    (0x0, 0x0),
    ((repeatRows 60 0xf1fc7f1fc7f1fc7), (repeatRows 60 0x3ff0000000000)),
    ((repeatRows 60 0xfe3f8fe3f8fe3f8), (repeatRows 60 0xffc000000000000))]
def g105C : List ColumnInfo := [(1,0,104,0,4)]
def g105D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g105L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g105D4)
  | _ => emptyPacking
def g105I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g105 : Forest := ⟨105, 4, fun i => (g105Y[i]?).getD (0,0), g105C, [[], [101], [48], [48, 101]], g105L, g105I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P4n0 : block g105 4 0 1 = true := by decide +kernel
theorem g105B4 : block g105 4 0 1 = true := g105P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105T : checkedTables g105 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g105 0 0 0 = true)
  · exact (rfl : block g105 1 0 0 = true)
  · exact (rfl : block g105 2 0 0 = true)
  · exact (rfl : block g105 3 0 0 = true)
  · exact g105B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105G : graphValid g105 (boundsBefore K102) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low105 : Lower true (varsX 105) (graphGoal 105) 5 := lower_forest (g:=g105) (i:=0) (hints:=20485) (before_sound K102 V102) g105G g105T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K105 := extendKnown K102 5 [(105,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V105 : Known true K105 := extend_ok (m:=105) V102 low105 (by decide +kernel)

def g106Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 60 0xaaeabaaeabaaeab), (repeatRows 60 0xffc0000000ffc00)),
    (0x0, 0x0),
    ((repeatRows 60 0xcf73dcf73dcf73d), (repeatRows 60 0x3ff00000)),
    (0x0, 0x0),
    ((repeatRows 60 0xf3bcef3bcef3bce), (repeatRows 60 0xffc0000000)),
    ((repeatRows 60 0xfc3f0fc3f0fc3f0), (repeatRows 60 0xfffff0000000000))]
def g106C : List ColumnInfo := [(2,0,104,0,4)]
def g106D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g106L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g106D4)
  | _ => emptyPacking
def g106I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g106 : Forest := ⟨106, 4, fun i => (g106Y[i]?).getD (0,0), g106C, [[], [83], [97], [97, 83]], g106L, g106I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106P4n0 : block g106 4 0 1 = true := by decide +kernel
theorem g106B4 : block g106 4 0 1 = true := g106P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106T : checkedTables g106 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g106 0 0 0 = true)
  · exact (rfl : block g106 1 0 0 = true)
  · exact (rfl : block g106 2 0 0 = true)
  · exact (rfl : block g106 3 0 0 = true)
  · exact g106B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g106G : graphValid g106 (boundsBefore K105) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low106 : Lower true (varsX 106) (graphGoal 106) 5 := lower_forest (g:=g106) (i:=0) (hints:=51384368) (before_sound K105 V105) g106G g106T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K106 := extendKnown K105 5 [(106,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V106 : Known true K106 := extend_ok (m:=106) V105 low106 (by decide +kernel)

def g108Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 63 0x55aad56ab55aad56), (repeatRows 63 0x3fe00ff803fe00)),
    ((repeatRows 63 0x66f379bcde6f379b), (repeatRows 63 0xffffc0000)),
    (0x0, 0x0),
    ((repeatRows 63 0x78fc7e3f1f8fc7e3), (repeatRows 63 0x3ffff000000000)),
    ((repeatRows 63 0x7f3f9fcfe7f3f9fc), (repeatRows 63 0x7fc0000000000000))]
def g108C : List ColumnInfo := [(4,0,104,0,4)]
def g108D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g108L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g108D4)
  | _ => emptyPacking
def g108I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g108 : Forest := ⟨108, 4, fun i => (g108Y[i]?).getD (0,0), g108C, [[], [83]], g108L, g108I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108P4n0 : block g108 4 0 1 = true := by decide +kernel
theorem g108B4 : block g108 4 0 1 = true := g108P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108T : checkedTables g108 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g108 0 0 0 = true)
  · exact (rfl : block g108 1 0 0 = true)
  · exact (rfl : block g108 2 0 0 = true)
  · exact (rfl : block g108 3 0 0 = true)
  · exact g108B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g108G : graphValid g108 (boundsBefore K106) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low108 : Lower true (varsX 108) (graphGoal 108) 5 := lower_forest (g:=g108) (i:=0) (hints:=36722176) (before_sound K106 V106) g108G g108T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K108 := extendKnown K106 5 [(108,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V108 : Known true K108 := extend_ok (m:=108) V106 low108 (by decide +kernel)

def g113Y : Array (Bits × Bits) := #[((repeatRows 55 0x55bab756eadd5b), (repeatRows 55 0x3ff800)),
    (0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 55 0x66dcdb9b736e6d), (repeatRows 55 0x1ffc00000)),
    ((repeatRows 55 0x78ef1de3bc778e), (repeatRows 55 0xffe00000000)),
    ((repeatRows 55 0x7f0fe1fc3f87f0), (repeatRows 55 0x7ff00000000000))]
def g113C : List ColumnInfo := [(1,0,112,0,4), (16,0,97,0,4), (32,0,81,0,4), (64,0,49,0,4)]
def g113D3 (j : Nat) : Nat := if j = 0 then 0x8028023ea6a1203e11240901 else 0
def g113D4 (j : Nat) : Nat := if j = 0 then 0x6090858702fd0901bd42407e40901 else 0
def g113D5 (j : Nat) : Nat := if j = 0 then 0x1a2047d01 else 0
def g113D6 (j : Nat) : Nat := if j = 0 then 0x7208f else 0
def g113L : Nat → Packing
  | 3 => (2, 3, 2, 0, 0, 5, 0, g113D3)
  | 4 => (3, 2, 2, 0, 0, 5, 0, g113D4)
  | 5 => (1, 1, 2, 0, 0, 1, 0, g113D5)
  | 6 => (1, 0, 2, 0, 0, 1, 0, g113D6)
  | _ => emptyPacking
def g113I : Nat → Nat → Option (Nat × Nat)
  | 4, tag => lookupShort 1 5 1 3 1 0 (fun j => if j=0 then 0xe000 else 0) tag
  | 5, tag => lookupShort 4 16 2 7 2 3 (fun j => if j=0 then 0xcae310000000004200024001ae0088 else 0) tag
  | 6, tag => lookupShort 3 9 1 8 1 5 (fun j => if j=0 then 0x636d0000506c60420 else 0) tag
  | _, _ => none
def g113 : Forest := ⟨113, 6, fun i => (g113Y[i]?).getD (0,0), g113C, [[], [101], [84], [84, 101], [100, 101], [100], [64], [64, 101], [64, 84], [64, 84, 101], [64, 100, 101], [64, 100], [80, 84], [80, 84, 101], [80], [80, 101], [80, 100], [80, 100, 101], [96, 100, 101], [96, 100], [96, 101], [96], [96, 84, 101], [96, 84]], g113L, g113I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113P3n0 : block g113 3 0 2 = true := by decide +kernel
theorem g113B3 : block g113 3 0 2 = true := g113P3n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113P4n0 : block g113 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113P4n2 : block g113 4 2 1 = true := by decide +kernel
theorem g113B4 : block g113 4 0 3 = true := (@block_merge g113 4 0 2 1 g113P4n0 g113P4n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113P5n0 : block g113 5 0 1 = true := by decide +kernel
theorem g113B5 : block g113 5 0 1 = true := g113P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113P6n0 : block g113 6 0 1 = true := by decide +kernel
theorem g113B6 : block g113 6 0 1 = true := g113P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113T : checkedTables g113 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g113 0 0 0 = true)
  · exact (rfl : block g113 1 0 0 = true)
  · exact (rfl : block g113 2 0 0 = true)
  · exact g113B3
  · exact g113B4
  · exact g113B5
  · exact g113B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g113G : graphValid g113 (boundsBefore K108) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low113 : Lower true (varsX 113) (graphGoal 113) 7 := lower_forest (g:=g113) (i:=0) (hints:=4) (before_sound K108 V108) g113G g113T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K113 := extendKnown K108 7 [(113,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V113 : Known true K113 := extend_ok (m:=113) V108 low113 (by decide +kernel)

def g114Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 60 0xaaeabaaeabaaeab), (repeatRows 60 0xffc0000000ffc00)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 60 0xcf73dcf73dcf73d), (repeatRows 60 0x3ff00000)),
    ((repeatRows 60 0xf3bcef3bcef3bce), (repeatRows 60 0xffc0000000)),
    ((repeatRows 60 0xfc3f0fc3f0fc3f0), (repeatRows 60 0xfffff0000000000))]
def g114C : List ColumnInfo := [(2,0,112,0,4)]
def g114D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g114L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g114D4)
  | _ => emptyPacking
def g114I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g114 : Forest := ⟨114, 4, fun i => (g114Y[i]?).getD (0,0), g114C, [[], [84], [97], [97, 84]], g114L, g114I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g114P4n0 : block g114 4 0 1 = true := by decide +kernel
theorem g114B4 : block g114 4 0 1 = true := g114P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g114T : checkedTables g114 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g114 0 0 0 = true)
  · exact (rfl : block g114 1 0 0 = true)
  · exact (rfl : block g114 2 0 0 = true)
  · exact (rfl : block g114 3 0 0 = true)
  · exact g114B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g114G : graphValid g114 (boundsBefore K113) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low114 : Lower true (varsX 114) (graphGoal 114) 5 := lower_forest (g:=g114) (i:=0) (hints:=68223040) (before_sound K113 V113) g114G g114T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K114 := extendKnown K113 5 [(114,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V114 : Known true K114 := extend_ok (m:=114) V113 low114 (by decide +kernel)

def g116Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 60 0xab6adab6adab6ad), (repeatRows 60 0x3ff00000ffc00)),
    (0x0, 0x0),
    ((repeatRows 60 0xcdf37cdf37cdf37), (repeatRows 60 0x3ff00000)),
    ((repeatRows 60 0xf1bc6f1bc6f1bc6), (repeatRows 60 0x3ffffc0000000)),
    ((repeatRows 60 0xfe3f8fe3f8fe3f8), (repeatRows 60 0xffc000000000000))]
def g116C : List ColumnInfo := [(4,0,112,0,4)]
def g116D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g116L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g116D4)
  | _ => emptyPacking
def g116I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g116 : Forest := ⟨116, 4, fun i => (g116Y[i]?).getD (0,0), g116C, [[], [100], [82], [82, 100]], g116L, g116I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g116P4n0 : block g116 4 0 1 = true := by decide +kernel
theorem g116B4 : block g116 4 0 1 = true := g116P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g116T : checkedTables g116 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g116 0 0 0 = true)
  · exact (rfl : block g116 1 0 0 = true)
  · exact (rfl : block g116 2 0 0 = true)
  · exact (rfl : block g116 3 0 0 = true)
  · exact g116B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g116G : graphValid g116 (boundsBefore K114) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low116 : Lower true (varsX 116) (graphGoal 116) 5 := lower_forest (g:=g116) (i:=0) (hints:=37880832) (before_sound K114 V114) g116G g116T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K116 := extendKnown K114 5 [(116,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V116 : Known true K116 := extend_ok (m:=116) V114 low116 (by decide +kernel)

def g120Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 60 0xab6adab6adab6ad), (repeatRows 60 0xffc00ffc00)),
    ((repeatRows 60 0xcdb36cdb36cdb36), (repeatRows 60 0xfffff00000)),
    ((repeatRows 60 0xf1fc7f1fc7f1fc7), (repeatRows 60 0x3ff0000000000)),
    ((repeatRows 60 0xfe3f8fe3f8fe3f8), (repeatRows 60 0xffc000000000000))]
def g120C : List ColumnInfo := [(8,0,112,0,4)]
def g120D4 (j : Nat) : Nat := if j = 0 then 0x2f else 0
def g120L : Nat → Packing
  | 4 => (1, 0, 1, 0, 0, 1, 0, g120D4)
  | _ => emptyPacking
def g120I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g120 : Forest := ⟨120, 4, fun i => (g120Y[i]?).getD (0,0), g120C, [[], [101], [67], [67, 101]], g120L, g120I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g120P4n0 : block g120 4 0 1 = true := by decide +kernel
theorem g120B4 : block g120 4 0 1 = true := g120P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g120T : checkedTables g120 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g120 0 0 0 = true)
  · exact (rfl : block g120 1 0 0 = true)
  · exact (rfl : block g120 2 0 0 = true)
  · exact (rfl : block g120 3 0 0 = true)
  · exact g120B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g120G : graphValid g120 (boundsBefore K116) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low120 : Lower true (varsX 120) (graphGoal 120) 5 := lower_forest (g:=g120) (i:=0) (hints:=53825536) (before_sound K116 V116) g120G g120T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K120 := extendKnown K116 5 [(120,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V120 : Known true K120 := extend_ok (m:=120) V116 low120 (by decide +kernel)

def g31Y : Array (Bits × Bits) := #[((repeatRows 231 0x55ab6ead5b756adbab56dd5ab6ead5b756adbab56dd5ab6ead5b756adb), (repeatRows 231 0xfffff8000000000000000fffff800003ffffe00000)),
    ((repeatRows 231 0x66cdbb366dd9b36ecd9b766cdbb366dd9b36ecd9b766cdbb366dd9b36e), (repeatRows 231 0x3ffffe00000ffffffffffc0000000000)),
    ((repeatRows 231 0x78f1cfc78e7e3c73f1e39f8f1cfc78e7e3c73f1e39f8f1cfc78e7e3c73), (repeatRows 231 0x1fffff00000000003ffffffffff000000000000000000000)),
    ((repeatRows 231 0x7f01f3f80f9fc07cfe03e7f01f3f80f9fc07cfe03e7f01f3f80f9fc07c), (repeatRows 231 0x7ffffc00001fffffffffffffffc0000000000000000000000000000000)),
    ((repeatRows 231 0x7ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80), (repeatRows 231 0x7fffffffffe00000000000000000000000000000000000000000000000)),
    (0x0, 0x0),
    (0x0, 0x0)]
def g31C : List ColumnInfo := [(0,8,21,2,5), (1,0,30,0,4), (2,0,21,0,4), (2,8,21,0,4), (4,0,27,0,4), (8,0,23,0,5)]
def g31D4 (j : Nat) : Nat := if j = 0 then 0x5b89504 else 0
def g31D5 (j : Nat) : Nat := if j = 0 then 0xa0120220d140fe04fd04fd02 else 0
def g31D6 (j : Nat) : Nat := if j = 0 then 0x2c68819f else 0
def g31L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g31D4)
  | 5 => (3, 1, 3, 0, 0, 5, 0, g31D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g31D6)
  | _ => emptyPacking
def g31I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x4 else 0) tag
  | 6, tag => lookupShort 3 8 2 5 2 1 (fun j => if j=0 then 0x60275d0420 else 0) tag
  | _, _ => none
def g31 : Forest := ⟨31, 6, fun i => (g31Y[i]?).getD (0,0), g31C, [[], [32]], g31L, g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P4n0 : block g31 4 0 1 = true := by decide +kernel
theorem g31B4 : block g31 4 0 1 = true := g31P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5n0 : block g31 5 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5n2 : block g31 5 2 1 = true := by decide +kernel
theorem g31B5 : block g31 5 0 3 = true := (@block_merge g31 5 0 2 1 g31P5n0 g31P5n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P6n0 : block g31 6 0 1 = true := by decide +kernel
theorem g31B6 : block g31 6 0 1 = true := g31P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact g31B4
  · exact g31B5
  · exact g31B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K120) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 7 := lower_forest (g:=g31) (i:=0) (hints:=4146) (before_sound K120 V120) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K120 7 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V120 low31 (by decide +kernel)

def g47Y : Array (Bits × Bits) := #[((repeatRows 231 0x555b6eaadb7556dbaab6dd55b6eaadb7556dbaab6dd55b6eaadb7556db), (repeatRows 231 0xfffff8000000000000000fffff800003ffffe00000)),
    ((repeatRows 231 0x666dbb336dd99b6eccdb7666dbb336dd99b6eccdb7666dbb336dd99b6e), (repeatRows 231 0x3ffffe00000ffffffffffc0000000000)),
    ((repeatRows 231 0x7871cfc38e7e1c73f0e39f871cfc38e7e1c73f0e39f871cfc38e7e1c73), (repeatRows 231 0x7ffffc00001fffff00000000003ffffffffff000000000000000000000)),
    ((repeatRows 231 0x7f81f3fc0f9fe07cff03e7f81f3fc0f9fe07cff03e7f81f3fc0f9fe07c), (repeatRows 231 0x1fffffffffffffffc0000000000000000000000000000000)),
    (0x0, 0x0),
    ((repeatRows 231 0x7ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80), (repeatRows 231 0x7fffffffffe00000000000000000000000000000000000000000000000)),
    (0x0, 0x0)]
def g47C : List ColumnInfo := [(0,4,42,1,5), (1,0,42,0,4), (1,4,42,0,4), (2,0,45,0,4), (4,0,43,0,5), (8,0,39,0,4)]
def g47D4 (j : Nat) : Nat := if j = 0 then 0x578d514 else 0
def g47D5 (j : Nat) : Nat := if j = 0 then 0x80128260d140fe14fd14fd13 else 0
def g47D6 (j : Nat) : Nat := if j = 0 then 0x2c68819f else 0
def g47L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g47D4)
  | 5 => (3, 1, 3, 0, 0, 5, 0, g47D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g47D6)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x0 else 0) tag
  | 6, tag => lookupShort 3 8 2 5 2 1 (fun j => if j=0 then 0xce2aed030 else 0) tag
  | _, _ => none
def g47 : Forest := ⟨47, 6, fun i => (g47Y[i]?).getD (0,0), g47C, [[], [49]], g47L, g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4n0 : block g47 4 0 1 = true := by decide +kernel
theorem g47B4 : block g47 4 0 1 = true := g47P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5n0 : block g47 5 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5n2 : block g47 5 2 1 = true := by decide +kernel
theorem g47B5 : block g47 5 0 3 = true := (@block_merge g47 5 0 2 1 g47P5n0 g47P5n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6n0 : block g47 6 0 1 = true := by decide +kernel
theorem g47B6 : block g47 6 0 1 = true := g47P6n0
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
def K47 := extendKnown K31 7 [(47,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)

def g55Y : Array (Bits × Bits) := #[((repeatRows 207 0x555b57aab6af556d5eaadabd55b57aab6af556d5eaadabd55b57), (repeatRows 207 0xfffffe000003fffff800000)),
    ((repeatRows 207 0x666d9accdb3599b66b336cd666d9accdb3599b66b336cd666d9a), (repeatRows 207 0x3fffff800000fffffffffffc00000000000)),
    ((repeatRows 207 0x7871e3f0e3c7e1c78fc38f1f871e3f0e3c7e1c78fc38f1f871e3), (repeatRows 207 0x7fffff000000000003fffffffffff00000000000000000000000)),
    (0x0, 0x0),
    ((repeatRows 207 0x7f81fcff03f9fe07f3fc0fe7f81fcff03f9fe07f3fc0fe7f81fc), (repeatRows 207 0x1fffffc0000000000000000000000000000000000)),
    ((repeatRows 207 0x7ffe00fffc01fff803fff007ffe00fffc01fff803fff007ffe00), (repeatRows 207 0x7ffffffffffe0000000000000000000000000000000000000000)),
    (0x0, 0x0)]
def g55C : List ColumnInfo := [(1,0,54,0,5), (2,0,53,0,5), (4,0,51,0,5), (32,0,23,0,5)]
def g55D6 (j : Nat) : Nat := if j = 0 then 0xe411f else 0
def g55L : Nat → Packing
  | 6 => (1, 0, 2, 0, 0, 1, 0, g55D6)
  | _ => emptyPacking
def g55I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g55 : Forest := ⟨55, 6, fun i => (g55Y[i]?).getD (0,0), g55C, [[], [80, 33]], g55L, g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P6n0 : block g55 6 0 1 = true := by decide +kernel
theorem g55B6 : block g55 6 0 1 = true := g55P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact (rfl : block g55 4 0 0 = true)
  · exact (rfl : block g55 5 0 0 = true)
  · exact g55B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 7 := lower_forest (g:=g55) (i:=0) (hints:=66) (before_sound K47 V47) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K47 7 [(55,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V47 low55 (by decide +kernel)

def g59Y : Array (Bits × Bits) := #[((repeatRows 207 0x5555b6aaab6d5556daaaadb5555b6aaab6d5556daaaadb5555b6), (repeatRows 207 0x3fffff800000fffffe000003fffff800000)),
    ((repeatRows 207 0x6666dbcccdb7999b6f3336de666dbcccdb7999b6f3336de666db), (repeatRows 207 0xfffffffffffc00000000000)),
    (0x0, 0x0),
    ((repeatRows 207 0x7878e3f0f1c7e1e38fc3c71f878e3f0f1c7e1e38fc3c71f878e3), (repeatRows 207 0xfffffe000003fffffffffff00000000000000000000000)),
    ((repeatRows 207 0x7f80fcff01f9fe03f3fc07e7f80fcff01f9fe03f3fc07e7f80fc), (repeatRows 207 0xfffffffffffc0000000000000000000000000000000000)),
    ((repeatRows 207 0x7fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00), (repeatRows 207 0x7fffff0000000000000000000000000000000000000000000000)),
    (0x0, 0x0)]
def g59C : List ColumnInfo := [(1,0,58,0,5), (2,0,57,0,5), (8,0,51,0,5), (16,0,43,0,5)]
def g59D6 (j : Nat) : Nat := if j = 0 then 0xe411f else 0
def g59L : Nat → Packing
  | 6 => (1, 0, 2, 0, 0, 1, 0, g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g59 : Forest := ⟨59, 6, fun i => (g59Y[i]?).getD (0,0), g59C, [[], [48, 65]], g59L, g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6n0 : block g59 6 0 1 = true := by decide +kernel
theorem g59B6 : block g59 6 0 1 = true := g59P6n0
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
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=4148) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 7 [(59,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)

def g61Y : Array (Bits × Bits) := #[((repeatRows 220 0xaaaedeaabb7aaaedeaabb7aaaedeaabb7aaaedeaabb7aaaedeaabb7), (repeatRows 220 0x3fffff00000000000fffffc00000)),
    (0x0, 0x0),
    ((repeatRows 220 0xcccb6f332dbcccb6f332dbcccb6f332dbcccb6f332dbcccb6f332db), (repeatRows 220 0xfffffc0000000000000000fffffc00000000003fffff00000000000)),
    ((repeatRows 220 0xf0f38bc3ce2f0f38bc3ce2f0f38bc3ce2f0f38bc3ce2f0f38bc3ce2), (repeatRows 220 0xfffffc00000ffffffffffffffffc0000000000000000)),
    ((repeatRows 220 0xff03f3fc0fcff03f3fc0fcff03f3fc0fcff03f3fc0fcff03f3fc0fc), (repeatRows 220 0xfffffffffff000000000000000000000000000000000)),
    ((repeatRows 220 0xfffc03fff00fffc03fff00fffc03fff00fffc03fff00fffc03fff00), (repeatRows 220 0xfffffffffff00000000000000000000000000000000000000000000)),
    (0x0, 0x0)]
def g61C : List ColumnInfo := [(0,8,21,32,5), (1,0,60,0,4), (4,0,57,0,5), (8,0,53,0,5), (16,0,45,0,4), (32,0,21,0,4), (32,8,21,0,4)]
def g61D4 (j : Nat) : Nat := if j = 0 then 0x5d85503 else 0
def g61D5 (j : Nat) : Nat := if j = 0 then 0x190808fd03 else 0
def g61D6 (j : Nat) : Nat := if j = 0 then 0x1ac6881df else 0
def g61L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g61D4)
  | 5 => (1, 1, 3, 0, 0, 1, 0, g61D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g61D6)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x60 else 0) tag
  | 6, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x40 else 0) tag
  | _, _ => none
def g61 : Forest := ⟨61, 6, fun i => (g61Y[i]?).getD (0,0), g61C, [[], [64]], g61L, g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P4n0 : block g61 4 0 1 = true := by decide +kernel
theorem g61B4 : block g61 4 0 1 = true := g61P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5n0 : block g61 5 0 1 = true := by decide +kernel
theorem g61B5 : block g61 5 0 1 = true := g61P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6n0 : block g61 6 0 1 = true := by decide +kernel
theorem g61B6 : block g61 6 0 1 = true := g61P6n0
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
theorem low61 : Lower true (varsX 61) (graphGoal 61) 7 := lower_forest (g:=g61) (i:=0) (hints:=20482) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 7 [(61,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)

def g62Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 220 0xaaaedeaabb7aaaedeaabb7aaaedeaabb7aaaedeaabb7aaaedeaabb7), (repeatRows 220 0xfffffc00000fffffc00000)),
    ((repeatRows 220 0xcccb6b332dacccb6b332dacccb6b332dacccb6b332dacccb6b332da), (repeatRows 220 0xfffffc0000000000000000fffffc00000fffffffffff00000000000)),
    ((repeatRows 220 0xf0f38fc3ce3f0f38fc3ce3f0f38fc3ce3f0f38fc3ce3f0f38fc3ce3), (repeatRows 220 0xfffffc00000fffffffffff0000000000000000000000)),
    ((repeatRows 220 0xff03f3fc0fcff03f3fc0fcff03f3fc0fcff03f3fc0fcff03f3fc0fc), (repeatRows 220 0xfffffffffff000000000000000000000000000000000)),
    ((repeatRows 220 0xfffc03fff00fffc03fff00fffc03fff00fffc03fff00fffc03fff00), (repeatRows 220 0xfffffffffff00000000000000000000000000000000000000000000)),
    (0x0, 0x0)]
def g62C : List ColumnInfo := [(0,4,42,16,5), (2,0,60,0,4), (4,0,58,0,5), (8,0,54,0,5), (16,0,42,0,4), (16,4,42,0,4), (32,0,30,0,4)]
def g62D4 (j : Nat) : Nat := if j = 0 then 0x5b89504 else 0
def g62D5 (j : Nat) : Nat := if j = 0 then 0x190808fd04 else 0
def g62D6 (j : Nat) : Nat := if j = 0 then 0x1ac6881df else 0
def g62L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g62D4)
  | 5 => (1, 1, 3, 0, 0, 1, 0, g62D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g62D6)
  | _ => emptyPacking
def g62I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x60 else 0) tag
  | 6, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x40 else 0) tag
  | _, _ => none
def g62 : Forest := ⟨62, 6, fun i => (g62Y[i]?).getD (0,0), g62C, [[], [81]], g62L, g62I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P4n0 : block g62 4 0 1 = true := by decide +kernel
theorem g62B4 : block g62 4 0 1 = true := g62P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P5n0 : block g62 5 0 1 = true := by decide +kernel
theorem g62B5 : block g62 5 0 1 = true := g62P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P6n0 : block g62 6 0 1 = true := by decide +kernel
theorem g62B6 : block g62 6 0 1 = true := g62P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62T : checkedTables g62 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g62 0 0 0 = true)
  · exact (rfl : block g62 1 0 0 = true)
  · exact (rfl : block g62 2 0 0 = true)
  · exact (rfl : block g62 3 0 0 = true)
  · exact g62B4
  · exact g62B5
  · exact g62B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62G : graphValid g62 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low62 : Lower true (varsX 62) (graphGoal 62) 7 := lower_forest (g:=g62) (i:=0) (hints:=1119280) (before_sound K61 V61) g62G g62T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K62 := extendKnown K61 7 [(62,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V62 : Known true K62 := extend_ok (m:=62) V61 low62 (by decide +kernel)

def g79Y : Array (Bits × Bits) := #[((repeatRows 231 0x55576eaabb7555dbaaaedd5576eaabb7555dbaaaedd5576eaabb7555db), (repeatRows 231 0xfffff8000000000000000fffff800003ffffe00000)),
    ((repeatRows 231 0x6665bb332dd9996ecccb76665bb332dd9996ecccb76665bb332dd9996e), (repeatRows 231 0x7ffffc000000000000000000003ffffe00000ffffffffffc0000000000)),
    ((repeatRows 231 0x7879cfc3ce7e1e73f0f39f879cfc3ce7e1e73f0f39f879cfc3ce7e1e73), (repeatRows 231 0x1fffff00000000003ffffffffff000000000000000000000)),
    ((repeatRows 231 0x7f81f3fc0f9fe07cff03e7f81f3fc0f9fe07cff03e7f81f3fc0f9fe07c), (repeatRows 231 0x1fffffffffffffffc0000000000000000000000000000000)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 231 0x7ffe03fff01fff80fffc07ffe03fff01fff80fffc07ffe03fff01fff80), (repeatRows 231 0x7fffffffffe00000000000000000000000000000000000000000000000))]
def g79C : List ColumnInfo := [(0,2,69,8,5), (1,0,78,0,4), (2,0,77,0,5), (4,0,75,0,4), (8,0,69,0,4), (8,2,69,0,4)]
def g79D4 (j : Nat) : Nat := if j = 0 then 0x5b89504 else 0
def g79D5 (j : Nat) : Nat := if j = 0 then 0x40118220d140fe04fd04fd02 else 0
def g79D6 (j : Nat) : Nat := if j = 0 then 0x2c68819f else 0
def g79L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g79D4)
  | 5 => (3, 1, 3, 0, 0, 5, 0, g79D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g79D6)
  | _ => emptyPacking
def g79I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x40 else 0) tag
  | 6, tag => lookupShort 3 9 1 5 2 1 (fun j => if j=0 then 0x301200281502 else 0) tag
  | _, _ => none
def g79 : Forest := ⟨79, 6, fun i => (g79Y[i]?).getD (0,0), g79C, [[], [32]], g79L, g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P4n0 : block g79 4 0 1 = true := by decide +kernel
theorem g79B4 : block g79 4 0 1 = true := g79P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5n0 : block g79 5 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P5n2 : block g79 5 2 1 = true := by decide +kernel
theorem g79B5 : block g79 5 0 3 = true := (@block_merge g79 5 0 2 1 g79P5n0 g79P5n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P6n0 : block g79 6 0 1 = true := by decide +kernel
theorem g79B6 : block g79 6 0 1 = true := g79P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g79 0 0 0 = true)
  · exact (rfl : block g79 1 0 0 = true)
  · exact (rfl : block g79 2 0 0 = true)
  · exact (rfl : block g79 3 0 0 = true)
  · exact g79B4
  · exact g79B5
  · exact g79B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K62) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 7 := lower_forest (g:=g79) (i:=0) (hints:=4146) (before_sound K62 V62) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K62 7 [(79,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V62 low79 (by decide +kernel)

def g87Y : Array (Bits × Bits) := #[((repeatRows 207 0x555757aaaeaf555d5eaababd55757aaaeaf555d5eaababd55757), (repeatRows 207 0xfffffe000003fffff800000)),
    ((repeatRows 207 0x66659acccb3599966b332cd66659acccb3599966b332cd66659a), (repeatRows 207 0x7fffff000000000003fffff800000fffffffffffc00000000000)),
    ((repeatRows 207 0x7879e3f0f3c7e1e78fc3cf1f879e3f0f3c7e1e78fc3cf1f879e3), (repeatRows 207 0x3fffffffffff00000000000000000000000)),
    (0x0, 0x0),
    ((repeatRows 207 0x7f81fcff03f9fe07f3fc0fe7f81fcff03f9fe07f3fc0fe7f81fc), (repeatRows 207 0x1fffffc0000000000000000000000000000000000)),
    (0x0, 0x0),
    ((repeatRows 207 0x7ffe00fffc01fff803fff007ffe00fffc01fff803fff007ffe00), (repeatRows 207 0x7ffffffffffe0000000000000000000000000000000000000000))]
def g87C : List ColumnInfo := [(2,0,85,0,7)]
def g87D7 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g87L : Nat → Packing
  | 7 => (1, 0, 1, 0, 0, 1, 0, g87D7)
  | _ => emptyPacking
def g87I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g87 : Forest := ⟨87, 7, fun i => (g87Y[i]?).getD (0,0), g87C, [[], [98], [32], [32, 98], [96, 98], [96]], g87L, g87I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g87P7n0 : block g87 7 0 1 = true := by decide +kernel
theorem g87B7 : block g87 7 0 1 = true := g87P7n0
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
theorem g87G : graphValid g87 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 8 := lower_forest (g:=g87) (i:=0) (hints:=66) (before_sound K79 V79) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K79 8 [(87,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V79 low87 (by decide +kernel)

def g91Y : Array (Bits × Bits) := #[((repeatRows 220 0xaaaedaaabb6aaaedaaabb6aaaedaaabb6aaaedaaabb6aaaedaaabb6), (repeatRows 220 0xfffffc00000fffffc00000fffffc00000)),
    ((repeatRows 220 0xcccb6f332dbcccb6f332dbcccb6f332dbcccb6f332dbcccb6f332db), (repeatRows 220 0xfffffc000000000000000000000000000fffffffffff00000000000)),
    (0x0, 0x0),
    ((repeatRows 220 0xf0f38fc3ce3f0f38fc3ce3f0f38fc3ce3f0f38fc3ce3f0f38fc3ce3), (repeatRows 220 0xfffffc00000fffffffffff0000000000000000000000)),
    ((repeatRows 220 0xff03f3fc0fcff03f3fc0fcff03f3fc0fcff03f3fc0fcff03f3fc0fc), (repeatRows 220 0xfffffffffff000000000000000000000000000000000)),
    (0x0, 0x0),
    ((repeatRows 220 0xfffc03fff00fffc03fff00fffc03fff00fffc03fff00fffc03fff00), (repeatRows 220 0xfffffffffff00000000000000000000000000000000000000000000))]
def g91C : List ColumnInfo := [(2,0,89,0,5)]
def g91D5 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g91L : Nat → Packing
  | 5 => (1, 0, 1, 0, 0, 1, 0, g91D5)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g91 : Forest := ⟨91, 5, fun i => (g91Y[i]?).getD (0,0), g91C, [[], [49, 100]], g91L, g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5n0 : block g91 5 0 1 = true := by decide +kernel
theorem g91B5 : block g91 5 0 1 = true := g91P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact (rfl : block g91 4 0 0 = true)
  · exact g91B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 6 := lower_forest (g:=g91) (i:=0) (hints:=4148) (before_sound K87 V87) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K87 6 [(91,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V87 low91 (by decide +kernel)

def g93Y : Array (Bits × Bits) := #[((repeatRows 207 0x5555b7aaab6f5556deaaadbd555b7aaab6f5556deaaadbd555b7), (repeatRows 207 0x7fffff000000000003fffff800000)),
    (0x0, 0x0),
    ((repeatRows 207 0x6666dbcccdb7999b6f3336de666dbcccdb7999b6f3336de666db), (repeatRows 207 0x3fffff800000000001fffffc00000000000)),
    ((repeatRows 207 0x7878e2f0f1c5e1e38bc3c717878e2f0f1c5e1e38bc3c717878e2), (repeatRows 207 0xfffffe000003ffffffffffffffffe00000000000000000)),
    ((repeatRows 207 0x7f80fcff01f9fe03f3fc07e7f80fcff01f9fe03f3fc07e7f80fc), (repeatRows 207 0xfffffffffffc0000000000000000000000000000000000)),
    (0x0, 0x0),
    ((repeatRows 207 0x7fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00), (repeatRows 207 0x7fffff0000000000000000000000000000000000000000000000))]
def g93C : List ColumnInfo := [(8,0,85,0,7)]
def g93D7 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g93L : Nat → Packing
  | 7 => (1, 0, 1, 0, 0, 1, 0, g93D7)
  | _ => emptyPacking
def g93I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g93 : Forest := ⟨93, 7, fun i => (g93Y[i]?).getD (0,0), g93C, [[], [66], [32], [32, 66], [64, 66], [64]], g93L, g93I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93P7n0 : block g93 7 0 1 = true := by decide +kernel
theorem g93B7 : block g93 7 0 1 = true := g93P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93T : checkedTables g93 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g93 0 0 0 = true)
  · exact (rfl : block g93 1 0 0 = true)
  · exact (rfl : block g93 2 0 0 = true)
  · exact (rfl : block g93 3 0 0 = true)
  · exact (rfl : block g93 4 0 0 = true)
  · exact (rfl : block g93 5 0 0 = true)
  · exact (rfl : block g93 6 0 0 = true)
  · exact g93B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g93G : graphValid g93 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low93 : Lower true (varsX 93) (graphGoal 93) 8 := lower_forest (g:=g93) (i:=0) (hints:=24578) (before_sound K91 V91) g93G g93T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K93 := extendKnown K91 8 [(93,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V93 : Known true K93 := extend_ok (m:=93) V91 low93 (by decide +kernel)

def g103Y : Array (Bits × Bits) := #[((repeatRows 220 0xaaaedeaabb7aaaedeaabb7aaaedeaabb7aaaedeaabb7aaaedeaabb7), (repeatRows 220 0xfffffc00000fffffc00000)),
    ((repeatRows 220 0xcccb6b332dacccb6b332dacccb6b332dacccb6b332dacccb6b332da), (repeatRows 220 0xfffffc0000000000000000fffffc00000fffffffffff00000000000)),
    ((repeatRows 220 0xf0f38fc3ce3f0f38fc3ce3f0f38fc3ce3f0f38fc3ce3f0f38fc3ce3), (repeatRows 220 0xfffffc00000fffffffffff0000000000000000000000)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 220 0xff03f3fc0fcff03f3fc0fcff03f3fc0fcff03f3fc0fcff03f3fc0fc), (repeatRows 220 0xfffffffffff000000000000000000000000000000000)),
    ((repeatRows 220 0xfffc03fff00fffc03fff00fffc03fff00fffc03fff00fffc03fff00), (repeatRows 220 0xfffffffffff00000000000000000000000000000000000000000000))]
def g103C : List ColumnInfo := [(0,2,69,32,5), (1,0,102,0,4), (2,0,101,0,5), (4,0,99,0,5), (32,0,69,0,4), (32,2,69,0,4), (64,0,39,0,4)]
def g103D4 (j : Nat) : Nat := if j = 0 then 0x5b89504 else 0
def g103D5 (j : Nat) : Nat := if j = 0 then 0x190808fd04 else 0
def g103D6 (j : Nat) : Nat := if j = 0 then 0x1ac6881df else 0
def g103L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g103D4)
  | 5 => (1, 1, 3, 0, 0, 1, 0, g103D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g103D6)
  | _ => emptyPacking
def g103I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0xc else 0) tag
  | 6, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x8 else 0) tag
  | _, _ => none
def g103 : Forest := ⟨103, 6, fun i => (g103Y[i]?).getD (0,0), g103C, [[], [96]], g103L, g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P4n0 : block g103 4 0 1 = true := by decide +kernel
theorem g103B4 : block g103 4 0 1 = true := g103P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P5n0 : block g103 5 0 1 = true := by decide +kernel
theorem g103B5 : block g103 5 0 1 = true := g103P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P6n0 : block g103 6 0 1 = true := by decide +kernel
theorem g103B6 : block g103 6 0 1 = true := g103P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact g103B4
  · exact g103B5
  · exact g103B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K93) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 7 := lower_forest (g:=g103) (i:=0) (hints:=82) (before_sound K93 V93) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K93 7 [(103,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V93 low103 (by decide +kernel)

def g107Y : Array (Bits × Bits) := #[((repeatRows 207 0x555756aaaead555d5aaabab555756aaaead555d5aaabab555756), (repeatRows 207 0x3fffff800000fffffe000003fffff800000)),
    ((repeatRows 207 0x66659bcccb3799966f332cde6659bcccb3799966f332cde6659b), (repeatRows 207 0x7fffff00000000000000000000000fffffffffffc00000000000)),
    (0x0, 0x0),
    ((repeatRows 207 0x7879e3f0f3c7e1e78fc3cf1f879e3f0f3c7e1e78fc3cf1f879e3), (repeatRows 207 0x3fffffffffff00000000000000000000000)),
    (0x0, 0x0),
    ((repeatRows 207 0x7f81fcff03f9fe07f3fc0fe7f81fcff03f9fe07f3fc0fe7f81fc), (repeatRows 207 0x1fffffc0000000000000000000000000000000000)),
    ((repeatRows 207 0x7ffe00fffc01fff803fff007ffe00fffc01fff803fff007ffe00), (repeatRows 207 0x7ffffffffffe0000000000000000000000000000000000000000))]
def g107C : List ColumnInfo := [(1,0,106,0,5), (2,0,105,0,5), (8,0,99,0,5), (64,0,43,0,5)]
def g107D6 (j : Nat) : Nat := if j = 0 then 0xe411f else 0
def g107L : Nat → Packing
  | 6 => (1, 0, 2, 0, 0, 1, 0, g107D6)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g107 : Forest := ⟨107, 6, fun i => (g107Y[i]?).getD (0,0), g107C, [[], [16, 99]], g107L, g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P6n0 : block g107 6 0 1 = true := by decide +kernel
theorem g107B6 : block g107 6 0 1 = true := g107P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact (rfl : block g107 4 0 0 = true)
  · exact (rfl : block g107 5 0 0 = true)
  · exact g107B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=4149) (before_sound K103 V103) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K103 7 [(107,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V103 low107 (by decide +kernel)

def g109Y : Array (Bits × Bits) := #[((repeatRows 207 0x5555afaaab5f5556beaaad7d555afaaab5f5556beaaad7d555af), (repeatRows 207 0x7fffff000000000003fffff800000)),
    (0x0, 0x0),
    ((repeatRows 207 0x6666cbcccd97999b2f33365e666cbcccd97999b2f33365e666cb), (repeatRows 207 0xfffffe000003fffff800000000001fffffc00000000000)),
    ((repeatRows 207 0x7878f2f0f1e5e1e3cbc3c797878f2f0f1e5e1e3cbc3c797878f2), (repeatRows 207 0x3ffffffffffffffffe00000000000000000)),
    (0x0, 0x0),
    ((repeatRows 207 0x7f80fcff01f9fe03f3fc07e7f80fcff01f9fe03f3fc07e7f80fc), (repeatRows 207 0xfffffffffffc0000000000000000000000000000000000)),
    ((repeatRows 207 0x7fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00), (repeatRows 207 0x7fffff0000000000000000000000000000000000000000000000))]
def g109C : List ColumnInfo := [(1,0,108,0,5), (4,0,105,0,5), (8,0,101,0,5), (32,0,77,0,5)]
def g109D6 (j : Nat) : Nat := if j = 0 then 0xe411f else 0
def g109L : Nat → Packing
  | 6 => (1, 0, 2, 0, 0, 1, 0, g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g109 : Forest := ⟨109, 6, fun i => (g109Y[i]?).getD (0,0), g109C, [[], [80, 50]], g109L, g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6n0 : block g109 6 0 1 = true := by decide +kernel
theorem g109B6 : block g109 6 0 1 = true := g109P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0 = true)
  · exact (rfl : block g109 1 0 0 = true)
  · exact (rfl : block g109 2 0 0 = true)
  · exact (rfl : block g109 3 0 0 = true)
  · exact (rfl : block g109 4 0 0 = true)
  · exact (rfl : block g109 5 0 0 = true)
  · exact g109B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=20482) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 7 [(109,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)

def g110Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 220 0xaaaabeaaaafaaaabeaaaafaaaabeaaaafaaaabeaaaafaaaabeaaaaf), (repeatRows 220 0xfffffc000000000000000000000000000fffffc00000fffffc00000)),
    ((repeatRows 220 0xcccf2b333cacccf2b333cacccf2b333cacccf2b333cacccf2b333ca), (repeatRows 220 0xfffffc00000fffffc00000fffffffffff00000000000)),
    ((repeatRows 220 0xf0f3cfc3cf3f0f3cfc3cf3f0f3cfc3cf3f0f3cfc3cf3f0f3cfc3cf3), (repeatRows 220 0xfffffffffff0000000000000000000000)),
    (0x0, 0x0),
    ((repeatRows 220 0xff03f3fc0fcff03f3fc0fcff03f3fc0fcff03f3fc0fcff03f3fc0fc), (repeatRows 220 0xfffffffffff000000000000000000000000000000000)),
    ((repeatRows 220 0xfffc03fff00fffc03fff00fffc03fff00fffc03fff00fffc03fff00), (repeatRows 220 0xfffffffffff00000000000000000000000000000000000000000000))]
def g110C : List ColumnInfo := [(0,4,42,64,5), (2,0,108,0,5), (4,0,106,0,5), (8,0,102,0,4), (32,0,78,0,4), (64,0,42,0,4), (64,4,42,0,4)]
def g110D4 (j : Nat) : Nat := if j = 0 then 0x5e81523 else 0
def g110D5 (j : Nat) : Nat := if j = 0 then 0x190808fd23 else 0
def g110D6 (j : Nat) : Nat := if j = 0 then 0x1ac6881df else 0
def g110L : Nat → Packing
  | 4 => (1, 2, 3, 0, 0, 1, 0, g110D4)
  | 5 => (1, 1, 3, 0, 0, 1, 0, g110D5)
  | 6 => (1, 0, 3, 0, 0, 1, 0, g110D6)
  | _ => emptyPacking
def g110I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x4 else 0) tag
  | 6, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x20 else 0) tag
  | _, _ => none
def g110 : Forest := ⟨110, 6, fun i => (g110Y[i]?).getD (0,0), g110C, [[], [83]], g110L, g110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P4n0 : block g110 4 0 1 = true := by decide +kernel
theorem g110B4 : block g110 4 0 1 = true := g110P4n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P5n0 : block g110 5 0 1 = true := by decide +kernel
theorem g110B5 : block g110 5 0 1 = true := g110P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P6n0 : block g110 6 0 1 = true := by decide +kernel
theorem g110B6 : block g110 6 0 1 = true := g110P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110T : checkedTables g110 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g110 0 0 0 = true)
  · exact (rfl : block g110 1 0 0 = true)
  · exact (rfl : block g110 2 0 0 = true)
  · exact (rfl : block g110 3 0 0 = true)
  · exact g110B4
  · exact g110B5
  · exact g110B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110G : graphValid g110 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low110 : Lower true (varsX 110) (graphGoal 110) 7 := lower_forest (g:=g110) (i:=0) (hints:=34608688) (before_sound K109 V109) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K110 := extendKnown K109 7 [(110,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V110 : Known true K110 := extend_ok (m:=110) V109 low110 (by decide +kernel)

def g115Y : Array (Bits × Bits) := #[((repeatRows 192 0xaaaeadaaaeadaaaeadaaaeadaaaeadaaaeadaaaeadaaaead), (repeatRows 192 0xffffff000000ffffff000000)),
    ((repeatRows 192 0xcccb36cccb36cccb36cccb36cccb36cccb36cccb36cccb36), (repeatRows 192 0xffffff000000000000000000ffffffffffff000000000000)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 192 0xf0f3c7f0f3c7f0f3c7f0f3c7f0f3c7f0f3c7f0f3c7f0f3c7), (repeatRows 192 0xffffff000000000000000000000000)),
    ((repeatRows 192 0xff03f8ff03f8ff03f8ff03f8ff03f8ff03f8ff03f8ff03f8), (repeatRows 192 0xffffff000000000000000000000000000000)),
    ((repeatRows 192 0xfffc00fffc00fffc00fffc00fffc00fffc00fffc00fffc00), (repeatRows 192 0xffffffffffff000000000000000000000000000000000000))]
def g115C : List ColumnInfo := [(2,0,113,0,7)]
def g115D7 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g115L : Nat → Packing
  | 7 => (1, 0, 1, 0, 0, 1, 0, g115D7)
  | _ => emptyPacking
def g115I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g115 : Forest := ⟨115, 7, fun i => (g115Y[i]?).getD (0,0), g115C, [[], [84], [96], [96, 84]], g115L, g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P7n0 : block g115 7 0 1 = true := by decide +kernel
theorem g115B7 : block g115 7 0 1 = true := g115P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g115 0 0 0 = true)
  · exact (rfl : block g115 1 0 0 = true)
  · exact (rfl : block g115 2 0 0 = true)
  · exact (rfl : block g115 3 0 0 = true)
  · exact (rfl : block g115 4 0 0 = true)
  · exact (rfl : block g115 5 0 0 = true)
  · exact (rfl : block g115 6 0 0 = true)
  · exact g115B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 8 := lower_forest (g:=g115) (i:=0) (hints:=68) (before_sound K110 V110) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K110 8 [(115,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V110 low115 (by decide +kernel)

def g117Y : Array (Bits × Bits) := #[((repeatRows 175 0x5555aeeaaad775556bbaaab5dd555aeeaaad775556bb), (repeatRows 175 0x3fffffe000000)),
    (0x0, 0x0),
    ((repeatRows 175 0x6666cb733365b999b2dcccd96e666cb733365b999b2d), (repeatRows 175 0x3fffffe0000000000007fffffc000000000000)),
    (0x0, 0x0),
    ((repeatRows 175 0x7878f3bc3c79de1e3cef0f1e77878f3bc3c79de1e3ce), (repeatRows 175 0xffffff8000000000000000000)),
    ((repeatRows 175 0x7f80fc3fc07e1fe03f0ff01f87f80fc3fc07e1fe03f0), (repeatRows 175 0x3ffffffffffff0000000000000000000000000)),
    ((repeatRows 175 0x7fff003fff801fffc00fffe007fff003fff801fffc00), (repeatRows 175 0x7fffffc0000000000000000000000000000000000000))]
def g117C : List ColumnInfo := [(4,0,113,0,7)]
def g117D7 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g117L : Nat → Packing
  | 7 => (1, 0, 1, 0, 0, 1, 0, g117D7)
  | _ => emptyPacking
def g117I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g117 : Forest := ⟨117, 7, fun i => (g117Y[i]?).getD (0,0), g117C, [[], [100], [82], [82, 100], [64], [64, 100], [64, 82], [64, 82, 100], [96, 100], [96], [96, 82, 100], [96, 82]], g117L, g117I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117P7n0 : block g117 7 0 1 = true := by decide +kernel
theorem g117B7 : block g117 7 0 1 = true := g117P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117T : checkedTables g117 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g117 0 0 0 = true)
  · exact (rfl : block g117 1 0 0 = true)
  · exact (rfl : block g117 2 0 0 = true)
  · exact (rfl : block g117 3 0 0 = true)
  · exact (rfl : block g117 4 0 0 = true)
  · exact (rfl : block g117 5 0 0 = true)
  · exact (rfl : block g117 6 0 0 = true)
  · exact g117B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g117G : graphValid g117 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low117 : Lower true (varsX 117) (graphGoal 117) 8 := lower_forest (g:=g117) (i:=0) (hints:=2) (before_sound K115 V115) g117G g117T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K117 := extendKnown K115 8 [(117,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V117 : Known true K117 := extend_ok (m:=117) V115 low117 (by decide +kernel)

def g118Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 207 0x55555daaaabb555576aaaaed5555daaaabb555576aaaaed5555d), (repeatRows 207 0x7fffff00000000000000000000000fffffe000003fffff800000)),
    ((repeatRows 207 0x666796cccf2d999e5b333cb666796cccf2d999e5b333cb666796), (repeatRows 207 0x1fffffc00000000000fffffffffffc00000000000)),
    (0x0, 0x0),
    ((repeatRows 207 0x7879e7f0f3cfe1e79fc3cf3f879e7f0f3cfe1e79fc3cf3f879e7), (repeatRows 207 0x7fffff00000000000000000000000)),
    ((repeatRows 207 0x7f81f8ff03f1fe07e3fc0fc7f81f8ff03f1fe07e3fc0fc7f81f8), (repeatRows 207 0x1fffffffffff80000000000000000000000000000)),
    ((repeatRows 207 0x7ffe00fffc01fff803fff007ffe00fffc01fff803fff007ffe00), (repeatRows 207 0x7ffffffffffe0000000000000000000000000000000000000000))]
def g118C : List ColumnInfo := [(2,0,116,0,5), (4,0,114,0,5), (32,0,86,0,5), (64,0,54,0,5)]
def g118D6 (j : Nat) : Nat := if j = 0 then 0xe411f else 0
def g118L : Nat → Packing
  | 6 => (1, 0, 2, 0, 0, 1, 0, g118D6)
  | _ => emptyPacking
def g118I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g118 : Forest := ⟨118, 6, fun i => (g118Y[i]?).getD (0,0), g118C, [[], [33, 101]], g118L, g118I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118P6n0 : block g118 6 0 1 = true := by decide +kernel
theorem g118B6 : block g118 6 0 1 = true := g118P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118T : checkedTables g118 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g118 0 0 0 = true)
  · exact (rfl : block g118 1 0 0 = true)
  · exact (rfl : block g118 2 0 0 = true)
  · exact (rfl : block g118 3 0 0 = true)
  · exact (rfl : block g118 4 0 0 = true)
  · exact (rfl : block g118 5 0 0 = true)
  · exact g118B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g118G : graphValid g118 (boundsBefore K117) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 7 := lower_forest (g:=g118) (i:=0) (hints:=34669632) (before_sound K117 V117) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K118 := extendKnown K117 7 [(118,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V117 low118 (by decide +kernel)

def g121Y : Array (Bits × Bits) := #[((repeatRows 192 0xaaab57aaab57aaab57aaab57aaab57aaab57aaab57aaab57), (repeatRows 192 0xffffff000000ffffff000000)),
    (0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 192 0xcccd9acccd9acccd9acccd9acccd9acccd9acccd9acccd9a), (repeatRows 192 0xffffff000000ffffffffffff000000000000)),
    ((repeatRows 192 0xf0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3f0f1e3), (repeatRows 192 0xffffffffffff000000000000000000000000)),
    ((repeatRows 192 0xff01fcff01fcff01fcff01fcff01fcff01fcff01fcff01fc), (repeatRows 192 0xffffff000000000000000000000000000000000000)),
    ((repeatRows 192 0xfffe00fffe00fffe00fffe00fffe00fffe00fffe00fffe00), (repeatRows 192 0xffffff000000000000000000000000000000000000000000))]
def g121C : List ColumnInfo := [(8,0,113,0,7)]
def g121D7 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g121L : Nat → Packing
  | 7 => (1, 0, 1, 0, 0, 1, 0, g121D7)
  | _ => emptyPacking
def g121I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g121 : Forest := ⟨121, 7, fun i => (g121Y[i]?).getD (0,0), g121C, [[], [101], [64], [64, 101]], g121L, g121I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121P7n0 : block g121 7 0 1 = true := by decide +kernel
theorem g121B7 : block g121 7 0 1 = true := g121P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121T : checkedTables g121 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g121 0 0 0 = true)
  · exact (rfl : block g121 1 0 0 = true)
  · exact (rfl : block g121 2 0 0 = true)
  · exact (rfl : block g121 3 0 0 = true)
  · exact (rfl : block g121 4 0 0 = true)
  · exact (rfl : block g121 5 0 0 = true)
  · exact (rfl : block g121 6 0 0 = true)
  · exact g121B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g121G : graphValid g121 (boundsBefore K118) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low121 : Lower true (varsX 121) (graphGoal 121) 8 := lower_forest (g:=g121) (i:=0) (hints:=20484) (before_sound K118 V118) g121G g121T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K121 := extendKnown K118 8 [(121,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V121 : Known true K121 := extend_ok (m:=121) V118 low121 (by decide +kernel)

def g122Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 192 0xaaaaafaaaaafaaaaafaaaaafaaaaafaaaaafaaaaafaaaaaf), (repeatRows 192 0xffffff000000000000000000000000000000ffffff000000)),
    (0x0, 0x0),
    ((repeatRows 192 0xcccf35cccf35cccf35cccf35cccf35cccf35cccf35cccf35), (repeatRows 192 0xffffff000000ffffff000000000000)),
    ((repeatRows 192 0xf0f3c6f0f3c6f0f3c6f0f3c6f0f3c6f0f3c6f0f3c6f0f3c6), (repeatRows 192 0xffffffffffff000000000000000000)),
    ((repeatRows 192 0xff03f8ff03f8ff03f8ff03f8ff03f8ff03f8ff03f8ff03f8), (repeatRows 192 0xffffff000000000000000000000000000000)),
    ((repeatRows 192 0xfffc00fffc00fffc00fffc00fffc00fffc00fffc00fffc00), (repeatRows 192 0xffffffffffff000000000000000000000000000000000000))]
def g122C : List ColumnInfo := [(2,0,120,0,5)]
def g122D5 (j : Nat) : Nat := if j = 0 then 0x5f else 0
def g122L : Nat → Packing
  | 5 => (1, 0, 1, 0, 0, 1, 0, g122D5)
  | _ => emptyPacking
def g122I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g122 : Forest := ⟨122, 5, fun i => (g122Y[i]?).getD (0,0), g122C, [[], [67], [49, 100], [49, 99, 100], [65, 67, 100], [65, 99], [97], [97, 67]], g122L, g122I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g122P5n0 : block g122 5 0 1 = true := by decide +kernel
theorem g122B5 : block g122 5 0 1 = true := g122P5n0
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
theorem low122 : Lower true (varsX 122) (graphGoal 122) 6 := lower_forest (g:=g122) (i:=0) (hints:=51449904) (before_sound K121 V121) g122G g122T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K122 := extendKnown K121 6 [(122,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V122 : Known true K122 := extend_ok (m:=122) V121 low122 (by decide +kernel)

def g124Y : Array (Bits × Bits) := #[(0x0, 0x0),
    (0x0, 0x0),
    ((repeatRows 207 0x5555abaaab575556aeaaad5d555abaaab575556aeaaad5d555ab), (repeatRows 207 0xfffffe00000000000000000fffffe000003fffff800000)),
    ((repeatRows 207 0x6666cecccd9d999b3b333676666cecccd9d999b3b333676666ce), (repeatRows 207 0x3fffff800000fffffffffffc00000000000)),
    ((repeatRows 207 0x7878f3f0f1e7e1e3cfc3c79f878f3f0f1e7e1e3cfc3c79f878f3), (repeatRows 207 0x3fffffffffff00000000000000000000000)),
    ((repeatRows 207 0x7f80fcff01f9fe03f3fc07e7f80fcff01f9fe03f3fc07e7f80fc), (repeatRows 207 0xfffffffffffc0000000000000000000000000000000000)),
    ((repeatRows 207 0x7fff00fffe01fffc03fff807fff00fffe01fffc03fff807fff00), (repeatRows 207 0x7fffff0000000000000000000000000000000000000000000000))]
def g124C : List ColumnInfo := [(4,0,120,0,5), (8,0,116,0,5), (16,0,108,0,5), (32,0,92,0,5)]
def g124D6 (j : Nat) : Nat := if j = 0 then 0xe411f else 0
def g124L : Nat → Packing
  | 6 => (1, 0, 2, 0, 0, 1, 0, g124D6)
  | _ => emptyPacking
def g124I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g124 : Forest := ⟨124, 6, fun i => (g124Y[i]?).getD (0,0), g124C, [[], [50, 84]], g124L, g124I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124P6n0 : block g124 6 0 1 = true := by decide +kernel
theorem g124B6 : block g124 6 0 1 = true := g124P6n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124T : checkedTables g124 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g124 0 0 0 = true)
  · exact (rfl : block g124 1 0 0 = true)
  · exact (rfl : block g124 2 0 0 = true)
  · exact (rfl : block g124 3 0 0 = true)
  · exact (rfl : block g124 4 0 0 = true)
  · exact (rfl : block g124 5 0 0 = true)
  · exact g124B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g124G : graphValid g124 (boundsBefore K122) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low124 : Lower true (varsX 124) (graphGoal 124) 7 := lower_forest (g:=g124) (i:=0) (hints:=36852736) (before_sound K122 V122) g124G g124T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K124 := extendKnown K122 7 [(124,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V124 : Known true K124 := extend_ok (m:=124) V122 low124 (by decide +kernel)

def g63Y : Array (Bits × Bits) := #[((repeatRows 663 0x5555555b56adbaaaaaab6ad5b75555556d5ab6eaaaaaadab56dd555555b56adbaaaaaab6ad5b75555556d5ab6eaaaaaadab56dd555555b56adbaaaaaab6ad5b75555556d5ab6eaaaaaadab56dd555555b56adb), (repeatRows 663 0xffffffffffffe00000000000000000000000000000000000000ffffffffffffe0000000000003ffffffffffff8000000000000)),
    ((repeatRows 663 0x6666666d9b36eccccccdb366dd999999b66cdbb3333336cd9b76666666d9b36eccccccdb366dd999999b66cdbb3333336cd9b76666666d9b36eccccccdb366dd999999b66cdbb3333336cd9b76666666d9b36e), (repeatRows 663 0x3ffffffffffff8000000000000fffffffffffffffffffffffffc0000000000000000000000000)),
    ((repeatRows 663 0x78787871e3c73f0f0f0e3c78e7e1e1e1c78f1cfc3c3c38f1e39f8787871e3c73f0f0f0e3c78e7e1e1e1c78f1cfc3c3c38f1e39f8787871e3c73f0f0f0e3c78e7e1e1e1c78f1cfc3c3c38f1e39f8787871e3c73), (repeatRows 663 0x7ffffffffffff000000000000000000000000000000000000007ffffffffffff00000000000000000000000003fffffffffffffffffffffffff000000000000000000000000000000000000000000000000000)),
    ((repeatRows 663 0x7f807f81fc07cff00ff03f80f9fe01fe07f01f3fc03fc0fe03e7f807f81fc07cff00ff03f80f9fe01fe07f01f3fc03fc0fe03e7f807f81fc07cff00ff03f80f9fe01fe07f01f3fc03fc0fe03e7f807f81fc07c), (repeatRows 663 0x1ffffffffffffc0000000000007fffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000)),
    ((repeatRows 663 0x7fff8001fff80ffff0003fff01fffe0007ffe03fffc000fffc07fff8001fff80ffff0003fff01fffe0007ffe03fffc000fffc07fff8001fff80ffff0003fff01fffe0007ffe03fffc000fffc07fff8001fff80), (repeatRows 663 0x1fffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    ((repeatRows 663 0x7ffffffe00000fffffffc00001fffffff800003fffffff000007ffffffe00000fffffffc00001fffffff800003fffffff000007ffffffe00000fffffffc00001fffffff800003fffffff000007ffffffe00000), (repeatRows 663 0x7ffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    (0x0, 0x0)]
def g63C : List ColumnInfo := [(0,4,42,17,6), (0,8,21,34,6), (1,0,62,0,7), (1,4,42,16,5), (2,0,61,0,7), (2,8,21,32,5), (3,0,60,0,4), (4,0,59,0,7), (5,0,58,0,5), (6,0,57,0,5), (8,0,55,0,7), (12,0,51,0,5), (13,0,50,0,4), (14,0,49,0,4), (16,0,47,0,7), (16,4,42,1,5), (17,0,42,0,4), (17,4,42,0,4), (18,0,45,0,4), (20,0,43,0,5), (21,0,42,0,4), (24,0,39,0,4), (32,0,31,0,7), (32,8,21,2,5), (33,0,30,0,4), (34,0,21,0,4), (34,8,21,0,4), (36,0,27,0,4), (40,0,23,0,5), (42,0,21,0,4)]
def g63D5 (j : Nat) : Nat := if j = 0 then 0xe040b6785b54603c98614549514d3a1751505412b38e11589904e354559514407cc5150545101e394559504407cc5151541101 else 0
def g63D6 (j : Nat) : Nat := if j = 0 then 0xa0108468820000204443988311100f67621468d8443d3b2a9f17928f8b0680d6404d8544430190882070008680820e046c58443d3b130680800441005711103100f67621001411020c443820001611104e0e8202c1a0602806a05db380030000a01081c0020a07010010584421a044411a04683821a1108685450484438ab9c1613098700d1127040c441820e043816aa70a3e4668c116a2642e800e49c23666c0d299a31e620b29622b6560a49362664908c9162263a0728de19e330648be1662804a88e10e2003a86a0660900c8120160013f5c6065175ea2c0c9a6dd35819349faeb032693f5c6064d3cf03a8a9a79d0751534e1a8a92a69b7596064d3cea2c0c9a5dd7581934bbae3032693f5c365452fb0baca8a7b61751514e5a8a92a29cf515054535ea2c0c8a4fd7581914f3c0e9a229e7419344527f0baca826fa0759504f740ea2a09cf51515412fd0ba0a827394541504dda6b13209bb4562641276bac4c825de37455029fccea2a033f5d7644067fbaac880cfd7559101d7a8ab22037ddd514407daa2a2880ef76545101deaca8a203fc41514407ca9a22880df97541101f728a82203bed95044077cb2a0880ff11541101 else 0
def g63D7 (j : Nat) : Nat := if j = 0 then 0x5888e44085ac4670e159c38446881010069822407a7440876d3864a4f9310e58a919c3250a0f90223440a0803cd176c3c74a159e2e4c504c34d8a4e949e2e4c504a34d888f9d293c5c88f141406b62a508ce94293e4488d141407130200334d894e1c283c588101010069a32d8b12541476c5890f1d102414249a6c58a4e949c3c5890a0986cd362c447ce949e2c485050003cd18244420218b14244670a0f102234408080389101e9c3220439a6fd890f1ca85670b1312134c36284484e141c243840401ad8b11203c743840a0a02ce0a8e04432415470808630d8b1121387030505017da76a4f921001d5080019a2c44706080873b588ae1c3150acf1e2438500e3558a9422b872acf1c2c4870908180896284570a0e1a20487081010071220b87270c0c72c5091120b85070d121c20200e28488ae1cab3860a121028080e284482e1da938688101824300ea3c9db9a496d8fe8a48587f778f7747136dc69763d5ce59e5364ff49e43d3ea3c839834530e2f32bc2541d716f1380d0068000ff81945bf81945ff41945f3c9734bf81934e751534f3c9534f349534f781934ff4d524bfd9514ff59514ef51514fbc9514fb49514ff41514bf81914ff41914e74d114bf59504ef51504ff4d504ff45504fe41504bb89904ff45502ff51501f7cd101f74d101bfd9101ff59101bf59101fd45101fe41101 else 0
def g63D8 (j : Nat) : Nat := if j = 0 then 0x2eb1e75454e3c824410201ceec79c54f24442fb2ca9e71538e2c8244102020d2fb1e71538b244097b2c99c6d450f2081c410201fb2c91e75454e38a24410201fb2ca2281e75454e3c8206102023b2c7dc71650e2c820710408086cb1f71d51448e2881c4102021b2c7dc71951440f20810201fb2d71d51538e30a20610201fce6cd805712c3f0c624c600c0007f517be69fd34ee9a7f493fa29fd04fe91ff44bfa05fd01 else 0
def g63D9 (j : Nat) : Nat := if j = 0 then 0x59ca390433f else 0
def g63L : Nat → Packing
  | 5 => (7, 4, 5, 0, 0, 6, 0, g63D5)
  | 6 => (47, 3, 5, 0, 0, 11, 0, g63D6)
  | 7 => (34, 2, 5, 0, 0, 12, 0, g63D7)
  | 8 => (11, 1, 5, 0, 0, 10, 0, g63D8)
  | 9 => (1, 0, 5, 0, 0, 1, 0, g63D9)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6, tag => lookupShort 6 17 3 6 3 1 (fun j => if j=0 then 0x25589ec4002d0000140e02c058d008 else 0) tag
  | 7, tag => lookupShort 31 92 4 9 6 1 (fun j => if j=0 then 0xf86016000000132d2002b000000e0000000d48001892006b4001161438960061a831002852780000aaa903a230009c0c00638400000000000000004504200a80000000ea00001a56fe360a60cd1235c49e20014c87d44882d8995a5d2a0489aaa360387c078380010f00010710000e0002017136161a0 else 0) tag
  | 8, tag => lookupShort 27 82 4 9 6 1 (fun j => if j=0 then 0x12000000000fd0802840064000010ca00031ccc08e09254e000003e8defc76a78109a00000022754a84d0b0013490ae76f30c1000000ee0040000109b0e528745c22672a00000003600850722f1e6560c000045c140000000188c00003131004100178202304230006 else 0) tag
  | 9, tag => lookupShort 10 29 3 7 4 1 (fun j => if j=0 then 0x85c80001434087a1a8000c407228000002d883988802b80d424c000600 else 0) tag
  | _, _ => none
def g63 : Forest := ⟨63, 9, fun i => (g63Y[i]?).getD (0,0), g63C, [[], [16, 50, 84]], g63L, g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5n0 : block g63 5 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5n2 : block g63 5 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5n4 : block g63 5 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5n6 : block g63 5 6 1 = true := by decide +kernel
theorem g63B5 : block g63 5 0 7 = true := (@block_merge g63 5 0 4 3 (@block_merge g63 5 0 2 2 g63P5n0 g63P5n2) (@block_merge g63 5 4 2 1 g63P5n4 g63P5n6))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n0 : block g63 6 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n2 : block g63 6 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n4 : block g63 6 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n6 : block g63 6 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n8 : block g63 6 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n10 : block g63 6 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n12 : block g63 6 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n14 : block g63 6 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n16 : block g63 6 16 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n18 : block g63 6 18 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n20 : block g63 6 20 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n22 : block g63 6 22 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n24 : block g63 6 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n26 : block g63 6 26 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n28 : block g63 6 28 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n30 : block g63 6 30 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n32 : block g63 6 32 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n34 : block g63 6 34 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n36 : block g63 6 36 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n38 : block g63 6 38 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n40 : block g63 6 40 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n42 : block g63 6 42 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n44 : block g63 6 44 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6n46 : block g63 6 46 1 = true := by decide +kernel
theorem g63B6 : block g63 6 0 47 = true := (@block_merge g63 6 0 24 23 (@block_merge g63 6 0 12 12 (@block_merge g63 6 0 6 6 (@block_merge g63 6 0 2 4 g63P6n0 (@block_merge g63 6 2 2 2 g63P6n2 g63P6n4)) (@block_merge g63 6 6 2 4 g63P6n6 (@block_merge g63 6 8 2 2 g63P6n8 g63P6n10))) (@block_merge g63 6 12 6 6 (@block_merge g63 6 12 2 4 g63P6n12 (@block_merge g63 6 14 2 2 g63P6n14 g63P6n16)) (@block_merge g63 6 18 2 4 g63P6n18 (@block_merge g63 6 20 2 2 g63P6n20 g63P6n22)))) (@block_merge g63 6 24 12 11 (@block_merge g63 6 24 6 6 (@block_merge g63 6 24 2 4 g63P6n24 (@block_merge g63 6 26 2 2 g63P6n26 g63P6n28)) (@block_merge g63 6 30 2 4 g63P6n30 (@block_merge g63 6 32 2 2 g63P6n32 g63P6n34))) (@block_merge g63 6 36 6 5 (@block_merge g63 6 36 2 4 g63P6n36 (@block_merge g63 6 38 2 2 g63P6n38 g63P6n40)) (@block_merge g63 6 42 2 3 g63P6n42 (@block_merge g63 6 44 2 1 g63P6n44 g63P6n46)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n0 : block g63 7 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n2 : block g63 7 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n4 : block g63 7 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n6 : block g63 7 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n8 : block g63 7 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n10 : block g63 7 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n12 : block g63 7 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n14 : block g63 7 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n16 : block g63 7 16 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n18 : block g63 7 18 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n20 : block g63 7 20 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n22 : block g63 7 22 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n24 : block g63 7 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n26 : block g63 7 26 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n28 : block g63 7 28 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n30 : block g63 7 30 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7n32 : block g63 7 32 2 = true := by decide +kernel
theorem g63B7 : block g63 7 0 34 = true := (@block_merge g63 7 0 16 18 (@block_merge g63 7 0 8 8 (@block_merge g63 7 0 4 4 (@block_merge g63 7 0 2 2 g63P7n0 g63P7n2) (@block_merge g63 7 4 2 2 g63P7n4 g63P7n6)) (@block_merge g63 7 8 4 4 (@block_merge g63 7 8 2 2 g63P7n8 g63P7n10) (@block_merge g63 7 12 2 2 g63P7n12 g63P7n14))) (@block_merge g63 7 16 8 10 (@block_merge g63 7 16 4 4 (@block_merge g63 7 16 2 2 g63P7n16 g63P7n18) (@block_merge g63 7 20 2 2 g63P7n20 g63P7n22)) (@block_merge g63 7 24 4 6 (@block_merge g63 7 24 2 2 g63P7n24 g63P7n26) (@block_merge g63 7 28 2 4 g63P7n28 (@block_merge g63 7 30 2 2 g63P7n30 g63P7n32)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8n0 : block g63 8 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8n2 : block g63 8 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8n4 : block g63 8 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8n6 : block g63 8 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8n8 : block g63 8 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8n10 : block g63 8 10 1 = true := by decide +kernel
theorem g63B8 : block g63 8 0 11 = true := (@block_merge g63 8 0 6 5 (@block_merge g63 8 0 2 4 g63P8n0 (@block_merge g63 8 2 2 2 g63P8n2 g63P8n4)) (@block_merge g63 8 6 2 3 g63P8n6 (@block_merge g63 8 8 2 1 g63P8n8 g63P8n10)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9n0 : block g63 9 0 1 = true := by decide +kernel
theorem g63B9 : block g63 9 0 1 = true := g63P9n0
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
theorem g63G : graphValid g63 (boundsBefore K124) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 10 := lower_forest (g:=g63) (i:=0) (hints:=4146) (before_sound K124 V124) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K124 10 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V124 low63 (by decide +kernel)

def g95Y : Array (Bits × Bits) := #[((repeatRows 663 0x5555555756adbaaaaaaaead5b75555555d5ab6eaaaaaabab56dd555555756adbaaaaaaaead5b75555555d5ab6eaaaaaabab56dd555555756adbaaaaaaaead5b75555555d5ab6eaaaaaabab56dd555555756adb), (repeatRows 663 0xffffffffffffe00000000000000000000000000000000000000ffffffffffffe0000000000003ffffffffffff8000000000000)),
    ((repeatRows 663 0x666666659b36ecccccccb366dd999999966cdbb3333332cd9b7666666659b36ecccccccb366dd999999966cdbb3333332cd9b7666666659b36ecccccccb366dd999999966cdbb3333332cd9b7666666659b36e), (repeatRows 663 0x7ffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffff8000000000000fffffffffffffffffffffffffc0000000000000000000000000)),
    ((repeatRows 663 0x78787879e3c73f0f0f0f3c78e7e1e1e1e78f1cfc3c3c3cf1e39f8787879e3c73f0f0f0f3c78e7e1e1e1e78f1cfc3c3c3cf1e39f8787879e3c73f0f0f0f3c78e7e1e1e1e78f1cfc3c3c3cf1e39f8787879e3c73), (repeatRows 663 0x7ffffffffffff00000000000000000000000003fffffffffffffffffffffffff000000000000000000000000000000000000000000000000000)),
    ((repeatRows 663 0x7f807f81fc07cff00ff03f80f9fe01fe07f01f3fc03fc0fe03e7f807f81fc07cff00ff03f80f9fe01fe07f01f3fc03fc0fe03e7f807f81fc07cff00ff03f80f9fe01fe07f01f3fc03fc0fe03e7f807f81fc07c), (repeatRows 663 0x1ffffffffffffc0000000000007fffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000)),
    ((repeatRows 663 0x7fff8001fff80ffff0003fff01fffe0007ffe03fffc000fffc07fff8001fff80ffff0003fff01fffe0007ffe03fffc000fffc07fff8001fff80ffff0003fff01fffe0007ffe03fffc000fffc07fff8001fff80), (repeatRows 663 0x1fffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    (0x0, 0x0),
    ((repeatRows 663 0x7ffffffe00000fffffffc00001fffffff800003fffffff000007ffffffe00000fffffffc00001fffffff800003fffffff000007ffffffe00000fffffffc00001fffffff800003fffffff000007ffffffe00000), (repeatRows 663 0x7ffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))]
def g95C : List ColumnInfo := [(2,0,93,0,8)]
def g95D8 (j : Nat) : Nat := if j = 0 then 0xbf else 0
def g95L : Nat → Packing
  | 8 => (1, 0, 1, 0, 0, 1, 0, g95D8)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | _, _ => none
def g95 : Forest := ⟨95, 8, fun i => (g95Y[i]?).getD (0,0), g95C, [[], [49, 100], [32], [32, 49, 100]], g95L, g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P8n0 : block g95 8 0 1 = true := by decide +kernel
theorem g95B8 : block g95 8 0 1 = true := g95P8n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g95 0 0 0 = true)
  · exact (rfl : block g95 1 0 0 = true)
  · exact (rfl : block g95 2 0 0 = true)
  · exact (rfl : block g95 3 0 0 = true)
  · exact (rfl : block g95 4 0 0 = true)
  · exact (rfl : block g95 5 0 0 = true)
  · exact (rfl : block g95 6 0 0 = true)
  · exact (rfl : block g95 7 0 0 = true)
  · exact g95B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 9 := lower_forest (g:=g95) (i:=0) (hints:=4146) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 9 [(95,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)

def g111Y : Array (Bits × Bits) := #[((repeatRows 663 0x55555557556dbaaaaaaaeaadb75555555d55b6eaaaaaabaab6dd5555557556dbaaaaaaaeaadb75555555d55b6eaaaaaabaab6dd5555557556dbaaaaaaaeaadb75555555d55b6eaaaaaabaab6dd5555557556db), (repeatRows 663 0xffffffffffffe00000000000000000000000000000000000000ffffffffffffe0000000000003ffffffffffff8000000000000)),
    ((repeatRows 663 0x6666666599b6ecccccccb336dd9999999666dbb3333332ccdb76666666599b6ecccccccb336dd9999999666dbb3333332ccdb76666666599b6ecccccccb336dd9999999666dbb3333332ccdb76666666599b6e), (repeatRows 663 0x7ffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000003ffffffffffff8000000000000fffffffffffffffffffffffffc0000000000000000000000000)),
    ((repeatRows 663 0x78787879e1c73f0f0f0f3c38e7e1e1e1e7871cfc3c3c3cf0e39f8787879e1c73f0f0f0f3c38e7e1e1e1e7871cfc3c3c3cf0e39f8787879e1c73f0f0f0f3c38e7e1e1e1e7871cfc3c3c3cf0e39f8787879e1c73), (repeatRows 663 0x1ffffffffffffc0000000000007ffffffffffff00000000000000000000000003fffffffffffffffffffffffff000000000000000000000000000000000000000000000000000)),
    ((repeatRows 663 0x7f807f81fe07cff00ff03fc0f9fe01fe07f81f3fc03fc0ff03e7f807f81fe07cff00ff03fc0f9fe01fe07f81f3fc03fc0ff03e7f807f81fe07cff00ff03fc0f9fe01fe07f81f3fc03fc0ff03e7f807f81fe07c), (repeatRows 663 0x7fffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000)),
    (0x0, 0x0),
    ((repeatRows 663 0x7fff8001fff80ffff0003fff01fffe0007ffe03fffc000fffc07fff8001fff80ffff0003fff01fffe0007ffe03fffc000fffc07fff8001fff80ffff0003fff01fffe0007ffe03fffc000fffc07fff8001fff80), (repeatRows 663 0x1fffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    ((repeatRows 663 0x7ffffffe00000fffffffc00001fffffff800003fffffff000007ffffffe00000fffffffc00001fffffff800003fffffff000007ffffffe00000fffffffc00001fffffff800003fffffff000007ffffffe00000), (repeatRows 663 0x7ffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))]
def g111C : List ColumnInfo := [(0,2,69,40,6), (0,4,42,65,6), (1,0,110,0,7), (1,4,42,64,5), (2,0,109,0,7), (3,0,108,0,5), (4,0,107,0,7), (5,0,106,0,5), (6,0,105,0,5), (7,0,104,0,4), (8,0,103,0,7), (8,2,69,32,5), (9,0,102,0,4), (14,0,97,0,4), (32,0,79,0,7), (32,2,69,8,5), (33,0,78,0,4), (34,0,77,0,5), (36,0,75,0,4), (40,0,69,0,4), (40,2,69,0,4), (42,0,69,0,4), (64,0,47,0,7), (64,4,42,1,5), (65,0,42,0,4), (65,4,42,0,4), (66,0,45,0,4), (69,0,42,0,4), (72,0,39,0,4)]
def g111D5 (j : Nat) : Nat := if j = 0 then 0xe040000b6785230602b98a10585934f3208515154138e515058d904e1d455953440fc6515054d103e39455950440fc65153541103 else 0
def g111D6 (j : Nat) : Nat := if j = 0 then 0x40008503820198176ce000c52a8200006045039a8314130f6a641464d8503d3aafab1a930f8b0680d6204d85048301881001000219020801b19020c381006858503d3b0b068081918164e0e8202c161a02850100012c2420c4c3da99040018042040008181004004161408503020e0438166a408641190a260c50119046438219140864545048403b289b900e098700d023a45e8b112a16416821029fe3de760d099a316620c097e2e65a0b295629e530948fe1ee3d0788e219e330608b6146260468860fe1d03685e0ae1402283a0060013f5ce06517cf1ba8a9a73d4541534dea0b0b2693d5d6164d35ea2c6c926ed258d9249faeb1b2493f5c236493d71ba8a927ad3751524e4a8a8aa49bb59636493d6a2c6c925ed758d924bdae11b2497b89d054527eb9eca825fa07595049fc6eb2a09be81d65413dd03a8a8273d454d504e6a8a8aa09ce515054135ea2c6c826f9058d9049faeb1b209eb8dd24413d69b248824fe67515039faebb22073fdd56440e7ebaac881ebd4559103f3a8a9a207b7d953440f6eb2a6881fd9054d103bf6ea822077e5d50440fdca2a0881efb6541103df2ca82207f64d50440fd49220881df6174d102 else 0
def g111D7 (j : Nat) : Nat := if j = 0 then 0x64b0e44085335a70e1598304468810100699305c826440876c58a131e3a5ca15050166098a4d1010dda74acc931001db4ed426324c4396284a70d56a85460c131028200f325db0f1daa306c90f14130cb62b3b546490f14128cb6283e72bd519243c50501ad8a9425395aa8c19262450501c440800c8a60800432d884e1c2830487081010069930d8b104c0c73664c362138506090e101006b62c4078e840a0a124e19284050218cb62c5674a8c902438504c3465b16283e74a8c921c2828001e64c362c4270e060a0a02cb15284272b54283048408080389901e3150a483996fd880f1da9306c80e12134c96283860a043962a5170c972850609081010071320b870c169072c54a1320b864b94182420200e2a509ae1c3058acc921024300e3758a2e1d2e5094c1b2448500e3358a9424b874b949b244070908180895284170e1928526c80c1404070748043a3c9db9a49519218ea8b38447ea79e73d6d56ba69863760059f55a52a4d046140e3a636f30e2d726f2381d016810008301b000ff81945bf81945ff41945ef51534ff41534bd85934f9c5724bf8d924eb51524f9c5524f945524fb8d924ff49514ff41514bfd9504ff59504bf59504ef51504ff4d504fdc5504fd45504fe41504bf8d904ff4d904eb49104ff51503bfd9103ff59103bf59103f74d103fbc9103fb49103fe41103ff4d102 else 0
def g111D8 (j : Nat) : Nat := if j = 0 then 0x2eb1e75454c34824410201db2caa899e71654c348244102022dec79d50d24442fb2c91e75450d2081c4102020cafb1e7543481c4097b2c89c5d451330c24410201fb2c81e75454c34820610201fb2d71c61654c34820610201fb2c7dc71751440c20710408082fb2d71d51448e3482040807ecb1f71c5d454c30a206102021ce6617d529263d8c6258630cc007f517fa69ef24fe927b493fa29fd04fe81ff44bfa05fd01 else 0
def g111D9 (j : Nat) : Nat := if j = 0 then 0x59ca310433f else 0
def g111L : Nat → Packing
  | 5 => (7, 4, 5, 0, 0, 6, 0, g111D5)
  | 6 => (47, 3, 5, 0, 0, 11, 0, g111D6)
  | 7 => (34, 2, 5, 0, 0, 12, 0, g111D7)
  | 8 => (11, 1, 5, 0, 0, 10, 0, g111D8)
  | 9 => (1, 0, 5, 0, 0, 1, 0, g111D9)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 6, tag => lookupShort 5 15 3 6 3 1 (fun j => if j=0 then 0x8f7052028000a80004b7a98060 else 0) tag
  | 7, tag => lookupShort 31 93 4 9 6 1 (fun j => if j=0 then 0x68c008141c914b432300393eb4904000440282000ca720000000000a9ac9540611ae9713ea0000076a9a340989e7abd0f860340000cc000001fc3e831600000033a1b00314014b85618230e002b800000020800000000053accb67156650cd30019490ab4002250473c0330000033001925000003000 else 0) tag
  | 8, tag => lookupShort 27 80 3 9 6 1 (fun j => if j=0 then 0xdfe6a2c010dcce5626000002800006c40d999fa380284000318234026c905a99702a0000870a2300000cb00000008400001e144c121d9c6200000000063c00928ee8001d1c80793600a18069c000017a8c00a2e6123500000142008b04d2381002e01002 else 0) tag
  | 9, tag => lookupShort 10 29 2 7 4 1 (fun j => if j=0 then 0xb28f8c501a91492c023b50018037e8044000000020600027812403 else 0) tag
  | _, _ => none
def g111 : Forest := ⟨111, 9, fun i => (g111Y[i]?).getD (0,0), g111C, [[], [48, 33, 101]], g111L, g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n0 : block g111 5 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n2 : block g111 5 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n4 : block g111 5 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5n6 : block g111 5 6 1 = true := by decide +kernel
theorem g111B5 : block g111 5 0 7 = true := (@block_merge g111 5 0 4 3 (@block_merge g111 5 0 2 2 g111P5n0 g111P5n2) (@block_merge g111 5 4 2 1 g111P5n4 g111P5n6))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n0 : block g111 6 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n2 : block g111 6 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n4 : block g111 6 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n6 : block g111 6 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n8 : block g111 6 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n10 : block g111 6 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n12 : block g111 6 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n14 : block g111 6 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n16 : block g111 6 16 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n18 : block g111 6 18 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n20 : block g111 6 20 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n22 : block g111 6 22 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n24 : block g111 6 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n26 : block g111 6 26 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n28 : block g111 6 28 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n30 : block g111 6 30 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n32 : block g111 6 32 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n34 : block g111 6 34 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n36 : block g111 6 36 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n38 : block g111 6 38 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n40 : block g111 6 40 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n42 : block g111 6 42 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n44 : block g111 6 44 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6n46 : block g111 6 46 1 = true := by decide +kernel
theorem g111B6 : block g111 6 0 47 = true := (@block_merge g111 6 0 24 23 (@block_merge g111 6 0 12 12 (@block_merge g111 6 0 6 6 (@block_merge g111 6 0 2 4 g111P6n0 (@block_merge g111 6 2 2 2 g111P6n2 g111P6n4)) (@block_merge g111 6 6 2 4 g111P6n6 (@block_merge g111 6 8 2 2 g111P6n8 g111P6n10))) (@block_merge g111 6 12 6 6 (@block_merge g111 6 12 2 4 g111P6n12 (@block_merge g111 6 14 2 2 g111P6n14 g111P6n16)) (@block_merge g111 6 18 2 4 g111P6n18 (@block_merge g111 6 20 2 2 g111P6n20 g111P6n22)))) (@block_merge g111 6 24 12 11 (@block_merge g111 6 24 6 6 (@block_merge g111 6 24 2 4 g111P6n24 (@block_merge g111 6 26 2 2 g111P6n26 g111P6n28)) (@block_merge g111 6 30 2 4 g111P6n30 (@block_merge g111 6 32 2 2 g111P6n32 g111P6n34))) (@block_merge g111 6 36 6 5 (@block_merge g111 6 36 2 4 g111P6n36 (@block_merge g111 6 38 2 2 g111P6n38 g111P6n40)) (@block_merge g111 6 42 2 3 g111P6n42 (@block_merge g111 6 44 2 1 g111P6n44 g111P6n46)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n0 : block g111 7 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n2 : block g111 7 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n4 : block g111 7 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n6 : block g111 7 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n8 : block g111 7 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n10 : block g111 7 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n12 : block g111 7 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n14 : block g111 7 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n16 : block g111 7 16 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n18 : block g111 7 18 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n20 : block g111 7 20 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n22 : block g111 7 22 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n24 : block g111 7 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n26 : block g111 7 26 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n28 : block g111 7 28 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n30 : block g111 7 30 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7n32 : block g111 7 32 2 = true := by decide +kernel
theorem g111B7 : block g111 7 0 34 = true := (@block_merge g111 7 0 16 18 (@block_merge g111 7 0 8 8 (@block_merge g111 7 0 4 4 (@block_merge g111 7 0 2 2 g111P7n0 g111P7n2) (@block_merge g111 7 4 2 2 g111P7n4 g111P7n6)) (@block_merge g111 7 8 4 4 (@block_merge g111 7 8 2 2 g111P7n8 g111P7n10) (@block_merge g111 7 12 2 2 g111P7n12 g111P7n14))) (@block_merge g111 7 16 8 10 (@block_merge g111 7 16 4 4 (@block_merge g111 7 16 2 2 g111P7n16 g111P7n18) (@block_merge g111 7 20 2 2 g111P7n20 g111P7n22)) (@block_merge g111 7 24 4 6 (@block_merge g111 7 24 2 2 g111P7n24 g111P7n26) (@block_merge g111 7 28 2 4 g111P7n28 (@block_merge g111 7 30 2 2 g111P7n30 g111P7n32)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n0 : block g111 8 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n2 : block g111 8 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n4 : block g111 8 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n6 : block g111 8 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n8 : block g111 8 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8n10 : block g111 8 10 1 = true := by decide +kernel
theorem g111B8 : block g111 8 0 11 = true := (@block_merge g111 8 0 6 5 (@block_merge g111 8 0 2 4 g111P8n0 (@block_merge g111 8 2 2 2 g111P8n2 g111P8n4)) (@block_merge g111 8 6 2 3 g111P8n6 (@block_merge g111 8 8 2 1 g111P8n8 g111P8n10)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P9n0 : block g111 9 0 1 = true := by decide +kernel
theorem g111B9 : block g111 9 0 1 = true := g111P9n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 9 := by
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
  · exact g111B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 10 := lower_forest (g:=g111) (i:=0) (hints:=4146) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 10 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)

def g119Y : Array (Bits × Bits) := #[((repeatRows 583 0x55555557556d5eaaaaaabaab6af5555555d55b57aaaaaaaeaadabd5555557556d5eaaaaaabaab6af5555555d55b57aaaaaaaeaadabd5555557556d5eaaaaaabaab6af5555555d55b57), (repeatRows 583 0xfffffffffffff80000000000003ffffffffffffe0000000000000)),
    ((repeatRows 583 0x6666666599b66b3333332ccdb359999999666d9acccccccb336cd6666666599b66b3333332ccdb359999999666d9acccccccb336cd6666666599b66b3333332ccdb359999999666d9a), (repeatRows 583 0x7ffffffffffffc00000000000000000000000000000000000000000000000000003ffffffffffffe0000000000000ffffffffffffffffffffffffffc00000000000000000000000000)),
    ((repeatRows 583 0x78787879e1c78fc3c3c3cf0e3c7e1e1e1e7871e3f0f0f0f3c38f1f8787879e1c78fc3c3c3cf0e3c7e1e1e1e7871e3f0f0f0f3c38f1f8787879e1c78fc3c3c3cf0e3c7e1e1e1e7871e3), (repeatRows 583 0x1fffffffffffff000000000000000000000000003ffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000)),
    (0x0, 0x0),
    ((repeatRows 583 0x7f807f81fe07f3fc03fc0ff03f9fe01fe07f81fcff00ff03fc0fe7f807f81fe07f3fc03fc0ff03f9fe01fe07f81fcff00ff03fc0fe7f807f81fe07f3fc03fc0ff03f9fe01fe07f81fc), (repeatRows 583 0x7ffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    ((repeatRows 583 0x7fff8001fff803fffc000fffc01fffe0007ffe00ffff0003fff007fff8001fff803fffc000fffc01fffe0007ffe00ffff0003fff007fff8001fff803fffc000fffc01fffe0007ffe00), (repeatRows 583 0x1ffffffffffffffffffffffffff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    ((repeatRows 583 0x7ffffffe000003fffffff000001fffffff800000fffffffc000007ffffffe000003fffffff000001fffffff800000fffffffc000007ffffffe000003fffffff000001fffffff800000), (repeatRows 583 0x7fffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))]
def g119C : List ColumnInfo := [(0,2,69,48,6), (1,0,118,0,7), (2,0,117,0,8), (3,0,116,0,5), (4,0,115,0,8), (16,0,103,0,7), (16,2,69,32,5), (17,0,102,0,4), (32,0,87,0,8), (64,0,55,0,7), (65,0,54,0,5), (66,0,53,0,5), (80,0,39,0,4)]
def g119D5 (j : Nat) : Nat := if j = 0 then 0x2f88a17540d01 else 0
def g119D6 (j : Nat) : Nat := if j = 0 then 0x406cf8e58441427c064a17a728204a14e5a06e7c070c57a030380973e2af40704685bf9b8903a8c0017b89d6540f7713aca81cee2759503eb26a82a07fc5d503407e89aa0680ef36540d01 else 0
def g119D7 (j : Nat) : Nat := if j = 0 then 0x19e081e51741320a104c30a6491d418c299e081e5d04c8284c3192781c5d3284128a649e071a5174c812d9e18195d140e2841800359e35d038828482d9e06d740e28402b9e07195d038820602e167b19e571143008a12000bfd9503ff59503bf59503f74d503fe41503fd4d501bdd9501bd59501fc40d01 else 0
def g119D8 (j : Nat) : Nat := if j = 0 then 0x52708a968490825e53841cb4248412f38ad0620808d6b807f417fa07f501 else 0
def g119D9 (j : Nat) : Nat := if j = 0 then 0x130a84233f else 0
def g119L : Nat → Packing
  | 5 => (1, 4, 4, 0, 0, 1, 0, g119D5)
  | 6 => (7, 3, 4, 0, 0, 9, 0, g119D6)
  | 7 => (9, 2, 4, 0, 0, 10, 0, g119D7)
  | 8 => (3, 1, 4, 0, 0, 7, 0, g119D8)
  | 9 => (1, 0, 4, 0, 0, 1, 0, g119D9)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x8 else 0) tag
  | 7, tag => lookupShort 4 13 1 6 3 1 (fun j => if j=0 then 0x485000009016d13c214 else 0) tag
  | 8, tag => lookupShort 6 17 3 7 4 1 (fun j => if j=0 then 0x8034469ce2809084007000000007884088 else 0) tag
  | 9, tag => lookupShort 3 8 1 5 2 1 (fun j => if j=0 then 0x8a1e001000 else 0) tag
  | _, _ => none
def g119 : Forest := ⟨119, 9, fun i => (g119Y[i]?).getD (0,0), g119C, [[], [96]], g119L, g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5n0 : block g119 5 0 1 = true := by decide +kernel
theorem g119B5 : block g119 5 0 1 = true := g119P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6n0 : block g119 6 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6n2 : block g119 6 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6n4 : block g119 6 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6n6 : block g119 6 6 1 = true := by decide +kernel
theorem g119B6 : block g119 6 0 7 = true := (@block_merge g119 6 0 4 3 (@block_merge g119 6 0 2 2 g119P6n0 g119P6n2) (@block_merge g119 6 4 2 1 g119P6n4 g119P6n6))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7n0 : block g119 7 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7n2 : block g119 7 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7n4 : block g119 7 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7n6 : block g119 7 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7n8 : block g119 7 8 1 = true := by decide +kernel
theorem g119B7 : block g119 7 0 9 = true := (@block_merge g119 7 0 4 5 (@block_merge g119 7 0 2 2 g119P7n0 g119P7n2) (@block_merge g119 7 4 2 3 g119P7n4 (@block_merge g119 7 6 2 1 g119P7n6 g119P7n8)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8n0 : block g119 8 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8n2 : block g119 8 2 1 = true := by decide +kernel
theorem g119B8 : block g119 8 0 3 = true := (@block_merge g119 8 0 2 1 g119P8n0 g119P8n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P9n0 : block g119 9 0 1 = true := by decide +kernel
theorem g119B9 : block g119 9 0 1 = true := g119P9n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
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
theorem low119 : Lower true (varsX 119) (graphGoal 119) 10 := lower_forest (g:=g119) (i:=0) (hints:=66) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 10 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)

def g123Y : Array (Bits × Bits) := #[((repeatRows 583 0x555555575556daaaaaaabaaab6d5555555d555b6aaaaaaaeaaadb555555575556daaaaaaabaaab6d5555555d555b6aaaaaaaeaaadb555555575556daaaaaaabaaab6d5555555d555b6), (repeatRows 583 0x3ffffffffffffe0000000000000fffffffffffff80000000000003ffffffffffffe0000000000000)),
    ((repeatRows 583 0x66666665999b6f3333332cccdb799999996666dbcccccccb3336de6666665999b6f3333332cccdb799999996666dbcccccccb3336de6666665999b6f3333332cccdb799999996666db), (repeatRows 583 0x7ffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffc00000000000000000000000000)),
    (0x0, 0x0),
    ((repeatRows 583 0x78787879e1e38fc3c3c3cf0f1c7e1e1e1e7878e3f0f0f0f3c3c71f8787879e1e38fc3c3c3cf0f1c7e1e1e1e7878e3f0f0f0f3c3c71f8787879e1e38fc3c3c3cf0f1c7e1e1e1e7878e3), (repeatRows 583 0xfffffffffffff80000000000003ffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000)),
    ((repeatRows 583 0x7f807f81fe03f3fc03fc0ff01f9fe01fe07f80fcff00ff03fc07e7f807f81fe03f3fc03fc0ff01f9fe01fe07f80fcff00ff03fc07e7f807f81fe03f3fc03fc0ff01f9fe01fe07f80fc), (repeatRows 583 0xffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    ((repeatRows 583 0x7fff8001fffc03fffc000fffe01fffe0007fff00ffff0003fff807fff8001fffc03fffc000fffe01fffe0007fff00ffff0003fff807fff8001fffc03fffc000fffe01fffe0007fff00), (repeatRows 583 0x1fffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    ((repeatRows 583 0x7ffffffe000003fffffff000001fffffff800000fffffffc000007ffffffe000003fffffff000001fffffff800000fffffffc000007ffffffe000003fffffff000001fffffff800000), (repeatRows 583 0x7fffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))]
def g123C : List ColumnInfo := [(1,0,122,0,6), (2,0,121,0,8), (3,0,120,0,5), (8,0,115,0,8), (9,0,114,0,5), (10,0,113,0,7), (16,0,107,0,7), (17,0,106,0,5), (24,0,99,0,5), (26,0,97,0,4), (32,0,91,0,6), (34,0,89,0,5), (40,0,83,0,5), (48,0,75,0,4), (64,0,59,0,7), (65,0,58,0,5), (66,0,57,0,5), (72,0,51,0,5), (74,0,49,0,4), (80,0,43,0,5), (81,0,42,0,4), (96,0,27,0,4)]
def g123D4 (j : Nat) : Nat := if j = 0 then 0x900201400800140081c65138b0c0651615155ce6448f28a6bc2c2eb224754595de1154d123aa32caf08aa6891dc1657484553448fa8412baa2a9a24770649595154d123 else 0
def g123D5 (j : Nat) : Nat := if j = 0 then 0x4008441005c08000020040000000005c0803004000000400802a04041a80200568808268708281350078604008a202000608000000a88c100000075f91b9d9e933d98c960efb77b8daecb5fa852a773597ca64714873fdf2e16db0d568a3d9d4ba5724108783618060240c030027986176d15239cd8399d4548ed99216545523f0d454d66448fd14d51599123d4d355d66448f594557599123d8d455ce6448e736157399123dc5155ce6448e738e175591239e6185d56448e7a8217559123e2d455956448f53dd53559123f0d454d56448f995951559123f45354556448f714d617591239e78585d6448e796161759123bca085d53448f72821754d123b8e485953448fc3515654d123dc7784553448f715e1154d123f87484553448fe1521154d123f45754553448f515d5154d123f45454553448fc1515154d123f45654553448e7986176811239cd8399d0448e5be1574419239ce385d10648e798617441923d8f744d10648fe24d10441923bc9809d123c0eb361a7448f03bc6185d123c0ef28217448f03 else 0
def g123D6 (j : Nat) : Nat := if j = 0 then 0xd76371f0881c140c18a09970705430371f0920208502184210a5715230301f0901000997868308220c108950428265c100dc230904a442882822605e5c918d0b8642c058a0998172423a342e1d0b016017025c083021a54100d8607c2424048302180c4219090041809706045c09706045088605d181c61085198d86c2206030428dc1a100dc2403898683862826dc1a07c24038a09b71504708cdc1a550c0c28a3706950403708e22541018a374443c341b0d0100e4010a06950403f0900e184210a06950301f08c023031006280e8c0c07c240395031006281a54100e8c0dc24048302045c4211563309008541008402152302068008641b0a0089e1a11c2802a7840370a00a0208002140c0018a0503a30371f0801118916d1210e504902d010fe4f58f4cf00ed4ea8e3cdf0d34c78c6cc50c34c18b7cb60b24af8adcab0a94a48a0c9e09949688ec8b08347c876c6f06b46285fc5805544e84dc4a04243e834c3202f42a825c2202041b815c1000e40c808c0017e81d654d37d03aca9a4fa0759534eba8a9aa69c7515354d36f1b2688279e364d104bdaeda2a47735cf4548ef733a8a91fcd3751523bdc8eb2a47db5156548fa6a2a6a91fe56745523ecaca8aa47d14d51548fd6a2cc891fcd3599123fca2b322477b5d66448ee6b9cc891ded7099123bdeeab22477b5d56448fd7a2ac891fad4559123ddacab2247f34d56448ff28aac891fe61759123bcc2eb22477b81d6448ee7baa6891fcd754d123b9aea9a247e3d153448fe6a2a6891f8d454d123f9aca9a247f14553448fe683a6891f8d3481123bdaed02247735ce0448ef733a0891fce3741123b9c6e82247f34d10448fc69a20891def7441923bdae883247bb5910648fe69a20c91fe90441923f9ce891e07f35d123c0fe48224781ecd6448f03dbc6eb2207f68dd0440fec9a20881f993441103 else 0
def g123D7 (j : Nat) : Nat := if j = 0 then 0x28b870a8c1b183c2040165070a0f1836307840802ca2e1c36306c60f0810059526b870d0e315284d70d8d8c1e10200b284d70e1a2a306c784a2ab870d151830e54a2e1c345460d8f094509ae1c34506c784929b870d0f18363078408030687001941a283a60d8f08024a0e1a283a60d8c1e10200c1e385070d8c1e1420401629306002141c283a60d8c1e10200b1a1d30610a0a0e98363c20081a29306002941a283a60d8f080247ee141d363c20081fb8507cd8c121004945eb95088c1a1e14280b28bd72a1118343c285016508af5ca844687850a02ca135c20386860f0a028a305eba4478d0d092b95088d0f0a14042e18a844687850a024a6e1aa84070d0c1e1405945ca84078c1a1e14280b28b95080f18343c2850165172a101e30487850a02c78d1518363c20081e3a306c60f081004cfdc2032307860105070d0f1b183c204928345070d8f08020a0a0f18363c2008a459f299f96f91c8d089984d8087ae79374e6f46a167f62c60a5cc5a355e5204db4884353e23963513132ce27b2281d51821440ff0c107c03e000bf59634bf58234bfd9534ff59534bf59534efd1534ff51534ef51534f74d534bf81934ff41934ef4d204bf58e04bf58204ff8d904bf8d904ff4d904ef8d104ff4d104ef4d104b758c04bd58404fbd1523fb51523fb59523f34d523f945523fb99123fb59123f34d123fb81123fb41123fb41923fe41303bf59303f348f03bf59103f74d103fe41103 else 0
def g123D8 (j : Nat) : Nat := if j = 0 then 0x144ce2871a30e10402d4b8e2871a30e10402d4b8e34a1c68c384100c3ee38a1e61a30e10403143ee38a1e61a30e10403543ee38a1e61a30e104034fb8e2879868c384100c52e2071838473ee38a1a30e1040294b8e2871a30e10402e94931fe6c15c420ba22848003fa6bfe34fe9a7fc13fc09fd04fe027b48ffe07fd03 else 0
def g123D9 (j : Nat) : Nat := if j = 0 then 0xe30c223f else 0
def g123L : Nat → Packing
  | 4 => (7, 5, 5, 0, 0, 6, 0, g123D4)
  | 5 => (45, 4, 5, 0, 0, 9, 0, g123D5)
  | 6 => (63, 3, 5, 0, 0, 12, 0, g123D6)
  | 7 => (39, 2, 5, 0, 0, 12, 0, g123D7)
  | 8 => (10, 1, 5, 0, 0, 10, 0, g123D8)
  | 9 => (1, 0, 5, 0, 0, 1, 0, g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 5, tag => lookupShort 5 17 1 6 3 1 (fun j => if j=0 then 0x36000001ac4046803e4da759 else 0) tag
  | 6, tag => lookupShort 27 81 4 9 6 1 (fun j => if j=0 then 0x4c80001a500000471504003582b83000000c01000019c0049c00260055b031f000000000000020000002140124508480014459a00000c7a6b3b2968146135bd406f0e00d02359e22cf45ca7840745b5400004441410c186326d2800017006a20001005021032020 else 0) tag
  | 7, tag => lookupShort 37 110 4 9 6 1 (fun j => if j=0 then 0x2e95526f400008cbd9768814800011c800c000004d80000210061a5a8d00000002f0000324aeac384721d0001e461fab08b193e558017927daa250a00002680000002c8013a004056d31c5ca159aab580001984700000831a000019300000000000629e31647ede298212dd2b31e005bdb7a619802200048ce008a002013130d3302130003000308200218010002 else 0) tag
  | 8, tag => lookupShort 30 89 4 9 6 1 (fun j => if j=0 then 0x1a687e051200d24322000000013250c3f5c00000000336000062c4a5423e5c010e4166b8020e16151a4ff0e23b19d9144abdd2001682a00455352998c32109000e9a580000c8f5801d50000000004e0033f9e0000001a10000000d191f6d06130000001c5372590001216101008002100310000 else 0) tag
  | 9, tag => lookupShort 8 23 3 7 4 1 (fun j => if j=0 then 0x19742170413840000880c40319700000004048329207118 else 0) tag
  | _, _ => none
def g123 : Forest := ⟨123, 9, fun i => (g123Y[i]?).getD (0,0), g123C, [[], [49, 100]], g123L, g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P4n0 : block g123 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P4n2 : block g123 4 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P4n4 : block g123 4 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P4n6 : block g123 4 6 1 = true := by decide +kernel
theorem g123B4 : block g123 4 0 7 = true := (@block_merge g123 4 0 4 3 (@block_merge g123 4 0 2 2 g123P4n0 g123P4n2) (@block_merge g123 4 4 2 1 g123P4n4 g123P4n6))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n0 : block g123 5 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n2 : block g123 5 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n4 : block g123 5 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n6 : block g123 5 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n8 : block g123 5 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n10 : block g123 5 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n12 : block g123 5 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n14 : block g123 5 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n16 : block g123 5 16 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n18 : block g123 5 18 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n20 : block g123 5 20 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n22 : block g123 5 22 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n24 : block g123 5 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n26 : block g123 5 26 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n28 : block g123 5 28 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n30 : block g123 5 30 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n32 : block g123 5 32 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n34 : block g123 5 34 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n36 : block g123 5 36 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n38 : block g123 5 38 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n40 : block g123 5 40 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n42 : block g123 5 42 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5n44 : block g123 5 44 1 = true := by decide +kernel
theorem g123B5 : block g123 5 0 45 = true := (@block_merge g123 5 0 22 23 (@block_merge g123 5 0 10 12 (@block_merge g123 5 0 4 6 (@block_merge g123 5 0 2 2 g123P5n0 g123P5n2) (@block_merge g123 5 4 2 4 g123P5n4 (@block_merge g123 5 6 2 2 g123P5n6 g123P5n8))) (@block_merge g123 5 10 6 6 (@block_merge g123 5 10 2 4 g123P5n10 (@block_merge g123 5 12 2 2 g123P5n12 g123P5n14)) (@block_merge g123 5 16 2 4 g123P5n16 (@block_merge g123 5 18 2 2 g123P5n18 g123P5n20)))) (@block_merge g123 5 22 12 11 (@block_merge g123 5 22 6 6 (@block_merge g123 5 22 2 4 g123P5n22 (@block_merge g123 5 24 2 2 g123P5n24 g123P5n26)) (@block_merge g123 5 28 2 4 g123P5n28 (@block_merge g123 5 30 2 2 g123P5n30 g123P5n32))) (@block_merge g123 5 34 6 5 (@block_merge g123 5 34 2 4 g123P5n34 (@block_merge g123 5 36 2 2 g123P5n36 g123P5n38)) (@block_merge g123 5 40 2 3 g123P5n40 (@block_merge g123 5 42 2 1 g123P5n42 g123P5n44)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n0 : block g123 6 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n2 : block g123 6 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n4 : block g123 6 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n6 : block g123 6 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n8 : block g123 6 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n10 : block g123 6 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n12 : block g123 6 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n14 : block g123 6 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n16 : block g123 6 16 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n18 : block g123 6 18 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n20 : block g123 6 20 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n22 : block g123 6 22 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n24 : block g123 6 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n26 : block g123 6 26 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n28 : block g123 6 28 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n30 : block g123 6 30 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n32 : block g123 6 32 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n34 : block g123 6 34 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n36 : block g123 6 36 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n38 : block g123 6 38 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n40 : block g123 6 40 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n42 : block g123 6 42 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n44 : block g123 6 44 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n46 : block g123 6 46 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n48 : block g123 6 48 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n50 : block g123 6 50 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n52 : block g123 6 52 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n54 : block g123 6 54 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n56 : block g123 6 56 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n58 : block g123 6 58 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n60 : block g123 6 60 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6n62 : block g123 6 62 1 = true := by decide +kernel
theorem g123B6 : block g123 6 0 63 = true := (@block_merge g123 6 0 32 31 (@block_merge g123 6 0 16 16 (@block_merge g123 6 0 8 8 (@block_merge g123 6 0 4 4 (@block_merge g123 6 0 2 2 g123P6n0 g123P6n2) (@block_merge g123 6 4 2 2 g123P6n4 g123P6n6)) (@block_merge g123 6 8 4 4 (@block_merge g123 6 8 2 2 g123P6n8 g123P6n10) (@block_merge g123 6 12 2 2 g123P6n12 g123P6n14))) (@block_merge g123 6 16 8 8 (@block_merge g123 6 16 4 4 (@block_merge g123 6 16 2 2 g123P6n16 g123P6n18) (@block_merge g123 6 20 2 2 g123P6n20 g123P6n22)) (@block_merge g123 6 24 4 4 (@block_merge g123 6 24 2 2 g123P6n24 g123P6n26) (@block_merge g123 6 28 2 2 g123P6n28 g123P6n30)))) (@block_merge g123 6 32 16 15 (@block_merge g123 6 32 8 8 (@block_merge g123 6 32 4 4 (@block_merge g123 6 32 2 2 g123P6n32 g123P6n34) (@block_merge g123 6 36 2 2 g123P6n36 g123P6n38)) (@block_merge g123 6 40 4 4 (@block_merge g123 6 40 2 2 g123P6n40 g123P6n42) (@block_merge g123 6 44 2 2 g123P6n44 g123P6n46))) (@block_merge g123 6 48 8 7 (@block_merge g123 6 48 4 4 (@block_merge g123 6 48 2 2 g123P6n48 g123P6n50) (@block_merge g123 6 52 2 2 g123P6n52 g123P6n54)) (@block_merge g123 6 56 4 3 (@block_merge g123 6 56 2 2 g123P6n56 g123P6n58) (@block_merge g123 6 60 2 1 g123P6n60 g123P6n62)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n0 : block g123 7 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n2 : block g123 7 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n4 : block g123 7 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n6 : block g123 7 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n8 : block g123 7 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n10 : block g123 7 10 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n12 : block g123 7 12 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n14 : block g123 7 14 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n16 : block g123 7 16 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n18 : block g123 7 18 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n20 : block g123 7 20 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n22 : block g123 7 22 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n24 : block g123 7 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n26 : block g123 7 26 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n28 : block g123 7 28 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n30 : block g123 7 30 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n32 : block g123 7 32 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n34 : block g123 7 34 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n36 : block g123 7 36 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7n38 : block g123 7 38 1 = true := by decide +kernel
theorem g123B7 : block g123 7 0 39 = true := (@block_merge g123 7 0 20 19 (@block_merge g123 7 0 10 10 (@block_merge g123 7 0 4 6 (@block_merge g123 7 0 2 2 g123P7n0 g123P7n2) (@block_merge g123 7 4 2 4 g123P7n4 (@block_merge g123 7 6 2 2 g123P7n6 g123P7n8))) (@block_merge g123 7 10 4 6 (@block_merge g123 7 10 2 2 g123P7n10 g123P7n12) (@block_merge g123 7 14 2 4 g123P7n14 (@block_merge g123 7 16 2 2 g123P7n16 g123P7n18)))) (@block_merge g123 7 20 10 9 (@block_merge g123 7 20 4 6 (@block_merge g123 7 20 2 2 g123P7n20 g123P7n22) (@block_merge g123 7 24 2 4 g123P7n24 (@block_merge g123 7 26 2 2 g123P7n26 g123P7n28))) (@block_merge g123 7 30 4 5 (@block_merge g123 7 30 2 2 g123P7n30 g123P7n32) (@block_merge g123 7 34 2 3 g123P7n34 (@block_merge g123 7 36 2 1 g123P7n36 g123P7n38)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8n0 : block g123 8 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8n2 : block g123 8 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8n4 : block g123 8 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8n6 : block g123 8 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8n8 : block g123 8 8 2 = true := by decide +kernel
theorem g123B8 : block g123 8 0 10 = true := (@block_merge g123 8 0 4 6 (@block_merge g123 8 0 2 2 g123P8n0 g123P8n2) (@block_merge g123 8 4 2 4 g123P8n4 (@block_merge g123 8 6 2 2 g123P8n6 g123P8n8)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P9n0 : block g123 9 0 1 = true := by decide +kernel
theorem g123B9 : block g123 9 0 1 = true := g123P9n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact g123B4
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=4148) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)

def g125Y : Array (Bits × Bits) := #[((repeatRows 583 0x55555555aaaedeaaaaaaad5576f55555556aabb7aaaaaaab555dbd5555555aaaedeaaaaaaad5576f55555556aabb7aaaaaaab555dbd5555555aaaedeaaaaaaad5576f55555556aabb7), (repeatRows 583 0x1fffffffffffff000000000000000000000000003ffffffffffffe0000000000000)),
    (0x0, 0x0),
    ((repeatRows 583 0x66666666cccb6f33333336665b79999999b332dbcccccccd9996de6666666cccb6f33333336665b79999999b332dbcccccccd9996de6666666cccb6f33333336665b79999999b332db), (repeatRows 583 0x3ffffffffffffe0000000000000000000000000000000000000003ffffffffffffe000000000000000000000000007ffffffffffffc00000000000000000000000000)),
    ((repeatRows 583 0x78787878f0f38bc3c3c3c7879c5e1e1e1e3c3ce2f0f0f0f1e1e7178787878f0f38bc3c3c3c7879c5e1e1e1e3c3ce2f0f0f0f1e1e7178787878f0f38bc3c3c3c7879c5e1e1e1e3c3ce2), (repeatRows 583 0xfffffffffffff80000000000003fffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000000000)),
    ((repeatRows 583 0x7f807f80ff03f3fc03fc07f81f9fe01fe03fc0fcff00ff01fe07e7f807f80ff03f3fc03fc07f81f9fe01fe03fc0fcff00ff01fe07e7f807f80ff03f3fc03fc07f81f9fe01fe03fc0fc), (repeatRows 583 0xffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    ((repeatRows 583 0x7fff8000fffc03fffc0007ffe01fffe0003fff00ffff0001fff807fff8000fffc03fffc0007ffe01fffe0003fff00ffff0001fff807fff8000fffc03fffc0007ffe01fffe0003fff00), (repeatRows 583 0x3ffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    ((repeatRows 583 0x7fffffff000003fffffff800001fffffffc00000fffffffe000007fffffff000003fffffff800001fffffffc00000fffffffe000007fffffff000003fffffff800001fffffffc00000), (repeatRows 583 0x7ffffffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))]
def g125C : List ColumnInfo := [(0,8,21,96,6), (1,0,124,0,7), (4,0,121,0,8), (8,0,117,0,8), (9,0,116,0,5), (16,0,109,0,7), (17,0,108,0,5), (24,0,101,0,5), (32,0,93,0,8), (64,0,61,0,7), (64,8,21,32,5), (65,0,60,0,4), (80,0,45,0,4)]
def g125D5 (j : Nat) : Nat := if j = 0 then 0x2f88613741502 else 0
def g125D6 (j : Nat) : Nat := if j = 0 then 0x207c65e78441427c064a179f28204a0cd59062c519f0d42720380973e2a84e484685bf9b8903a8c0017d85d364177b0baca81cf61759503eb26a82a07fa4dd0540bb49aa0a816e905d8d02 else 0
def g125D7 (j : Nat) : Nat := if j = 0 then 0xba782151730f20a104c30b19515218c2c9e15173ca104a30b6782069730f20a130b2992781a5173c812ca678615123c9284180034b299e351230f20602f9e151230f28482b9e075448f28402a167b1aa571143007810800bf8d905ff4d905df4d505bf59503fe41503fb4d502fa41502bbd8d02bb58d02 else 0
def g125D8 (j : Nat) : Nat := if j = 0 then 0x5a708a966390825e538418b31c8412f38a90720808d6b807f417fa07ed02 else 0
def g125D9 (j : Nat) : Nat := if j = 0 then 0x130a64233f else 0
def g125L : Nat → Packing
  | 5 => (1, 4, 4, 0, 0, 1, 0, g125D5)
  | 6 => (7, 3, 4, 0, 0, 9, 0, g125D6)
  | 7 => (9, 2, 4, 0, 0, 10, 0, g125D7)
  | 8 => (3, 1, 4, 0, 0, 7, 0, g125D8)
  | 9 => (1, 0, 4, 0, 0, 1, 0, g125D9)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 6, tag => lookupShort 1 2 1 3 1 0 (fun j => if j=0 then 0x20 else 0) tag
  | 7, tag => lookupShort 4 12 2 6 3 1 (fun j => if j=0 then 0x5226404c0800d85c40c0 else 0) tag
  | 8, tag => lookupShort 6 17 3 7 4 1 (fun j => if j=0 then 0x9f134ca0200300000000023086e6918d87 else 0) tag
  | 9, tag => lookupShort 3 8 1 5 2 1 (fun j => if j=0 then 0x1407241060 else 0) tag
  | _, _ => none
def g125 : Forest := ⟨125, 9, fun i => (g125Y[i]?).getD (0,0), g125C, [[], [64]], g125L, g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5n0 : block g125 5 0 1 = true := by decide +kernel
theorem g125B5 : block g125 5 0 1 = true := g125P5n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6n0 : block g125 6 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6n2 : block g125 6 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6n4 : block g125 6 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6n6 : block g125 6 6 1 = true := by decide +kernel
theorem g125B6 : block g125 6 0 7 = true := (@block_merge g125 6 0 4 3 (@block_merge g125 6 0 2 2 g125P6n0 g125P6n2) (@block_merge g125 6 4 2 1 g125P6n4 g125P6n6))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7n0 : block g125 7 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7n2 : block g125 7 2 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7n4 : block g125 7 4 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7n6 : block g125 7 6 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7n8 : block g125 7 8 1 = true := by decide +kernel
theorem g125B7 : block g125 7 0 9 = true := (@block_merge g125 7 0 4 5 (@block_merge g125 7 0 2 2 g125P7n0 g125P7n2) (@block_merge g125 7 4 2 3 g125P7n4 (@block_merge g125 7 6 2 1 g125P7n6 g125P7n8)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8n0 : block g125 8 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8n2 : block g125 8 2 1 = true := by decide +kernel
theorem g125B8 : block g125 8 0 3 = true := (@block_merge g125 8 0 2 1 g125P8n0 g125P8n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P9n0 : block g125 9 0 1 = true := by decide +kernel
theorem g125B9 : block g125 9 0 1 = true := g125P9n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g125 0 0 0 = true)
  · exact (rfl : block g125 1 0 0 = true)
  · exact (rfl : block g125 2 0 0 = true)
  · exact (rfl : block g125 3 0 0 = true)
  · exact (rfl : block g125 4 0 0 = true)
  · exact g125B5
  · exact g125B6
  · exact g125B7
  · exact g125B8
  · exact g125B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 10 := lower_forest (g:=g125) (i:=0) (hints:=20482) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 10 [(125,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)

def g126Y : Array (Bits × Bits) := #[(0x0, 0x0),
    ((repeatRows 624 0xaaaaaaaaaabb7aaaaaaaaaabb7aaaaaaaaaabb7aaaaaaaaaabb7aaaaaaaaaabb7aaaaaaaaaabb7aaaaaaaaaabb7aaaaaaaaaabb7aaaaaaaaaabb7aaaaaaaaaabb7aaaaaaaaaabb7aaaaaaaaaabb7), (repeatRows 624 0xfffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffffffffff0000000000000fffffffffffff0000000000000)),
    ((repeatRows 624 0xcccccccf332dacccccccf332dacccccccf332dacccccccf332dacccccccf332dacccccccf332dacccccccf332dacccccccf332dacccccccf332dacccccccf332dacccccccf332dacccccccf332da), (repeatRows 624 0xfffffffffffff000000000000000000000000000000000000000fffffffffffff0000000000000ffffffffffffffffffffffffff00000000000000000000000000)),
    ((repeatRows 624 0xf0f0f0f3c3ce3f0f0f0f3c3ce3f0f0f0f3c3ce3f0f0f0f3c3ce3f0f0f0f3c3ce3f0f0f0f3c3ce3f0f0f0f3c3ce3f0f0f0f3c3ce3f0f0f0f3c3ce3f0f0f0f3c3ce3f0f0f0f3c3ce3f0f0f0f3c3ce3), (repeatRows 624 0xfffffffffffff0000000000000ffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000)),
    ((repeatRows 624 0xff00ff03fc0fcff00ff03fc0fcff00ff03fc0fcff00ff03fc0fcff00ff03fc0fcff00ff03fc0fcff00ff03fc0fcff00ff03fc0fcff00ff03fc0fcff00ff03fc0fcff00ff03fc0fcff00ff03fc0fc), (repeatRows 624 0xffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    ((repeatRows 624 0xffff0003fff00ffff0003fff00ffff0003fff00ffff0003fff00ffff0003fff00ffff0003fff00ffff0003fff00ffff0003fff00ffff0003fff00ffff0003fff00ffff0003fff00ffff0003fff00), (repeatRows 624 0xffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)),
    ((repeatRows 624 0xfffffffc00000fffffffc00000fffffffc00000fffffffc00000fffffffc00000fffffffc00000fffffffc00000fffffffc00000fffffffc00000fffffffc00000fffffffc00000fffffffc00000), (repeatRows 624 0xffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))]
def g126C : List ColumnInfo := [(0,4,42,80,6), (2,0,124,0,7), (4,0,122,0,6), (8,0,118,0,7), (16,0,110,0,7), (64,0,62,0,7)]
def g126D7 (j : Nat) : Nat := if j = 0 then 0xdcb2901b72ca45d03ee29f514 else 0
def g126D8 (j : Nat) : Nat := if j = 0 then 0x58d1033f else 0
def g126L : Nat → Packing
  | 7 => (2, 1, 3, 0, 0, 5, 0, g126D7)
  | 8 => (1, 0, 3, 0, 0, 1, 0, g126D8)
  | _ => emptyPacking
def g126I : Nat → Nat → Option (Nat × Nat)
  | 8, tag => lookupShort 1 3 1 3 1 0 (fun j => if j=0 then 0x18 else 0) tag
  | _, _ => none
def g126 : Forest := ⟨126, 8, fun i => (g126Y[i]?).getD (0,0), g126C, [[], [49, 100]], g126L, g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7n0 : block g126 7 0 2 = true := by decide +kernel
theorem g126B7 : block g126 7 0 2 = true := g126P7n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P8n0 : block g126 8 0 1 = true := by decide +kernel
theorem g126B8 : block g126 8 0 1 = true := g126P8n0
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
  · exact g126B7
  · exact g126B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 9 := lower_forest (g:=g126) (i:=0) (hints:=34673712) (before_sound K125 V125) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 9 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)

def g127Y : Array (Bits × Bits) := #[(0x55555555555555575555556d5ab6eaaaaaaaaaaaaaabaaaaaab6ad5b7555555555555555d555555b56adbaaaaaaaaaaaaaaaeaaaaaadab56dd5555555555555575555556d5ab6eaaaaaaaaaaaaaabaaaaaab6ad5b7555555555555555d555555b56adbaaaaaaaaaaaaaaaeaaaaaadab56dd5555555555555575555556d5ab6eaaaaaaaaaaaaaabaaaaaab6ad5b7555555555555555d555555b56adbaaaaaaaaaaaaaaaeaaaaaadab56dd5555555555555575555556d5ab6eaaaaaaaaaaaaaabaaaaaab6ad5b7555555555555555d555555b56adb, 0xffffffffffffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffff80000000000000000000000000003fffffffffffffffffffffffffffe0000000000000000000000000000),
    (0x6666666666666665999999b66cdbb333333333333332ccccccdb366dd9999999999999996666666d9b36ecccccccccccccccb3333336cd9b76666666666666665999999b66cdbb333333333333332ccccccdb366dd9999999999999996666666d9b36ecccccccccccccccb3333336cd9b76666666666666665999999b66cdbb333333333333332ccccccdb366dd9999999999999996666666d9b36ecccccccccccccccb3333336cd9b76666666666666665999999b66cdbb333333333333332ccccccdb366dd9999999999999996666666d9b36e, 0x7fffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffffffffffffffffffffffe0000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000000000000000000),
    (0x7878787878787879e1e1e1c78f1cfc3c3c3c3c3c3c3cf0f0f0e3c78e7e1e1e1e1e1e1e1e78787871e3c73f0f0f0f0f0f0f0f3c3c3c38f1e39f878787878787879e1e1e1c78f1cfc3c3c3c3c3c3c3cf0f0f0e3c78e7e1e1e1e1e1e1e1e78787871e3c73f0f0f0f0f0f0f0f3c3c3c38f1e39f878787878787879e1e1e1c78f1cfc3c3c3c3c3c3c3cf0f0f0e3c78e7e1e1e1e1e1e1e1e78787871e3c73f0f0f0f0f0f0f0f3c3c3c38f1e39f878787878787879e1e1e1c78f1cfc3c3c3c3c3c3c3cf0f0f0e3c78e7e1e1e1e1e1e1e1e78787871e3c73, 0x1ffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000001ffffffffffffffffffffffffffff000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    (0x7f807f807f807f81fe01fe07f01f3fc03fc03fc03fc0ff00ff03f80f9fe01fe01fe01fe07f807f81fc07cff00ff00ff00ff03fc03fc0fe03e7f807f807f807f81fe01fe07f01f3fc03fc03fc03fc0ff00ff03f80f9fe01fe01fe01fe07f807f81fc07cff00ff00ff00ff03fc03fc0fe03e7f807f807f807f81fe01fe07f01f3fc03fc03fc03fc0ff00ff03f80f9fe01fe01fe01fe07f807f81fc07cff00ff00ff00ff03fc03fc0fe03e7f807f807f807f81fe01fe07f01f3fc03fc03fc03fc0ff00ff03f80f9fe01fe01fe01fe07f807f81fc07c, 0x7fffffffffffffffffffffffffffc0000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    (0x7fff80007fff8001fffe0007ffe03fffc0003fffc000ffff0003fff01fffe0001fffe0007fff8001fff80ffff0000ffff0003fffc000fffc07fff80007fff8001fffe0007ffe03fffc0003fffc000ffff0003fff01fffe0001fffe0007fff8001fff80ffff0000ffff0003fffc000fffc07fff80007fff8001fffe0007ffe03fffc0003fffc000ffff0003fff01fffe0001fffe0007fff8001fff80ffff0000ffff0003fffc000fffc07fff80007fff8001fffe0007ffe03fffc0003fffc000ffff0003fff01fffe0001fffe0007fff8001fff80, 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    (0x7fffffff80000001fffffff800003fffffffc0000000fffffffc00001fffffffe00000007ffffffe00000ffffffff00000003fffffff000007fffffff80000001fffffff800003fffffffc0000000fffffffc00001fffffffe00000007ffffffe00000ffffffff00000003fffffff000007fffffff80000001fffffff800003fffffffc0000000fffffffc00001fffffffe00000007ffffffe00000ffffffff00000003fffffff000007fffffff80000001fffffff800003fffffffc0000000fffffffc00001fffffffe00000007ffffffe00000, 0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000),
    (0x7ffffffffffffffe0000000000003fffffffffffffff0000000000001fffffffffffffff8000000000000fffffffffffffffc0000000000007ffffffffffffffe0000000000003fffffffffffffff0000000000001fffffffffffffff8000000000000fffffffffffffffc0000000000007ffffffffffffffe0000000000003fffffffffffffff0000000000001fffffffffffffff8000000000000fffffffffffffffc0000000000007ffffffffffffffe0000000000003fffffffffffffff0000000000001fffffffffffffff8000000000000, 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)]
def g127C : List ColumnInfo := [(1,0,126,0,9), (1,4,42,80,6), (2,0,125,0,10), (4,0,123,0,10), (8,0,119,0,10), (16,0,111,0,10), (32,0,95,0,9), (36,0,91,0,6), (64,0,63,0,10)]
def g127D8 (j : Nat) : Nat := if j = 0 then 0xf01faf4c68f9322506817e03f5e98c1f225409f1d7a53e4c900ff1b80f6e5841d25b6e5841d25f6a0849505 else 0
def g127D9 (j : Nat) : Nat := if j = 0 then 0x70c4daaba291879240a06f0c4daaba291e4902819c0dae89879404421b007ee07497f683a4bdb49505 else 0
def g127D10 (j : Nat) : Nat := if j = 0 then 0x18356839407c20d52d0931c84032100fb497fd05 else 0
def g127D11 (j : Nat) : Nat := if j = 0 then 0x21950c8077f else 0
def g127L : Nat → Packing
  | 8 => (3, 3, 4, 0, 0, 7, 0, g127D8)
  | 9 => (3, 2, 4, 0, 0, 8, 0, g127D9)
  | 10 => (2, 1, 4, 0, 0, 7, 0, g127D10)
  | 11 => (1, 0, 4, 0, 0, 1, 0, g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 9, tag => lookupShort 2 5 1 4 2 0 (fun j => if j=0 then 0x2b0014 else 0) tag
  | 10, tag => lookupShort 2 5 1 4 2 0 (fun j => if j=0 then 0x242810 else 0) tag
  | 11, tag => lookupShort 1 3 1 3 1 0 (fun j => if j=0 then 0x7c else 0) tag
  | _, _ => none
def g127 : Forest := ⟨127, 11, fun i => (g127Y[i]?).getD (0,0), g127C, [[], [49, 100]], g127L, g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n0 : block g127 8 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8n2 : block g127 8 2 1 = true := by decide +kernel
theorem g127B8 : block g127 8 0 3 = true := (@block_merge g127 8 0 2 1 g127P8n0 g127P8n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n0 : block g127 9 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9n2 : block g127 9 2 1 = true := by decide +kernel
theorem g127B9 : block g127 9 0 3 = true := (@block_merge g127 9 0 2 1 g127P9n0 g127P9n2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10n0 : block g127 10 0 2 = true := by decide +kernel
theorem g127B10 : block g127 10 0 2 = true := g127P10n0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P11n0 : block g127 11 0 1 = true := by decide +kernel
theorem g127B11 : block g127 11 0 1 = true := g127P11n0
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
  · exact g127B8
  · exact g127B9
  · exact g127B10
  · exact g127B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=4146) (before_sound K126 V126) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end PEqualNP.Outside.L_meta_52070.Certificate10560

namespace PEqualNP.Outside.L_meta_52070

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

private theorem signed_av {s : Set F} (point : Certificate10560.Row → X)
    {bank : List (Certificate10560.Wire Certificate10560.Row)}
    (hs : ∀ v ∈ s, Certificate10560.Available true bank (fun r => v (point r)))
    {f : F} (h : Av s f) :
    Certificate10560.Available true bank (fun r => f (point r)) := by
  rcases h with ⟨b,rfl⟩ | ⟨a,ha,rfl | rfl⟩
  · exact Or.inr (Or.inl ⟨b,rfl⟩)
  · exact hs _ ha
  · exact Certificate10560.avail_inv rfl (hs _ ha)

private theorem signed_prog {s : Set F} {f : F} {k : Nat} (p : Prog s f k)
    (point : Certificate10560.Row → X) (roots : List (Certificate10560.Wire Certificate10560.Row)) :
    ∀ m bank, Certificate10560.Reach true roots m bank →
      (∀ v ∈ s, Certificate10560.Available true bank (fun r => v (point r))) →
      ∃ pool, Certificate10560.Reach true roots (m+k) pool ∧
        Certificate10560.Available true pool (fun r => f (point r)) := by
  induction p with
  | done h => intro m bank hm hs; exact ⟨bank,hm,signed_av point hs h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro m bank hm hs
    let a' := fun r => a (point r)
    let b' := fun r => b (point r)
    let w := Certificate10560.combine (!tag) a' b'
    have hl : (fun r => comb tag a b (point r)) = w := by
      cases tag <;> rfl
    have hr : Certificate10560.Reach true roots (m+1) (w :: bank) :=
      Certificate10560.Reach.two (!tag) hm (signed_av point hs ha) (signed_av point hs hb)
    obtain ⟨pool,hp,hv⟩ := ih (m+1) (w :: bank) hr (by
      intro v h
      rcases Set.mem_insert_iff.mp h with rfl | h
      · rw [hl]
        exact Or.inl (List.mem_cons_self)
      · exact Certificate10560.available_cons w (hs _ h))
    exact ⟨pool,by simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hp,hv⟩

private theorem from_signed_L_meta_10560 {f : F} {L : Nat}
    {roots : List Certificate10560.Sig} {targetWord : Certificate10560.Sig}
    (cols : Fin 8 → Certificate10560.Sig)
    (hcols : ∀ i, cols i ∈ roots ∨ cols i = Certificate10560.zero)
    (he : ∀ r : Certificate10560.Row, Certificate10560.bit r targetWord =
      f (fun i => Certificate10560.bit r (cols i)))
    (h : Certificate10560.Lower true roots targetWord L) : Low L f := by
  intro k p
  let point := fun r i => Certificate10560.bit r (cols i)
  obtain ⟨pool,hp,hv⟩ := signed_prog p point (roots.map Certificate10560.observe) 0
    (roots.map Certificate10560.observe) Certificate10560.Reach.start (by
      rintro _ ⟨i,rfl⟩
      rcases hcols i with hmem | hz
      · exact Or.inl (List.mem_map.mpr ⟨cols i,hmem,rfl⟩)
      · apply Or.inr; apply Or.inl
        exact ⟨false,by funext r; change Certificate10560.bit r (cols i) = false
                        rw [hz]; simp [Certificate10560.bit,Certificate10560.zero]⟩)
  have eq : Certificate10560.observe targetWord = fun r => f (point r) := funext he
  rw [← eq] at hv
  exact h k pool (by simpa using hp) hv

def target : F := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem lower : Low 13 target := (one 2 false (good_at 32 9 0 (by decide +kernel)) (from_signed_L_meta_10560 (f := (rs 2 false target)) ![(Certificate10560.inputs.getD 5 Certificate10560.zero), (Certificate10560.inputs.getD 2 Certificate10560.zero), Certificate10560.zero, (Certificate10560.inputs.getD 1 Certificate10560.zero), (Certificate10560.inputs.getD 0 Certificate10560.zero), (Certificate10560.inputs.getD 3 Certificate10560.zero), (Certificate10560.inputs.getD 4 Certificate10560.zero), (Certificate10560.inputs.getD 6 Certificate10560.zero)] (by decide +kernel) (by decide +kernel) Certificate10560.low127))

def witness : List Gate := [⟨.or, [6, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [4, 12]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [1, 19]⟩, ⟨.or, [18, 20]⟩]

theorem witness_ok : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : X, Circuit.eval ⟨witness, 21⟩ (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem target_eq : ∀ x : X, target x = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_52070

open PEqualNP.Outside.L_meta_52070 in
theorem PEqualNP.Outside.L_meta_52070 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hg _ he
  by_cases hs : 14 ≤ gates.length
  · exact ⟨witness, 21, witness_ok, hs, fun x => (witness_eval x).trans (target_eq x)⟩
  · exact ⟨gates, o, all_not_not_of_guillabert_pr42591 lower gates o hg (by omega)
      (fun x => (he x).trans (target_eq x).symm), le_rfl, he⟩
