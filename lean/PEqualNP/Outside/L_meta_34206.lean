import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_34206.Certificate30704

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

theorem restoreInput {α : Type} [DecidableEq α] (U : Finset α) (a : α) :
    (if a ∈ U then insert a (U.erase a) else U.erase a) = U := by
  by_cases ha : a ∈ U
  · rw [if_pos ha, Finset.insert_erase ha]
  · rw [if_neg ha, Finset.erase_eq_of_notMem ha]

theorem restoreInputs {α : Type} [DecidableEq α] (U : Finset α) (a b : α) (hab : a ≠ b) :
    let s := (U.erase a).erase b
    let t := if b ∈ U then insert b s else s
    (if a ∈ U then insert a t else t) = U := by
  have member : b ∈ U.erase a ↔ b ∈ U := by
    rw [Finset.mem_erase]
    exact ⟨And.right, fun h => ⟨Ne.symm hab, h⟩⟩
  have inner : (if b ∈ U then insert b ((U.erase a).erase b) else (U.erase a).erase b) = U.erase a := by
    by_cases hb : b ∈ U
    · rw [if_pos hb, Finset.insert_erase (member.mpr hb)]
    · rw [if_neg hb, Finset.erase_eq_of_notMem (fun h => hb (member.mp h))]
  dsimp only
  rw [inner]
  exact restoreInput U a

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
      rw [kept_fin, kept_fin, er]
      simpa only [ka, kb, decide_eq_true_eq] using restoreInputs U a b hab
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

def graph : Sig := 0xffffffffffffffffffffffffffeaeae8fffefefcfffafaf8ffeeeeecffeaeae8ffffffffffffffffffffffffffeaeae8fffefefcfffafaf8ffeeeeecffeaeae8

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
      rw [kept_fin, kept_fin, er, he, Finset.erase_insert_eq_erase,
        Finset.erase_insert_of_ne (Ne.symm hab), Finset.erase_insert_eq_erase]
      simpa only [ka, kb, decide_eq_true_eq] using restoreInputs U a b hab
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
  (x 0 &&& x 3) ||| (x 0 &&& x 5) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 1 &&& x 6) ||| (x 2 &&& x 4) ||| (x 2 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)

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

abbrev Bits := BitVec 256

abbrev Signals := Bits × Bits

abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn

theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

def pairSig (r s : Fin 256 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)

def properPairs (T : Sig) (r s : Fin 256 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false

theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 256 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩

def faithful (r s : Fin 256 → Row) (x : Decor) := x.2 = pairSig r s x.1

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

def asRow (cols : Nat → Bits) (i : Fin 256) : Row :=
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

theorem asRow_bit (cols : Nat → Bits) (i : Fin 256) (j : Fin 9) :
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
  (x 0 &&& x 3) ||| (x 0 &&& x 5) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 1 &&& x 6) ||| (x 2 &&& x 4) ||| (x 2 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)

theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 256) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]

theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 256) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide)]

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
    if (rs ||| column d z.2) != BitVec.allOnes 256 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 256) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 256 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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

theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 256) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i

theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 256) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 256) &&
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

def K0 : List (Nat × Nat) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V0 : Known true K0 := baseKnown

def g22Y : Array (Bits × Bits) := #[ (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbf57,0x4414), (0xe7ee,0x120a), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdef9,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2061), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g22C : List ColumnInfo := []
def g22D3 (_ : Nat) : Nat := 0x7
def g22L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,g22D3)
  | _ => emptyPacking
def g22I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g22 : Forest := ⟨22,3,fun i => g22Y[i]?.getD (0,0),g22C,[[]],g22L,g22I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g22P3_0 : block g22 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g22B3 : block g22 3 0 1 = true := g22P3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g22T : checkedTables g22 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g22B3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g22G : graphValid g22 (boundsBefore K0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low22 : Lower true (varsX 22) (graphGoal 22) 4 := lower_forest (g:=g22) (i:=0) (hints:=65824) (before_sound K0 V0) g22G g22T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K22 := extendKnown K0 4 [(22,[]),(41,[16, 50, 84]),(70,[84, 101]),(82,[50, 83, 84, 101]),(84,[49, 50, 83, 84, 101]),(88,[49, 82, 84, 101]),(100,[49, 50, 83, 100]),(104,[49, 82, 100])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V22 : Known true K22 := extend_ok (m:=22) V0 low22 (by decide +kernel)

def g27Y : Array (Bits × Bits) := #[ (0xcdf5abbfb3742b5a,0x33182446f6050b42), (0xffffffffffffffffffffffffffffffffffffffffffffffffaefc75bfacc35f15,0xffffffffffffffffffffffffffffffffffffffffffffffff518a82b302893a15), (0x0,0x0), (0xf75fbbf6db7cf8fe,0x880431000d8603c), (0xffffffffffffffffffffffffffffffffffffffffffffffff7faf77df7d9bd7e5,0x8214080c4d0405c0), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g27C : List ColumnInfo := []
def g27D3 (_ : Nat) : Nat := 0xf
def g27L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,g27D3)
  | _ => emptyPacking
def g27I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g27 : Forest := ⟨27,3,fun i => g27Y[i]?.getD (0,0),g27C,[[]],g27L,g27I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g27P3_0 : block g27 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g27B3 : block g27 3 0 1 = true := g27P3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g27B3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K22) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=65603) (before_sound K22 V22) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K22 4 [(27,[]),(29,[33]),(39,[66, 67, 84]),(46,[32, 33, 50, 84]),(53,[33, 66, 83]),(58,[32, 33, 82, 67]),(75,[84, 101]),(77,[33, 84, 101]),(99,[83, 100]),(113,[33, 82, 99, 84, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V22 low27 (by decide +kernel)

def g30Y : Array (Bits × Bits) := #[ (0x0,0x0), (0x3def6dcdedf8967a,0x420883154c820650), (0xfffffffffffffffffffffffffffffffffffffffffffffffff6fedb4bfad0fc37,0xffffffffffffffffffffffffffffffffffffffffffffffff894060a8b2011823), (0x5c5eac3fc34f4bb0,0x2323f10a7c4b0ab0), (0xffffffffffffffffffffffffffffffffffffffffffffffffefdff7be57affbcd,0x100400400100c10c), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g30C : List ColumnInfo := [(8,0,22,0,4)]
def g30D4 (_ : Nat) : Nat := 0x2f
def g30L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g30D4)
  | _ => emptyPacking
def g30I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g30 : Forest := ⟨30,4,fun i => g30Y[i]?.getD (0,0),g30C,[[]],g30L,g30I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g30P4_0 : block g30 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g30B4 : block g30 4 0 1 = true := g30P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g30T : checkedTables g30 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g30B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g30G : graphValid g30 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low30 : Lower true (varsX 30) (graphGoal 30) 5 := lower_forest (g:=g30) (i:=0) (hints:=82208) (before_sound K27 V27) g30G g30T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K30 := extendKnown K27 5 [(30,[]),(45,[16, 50, 84]),(54,[66, 83]),(57,[16, 82, 67]),(78,[84, 101]),(89,[48, 49, 82, 67, 101]),(101,[48, 49, 50, 83, 100, 101]),(106,[49, 82, 100]),(114,[82, 99, 84, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V30 : Known true K30 := extend_ok (m:=30) V27 low30 (by decide +kernel)

def g90Y : Array (Bits × Bits) := #[ (0x0,0x0), (0xfffffffffffffffffffffffffffffffffffffffffffffffff77a55cf1cf750f5,0xfffffffffffffffffffffffffffffffffffffffffffffffff8840e283c14c0c5), (0x0,0x0), (0x5eca7b5f1cee58e,0xa0110e9281ac486), (0xffffffffffffffffffffffffffffffffffffffffffffffffffabfeaf9759fba3,0x70001000412320), (0x0,0x0), (0xefd6df8eeaf7e5c,0x10a800080801818), (0x0,0x0), (0x0,0x0) ]
def g90C : List ColumnInfo := [(8,0,82,0,4), (2,0,88,0,4)]
def g90D4 (_ : Nat) : Nat := 0x2f
def g90L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g90D4)
  | _ => emptyPacking
def g90I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g90 : Forest := ⟨90,4,fun i => g90Y[i]?.getD (0,0),g90C,[[]],g90L,g90I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g90P4_0 : block g90 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g90B4 : block g90 4 0 1 = true := g90P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g90T : checkedTables g90 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g90B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g90G : graphValid g90 (boundsBefore K30) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low90 : Lower true (varsX 90) (graphGoal 90) 5 := lower_forest (g:=g90) (i:=0) (hints:=16859200) (before_sound K30 V30) g90G g90T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K90 := extendKnown K30 5 [(90,[]),(92,[33]),(102,[66, 67, 84]),(105,[16, 67, 84, 101]),(108,[33, 84]),(116,[33, 66, 83]),(120,[33, 82, 67, 84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V90 : Known true K90 := extend_ok (m:=90) V30 low90 (by decide +kernel)

def g86Y : Array (Bits × Bits) := #[ (0x0,0x0), (0x77bbe51fd8d5b8,0x8440604804190), (0xffffffffffffffffffffffffffffffffffffffffffffffffffef8d3fb2bde81f,0x1002415201080c), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffffbe5aafef07f365,0xffffffffffffffffffffffffffffffffffffffffffffffffffc0a81020009221), (0x0,0x0), (0x7a7d5d75f71ec2,0x7008081140442), (0x0,0x0), (0x0,0x0) ]
def g86C : List ColumnInfo := [(64,0,22,0,4), (16,0,70,0,4), (4,0,82,0,4), (2,0,84,0,4)]
def g86D3 (_ : Nat) : Nat := 0x20080080200010021042a509e2c4c808009d02a68897144d3244a6c2a9a205c9034c9029712a6880c78d524407a20698a03e10248501
def g86H3 (_ : Nat) : Nat := 0x7aa2c0b808c01ad46628
def g86D4 (_ : Nat) : Nat := (0xd3240bb44902be34406f4d101be24406f49101f930407e48101f531407d48501 + ((0x1340ef8d112bd3444af81112f53144bb4c912be3440af4d102be1440be4c102e + ((0x8150701c00be1448ef81123be2444ef81113dd2344ef89103be1440f748d03dd + ((0x88423008c42894320d00793b1ccd86531174b4532612488411d0cc5829120843 + (0x2108000c4232080304010088020081004023008c8200410001200 <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g86H4 (_ : Nat) : Nat := 0x64646e447f40024c00302c45c000000333f6e1b8b2f9e923b0aa1227cd6081dc5007d70ded004c0431c000b403
def g86D5 (_ : Nat) : Nat := 0x68811a20468811a20468811a204b521b242403e91fd13fa07f44be817d01
def g86H5 (_ : Nat) : Nat := 0x1da586004000258
def g86D6 (_ : Nat) : Nat := 0x7208f
def g86L : Nat → Packing
  | 3 => (8,3,2,0,0,7,0,g86D3)
  | 4 => (28,2,2,0,0,9,0,g86D4)
  | 5 => (6,1,2,0,0,7,0,g86D5)
  | 6 => (1,0,2,0,0,1,0,g86D6)
  | _ => emptyPacking
def g86I : Nat → Nat → Option (Nat × Nat)
  | 4, h => lookupWord 3 10 3 7 3 0 g86H3 h
  | 5, h => lookupWord 11 35 5 9 5 0 g86H4 h
  | 6, h => lookupWord 3 9 1 7 3 0 g86H5 h
  | _, _ => none
def g86 : Forest := ⟨86,6,fun i => g86Y[i]?.getD (0,0),g86C,[[]],g86L,g86I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86P3_0 : block g86 3 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86P3_5 : block g86 3 5 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86B3 : block g86 3 0 8 = true := (@block_merge g86 3 0 5 3 g86P3_0 g86P3_5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86P4_0 : block g86 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86P4_5 : block g86 4 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86P4_10 : block g86 4 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86P4_15 : block g86 4 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86P4_20 : block g86 4 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86P4_25 : block g86 4 25 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86B4 : block g86 4 0 28 = true := (@block_merge g86 4 0 20 8 (@block_merge g86 4 0 10 10 (@block_merge g86 4 0 5 5 g86P4_0 g86P4_5) (@block_merge g86 4 10 5 5 g86P4_10 g86P4_15)) (@block_merge g86 4 20 5 3 g86P4_20 g86P4_25))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86P5_0 : block g86 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86P5_5 : block g86 5 5 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86B5 : block g86 5 0 6 = true := (@block_merge g86 5 0 5 1 g86P5_0 g86P5_5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86P6_0 : block g86 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86B6 : block g86 6 0 1 = true := g86P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86T : checkedTables g86 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g86B3
  · exact g86B4
  · exact g86B5
  · exact g86B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g86G : graphValid g86 (boundsBefore K90) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low86 : Lower true (varsX 86) (graphGoal 86) 7 := lower_forest (g:=g86) (i:=0) (hints:=16843040) (before_sound K90 V90) g86G g86T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K86 := extendKnown K90 7 [(86,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V86 : Known true K86 := extend_ok (m:=86) V90 low86 (by decide +kernel)

def g61Y : Array (Bits × Bits) := #[ (0xf9a67fdfa9b32e9fa45c3de975b79bb4cdc79c7e063b7a599bb11e8,0x6588000c6cc1a022083000a91c9946c015350a6001128718b21188), (0x0,0x0), (0xfffffffff7d63b752bfd8f77b52dfd2e03fca75b9aa2e42a9db2ceffb800fbcb,0xfffffffff828c042e40290a882bc8a0d0000d848060267088133a0c06800d3c1), (0xfffffffffdf5b3eedfefe8fefcdb4a7bfd2a5ccfeb5b5b51568ebbac6ece9455,0xfffffffff2080411a001140810a0846c0080402100404200150a2160604c8041), (0xfffffffffe3fc6e3b3eb8fbf63f6697e2aad91d9f375f665879c061bbd942f2d,0x1c0192c0a50601144404182d93e2200803100e56a80060b86902c2c), (0xb7f5ffaed5dd5f396efdcf9cc5fef3655be209f3afb59d1e371c8b6,0x480230012002a024d01411000222010218800a10880081087010836), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g61C : List ColumnInfo := [(16,0,45,0,5), (4,0,57,0,5), (20,0,41,0,4), (32,0,29,0,4), (8,0,53,0,4)]
def g61D5 (_ : Nat) : Nat := 0x5f
def g61L : Nat → Packing
  | 5 => (1,0,3,0,0,1,0,g61D5)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g61 : Forest := ⟨61,5,fun i => g61Y[i]?.getD (0,0),g61C,[[]],g61L,g61I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g61P5_0 : block g61 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g61B5 : block g61 5 0 1 = true := g61P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g61B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K86) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 6 := lower_forest (g:=g61) (i:=0) (hints:=132099) (before_sound K86 V86) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K86 6 [(61,[]),(62,[16, 50, 84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V86 low61 (by decide +kernel)

def g124Y : Array (Bits × Bits) := #[ (0x0,0x0), (0x0,0x0), (0xb778efdab6cfb5eb785fc8ebe1ac0edd30efcd686d10ce5c,0x48b2002049200b4009834c081012069100e30a0022808e50), (0x3f6fd7bec6359bdce4f2bd929eb1fe25e5d42a57c3c61fa2,0xc0900071118004423e80400c9090069400000a02e3c60e80), (0xffffffffffffffffdb79f6f56dab57c187fb627ba3b1efca4db976c60d456369,0x244409020455001800600132456c38484b08306004016128), (0xebbfe13d9ceda1db6c2d1fce5bd6d55ed266397d98eb183c,0x14409d002210c0bd00402032200451404b0c01740821102c), (0xfffffffffffffffffdff99f3ff5af8757fa3da76956fe3637a13d993f639a483,0xffffffffffffffff0208220c00001000c0040041080080023010400100180003), (0x0,0x0), (0x0,0x0) ]
def g124C : List ColumnInfo := [(32,0,92,0,5), (16,0,108,0,5), (8,0,116,0,5), (4,0,120,0,5), (40,0,84,0,4), (36,0,88,0,4), (24,0,100,0,4), (20,0,104,0,4)]
def g124D5 (_ : Nat) : Nat := 0x5f
def g124L : Nat → Packing
  | 5 => (1,0,3,0,0,1,0,g124D5)
  | _ => emptyPacking
def g124I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g124 : Forest := ⟨124,5,fun i => g124Y[i]?.getD (0,0),g124C,[[]],g124L,g124I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g124P5_0 : block g124 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g124B5 : block g124 5 0 1 = true := g124P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g124T : checkedTables g124 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g124B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g124G : graphValid g124 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low124 : Lower true (varsX 124) (graphGoal 124) 6 := lower_forest (g:=g124) (i:=0) (hints:=35800064) (before_sound K61 V61) g124G g124T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K124 := extendKnown K61 6 [(124,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V124 : Known true K124 := extend_ok (m:=124) V61 low124 (by decide +kernel)

def g91Y : Array (Bits × Bits) := #[ (0xfffffffffcb517acc9eedd472904f9fd7cd4e5983db759b94d6fc251c12c255f,0xfffffffff34aea66301108bac518b70012bd69080e2170da7a4f4c01c02c254d), (0xfffffffffbaeedaff38abf0b88e977f3077fd1eb35bcb2818f4b9f27beaba82b,0xfffffffff4512310041544c11200ec30f0e182030094221503581127018b2023), (0x0,0x0), (0xfcfb2679dbbfe7f7577bcd4fa6437ddafd3c77c51ff42bc979a54d6,0x300198024010401020082220408032611002040130121a15920092), (0x5ffff5c96e73fd55fff6bab9eff381bc576ce8aba3da9cf7866e3e0,0xa000021f80800220c4800800b00440c08028c029805c8000024c240), (0x0,0x0), (0xfffffffffff22bf7ff7675e8ffeee51929c9dbff7e693f4fadc635794ed51f09,0xe540000028a1840041005001a308084600148640204400a401d08), (0x0,0x0), (0x0,0x0) ]
def g91C : List ColumnInfo := [(2,0,89,0,5), (1,0,90,0,5), (9,0,82,0,4), (3,0,88,0,4), (64,0,27,0,4), (16,0,75,0,4)]
def g91D4 (_ : Nat) : Nat := 0x81bc560bb0aa697a35412f48a81de51503
def g91H4 (_ : Nat) : Nat := 0x39000033a0e0
def g91D5 (_ : Nat) : Nat := 0x4100c86032180e4480fd34f904f903
def g91H5 (_ : Nat) : Nat := 0x127c0018810
def g91D6 (_ : Nat) : Nat := 0x588815f
def g91L : Nat → Packing
  | 4 => (4,2,3,0,0,5,0,g91D4)
  | 5 => (3,1,3,0,0,6,0,g91D5)
  | 6 => (1,0,3,0,0,1,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 4 7 1 6 2 0 g91H4 h
  | 6, h => lookupWord 5 7 1 6 2 0 g91H5 h
  | _, _ => none
def g91 : Forest := ⟨91,6,fun i => g91Y[i]?.getD (0,0),g91C,[[]],g91L,g91I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g91P4_0 : block g91 4 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g91B4 : block g91 4 0 4 = true := g91P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : block g91 5 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g91B5 : block g91 5 0 3 = true := g91P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : block g91 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g91B6 : block g91 6 0 1 = true := g91P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g91B4
  · exact g91B5
  · exact g91B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K124) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=16842819) (before_sound K124 V124) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K124 7 [(91,[]),(93,[33]),(103,[66, 67, 84]),(107,[16, 67, 84, 101]),(117,[33, 66, 83])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V124 low91 (by decide +kernel)

def g31Y : Array (Bits × Bits) := #[ (0xffffffb5d17bc7a6ced6a699e4f7e0d1767e6efc8fbc63be107a4dbd51634f83,0xffffffca2e10085b222552129c13819e4b15b0100424c2ce145aa884e0634d03), (0x7cbdf5defcaf2e2f7fd7d4f9bd8c579e63268f54574b2f96b6fa1b99ce,0x34202620250e04a821082084504c269104209405d8803c622000b10ca), (0xfffffffb5bdefbd23ce7af4b8fbd1d676dbdacf2f0d5b1a76bdfacb12fe0983f,0x4a900042d0718050d0130a2801b208405109403224104285827e08824), (0x7e6c3df96746ff72d7f55b3adbff6047dedffc6ead94e55b684ba5f6c0,0x191c002209140ada40220344024020e4448992001c0a0506a0f80b2c0), (0xffffff9fff93ff3bdf79fbacb9ffdf1ea7eeb787785addd3bd9a3b47d6de6171,0xffffffe0002c8880200400108044012a4010008a0060948004080101d0144111), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g31C : List ColumnInfo := [(1,0,30,0,5), (9,0,22,0,4), (4,0,27,0,4), (2,0,29,0,4)]
def g31D4 (_ : Nat) : Nat := 0x820082008303481405e41624bb0aa497905852dc4a8a768d504
def g31H4 (_ : Nat) : Nat := 0x1d8000e4612c004
def g31D5 (_ : Nat) : Nat := 0x1608050240481c27795240fe24fd24fe14fd14f904fd12
def g31H5 (_ : Nat) : Nat := 0x3ac3018407c15a000
def g31D6 (_ : Nat) : Nat := 0xe411f
def g31L : Nat → Packing
  | 4 => (5,2,2,0,0,6,0,g31D4)
  | 5 => (6,1,2,0,0,6,0,g31D5)
  | 6 => (1,0,2,0,0,1,0,g31D6)
  | _ => emptyPacking
def g31I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 3 7 3 7 3 0 g31H4 h
  | 6, h => lookupWord 3 9 1 7 3 0 g31H5 h
  | _, _ => none
def g31 : Forest := ⟨31,6,fun i => g31Y[i]?.getD (0,0),g31C,[[]],g31L,g31I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31P4_0 : block g31 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31B4 : block g31 4 0 5 = true := g31P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31P5_5 : block g31 5 5 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31B5 : block g31 5 0 6 = true := (@block_merge g31 5 0 5 1 g31P5_0 g31P5_5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31P6_0 : block g31 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31B6 : block g31 6 0 1 = true := g31P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g31B4
  · exact g31B5
  · exact g31B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 7 := lower_forest (g:=g31) (i:=0) (hints:=65827) (before_sound K91 V91) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K91 7 [(31,[]),(47,[16, 50, 84]),(55,[66, 83]),(59,[16, 82, 67]),(79,[84, 101]),(115,[82, 99, 84, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V91 low31 (by decide +kernel)

def g109Y : Array (Bits × Bits) := #[ (0xfffffffffffffa56b49e3cbbef7efc6b28b9d97480f61cf894bcb9cba6bd4703,0xffffffffffff85884943c5440a908930b00681228755050c1d2888caa2250703), (0x0,0x0), (0x4f7cf97a7a895cf716ebb52c2d2bdbc5b2c7c34e0b7be8e93664,0x308196400574a042a4a29264889460312249f350094520e81660), (0xffffffffffffd7de7efb876b3b63f9771bc767f8c1fa7e633c915aef53ead01b,0x2821a00420b0010120834420188010a0780260d0000540ca5010), (0x0,0x0), (0x7debf7efdfbd8f9fcffee394ffa47ea1efba266bad21bd540ddc,0x210000000035400004008004401000880a0000100200410080c), (0xffffffffffffbbefba476e6ff77966bbd46be78b675ce515cba756dcf483bba1,0xffffffffffffc40801b090080820481c201021408b000514080692089201a181), (0x0,0x0), (0x0,0x0) ]
def g109C : List ColumnInfo := [(64,0,45,0,5), (8,0,101,0,5), (4,0,105,0,5), (1,0,108,0,5), (68,0,41,0,4), (9,0,100,0,4), (5,0,104,0,4), (32,0,77,0,4)]
def g109D6 (_ : Nat) : Nat := 0x68811f
def g109L : Nat → Packing
  | 6 => (1,0,3,0,0,1,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g109 : Forest := ⟨109,6,fun i => g109Y[i]?.getD (0,0),g109C,[[]],g109L,g109I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g109P6_0 : block g109 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g109B6 : block g109 6 0 1 = true := g109P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g109B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=33555715) (before_sound K31 V31) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K31 7 [(109,[]),(110,[16, 50, 101]),(121,[66, 83]),(122,[16, 66, 99, 100, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V31 low109 (by decide +kernel)

def g94Y : Array (Bits × Bits) := #[ (0x0,0x0), (0xffffffffffffffffcff4ed7b4aedcc3f9b765f54f6a5490571bfebb382e330d5,0xffffffffffffffff3008520475002a80284108410e1040052114898d008230c1), (0x77f7d795fc4553d7e470fafe86b74fe08b323af37a957c06,0x8800a9280232040200acd080e0c08c480222206249154006), (0xffffffffffffffff2fbdeaf39c826726bfc9b127c301fc0bff58bc3c554c9387,0xffffffffffffffffd002090567790e48a6a05ec1420b044c2078393d19449187), (0xfe6bdb7fcd7ed909bf85d1fbdffae6bfe6c74ce81a540bf8,0x1100490008041005002000000241202c001000002000a18), (0x0,0x0), (0xfffffffffffffffffd2efdd9f79f3ff25feabcb53ee936723c5df346e5aac42b,0x2e10002000080000110003c010000201c00420000280420), (0x0,0x0), (0x0,0x0) ]
def g94C : List ColumnInfo := [(8,0,86,0,7), (64,0,30,0,5), (16,0,78,0,5), (4,0,90,0,5), (2,0,92,0,5), (72,0,22,0,4), (24,0,70,0,4), (12,0,82,0,4), (10,0,84,0,4), (6,0,88,0,4)]
def g94D7 (_ : Nat) : Nat := 0x5f
def g94L : Nat → Packing
  | 7 => (1,0,4,0,0,1,0,g94D7)
  | _ => emptyPacking
def g94I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g94 : Forest := ⟨94,7,fun i => g94Y[i]?.getD (0,0),g94C,[[]],g94L,g94I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g94P7_0 : block g94 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g94B7 : block g94 7 0 1 = true := g94P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g94B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 8 := lower_forest (g:=g94) (i:=0) (hints:=16859424) (before_sound K109 V109) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K109 8 [(94,[]),(118,[66, 83])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V109 low94 (by decide +kernel)

def g63Y : Array (Bits × Bits) := #[ (0x28f2f253952f1f276c144031ceb87eeff43768ea9d0a5513a54b1e42166a0fa3,0x8d0801404065617e4c00211dc230429c4076c022c00011224491c4204680fa0), (0xbd482ff86c2870b99305d709e4434b4cc7bed538c705d6705a4cf127ec0b98a9,0x4a212648201202838204e50102020a0400b465884e9016604254b1038c0b9809), (0xcf884f2f16640bfe21eb196bd197b1334dd9c83010887ef96c65ee3b21b1c260,0x10091355000840029c1107c41819500490008201000601d20000a2821204260), (0x78f7dbd7e2f8f0cffa34e0bc41601351abd92acf64794b4fd3fa12802b6cb45d,0x400019a0502080000831e06c010001402298018c00186a25100002002b049051), (0xdb15b5cefa9fffdd92829f423d1cc1372c26df0cf6778b17bda88d9cd05039d0,0x940200028108681c54000a80101c40b304029002a025018089a8049450502180), (0x7dd0beb2d47adc56578e0af0becaeaa52e60045cbe7a588ea31f1541d87630e,0x96012642808001c000000c820240228200601040c1c38480c8b4c1141083200e), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g63C : List ColumnInfo := [(32,0,31,0,7), (16,0,47,0,7), (8,0,55,0,7), (4,0,59,0,7), (2,0,61,0,6), (1,0,62,0,6), (33,0,30,0,5), (18,0,45,0,5), (9,0,54,0,5), (6,0,57,0,5), (41,0,22,0,4), (22,0,41,0,4), (36,0,27,0,4), (34,0,29,0,4), (24,0,39,0,4), (17,0,46,0,4), (10,0,53,0,4), (5,0,58,0,4)]
def g63D7 (_ : Nat) : Nat := 0x1448c388284180029fd01
def g63H7 (_ : Nat) : Nat := 0x40
def g63D8 (_ : Nat) : Nat := 0x1483104033f
def g63L : Nat → Packing
  | 7 => (1,1,5,0,0,1,0,g63D7)
  | 8 => (1,0,5,0,0,1,0,g63D8)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 8, h => lookupWord 2 2 1 5 1 0 g63H7 h
  | _, _ => none
def g63 : Forest := ⟨63,8,fun i => g63Y[i]?.getD (0,0),g63C,[[]],g63L,g63I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63B7 : block g63 7 0 1 = true := g63P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63B8 : block g63 8 0 1 = true := g63P8_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g63B7
  · exact g63B8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 9 := lower_forest (g:=g63) (i:=0) (hints:=65827) (before_sound K94 V94) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K94 9 [(63,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V94 low63 (by decide +kernel)

def g125Y : Array (Bits × Bits) := #[ (0x870abd9c26e8d6b6b7ed6a1a408b3fd7ded40e3a618f220ad3b569a1e5d81c16,0x1b3a0430045810400687c83850070550d2d22823008e2a00d7d11120e1d81c14), (0x0,0x0), (0x5dddd36b30d9e02046966ea4ba6109265ac0f08bad61dbf3e3a707ee1990250d,0x1c0002840051b00841000084200008724880710d1921082103a243a409902109), (0x9e7b12d6bfcebf998ca8b5de018f584cd119956cd2f914f89a6ac9902e5413e8,0x404420840801000800282440008808040000d10c12610449000242900e000128), (0x229ad6775c48edfa7e3ed5e30939d6aaa2241a7f0eda538225d79768a02ccb27,0x99d962940a00b6080508224f337200822c00520418508204540048a02c4206), (0x354fff23bf351daef9cd6515ee10f7910d9b4592aa3feccc6a96200bc287605a,0x81190360000e21900011010e207280052804c0a00000802004000b00064042), (0x6ae24ccb4f7b2973deb78a59bdd4ce29e7e7ba8055a40735c5181014196bcc90,0x810200100204010004c28210900484090003020040802310d000100010418c90), (0x0,0x0), (0x0,0x0) ]
def g125C : List ColumnInfo := [(32,0,93,0,7), (8,0,117,0,7), (16,0,109,0,7), (4,0,121,0,7), (64,0,61,0,6), (1,0,124,0,6), (80,0,45,0,5), (68,0,57,0,5), (36,0,89,0,5), (24,0,101,0,5), (33,0,92,0,5), (20,0,105,0,5), (17,0,108,0,5), (9,0,116,0,5), (5,0,120,0,5), (84,0,41,0,4), (41,0,84,0,4), (37,0,88,0,4), (25,0,100,0,4), (21,0,104,0,4), (96,0,29,0,4), (72,0,53,0,4), (48,0,77,0,4), (12,0,113,0,4)]
def g125D7 (_ : Nat) : Nat := 0x51238a18061448c38828418002851238a1806d8a807ec17fa0bf905
def g125H7 (_ : Nat) : Nat := 0x67e402
def g125D8 (_ : Nat) : Nat := 0x1483104033f
def g125L : Nat → Packing
  | 7 => (3,1,5,0,0,7,0,g125D7)
  | 8 => (1,0,5,0,0,1,0,g125D8)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 8, h => lookupWord 3 5 2 6 2 0 g125H7 h
  | _, _ => none
def g125 : Forest := ⟨125,8,fun i => g125Y[i]?.getD (0,0),g125C,[[]],g125L,g125I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125B7 : block g125 7 0 3 = true := g125P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P8_0 : block g125 8 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125B8 : block g125 8 0 1 = true := g125P8_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g125B7
  · exact g125B8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 9 := lower_forest (g:=g125) (i:=0) (hints:=33686531) (before_sound K63 V63) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K63 9 [(125,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V63 low125 (by decide +kernel)

def g111Y : Array (Bits × Bits) := #[ (0xcca7711a8dd258e25962ec2fe443a23276d1f266656a50c89f15eb8a1964c26e,0x88a14c510530050808408a0b6804a80404e1b0e6206870808e130b8a09444066), (0x1e1fa1e797d481e87a89855edb18929ee49c09b1da34f9ea1ee0cbc36a381b03,0x6bee42c91093411070900450c09a96146494180a5834a830146486c340281b03), (0xaf6062a55a7e2c6137dcf7f3726d32cf19320fcc827e4847e6c008010e96ec37,0x400001041080062812c3b2232442002080023c081034046600808000e12c434), (0x1d1e1c5bfc57d7d3e75f4cd307e0e1024f0d8e43d1bb123239bff41f0479958c,0x414008a004a1036041c55100590000241040e018103020601ccc40504389488), (0x0,0x0), (0xd9d75b84762d791d6dac103ca02ebf29f1cef33d74918613e5303cf0918057d1,0x13488000028442006000000400221609b0084008481400100020307010800301), (0x36fd9d5eeb98be1ff49fa2897d915df1aca44c54a842ffad403b936ce40f2060,0x8000192488000c0908438089080109a0006100140000100900120108a0052040), (0x0,0x0), (0x0,0x0) ]
def g111C : List ColumnInfo := [(8,0,103,0,7), (4,0,107,0,7), (64,0,47,0,7), (32,0,79,0,7), (2,0,109,0,7), (1,0,110,0,7), (66,0,45,0,5), (33,0,78,0,5), (10,0,101,0,5), (5,0,106,0,5), (9,0,102,0,5), (6,0,105,0,5), (3,0,108,0,5), (70,0,41,0,4), (41,0,70,0,4), (11,0,100,0,4), (7,0,104,0,4), (72,0,39,0,4), (65,0,46,0,4), (36,0,75,0,4), (34,0,77,0,4), (12,0,99,0,4)]
def g111D4 (_ : Nat) : Nat := (0x514b1834a4ea2a0a8a64c9e1454d905453260f0a2a6c82a29f01354910545123 + ((0x5551149d104a71b12488a5c48e56751505452e4452b3a8a82a296326949d4541 + (0x1e6d85523cc2460c04cc86528d91454166a432946c69aa0b332094e36 <<< 256)) <<< 256))
def g111H4 (_ : Nat) : Nat := 0x345065595692aa87e89100f300a18
def g111D5 : Nat → Nat
  | 0 => (0xa9e9614654101ab64855941406378e167515018ee2859d45407cc4510551501 + ((0x1028f6785591440b8d5155645102ea5245591440bcc5155045102fa124541144 + ((0x4540bca49105515028be4859d3540a3d861674d502f49234153540be841d2445 + ((0x755902a7a585195040a9e96136541028de3859d4540a3d8616751502e2d24595 + ((0x5050544fe14c91449113ab6484d94144a1f961674d1128fa0859d3444a3d5221 + ((0x5d35415138fa785190544f8e5514641513e59355190544fcc5514141513f5135 + ((0x6485594144e3b8a167515138fa0859d4544f875913551513f15144d54544fd44 + ((0xe14915345123f31454151448fd44d50545123fa1244151448e3e5620751913ab + ((0x3e35455591448fa94915645123ba5485491448fc95155245123f154554d1448f + ((0x48ebc8216745123ba6584911448fe14dd2445123ea5249591448e3d9e1564512 + ((0x1523f49355090548ed65614341523f195450d0548ead5236745123a765859d14 + ((0x50548f964d646415238fa785190548f8e5514641523e59355190548fca551424 + ((0x3551523a7958d9d0548eae9216741523af21859d0548ed69213541523f49274d + ((0x45954548f874d16551523e2d644954548fc34d12551523e1d644d54548fc3491 + ((0x52217559238f61855e4648e3e56207519238f61859d4548e3e8216751523e2d2 + ((0x314549905453e85c92441514fa36249105453cc4d524415148fa0851e5648e3d + ((0x27c1e13641514f51534d905453cc5153641514f314589905452dc9612641514f + ((0x14f322751505453cc49d4541514f53734d505453cc51636415149f2784d90545 + ((0x5453cc99d4541514f316751505453cc19d4541514f323751505453cc4dd45415 + ((0x41514f323851505453cc4e14541514f322851505453cc4a14541514f33675150 + ((0x9d05452f48e16741514be22859d05452ec9213741514af26849d05452bc1a127 + ((0x14541514f316051505452dc5636741514bb14899d05452dc9616741514bb2485 + ((0x4899d05452758e167415149e62859d05453cc8214541514d362751505453ccd8 + ((0x94996549514f254259525453c98a14549514f256251525453e8d8924c15149b5 + ((0xf1638515354534d89d454d514f156351535452798a16749514da62851d254539 + ((0x52ec8213649114ba628419244526d522674d5149e62859d354527c821674d514 + ((0x114ba538d8924452e94236249114ba62855924453a98995649114ba6284d9244 + ((0x544538d9592655114b365841954452e98a15749114bb2084dd24452e95636249 + ((0x555114b36584d954452ec8213655114e36564d95445369dca2655114b3658499 + ((0x4de26452ec8213755114b963841d54452cd4e36555114b3528d9554452cd4236 + ((0x5d4541514f3117515054538e51636415149f2084de564527c562074d9149f208 + (0xa084de264529e5636741514ada3859d05452ba8a16741514f321851505453cc8 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0xca8a14541524f2927515054938e5163641524f53734d505c523e82137959148f + ((0x48fa084de564938b4963655124a7958d9d05492b68e16741524af21859d05493 + ((0x4d3664dd4741534e5a38595054d3c651d3541534f1a38515054d3c64dd454153 + ((0xd505b721849935416d68e1164d505b1e284d5544d33c85e0649534ada3859d05 + ((0xd35416d64a3634d505b5918d8d35416d68e1464d505e5a3651935416d68e1264 + ((0x2651505e3a4649945416ce9211651505b5a3851d35416dc861274d505b5948d8 + ((0x8d914541756dce3651505b3a484d9454178e9193651505b3a4849945416dc861 + ((0x5221749905b721849d45416da8a11751505b3938d9145416ce4a36451505b391 + ((0xf61849e464d63d86127919058f61849e364167c86127919059f21849e364167c + ((0x21036054078008f61849e365163b8a1178d9458fa084de26516378e107899458 + ((0x1c236c660bd16e2c4558a513e2644988d10e2043d8750cc15c288420780d8138 + ((0xe684cd97a2e85b8b41622a6534a39412764d4979292464748b9112163f07b0e7 + ((0xc1352644bc93d202314568950fa19426834f61e63c0768ea1ce3906e4d99ad34 + ((0xb336067ece599b12618c19802fa5e8bb96fad95a6b1151a9451ca214127c4ec9 + ((0x45c8890fa1c43285909a0bc117f2fcdf6bde79ef25e1bb475cea1d138a708db1 + ((0x9a2743683d019f73d677ce99c7352674c89852f25b4b09552924ac8f9011c631 + ((0xa172ae25beb716cad65a6b4166ac1573adb59eb0d52a874f69bd31a574968fd1 + ((0xa6749e8dd0fa073966cccd9832d654c9d8ff18621c3780efedf7be37aef2ddfb + ((0x79af2fe53c8f8ef17e23c2f82effde1b876ded5d9fb2761ebdd6fac755ea5d3f + ((0x4009020004804420800000000000000000080120820050100024820000000c0 + ((0x80400c0000000004a080000000e5a09043000000120200000000000000000040 + ((0x24020004b049622b08629040000000000000018202042a0800000000392 + ((0x41000030106020002a040000072942001ac40800018e170060002a21b8030000 + ((0x2104000000000000440800d044208841001a22080000000708200304 + ((0x430400000000000000610c2b00200000381c1820000000000000000 + (0xd07040800000000000000000000000080100000000020020e04800800e2184 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g111H5 (_ : Nat) : Nat := (0x71c20411021410000030020010024080031810c2242400000140008005100180 + ((0xb800061d6cfe92e6c0ce0a028204502020100a4227c20073c20030030915c324 + ((0x93b0afa6838c0ae63ad78108b9d549710b1469026500063097e6d48d1a800005 + ((0x3cc10003b95a07b525754fea218a01880bea7694d98cc530c891c50000c51000 + ((0xc8740a4caf2700045e68fd12f9ebc63a4d3560693cd1cb79684d17000e8 + ((0x567f9b22b807000000169d64d43954000e9700031600097f74ea6eabf1c92b70 + ((0x9c7f33101e7c000625420aa1352a0f559629000c2d000f7a65b5a59c404a + ((0x229bb000315f0e0005a36891a6c2f000a76000000a39000d05000838a46fb300 + ((0x7b103427111b3c0eaad7329610934566aece65f00007d16b3265b00000000000 + ((0xd5475616029605d504bd28199a5821a5bc32cc40f63e9cc81c2a70048b0ada62 + ((0x1fb88000000000324000d55acde950007cbf42f32ac8d82977436893a44dd2d6 + ((0x8b6d4cd31356aa908d45a2ab63f966eccad027463d14827b8bed03fd3d86b139 + ((0x361997571e000a8efb49ba76ff9a59febd000d5380d000d2163ebb2000e2ec37 + (0x15c00037294d05d8a8eac104f41470a115856c35c222 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g111D6 : Nat → Nat
  | 0 => (0x9504077aab28280ff150505019fccea2a033f59d45407da8a28a80f790551501 + ((0x17a52445102f6aa88a205bd5591440bf8a8228814fe47559019fcaea3203be51 + ((0xaa2a053f59d3540afd03a6a817cd234d502ef20a9aa05bd59d1440bf883a288 + ((0x40bf4a8264814fe67515029facea2a057e41d4540bd69228a8167d6551502ef2 + ((0xa4754102df28ca8205be4d95040b7cab280816ed5650902fd2a0a1205bb55932 + ((0xa2253f91d5640a7f1baac816f617559029ec2eab2053f95d4640a7f2ba6c815f + ((0x7f13aac81df617495039fc6ea32253f91d3644b7a9b282894fd674d112bf40e9 + ((0x41513ef28a82a27be5190544ff8a0a0a89df61749113f9a6492227ed4512444e + ((0x77d45d4544f5eb228a89fb51451513eba6aa2a27be59d0544ff88ba0a89f5935 + ((0xb28289edd4654d13faa82a9a27b75192344feaa0a4689cfe67515139facea2a2 + ((0x139fcaea32273f89d4644f7d03a8c89cfa0751913dea8ca8a277d95d4144f7aa + ((0x5511448f7b2b22891ef55645123fcaa48a247f554d1448ff882a2891cfe47559 + ((0x891fad2445123deece8a247bd59d1448ff313a2891fd53745123f4a488a247ed + ((0xf28a82a47be9190548f7ca320a91fe94241523fb28682a477b89d1448f7bb0a2 + ((0x548fae9aa0a91efb6741523df2ce82a47fa49d0548fed1ba0a91f593541523e + ((0xfad2451523f3a68a2a479f5954548fb692a8a91f5d3551523bbc6e82a47bed81 + ((0xca1a47f35494348e7f33a8a91cfd6751523bda4ea2a47774dd4548f5eb228a91 + ((0x8f76ab28491dde4754d23dbc8ca9a47b75195348fe6a12a691ede5650d23dbaa + ((0x7519239fa8f0b2473f55e0648f77232a491eed4654923bdcaea1247bb959424 + ((0x2473f55e4648e7e8bc8c91dfa07519239fcaea32473f85d4648f7d03a8c91cfa + ((0xea3cac91cfd0795923bec2eab2473f91d5648f7b0baac91cf617559239fc0eab + ((0x5904dbc6eab209378dd564127f13aac824fe1755904bf44ea82097d85d254127 + ((0xdc4d505453f91b20a8a7f13641514fe44c82a29fc49905453d89220a8a6fa075 + ((0xa0a8a7f06741514fe46e82a29fc4dd05453f913a0a8a7f12741514e628a82a29 + ((0x4fe6c082a29fc581054539aa2a0a8a7b52441514fe6ce82a29fc99d05453f8b3 + ((0x1525453f91360a8a7f126c1514f624982a297d99d05452fab3a0a8a5f6274151 + ((0x8a7b5244d514beace92a296d51d25453f2b124a8a7a54249514eeaca92a29cd5 + ((0xc0c92229ed41924452fb33a6a8a5f5674d514bec4e9aa29f558d354539aa2a6a + ((0x4453da83a488a7a76249114f6cac92229ed55924453db1b2488a7b53649114f6 + ((0xb62655114f6a4caa229ed81954453da832a88a5b65749114f6aae92229ed4dd2 + ((0xaa229ed49d54453db03aa88a7b50755114e6ecaaa229ed8d954453da9b2a88a7 + (0x2fa93c0c8a5f65741914bec4e83229ed8dd54453da9baa88a7b62755114b6c4e <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0x689914becae932297d8dd26452fb03a4c8a6f65649914deaac932297d55e0645 + ((0x297c81d364537b2b26c8a6f5564d914beaaf132297d4de26452fa83c4c8a6f55 + ((0x3aac8a5f5578d914bea4f1b229bd55a36452fb2ba6c8a5f6274d914fe40e9b2 + ((0x914bea0f2b2297d8dd56452fb13aac8a7e62755914bcc4eab229f909d56452fb + ((0xc85d05453f88ba0a8a7394541514ef26a82a29be8d905452fa9bcac8a5f52795 + ((0x6a8a73d454d514bec2e82a29bed81054539ea2a0a8a6fb6741514df2ce82a29f + ((0xbf40e9b2293f4de264527eabc0c8a6f63654514f6c2eaa229af8d954452fb0ba + ((0xd564527f1baac8a6ee27559149dc4eab2293f81d564527eabc6c8a4fd278d914 + ((0xa7f13741714ee26a82e293f4de564527e83cac8a5f61755914bdc4eab229bd85 + ((0xce82a49be59d05493f493a0a927394541524ef26a82a49be8d905493f91ba0b8 + ((0x493d713aa89272d2555124d7c6caa249cf515354937db020a9273d4541524df6 + ((0xe07559249faaf1b2493f45e36492fd03a6c924fd37859249faaf03249bb8d952 + ((0xb2497b89d56492fb0baac926ee27559249fc6eab249bd85d564927b0baac924f + ((0xec9ba0a9a7b94741534cf2ca82a69d64d5054d39ca2a0a9a4fd37959249fa0f2 + ((0x55134e3a6aaa2697d85d254d39ea2a4a9a6fa0649534df40c8aa69be59d054d3 + ((0x93f89d564d27f0baac9a6fa07559349f40eab2693e55e064d2ef13aa69a79e37 + ((0x326a82f79464d505ef44c9aa0bde49935417bd0b26a82f79164d505dbc6eab26 + ((0x5ef22ca2a0b5e91d35417bca3a6a82f79274d505ef22e9aa0bd6d8d35417bd2 + ((0x45d454179db228a82f7a3651505ef26ca2a0bde89945417bc9328a82f7a16515 + ((0xc82f7a3751505af46ea2a0bde4dd45417bd13a8a82f792751505ef42ea2a0bde + ((0xe42e9320bbe919264177ca324c82df94785905bf26f0b20b7e91d16416fd1ba2 + ((0x36416fca3c4c82df93789905df28d1320b7e91d26416fd1ba4c82ff21749905b + ((0xdf9178d905df28d1b20b7e91d36416fd13a6c82dfa174d905df48c9b20bbe519 + ((0xea320b768dd46417ec1ba8c82dfa2751905bf42ea320b7e51e36416fc93c6c82 + ((0x17bd03a8a82e7e2651505bf26f2320b7e49e46416fc8bc8c82dfa3751905fb46 + ((0x751905bbc6ea320b3f49e364167ea3c4c82cfd3789905bec2e9320b3f51e164 + ((0x26bd78dd454d73f1328a9acf54785925edc4ea2a4b3f49e464167e8bc8c82dfa + ((0xf1ba8c9adfa07519359fa8f1326b3f41e264d6fb0ba4c9acfd47859359fa4f03 + ((0x5945bdc4e8b28b3f49e065167e8bc0ca2dde37419459fa4f2326b3f45e464d6e + ((0x3f45e36516fd03a6ca2cfd37899459fa0f1328b7d85d265167e9bc2ca2cfd078 + ((0x40095047020c0c0059029011c08003901900ac038019007001c0009fa4f1b28b + (0x13d09b04bc25812508d044c218101079038c1c00d5065031c1800b9057029c1 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 2 => (0x1ed0f3076c3701b10d5067c3301910c3060c30017d0bb05ac2c015d0ab053c29 + ((0x8914109fc4f0271135098c4b0251127091c480235113085c4282090ff07dc3e0 + ((0x91bb0dac69034119f0cdc66032118d0c3c6002f91750b7c5982a91510a7c5302 + ((0x211107c830411203100c7f03ed1f10f6c7b03d11e50f0c7803b91d70e7c73038 + ((0x47121c90047d23b11cc8e0469233117c8b0451225110c87843921b10bc858429 + ((0x114fca7051d283140c9f84f1271132c9804b925712ac9504a5251126c9304952 + ((0x18ecc406152ff17ccbd05cd2e316ecb685ad2d115fcae056d2b5157cab85512a + ((0xd0ce607213891c1cdf06e536d1b2cd706ad3511a7cd2869134319bccd0661325 + ((0xed060829411207d0288093ff1fbcfc87d53e31eecf507993c71dfced07593a71 + ((0xd2088f1473238d1c08d546722fd1608a544d225d110879435217d0a084541f20 + ((0x3c09dd4eb273d3909bd4d9268d3389914c525fd2b894d4a324dd25892148f243 + ((0xf8a75539299d4b8a4151d28dd458a2550d285d420a0550127fd3f09f14f5278d + ((0xb155852bfd5f8af95792bbd5d8ae55712b6d580abd55d2acd558aa954f2a4d4 + ((0xbed5ef2f6d7a8bb95d92ebd750ba55cf2e3d708b6d5a92ced668b315952c8d63 + ((0xe166b331d978cb164f323d900c75635315d898c3d615307d828c09603300d7f0 + ((0x96ed372db80db56d9368db38d996c535fdae8d616a9351da70d2d68d341d9e0c + ((0x7513a5dd10e7d735397dcb8e5972538edc60e2170b383dc18e016fd37ddbe0de + ((0x973cade48f2178d3c5de10f0177d3bdddd8ee576f3b6dda8ecd7633b0dd78eb1 + ((0x20c04301f8d7c33dfdef0f717b53d9dec8f5d7ad3d5dea0f497a33cfde70f357 + ((0x10c4108504c3927140d0780842045014941080c102040810304320d083000400 + ((0xc109830912800030980200c004000804802000c10904100c2010614109200840 + ((0x20842000000c103810814082001016004101a2c1080810204002040880203040 + ((0x108840020204201003c10c400848443523100b8500843044814840080018404 + ((0x400d041000c1050584105068f00202040030408108820916840430881210c005 + ((0x890070034005150b04324400821970504414130ee5240341c021081005010d42 + ((0xc00c25930100425410848443497900b050084304012050010e43410c00103400 + ((0x959020014102240008940420204015040c11504001040904225c1000d0414443 + ((0x10406881001010000504005068c1030408102040810000304000081000c10306 + ((0x89805012014461092c89843a54443a261143800200070e882000000050400010 + ((0x322e1e02295848430006160080256008a90d80300a41a5c44322e1e01897130c + ((0x340c8a8454461092d8420ea54443a26118881212009841220430882140ea5430 + (0x20882140e0322a0148410d044c34128a8450d0b220c504c340e8884606210850 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 3 => (0x76508508580314840421101884214a1210c21968484414210830842009484200 + ((0x20865220c521012888850b22610c508820c22084c198a844130d440c39958030 + ((0x21080d8020e65600c0d8420ba2610c4c351030322081d960d8041422600c5088 + ((0x48030662210c20948430c210835888430b220a8410034842210488100308820c + ((0xe1884286c4c3a2121a8820006120098410825220c208480388250b130c200898 + ((0xc10c43084837110c880b87808c460400d8010825220c2c8820c2208006c3210 + ((0xc3a208000001c404141020400180103068010322090c08212a5c40d0c1414009 + ((0x8350c0b04540040256008a98020d25c4c32260181410088002c4043400200041 + ((0x102c3a208000001000020400304340c880904046000020704101110020943084 + ((0xc1d002110e05c3c01448443b0c09006120e4302c014141000010d04340020034 + ((0x800038142c3a2083b0d883000c10e03220240001b14102901003810e0a430 + ((0xc35918430664084880212850520101c80212a0200c259280804122008308020e + ((0x260104a14168c8c50a23600c488c20964230c488c20c2308441d8e804110e450 + ((0x830c2008098020aa30260104439143026108359184382020819920984412230 + ((0x400e200880101801600424900830960200e24902c5c20802321600c8c100308c + ((0x880387200a1f168f08487a3080001d8c8030924200c308020e63200c28082a00 + ((0xf0830204101008c002c50410100041c5040c1018410a020824900830c02081f0 + ((0x40410e041410004341000c2040030c104040000438100001000c10008100358 + (0x4 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g111H6 (_ : Nat) : Nat := (0x112c02010106001004000603290b11000200010002000001010105040b000a00 + ((0xa0505030c000114000214020909070203000d010013001e0b000300010f1401 + ((0x1800040160300300060606000307000802000b048102070300030502010402 + ((0x505090507012328030203210004000417481300060b00000301090004014304 + ((0xe2c8327d26c4c99040000000001a7e6c0b961b19eb5c731d02172b3100000e1a + ((0x1eda000312800071d1840000707f698542b62a9cb248837d170e3654fbfeb2 + ((0xecf8b611aacb4f970df8f6afacc2840d5bac070079304b5051b45fb44c3a8058 + ((0xf71427dc3e69bed75755f3f8adeee76aa2089de52456818ae69a672fc0429655 + ((0xc2900000010a12ee71f8000001e46000000094f49531f30f7d88ce4156b28d66 + ((0x6015ab1d3ce365952d0d9428c3e458000c33470e5e038149800080e4cfbeed + ((0x8e527ad15d3c74da98002ebcb6e2324335b27c3b098f18ce477920002e41a780 + ((0xd9eea50006b9acad225209dbc0e914475c718de2a200068591e4cd02f + ((0x299b000000034fc496497a41d9c0000000000e59e146ae96e11053cec0fc4f4 + ((0x45248000afc3ab29485b906251010d76b63134142a4ca43989dbc58a800063ae + ((0x2f79fe0000003c6285b729e900d5c4cc4559402a67d9458823788740000008b + ((0xd88000d58448f84be2302492c2a6ac9f01f777d2c2300000e5d8003d0984e000 + ((0x314ba0001760003ebe000d79e8b28735861c3fa2747000000039b7c316c50007 + ((0x981f42e0552628000cae532f846a360006376a36cd6000710f276b038bf4a7aa + ((0x6945170194260a15382a3f91242bb0b82968e37e34a01b9af85c69611f000706 + ((0x4e00014a0000001483d6de0c140e6ed0007a20c63072b8480f01afa14933d968 + ((0x8ac713d345956b6d968e30415e33940881d012fbf7b6680000ae6a8560ae3aec + ((0xe5158da5de7ad07fb6b20467589b19108d0ab2365d822cdb30a6c95bf25800b + ((0xafe6f6534da99197bd3dc3e0a000a5b317faf3f024b1e911b2fce8b937d72c56 + ((0x2d609b3bc67e57b02782eee2949195d27291fc5b0752d98e183502032bd6d0f2 + ((0x52f45f3deec1e1a3acbb81981b4b6714deee8d1106e5adb19b557cb443aa84d1 + ((0x3c4b546012e2e5022eb1acb910000002f095280000000001843000643dace48a + ((0x2b315a400000045071900002718001d2c8fde99845629955200019db01c6a2b + ((0x6a394124facb97a98000000e34c123b1ee000000000000000c3dd98026800000 + (0x290db9583bad84c4d4dd0006108001d39254f9abd8587d348 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g111D7 : Nat → Nat
  | 0 => (0x2fb4c902ff51502ff4d502fd45102bf55901bf51901fe54101fd50501ff51501 + ((0x12bf4d912fd50512ff4d112bf55902bf51902bf4d902fe54102fe50102fb5090 + ((0x513f754d13f748d13ff51513fe41513ff49113bf55903fe54103ff49503bf519 + ((0x1523ff41523fe41523fdc5123ff45123fd45123bf55913bf51913fd54513fd50 + ((0x85923ff45923bf81923ff41923fb54923fb50923f754d23f750d23ff51523fec + ((0xe54104ff49504ff45504bf95923ff55923bf55923bf91923ff51923bf51923bf + ((0xfd41914ed55114ed49114fd4d514fd49514fcc1514fd41514fc41514bf55904f + ((0x4ff41514fe41514fd95914fd55914fd8d914fd4d914fd89914fd49914fd81914 + ((0x14bf89914ff49914bf81914ff41914fd54514ef55114ef49114ff4d514fec151 + ((0x524fd4d714fcc1714fd41714fc41714bf95914ff55914bf55914bf8d914ff4d9 + ((0x5924ff45924bf81924ff41924fb54924ef55124ff4d524fec1524ff41524fe41 + ((0x55134ff49534ff45534fe41534bf95924ff55924bf55924bf8d924ff4d924bf8 + ((0xe89905fe49905fe85905fe45905de51505de4d505bf55934be81934f754d34ef + ((0xff49905bf85905ff45905df51505df4d505fe91905fe51905fe8d905fe4d905f + ((0x5ff41935df51535bd85925df51525bf91905ff51905bf8d905ff4d905bf89905 + ((0x45bf81945ff41945bf91935ff51935bf89935ff49935bf85935ff45935bf8193 + ((0x945bf8d945ff4d945ff89945bf89945ff49945ff85945bf85945ff45945ff819 + ((0x443b10803d40e0432e0b5028808f01f007541ba059c11403040670034000ff8d + ((0x4894623cc8b521a48161f2877e1c906d81a30671187860316c055614ec4e8125 + ((0x860e0436e0d88350ccf7331cc8230a0bf82e78b6e2ca4add2a44a4c288c9d026 + ((0x4ae927c48f91f946b516844a90de426505b4058fd13e30f553c08ed23a34e3a3 + ((0x75ec17565c7d6d35a8d65e582d5d455e954a53c14c051b54214f1d3974cf530d + ((0x277015bc06dd1b4b6c35ac16a45a37681d9ad661194d64598f462a187860cd7e + ((0xad81f60317f5df927d51f0f7b45e8c7901df476bdd7174b1cee72f9c87715dc + ((0x252c93824b791ae43b8f863b88d7a32e8bde2c78a5e24b886e1c1864613e841e + ((0x1420386450a1118385060183019dd27289bfe6dd9a46668991a5fa972a5a8957 + ((0x921e346068b101a20200b284070c0f1622304040164878d18162048688141806 + ((0xa151830380a2a3c7098a162014000a1214106444850ca0e9315223070a0e0805 + ((0x426284060a0a02c90d1216243440a0818080c20384870a8c1c10280a26407098 + ((0x3070a0818060e1694324344c5080d141c000a26407090f1422305040165478e1 + ((0x3068a48194264068b0b111828200b2a3c68b101620305050165080d171422 + (0x6c84b121a205860c02c98808192223c70a8a101a20300b243c70a0b121a20506 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0x14223070a0a18000c223c6888811102c200a2a3c6888b102210200a101018648 + ((0x4478d10182c406880c02ca0e101622305840c02878d1018222048600028a0e11 + ((0x440a0c02870dcb15204460e1418059528902410300010507658a911838506014 + ((0xc1020092a0c1010028e1a942e4890d1028300b2a4928582060002090d4b92243 + ((0x8dca9110203000125498eca9118303000145488d4b91102820401454725c88c1 + ((0x5203c40a0818000c2a2c424090462a3c725098c182820600030a8a12942c018a + ((0x80d141804951c1422305040c00051526392a3063152638284460a0c024a8f1a1 + ((0x183440a0c02c6870a9040e1822a34284068a0818000a2a446a4440862a446850 + ((0x8700e50725890c1a2c2870202d2c4868b0e01890e0f142434404012487070b12 + ((0xc04131d9620407890e024a0e4b121834485012506a5890c1a2428091c9624345 + ((0x282d2c486890a020a0e4b12183448702028a0e189624344850123b2c4080d161 + ((0xc486890a020a0e4b121a2c285012507084b121a2c285014512c4090f12242809 + ((0x81618382018509250b1020c486a5890d102c3070402ca2588121a24280828192 + ((0x6e588101a20587014509901b962040789081c061423102200030e1a942c4868 + ((0x71108118a101c96204860c101c000c28303a50b1062834325090c1a204850165 + ((0x24a0e0b1218305840a0005941c212c4400072840685890c1e2048408030a131 + ((0x20306a5890d161c03941a162430688101005140d11102423141a182c4868808 + ((0x2c486881418048e1a96204860d1214050d4b121a2c38071c352c4090c1a2c287 + ((0x440808e4c683440a0811c991020041c35285890d1028300a2649285820462435 + ((0x83c40a08100614262d204823132039284860c14103800184c4874a1452636183 + ((0x5222042931a1424345040104c705090c14102800145498e4a8000c4c80d0a921 + ((0x30e1b152010030e0d1420848725890d10283009263428486881410200a263 + ((0x6c50b93182c2809223828486880c020764878b0c01888e860d1020038e068814 + ((0x8e121c080a24362a447081614280a2434645488e1214048d8a17223058701044 + ((0x4280825142a4c68e1214049215152238485010486c5488e121c080924344c548 + ((0xb9118305870144888f1d142e4c60b0a0006128a1522384090a0249078a911c2 + ((0x242070002c90d1315221023921e362a4080e102c204018486068a9020c48745 + ((0x8101005120f15183403121e3a284c60e10202800184888a8a8000c486c5080e1 + ((0x3091114942c01888e460c1400038dcb8e141c030d460c141023121d14223070 + ((0x52235221023111e342a4070816103000184440648105223c725098c1c2040600 + ((0xa241d28586806223828447081018000a22392a3062911a1420384840c00051 + (0x481210210685490c1c2058408028a06481212119285060841c942430708101c0 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 2 => 0x182400041d9428487081014000a22392a0002830484088342e4090e10242040144c6a442045
  | _ => 0
def g111H7 (_ : Nat) : Nat := (0x1004604bf938a35d60c004708014510204120f5430800416001191c1042040 + ((0xfdb3c23d161530b648f4fba0e5b6df865800000240f63965005ce68005c7400c + ((0xc218e86280049ec7d8b98938865ec040c5325d8300fe80715b03e8dfd1c6165a + ((0x1a0c4e1cf96c0009e3dbfdeae5613000207654c0030391840035341c2200e6a4 + ((0x84e91640b295781416b90e8941d605c42be43a4ed39d6189913f4f2a456660f7 + ((0xdad80a375dc98b9d10e741d87066200861944541aa1e26c5f3d13a2f599cce1b + ((0x8a2c2c001c48000000000d2c001d7fd2254be4a901cd61280018835e4918001c + ((0x80031268cad9f5040000000000021c6c7a22ad46dd99940d14a6088c34000000 + ((0x741fc001a21225424003dab8acce000101195fa08508000003972e121f400145 + (0x286e1400681cb8640a8cefcc5da6d936040000bf230001d78002e3e456d <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g111D8 (_ : Nat) : Nat := (0xfec17fa0bf905fe9a7f493ee29fd14fa8a7f413fa47fd13fe81ff44bfa05fd01 + ((0x27c4a48d1039ef396678c0153276444720b711a180180007f517fa6bfd25fe8a + ((0xc388206000e40f38d2459048c388206000f40f38d3051230e20a106000fb3550 + ((0xe208100e3ce3489451230e20a104038f38a1641230e20a10403503cd2e51448 + ((0xd94510388284180038e9440e28601d03871641038828418003553ce365164123 + ((0x601ce9459040e20a10402d340e36516410388206000e40e3651038a180951038 + ((0x1a51448c30a106000d3ce3459230a180948f38d1641230c284180038d1648c28 + (0x38d9459040c28418003113ce3651641230c284100e3651641230c206000b3cd <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g111H8 (_ : Nat) : Nat := 0x25804658bddc6311641ce0012b480c71243079a0000003d40000000d200100110130a
def g111D9 (_ : Nat) : Nat := 0x1483104033f
def g111L : Nat → Packing
  | 4 => (11,5,5,0,0,6,0,g111D4)
  | 5 => (214,4,5,0,0,11,0,g111D5)
  | 6 => (408,3,5,0,0,13,0,g111D6)
  | 7 => (156,2,5,0,0,14,0,g111D7)
  | 8 => (19,1,5,0,0,11,0,g111D8)
  | 9 => (1,0,5,0,0,1,0,g111D9)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 4 13 3 8 4 0 g111H4 h
  | 6, h => lookupWord 74 255 6 12 8 0 g111H5 h
  | 7, h => lookupWord 137 483 8 13 9 0 g111H6 h
  | 8, h => lookupWord 53 186 6 12 8 0 g111H7 h
  | 9, h => lookupWord 10 26 4 9 5 0 g111H8 h
  | _, _ => none
def g111 : Forest := ⟨111,9,fun i => g111Y[i]?.getD (0,0),g111C,[[]],g111L,g111I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P4_0 : block g111 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P4_5 : block g111 4 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P4_10 : block g111 4 10 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111B4 : block g111 4 0 11 = true := (@block_merge g111 4 0 10 1 (@block_merge g111 4 0 5 5 g111P4_0 g111P4_5) g111P4_10)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_0 : block g111 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_5 : block g111 5 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_10 : block g111 5 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_15 : block g111 5 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_20 : block g111 5 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_25 : block g111 5 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_30 : block g111 5 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_35 : block g111 5 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_40 : block g111 5 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_45 : block g111 5 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_50 : block g111 5 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_55 : block g111 5 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_60 : block g111 5 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_65 : block g111 5 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_70 : block g111 5 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_75 : block g111 5 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_80 : block g111 5 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_85 : block g111 5 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_90 : block g111 5 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_95 : block g111 5 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_100 : block g111 5 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_105 : block g111 5 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_110 : block g111 5 110 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_115 : block g111 5 115 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_120 : block g111 5 120 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_125 : block g111 5 125 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_130 : block g111 5 130 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_135 : block g111 5 135 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_140 : block g111 5 140 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_145 : block g111 5 145 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_150 : block g111 5 150 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_155 : block g111 5 155 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_160 : block g111 5 160 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_165 : block g111 5 165 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_170 : block g111 5 170 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_175 : block g111 5 175 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_180 : block g111 5 180 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_185 : block g111 5 185 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_190 : block g111 5 190 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_195 : block g111 5 195 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_200 : block g111 5 200 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_205 : block g111 5 205 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P5_210 : block g111 5 210 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111B5 : block g111 5 0 214 = true := (@block_merge g111 5 0 160 54 (@block_merge g111 5 0 80 80 (@block_merge g111 5 0 40 40 (@block_merge g111 5 0 20 20 (@block_merge g111 5 0 10 10 (@block_merge g111 5 0 5 5 g111P5_0 g111P5_5) (@block_merge g111 5 10 5 5 g111P5_10 g111P5_15)) (@block_merge g111 5 20 10 10 (@block_merge g111 5 20 5 5 g111P5_20 g111P5_25) (@block_merge g111 5 30 5 5 g111P5_30 g111P5_35))) (@block_merge g111 5 40 20 20 (@block_merge g111 5 40 10 10 (@block_merge g111 5 40 5 5 g111P5_40 g111P5_45) (@block_merge g111 5 50 5 5 g111P5_50 g111P5_55)) (@block_merge g111 5 60 10 10 (@block_merge g111 5 60 5 5 g111P5_60 g111P5_65) (@block_merge g111 5 70 5 5 g111P5_70 g111P5_75)))) (@block_merge g111 5 80 40 40 (@block_merge g111 5 80 20 20 (@block_merge g111 5 80 10 10 (@block_merge g111 5 80 5 5 g111P5_80 g111P5_85) (@block_merge g111 5 90 5 5 g111P5_90 g111P5_95)) (@block_merge g111 5 100 10 10 (@block_merge g111 5 100 5 5 g111P5_100 g111P5_105) (@block_merge g111 5 110 5 5 g111P5_110 g111P5_115))) (@block_merge g111 5 120 20 20 (@block_merge g111 5 120 10 10 (@block_merge g111 5 120 5 5 g111P5_120 g111P5_125) (@block_merge g111 5 130 5 5 g111P5_130 g111P5_135)) (@block_merge g111 5 140 10 10 (@block_merge g111 5 140 5 5 g111P5_140 g111P5_145) (@block_merge g111 5 150 5 5 g111P5_150 g111P5_155))))) (@block_merge g111 5 160 40 14 (@block_merge g111 5 160 20 20 (@block_merge g111 5 160 10 10 (@block_merge g111 5 160 5 5 g111P5_160 g111P5_165) (@block_merge g111 5 170 5 5 g111P5_170 g111P5_175)) (@block_merge g111 5 180 10 10 (@block_merge g111 5 180 5 5 g111P5_180 g111P5_185) (@block_merge g111 5 190 5 5 g111P5_190 g111P5_195))) (@block_merge g111 5 200 10 4 (@block_merge g111 5 200 5 5 g111P5_200 g111P5_205) g111P5_210)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_0 : block g111 6 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_5 : block g111 6 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_10 : block g111 6 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_15 : block g111 6 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_20 : block g111 6 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_25 : block g111 6 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_30 : block g111 6 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_35 : block g111 6 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_40 : block g111 6 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_45 : block g111 6 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_50 : block g111 6 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_55 : block g111 6 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_60 : block g111 6 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_65 : block g111 6 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_70 : block g111 6 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_75 : block g111 6 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_80 : block g111 6 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_85 : block g111 6 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_90 : block g111 6 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_95 : block g111 6 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_100 : block g111 6 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_105 : block g111 6 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_110 : block g111 6 110 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_115 : block g111 6 115 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_120 : block g111 6 120 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_125 : block g111 6 125 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_130 : block g111 6 130 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_135 : block g111 6 135 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_140 : block g111 6 140 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_145 : block g111 6 145 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_150 : block g111 6 150 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_155 : block g111 6 155 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_160 : block g111 6 160 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_165 : block g111 6 165 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_170 : block g111 6 170 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_175 : block g111 6 175 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_180 : block g111 6 180 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_185 : block g111 6 185 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_190 : block g111 6 190 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_195 : block g111 6 195 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_200 : block g111 6 200 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_205 : block g111 6 205 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_210 : block g111 6 210 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_215 : block g111 6 215 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_220 : block g111 6 220 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_225 : block g111 6 225 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_230 : block g111 6 230 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_235 : block g111 6 235 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_240 : block g111 6 240 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_245 : block g111 6 245 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_250 : block g111 6 250 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_255 : block g111 6 255 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_260 : block g111 6 260 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_265 : block g111 6 265 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_270 : block g111 6 270 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_275 : block g111 6 275 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_280 : block g111 6 280 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_285 : block g111 6 285 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_290 : block g111 6 290 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_295 : block g111 6 295 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_300 : block g111 6 300 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_305 : block g111 6 305 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_310 : block g111 6 310 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_315 : block g111 6 315 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_320 : block g111 6 320 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_325 : block g111 6 325 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_330 : block g111 6 330 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_335 : block g111 6 335 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_340 : block g111 6 340 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_345 : block g111 6 345 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_350 : block g111 6 350 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_355 : block g111 6 355 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_360 : block g111 6 360 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_365 : block g111 6 365 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_370 : block g111 6 370 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_375 : block g111 6 375 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_380 : block g111 6 380 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_385 : block g111 6 385 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_390 : block g111 6 390 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_395 : block g111 6 395 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_400 : block g111 6 400 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P6_405 : block g111 6 405 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111B6 : block g111 6 0 408 = true := (@block_merge g111 6 0 320 88 (@block_merge g111 6 0 160 160 (@block_merge g111 6 0 80 80 (@block_merge g111 6 0 40 40 (@block_merge g111 6 0 20 20 (@block_merge g111 6 0 10 10 (@block_merge g111 6 0 5 5 g111P6_0 g111P6_5) (@block_merge g111 6 10 5 5 g111P6_10 g111P6_15)) (@block_merge g111 6 20 10 10 (@block_merge g111 6 20 5 5 g111P6_20 g111P6_25) (@block_merge g111 6 30 5 5 g111P6_30 g111P6_35))) (@block_merge g111 6 40 20 20 (@block_merge g111 6 40 10 10 (@block_merge g111 6 40 5 5 g111P6_40 g111P6_45) (@block_merge g111 6 50 5 5 g111P6_50 g111P6_55)) (@block_merge g111 6 60 10 10 (@block_merge g111 6 60 5 5 g111P6_60 g111P6_65) (@block_merge g111 6 70 5 5 g111P6_70 g111P6_75)))) (@block_merge g111 6 80 40 40 (@block_merge g111 6 80 20 20 (@block_merge g111 6 80 10 10 (@block_merge g111 6 80 5 5 g111P6_80 g111P6_85) (@block_merge g111 6 90 5 5 g111P6_90 g111P6_95)) (@block_merge g111 6 100 10 10 (@block_merge g111 6 100 5 5 g111P6_100 g111P6_105) (@block_merge g111 6 110 5 5 g111P6_110 g111P6_115))) (@block_merge g111 6 120 20 20 (@block_merge g111 6 120 10 10 (@block_merge g111 6 120 5 5 g111P6_120 g111P6_125) (@block_merge g111 6 130 5 5 g111P6_130 g111P6_135)) (@block_merge g111 6 140 10 10 (@block_merge g111 6 140 5 5 g111P6_140 g111P6_145) (@block_merge g111 6 150 5 5 g111P6_150 g111P6_155))))) (@block_merge g111 6 160 80 80 (@block_merge g111 6 160 40 40 (@block_merge g111 6 160 20 20 (@block_merge g111 6 160 10 10 (@block_merge g111 6 160 5 5 g111P6_160 g111P6_165) (@block_merge g111 6 170 5 5 g111P6_170 g111P6_175)) (@block_merge g111 6 180 10 10 (@block_merge g111 6 180 5 5 g111P6_180 g111P6_185) (@block_merge g111 6 190 5 5 g111P6_190 g111P6_195))) (@block_merge g111 6 200 20 20 (@block_merge g111 6 200 10 10 (@block_merge g111 6 200 5 5 g111P6_200 g111P6_205) (@block_merge g111 6 210 5 5 g111P6_210 g111P6_215)) (@block_merge g111 6 220 10 10 (@block_merge g111 6 220 5 5 g111P6_220 g111P6_225) (@block_merge g111 6 230 5 5 g111P6_230 g111P6_235)))) (@block_merge g111 6 240 40 40 (@block_merge g111 6 240 20 20 (@block_merge g111 6 240 10 10 (@block_merge g111 6 240 5 5 g111P6_240 g111P6_245) (@block_merge g111 6 250 5 5 g111P6_250 g111P6_255)) (@block_merge g111 6 260 10 10 (@block_merge g111 6 260 5 5 g111P6_260 g111P6_265) (@block_merge g111 6 270 5 5 g111P6_270 g111P6_275))) (@block_merge g111 6 280 20 20 (@block_merge g111 6 280 10 10 (@block_merge g111 6 280 5 5 g111P6_280 g111P6_285) (@block_merge g111 6 290 5 5 g111P6_290 g111P6_295)) (@block_merge g111 6 300 10 10 (@block_merge g111 6 300 5 5 g111P6_300 g111P6_305) (@block_merge g111 6 310 5 5 g111P6_310 g111P6_315)))))) (@block_merge g111 6 320 80 8 (@block_merge g111 6 320 40 40 (@block_merge g111 6 320 20 20 (@block_merge g111 6 320 10 10 (@block_merge g111 6 320 5 5 g111P6_320 g111P6_325) (@block_merge g111 6 330 5 5 g111P6_330 g111P6_335)) (@block_merge g111 6 340 10 10 (@block_merge g111 6 340 5 5 g111P6_340 g111P6_345) (@block_merge g111 6 350 5 5 g111P6_350 g111P6_355))) (@block_merge g111 6 360 20 20 (@block_merge g111 6 360 10 10 (@block_merge g111 6 360 5 5 g111P6_360 g111P6_365) (@block_merge g111 6 370 5 5 g111P6_370 g111P6_375)) (@block_merge g111 6 380 10 10 (@block_merge g111 6 380 5 5 g111P6_380 g111P6_385) (@block_merge g111 6 390 5 5 g111P6_390 g111P6_395)))) (@block_merge g111 6 400 5 3 g111P6_400 g111P6_405)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_5 : block g111 7 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_10 : block g111 7 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_15 : block g111 7 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_20 : block g111 7 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_25 : block g111 7 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_30 : block g111 7 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_35 : block g111 7 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_40 : block g111 7 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_45 : block g111 7 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_50 : block g111 7 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_55 : block g111 7 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_60 : block g111 7 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_65 : block g111 7 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_70 : block g111 7 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_75 : block g111 7 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_80 : block g111 7 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_85 : block g111 7 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_90 : block g111 7 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_95 : block g111 7 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_100 : block g111 7 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_105 : block g111 7 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_110 : block g111 7 110 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_115 : block g111 7 115 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_120 : block g111 7 120 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_125 : block g111 7 125 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_130 : block g111 7 130 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_135 : block g111 7 135 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_140 : block g111 7 140 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_145 : block g111 7 145 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_150 : block g111 7 150 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P7_155 : block g111 7 155 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111B7 : block g111 7 0 156 = true := (@block_merge g111 7 0 80 76 (@block_merge g111 7 0 40 40 (@block_merge g111 7 0 20 20 (@block_merge g111 7 0 10 10 (@block_merge g111 7 0 5 5 g111P7_0 g111P7_5) (@block_merge g111 7 10 5 5 g111P7_10 g111P7_15)) (@block_merge g111 7 20 10 10 (@block_merge g111 7 20 5 5 g111P7_20 g111P7_25) (@block_merge g111 7 30 5 5 g111P7_30 g111P7_35))) (@block_merge g111 7 40 20 20 (@block_merge g111 7 40 10 10 (@block_merge g111 7 40 5 5 g111P7_40 g111P7_45) (@block_merge g111 7 50 5 5 g111P7_50 g111P7_55)) (@block_merge g111 7 60 10 10 (@block_merge g111 7 60 5 5 g111P7_60 g111P7_65) (@block_merge g111 7 70 5 5 g111P7_70 g111P7_75)))) (@block_merge g111 7 80 40 36 (@block_merge g111 7 80 20 20 (@block_merge g111 7 80 10 10 (@block_merge g111 7 80 5 5 g111P7_80 g111P7_85) (@block_merge g111 7 90 5 5 g111P7_90 g111P7_95)) (@block_merge g111 7 100 10 10 (@block_merge g111 7 100 5 5 g111P7_100 g111P7_105) (@block_merge g111 7 110 5 5 g111P7_110 g111P7_115))) (@block_merge g111 7 120 20 16 (@block_merge g111 7 120 10 10 (@block_merge g111 7 120 5 5 g111P7_120 g111P7_125) (@block_merge g111 7 130 5 5 g111P7_130 g111P7_135)) (@block_merge g111 7 140 10 6 (@block_merge g111 7 140 5 5 g111P7_140 g111P7_145) (@block_merge g111 7 150 5 1 g111P7_150 g111P7_155)))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P8_0 : block g111 8 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P8_5 : block g111 8 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P8_10 : block g111 8 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P8_15 : block g111 8 15 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111B8 : block g111 8 0 19 = true := (@block_merge g111 8 0 10 9 (@block_merge g111 8 0 5 5 g111P8_0 g111P8_5) (@block_merge g111 8 10 5 4 g111P8_10 g111P8_15))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111P9_0 : block g111 9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111B9 : block g111 9 0 1 = true := g111P9_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g111B4
  · exact g111B5
  · exact g111B6
  · exact g111B7
  · exact g111B8
  · exact g111B9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 10 := lower_forest (g:=g111) (i:=0) (hints:=16777507) (before_sound K125 V125) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K125 10 [(111,[]),(123,[66, 83])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V125 low111 (by decide +kernel)

def g95Y : Array (Bits × Bits) := #[ (0x16faeb053b8ad9ad64b16549510e4bb9e36215dfa58280edd59fa3bab78c4182,0xc43a0527228a9b480018648230ea0f9e2f34ac3240a80c0051ba3bab68c0180), (0x81f5ed3b5b542b435bd7128d293c2ac1fe0e92d1dabdab3c9863d387db130038,0xe48451850090c1414280108120242001d10c22906020212e984200069b020038), (0xe3fac8d2c60809f6cf36b1e6cdaa1916faa0de7a4f0a445467635a7530b8f011,0x33882306a0100028c282044c8c8090602405c4a0a48444000a012212018f001), (0x6e327f0c7ef2752ea749284b0ee5463c955c35ef24415b9fc4fc3c09894ad3d6,0xe1b4480d888002430c2808818c600206050835280860281e40e400010942d016), (0x5b2ff5d8a5f59cdb86cd5c74dd4db4e500bde5009536cec91b4a8d620c85af0c,0x410000040a10041041002011008040009080009502020100188d4004810700), (0x0,0x0), (0xbc1d802f1659b3ba5ceccf3b32b2c5bf4e2b08aa52c735622a2d849066661ce1,0x8000002004424182006c30a020044b0082100000085000002012090402408c0), (0x0,0x0), (0x0,0x0) ]
def g95C : List ColumnInfo := [(1,0,94,0,8), (9,0,86,0,7), (4,0,91,0,7), (2,0,93,0,7), (64,0,31,0,7), (16,0,79,0,7), (65,0,30,0,5), (17,0,78,0,5), (6,0,89,0,5), (5,0,90,0,5), (3,0,92,0,5), (73,0,22,0,4), (25,0,70,0,4), (13,0,82,0,4), (11,0,84,0,4), (7,0,88,0,4), (68,0,27,0,4), (66,0,29,0,4), (20,0,75,0,4), (18,0,77,0,4)]
def g95D5 (_ : Nat) : Nat := (0x4bc94512551512a7a585190544be84514241512aba485590444bd84555241112 + ((0x512d65274554544b8d5911551512f25244554544b5945d2551512e2d64495454 + ((0x4544a3b8a16751512da5274514544b6945d2451512e35145954544b8b4916551 + ((0x654912ba6584514244b6995d1450912ea5145594244a3e42267515128f61859d + ((0x59d15412768e167455049ea2859d15412d99211554912d66474555244b994554 + ((0x2267495049ba4859d25412768e167495049f21859d254126e52267455049ba48 + ((0xa4845d56412b68e11755904aea2845d564131edd55649904c7b75559164126e5 + ((0xb68e16741514aea2859d05452ae9212755904ada3849d56412bc8612755904ab + ((0x4e2d42595254534d51d1549514f2542455254529e5636741514a7a5859d05452 + ((0x4933985c2755914b3628455544534d89d1555114f3107455544538d456265511 + ((0x5124e2d25859544929e5636741524a7a5859d05492b68e16741524af21859d05 + ((0x906516ba8a11641945ce62705d56492cb8612555124d2e1749554493ca41d255 + ((0xa224c841d46615c480e42a0901503c00cda3841e26517368e10785945af21849 + ((0xd5b95f5654a4ed354bd2948d1d45d1142d053fcf93cced39ce136ccc318c02c4 + ((0x9925591a378c62b896047f9f87c9ec799e0769d46cdad69da166d9563d8960d7 + ((0x41000018202040a08141018204042208081020210040210201081 + ((0x8250dc21800000000000000107820800107820800000000000000 + (0x410083a1074208000104a138430 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g95H5 (_ : Nat) : Nat := (0x85f78b3b82b2147abf524f86e70bc57b6019111b00c0892560001400010410c4 + ((0x4660000000ac46d53ac4dce535943c635f7fc9d08ba5c280262d3f0c4836ce + ((0x1512c0000000256000006180050400000244bc437af8200023da405ed51d46c + (0xf5e91a612a757c81f99aa3e272317d51ce80000 <<< 256)) <<< 256)) <<< 256))
def g95D6 : Nat → Nat
  | 0 => (0x90544b7cb3a08895fa5741112bf2ae82225be5590444bf8a8a08897e95241112 + ((0x97751551512eda4aa2a25be59d0544afd23a0a896f94641512fe28282a25fa50 + ((0xcea2a257d45d4544af693a8a896bd6451512f6a28a2a25eb4914544b3eb2a8a8 + ((0x44bf2a0aa4895ee5750912f4a28a1225bb5594244bf2a8a84894fe67515129fa + ((0x64754512dea8ca8a257d95d4144b7aab282895ee4754912eca2aa9225bb51952 + ((0x2a097e99d15412fcb3a2a825fa2745504ef24a8aa093f91d5644a7f2ba8c895f + ((0xfd2ba2c825fa2745904df2ac8b209be49916412fd33a4a825f96749504bf42e9 + ((0x55904df24eab209be85d564137c8baac825fa5749904bf42e93209be55926412 + ((0x9ee49105453ed1baac825da3755904bf44eab2097e85d564136d1baac826fa27 + ((0x124a8a67d6549514eea2a92a29cf515254537db3a0a8a6f96741514df44c82a2 + ((0x14d7c4caa2296f95d244535f2b2488a6bd5649114f6aa2922296f51d25453d6a + ((0x55e26452fb13aa28a6f62654514f6c2eaa2296f89d54453dc83aa88a73515551 + ((0xc8a5ee2755914dec2eab2293f89d564537713aac8a4ee2755914dd84eab2293f + ((0xda4a8aa49cf515154937db3a0a926f96741524df42c82a493f49e56452fb0baa + ((0x52493d713aa8925be1755124f720eaa249cb495544935f0b2a89267d6545524e + ((0x4fe1755924dec2eab2493d85d564937a0baac924fd5785924bdc2ea9249bb859 + ((0xe8b20bbe519164177c9322c82cfd1795924bdc4eab2497d85d564937713aac92 + ((0x16fd13a8c82dfa1751905bf48e9320b7e85d264177ca324c82dfa4745905bf44 + ((0x2751515ef20ea2a2b9f89945456bf23a4a8ae7e4649515fb46ea320b768dd464 + ((0xa4b9f859454967e93c8c8adf61751915bdc4ea322b3f51e26457bb0ba8a8ad7e + ((0xe8bc8c92dee2751925bec2ea324b3f51e16497b713a8a92d7e1751525ef20ea2 + ((0x5945bdc4e8b28bf68dd065177d1320ca2ef92641945df42c8328bbe459065167 + ((0xbe41e265167c83c4ca2df61749945bf20f0b28b3f49e165177c83c2ca2cf9078 + ((0x5e05705405104a04303c03502e02702001500e0070005f907899459fa2f1328b + ((0x11911611310c1050fe0f70f00cd0c60bf0b809508e08707c07907206b0640610 + ((0xb1c81c11ba19f19818918217316c16915e15715414914213f13413112e123120 + ((0x8627f27827126a25723822d22a22722021d21621320c2092021ff1f41f11ea1d + ((0x33532e32732030d2ee2e32dc2d92d22cf2c42c12be2b72b42ad2aa2a329028d2 + ((0xb3d83c93b63af3a83a139e39338c38937e37737436d36a36336035934634333c + ((0x8a47f47446945e45b45445144a44343c42941e41b41441140a4033fc3e93de3d + ((0x80a1028608783840e110840a0a102860d2451d5124fb4f04d54ce4c34ac4a14 + (0x20608402a181c10170f0100a088838400100040818208080002820001e0e102 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0x8046021000110084011020000408202040828206084022181c10170f01008088 + ((0x2c60c3c362d220808d820b1e0a087820b160a08744080448215182011a084440 + ((0xc3c03d20204000040800608004080200808402100840c3c300870d4883802310 + ((0x200002001038b49c3c0200c80e283480828386083c261b0880a48088607 + ((0xc80e283480828384083c26130880a48088405c3c03d202040608022080860210 + ((0xa838023102c60d1020112085460804682111020000200002001838b49c3c0200 + ((0x8408342e130894a0a10000080ca082038608342e1b0894a0a100043c300870f4 + ((0x8b8946c2022e270050f0d884340284d084c7421055084c54210000080ca08203 + (0xe0d8842400033182c200162e25130808b89c010383621090000cc40b08005 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g95H6 (_ : Nat) : Nat := (0x8244c237080030110000118414307000010f0001a000e0038100300082000000 + ((0x500698c61323f1341338a8ca6081c271a06900228c2d001000342a81961000c9 + ((0xc962000364103fd61114208c5e98756420260f13e1d654887711e5af544494c4 + ((0xd50001155d981b4048256412dfd57549c65800350e81b1c5d080200039f00008 + ((0x94ad2078b000000296c000001510000000000cbe0e489acf4d95c4c5f4cb88cf + ((0x9f8a11d9a16cd201d1eb57cd3a64c00000395b0880000015800004ec00042c11 + ((0xdb0e2c001cd74ead925e0179dbce5255c4f3260001cde1c80039b8469d26e331 + ((0x7c780031a9168003d4000082908f4509738d81e643400092bc30a5c000c5aa46 + ((0x3b8c0002c421dd0fa46400286dc16454e29403c7d52e0fe0b40021221a61fa08 + ((0x5c39d1a34ce10c521b40a21e090e3800298b0609ec00054c4709cf64b904e254 + (0x10040f <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g95D7 (_ : Nat) : Nat := (0x4bf55912bf51912fd54512fd50512fb54912fb50912ff51512fe41512fe41112 + ((0x14ff49514fe41514be95904fe55904be55904fe49904fe45904fe49504fe4550 + ((0x524fe41524bf95914ff55914bf55914bf89914ff49914fd54514ef55114ef491 + ((0x9905fe45905bf95924ff55924bf55924bf85924ff45924fb54924ef55124ff45 + ((0x51525bf91915ff51915bf89915ff49915df51515df49515be91905fe51905fe4 + ((0xf49945ff85945bf85945ff45945fe41945bf91925ff51925bf85925ff45925df + ((0x143c3e93a435f31a2d529023d1ea1a516011b0d609804c000ff89945bf89945f + ((0xd699194c8f98d088482a8017bc77e74e7096b668d6415e75be57953b4f64c648 + ((0x10280aebde6ae33dfcda9d72d2dcdacb1c57c2ebf0b9db74b1aaf1ab3a6ea299 + ((0x210942c3060b0e02440548101c204808901a2a4090e1210280a901d285890e12 + ((0x1c2c2070002c88848101c205870124c4250a0e102c38092021204860c161c049 + ((0x3c50a911a282060121e285488d141030092240405490e16103800164c9084a12 + ((0x8f12282060161c345498f14103009121e2a4468a0818048a0f1522345040c024 + ((0x440b0e0249900a101821834548121c242050121e2a4c78a081800090e1a2a4c6 + ((0xa205840e0006132421102149918a1520407870124c2a4090c1e1c04132416183 + ((0x50124e2a4090c182c2070002c991481110a4c8c5490c16103800144e2e4090c1 + ((0x8c18a488450a90202c38092415204840b0e0209110a101821834548121c2420 + ((0x1038001648824088c524422a4070b081c000a2517204460e102c207000309921 + ((0x5898d1e245040c02c4864b111a2820601228325888d141030092515204070816 + ((0x890108810a45285090c1e1c04112012183440b0e024325898f14103000121c32 + ((0x12102c38082296204860c16103800164c8a50a88523942c4860d102c20700030 + ((0x80e102c2070002c9104a1518a43285888c1c205840e0006112021183148250a + ((0x83c08078b10223078816103800164c8c4460d1601c3868b131e24280012412c4 + (0xb10222058100f16204c60d102c2070002c910888d102c038588111 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g95H7 (_ : Nat) : Nat := (0x2b4003a900252000c1cdbcc73811e20400006118006482220c4e16180500000 + ((0xaa638deaf19f5db99f001d38b102000afc795c1a000ac800dc2590034d294cf0 + ((0x37eafa0f5f9b06000b5800d84000002d0000000395d1c4502584993e2d40a7b6 + (0x703339e000f28002c583e765462f <<< 256)) <<< 256)) <<< 256))
def g95D8 (_ : Nat) : Nat := (0x1030a106000be46027108601e09000fea2ff497fa2bf905fe927f453f209fd12 + ((0x51238810074859048c30a106000b4c59040e20a106000b1c5923881007225164 + (0x51230e20a106000a4251448c30a106000b4651440e20a106000b1a <<< 256)) <<< 256))
def g95H8 (_ : Nat) : Nat := 0x88e8c900000dbe7b3c000085
def g95D9 (_ : Nat) : Nat := 0x1483104033f
def g95L : Nat → Packing
  | 5 => (64,4,5,0,0,10,0,g95D5)
  | 6 => (153,3,5,0,0,12,0,g95D6)
  | 7 => (57,2,5,0,0,12,0,g95D7)
  | 8 => (8,1,5,0,0,9,0,g95D8)
  | 9 => (1,0,5,0,0,1,0,g95D9)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 6, h => lookupWord 24 78 6 10 6 0 g95H5 h
  | 7, h => lookupWord 54 184 7 12 8 0 g95H6 h
  | 8, h => lookupWord 26 75 5 10 6 0 g95H7 h
  | 9, h => lookupWord 6 13 2 7 3 0 g95H8 h
  | _, _ => none
def g95 : Forest := ⟨95,9,fun i => g95Y[i]?.getD (0,0),g95C,[[]],g95L,g95I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_0 : block g95 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_5 : block g95 5 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_10 : block g95 5 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_15 : block g95 5 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_20 : block g95 5 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_25 : block g95 5 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_30 : block g95 5 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_35 : block g95 5 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_40 : block g95 5 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_45 : block g95 5 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_50 : block g95 5 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_55 : block g95 5 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P5_60 : block g95 5 60 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B5 : block g95 5 0 64 = true := (@block_merge g95 5 0 40 24 (@block_merge g95 5 0 20 20 (@block_merge g95 5 0 10 10 (@block_merge g95 5 0 5 5 g95P5_0 g95P5_5) (@block_merge g95 5 10 5 5 g95P5_10 g95P5_15)) (@block_merge g95 5 20 10 10 (@block_merge g95 5 20 5 5 g95P5_20 g95P5_25) (@block_merge g95 5 30 5 5 g95P5_30 g95P5_35))) (@block_merge g95 5 40 20 4 (@block_merge g95 5 40 10 10 (@block_merge g95 5 40 5 5 g95P5_40 g95P5_45) (@block_merge g95 5 50 5 5 g95P5_50 g95P5_55)) g95P5_60))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_5 : block g95 6 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_10 : block g95 6 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_15 : block g95 6 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_20 : block g95 6 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_25 : block g95 6 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_30 : block g95 6 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_35 : block g95 6 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_40 : block g95 6 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_45 : block g95 6 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_50 : block g95 6 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_55 : block g95 6 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_60 : block g95 6 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_65 : block g95 6 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_70 : block g95 6 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_75 : block g95 6 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_80 : block g95 6 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_85 : block g95 6 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_90 : block g95 6 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_95 : block g95 6 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_100 : block g95 6 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_105 : block g95 6 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_110 : block g95 6 110 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_115 : block g95 6 115 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_120 : block g95 6 120 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_125 : block g95 6 125 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_130 : block g95 6 130 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_135 : block g95 6 135 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_140 : block g95 6 140 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_145 : block g95 6 145 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_150 : block g95 6 150 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B6 : block g95 6 0 153 = true := (@block_merge g95 6 0 80 73 (@block_merge g95 6 0 40 40 (@block_merge g95 6 0 20 20 (@block_merge g95 6 0 10 10 (@block_merge g95 6 0 5 5 g95P6_0 g95P6_5) (@block_merge g95 6 10 5 5 g95P6_10 g95P6_15)) (@block_merge g95 6 20 10 10 (@block_merge g95 6 20 5 5 g95P6_20 g95P6_25) (@block_merge g95 6 30 5 5 g95P6_30 g95P6_35))) (@block_merge g95 6 40 20 20 (@block_merge g95 6 40 10 10 (@block_merge g95 6 40 5 5 g95P6_40 g95P6_45) (@block_merge g95 6 50 5 5 g95P6_50 g95P6_55)) (@block_merge g95 6 60 10 10 (@block_merge g95 6 60 5 5 g95P6_60 g95P6_65) (@block_merge g95 6 70 5 5 g95P6_70 g95P6_75)))) (@block_merge g95 6 80 40 33 (@block_merge g95 6 80 20 20 (@block_merge g95 6 80 10 10 (@block_merge g95 6 80 5 5 g95P6_80 g95P6_85) (@block_merge g95 6 90 5 5 g95P6_90 g95P6_95)) (@block_merge g95 6 100 10 10 (@block_merge g95 6 100 5 5 g95P6_100 g95P6_105) (@block_merge g95 6 110 5 5 g95P6_110 g95P6_115))) (@block_merge g95 6 120 20 13 (@block_merge g95 6 120 10 10 (@block_merge g95 6 120 5 5 g95P6_120 g95P6_125) (@block_merge g95 6 130 5 5 g95P6_130 g95P6_135)) (@block_merge g95 6 140 10 3 (@block_merge g95 6 140 5 5 g95P6_140 g95P6_145) g95P6_150))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_5 : block g95 7 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_10 : block g95 7 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_15 : block g95 7 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_20 : block g95 7 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_25 : block g95 7 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_30 : block g95 7 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_35 : block g95 7 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_40 : block g95 7 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_45 : block g95 7 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_50 : block g95 7 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_55 : block g95 7 55 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B7 : block g95 7 0 57 = true := (@block_merge g95 7 0 40 17 (@block_merge g95 7 0 20 20 (@block_merge g95 7 0 10 10 (@block_merge g95 7 0 5 5 g95P7_0 g95P7_5) (@block_merge g95 7 10 5 5 g95P7_10 g95P7_15)) (@block_merge g95 7 20 10 10 (@block_merge g95 7 20 5 5 g95P7_20 g95P7_25) (@block_merge g95 7 30 5 5 g95P7_30 g95P7_35))) (@block_merge g95 7 40 10 7 (@block_merge g95 7 40 5 5 g95P7_40 g95P7_45) (@block_merge g95 7 50 5 2 g95P7_50 g95P7_55)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P8_5 : block g95 8 5 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B8 : block g95 8 0 8 = true := (@block_merge g95 8 0 5 3 g95P8_0 g95P8_5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P9_0 : block g95 9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B9 : block g95 9 0 1 = true := g95P9_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g95B5
  · exact g95B6
  · exact g95B7
  · exact g95B8
  · exact g95B9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 10 := lower_forest (g:=g95) (i:=0) (hints:=16843043) (before_sound K111 V111) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K111 10 [(95,[]),(119,[66, 83])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V111 low95 (by decide +kernel)

def g126Y : Array (Bits × Bits) := #[ (0x0,0x0), (0xfaf103d66bbd7ed4f8799fad0a227268ddf51d9720f03652d63b8d523b09c1e8,0x34401114a03291a086410e5088222420da511511015c004240350d123b00c0a0), (0xf135c3636d591613575adf76149133133c39ad98cccbb7a987f112280408f735,0x22004200000040410009004004012150020888884012a890280020804081311), (0x18de7c3db8b3bd4e45a7b9bfe0e1debc430b85237b162bcda8a1e9c1e79a02a3,0xa001a0304484849440812480e2f2054201800bcb040a0782a18000e7880221), (0xf4cabff1a82c943891f9d0cd72d89d1b504da070e168e43591b76ed59212a0a,0x42248088800512182008a520500802504020410024420010830e10021280a), (0x998de074f8fbe4afb7e86ebf589d5ca44a2e71693279d43d30fc1e7116e74490,0x294a0a58cc9b52422128089210110c80004a53143078d420511c08f110274480), (0x25bbb478f5b44ca92937c241bf7e82cae0d3d2e0c5e1419400cce916a0741845,0x4011800002000800001020010408004800000020008001100040400400500044), (0x0,0x0), (0x0,0x0) ]
def g126C : List ColumnInfo := [(32,0,94,0,8), (8,0,118,0,8), (40,0,86,0,7), (16,0,110,0,7), (4,0,122,0,7), (64,0,62,0,6), (2,0,124,0,6), (96,0,30,0,5), (72,0,54,0,5), (48,0,78,0,5), (20,0,106,0,5), (12,0,114,0,5), (36,0,90,0,5), (34,0,92,0,5), (24,0,102,0,5), (18,0,108,0,5), (10,0,116,0,5), (6,0,120,0,5), (104,0,22,0,4), (56,0,70,0,4), (44,0,82,0,4), (42,0,84,0,4), (38,0,88,0,4), (26,0,100,0,4), (22,0,104,0,4), (80,0,46,0,4), (68,0,58,0,4)]
def g126D4 (_ : Nat) : Nat := (0x1129c31caf0a8a68896e0825385453444ae0a733aaa29a2257065958d514d112 + ((0x64d1129c2c4a27ab268894e1865385593444b30cf089aac9a225385399e1514d + ((0x5d134d112b4334aae89a68894e14666854d3444ae0cb28baa69a225b05184d75 + (0x19810066040006604000660401981000e1aad549cf9c3244706060138589d <<< 256)) <<< 256)) <<< 256))
def g126H4 (_ : Nat) : Nat := 0x648035cac0992a0071ee7bb32400684d106e
def g126D5 (_ : Nat) : Nat := (0x4be158d514d112ae568d5d21c06f84235748701be20855d21c06e99215748701 + ((0x112b85385453444bc99d5514d112f25755453444be14d5514d112f0535545344 + ((0x3444ba34d9564d112f85135593444ae99e1514d112ba5785453444be14e1514d + ((0x64d112f0d35d593444be144f564d1129ae785593444ae34e1564d112f0d35559 + ((0x44d3444ae39a1534d112f851854d3444be145d534d112b8d38d593444ae94635 + ((0x63574d112aae6855d3444b6945d574d112b8e5858d3444be1d5d134d112f8557 + ((0xe4859d0544a738e16741512f61604550544ae9961174d112b8d38d5d3444ae94 + ((0xd144d654d512f45634553544a6b92167815129e51899d0544a7986167415129a + ((0x29ea0859d3544b78821174d512b65189953544bd144e654d512e4d365953544b + ((0x44ae9921564c5129ae4859e3544a79462674d5129e61859d3544a6b921674d51 + ((0x4512b66584d95144ad996106545129e578d593144af14e3564c512bc63855931 + ((0xd43c0ee64235750f03b9a0855d43c0ee38a15750f039ad3891d5644af8821375 + ((0x5750d13b8e2855d4344fa68215650d13f16755454344fc55d55150d13a9d68d5 + ((0x859d054d26d8616741534f19604d5054d2a75a35750d13b9518d5d4344ee5861 + ((0x4596545534f15614d5154d26b8a1678153499d3899d054d2678e167415349ae2 + ((0x9d3899d154d2678e167455349ae2859d154d26e8216745534b1d38995154d38d + ((0x26b4622755934b9a0845d534d2c79611654d34b1e58419534d26b8a167855349 + ((0x5c5593e4992046914414ff39ccf324ba2d09c21063174450d830060120300600 + ((0xb9564f9023a8d22e87e1984e0d7f9ef7a5da751ce721b06859b6558f6257a5ad + ((0xce72ac9315c3f09c0eebb72d6b42caaeeb5a9aa0a6a94a3a88a0a7c9da679865 + ((0x2882820c028cc1804b1384a30400712c2000000dfb78dcb6cd9b57d474bd173f + ((0xe0488092c1005e0a081829080000118201984010a49010029040331042 + ((0x4c08000000981000004c08000023044a0800104000012c10206020 + (0x4c08000000025040000200000960611181000008c080440400 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g126H5 (_ : Nat) : Nat := (0xa05d9239a3ee01c6eaa02414c00dec100909100700b2c30033082c01981010c0 + ((0x458ab711070eda54767e32d8344568954012694235a5ba6922daa49e4a9d4a2f + ((0x1c9824d158263bbe5d6329840f0174a0000d1c4b446ccbadb1c00359f1ed8530 + ((0xc000191a89383d7400000000c388bcdb000001d2815800ea5ca400000978d395 + ((0x192003c1507513ef800090d404d41659333b8280073d000121d0f04000001679 + (0xc71f4f8299b <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g126D6 : Nat → Nat
  | 0 => (0xd21c0772ab24380fe15048701dec2eab203fc85d50407f882aa280f710554501 + ((0x9785134d112f1aa69a225ebd593444bd6ab268897a5514d112fceae90e03f955 + ((0x2a82a25d94550544bd6b3a68897a5174d112f5eae9a225eb55d3444bc6b1a688 + ((0x44bb28ac0a895ee6741512bdace82a25f985d0544af30ba0a897e96041512fca + ((0x5134d512edcca9aa25db5953544bf28aa6a89765154d512bdacf02a257945e05 + ((0xaa25d94563544af733a6a895ed674d512fca2e9aa257945d3544be6b1a6a897c + ((0xf29b2a2897e50654512fceac98a25f95593144af6b3c6a895e5178d512edacb1 + ((0x4d912ddaac9b2257b95d0644b76ab20c895e63754512fca6ea8a25f941d5144b + ((0x57b4df5644af683eac897ae4755912b5c8eab2257b8dd5644af703aac895ee57 + ((0xb28781f995050f03dbc6eab207f68dd5040fec82aa681f590554d03bca2fab22 + ((0x13f3eaea1a27e755d4344f4eab28689f955150d13f3eaea1e07e755d43c0f4ea + ((0x581054d3ce9aa0a9a71d3541534df40eab2273e81d5644fea8aaa689f551554d + ((0xa9a59d3781534e3a6b02a696f99d054d2deb3a0a9a79e3741534b3c6e82a69ee + ((0x3a6e8aa69ed585154d39f32a2a9a73d6545534f3a6a8aa69c74d5154d2deb3c0 + ((0x534d2deb3c2a9a59d3785534e7acb0aa69c74d6154d2df33a2a9a5bd6745534f + ((0x5be5741934d7aac832696785d534d3ce8baa69a79d0754d34f3a2ca9a69e7419 + ((0xfab269eb89d564d2d713aac9a5be1755934b7c0eab2696f95d164d35eab22c9a + ((0x576fb1a6a82f5f634d505deec28aa0bddd8515416ce9beac9a5bd17d5934b7a0 + ((0x43c1c00bd05b029c10807d035014c078035017008c000bf40e8b26b7e81d364 + ((0xabc52829114309cc4a8249119085c4282090fd076c3981bd0cb060c2a814d09f + ((0x9c7b83d51e50eec73838d1c10dcc6c03591a30cec63831517d0bdc5d82d915d0 + ((0xca5852528913cc9b04d125f129c92048924111dc8a842d213107c8284011f90f + ((0xd3868933f19ecce065931d18bcc305fd2fd17bcbc05c12d9168caf85752b1154 + ((0x807b93d71e6cf187813bb1dbcec875539b1c9ce3870d37d1bbcd986c53551a9c + ((0x93c2d1b8050004181050408604418161013878088094031ffcff07f13f51f1cf + ((0xc423c120208c12948230c61452d99128d068084604211a058044f084604e0146 + ((0x52c9d103182f0e4b2966c42382c1202c60bd2c28a599108e0b0680b182f2966 + ((0x32625040c6860442c9895101380914132982106144312ca599128e090680b44 + ((0x20086094100780518110b2625e01802320089910103181126440401e01c40961 + ((0x289a8c078070e2508602c28108f80600208c21a2504a31068602c94128f80708 + ((0x8d804082008609894128c078070804602c28968f80600988021a2f0a04106860 + (0x10225c4600c68602c98118f8071a110a0c449820e0b250c402c9894423042c20 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0xb262504c101e020248c104062080288c4c16010208c80308040838102230440 + ((0x1d198600451074603e1146544251b8450004181050308603c18160c0f878081a + ((0x281510120c0f878094404241d1184419180a46c4e1001c602825100f8464604 + ((0x3e1001c34960c32625030c64603c2498950c0f8490607130f878040504030c6 + ((0x2496900f84707210860940f84005180f092625e1180242108990c0c3180f2643 + ((0x807046028249693846009884219310a031030942001c9021925a44303146460 + ((0x602499900f847190f0a0c3c9820c09250c342498944072108609896910c0f840 + ((0x200c103061c84287c361c0101c0c843070308300c22404340c225c3610c64 + (0x414100041411909262503e1c <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g126H6 (_ : Nat) : Nat := (0x90000300300c000a00dd161a70085121c18220043800c1850854240180014107 + ((0x48c79aab3776d906ab340677ca4c94f0aa71c54d40008e6b380043002030b800 + ((0xc77999391e6b1495dab694040d7227f8d43b4288e3698800e87ab6c7b52388b0 + ((0x19769b1dcda663000a2c0000000000000792a5e8a800188375ef817000ab5c4 + ((0x844c347ca0f7535a00263ce24cc597016b200066c000000000000067000174c0 + ((0x4626004466025707b8e93cf3a6516d000480001b7799490000000001b0a19 + ((0x15ac52d102a2b592be4fe4e000f742ccd2191230bcd9617a4b25cd840001e800 + (0xcb2030e2b09a22e1d50b067e86886921dec <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g126D7 (_ : Nat) : Nat := (0x2fb81512fb41512eb4d112bf55b01fe54301f948701bf55901fe54101fd54501 + ((0x3f754d03fbd5912fb55912fb4d912fb41912f954512f94c512fb8d512fb4d51 + ((0x534bf55913fd54513f754d13e750d13bf55b03fe54303e750f03bf55903fe541 + ((0x5805efd5934ef55934ef45934ef41934e754d34ef85534ef45534ef81534ef41 + ((0x8d505ff4d505df4d505df85505ff45505df45505af51805b74d805bb49805bd4 + ((0xf45a05df4d605df45605ff8d905bf8d905ff4d905ff85905bf85905ff45905df + ((0xbf8d915ff4d915bf81915ff41915df8d515ff4d515df4d515bf41a05bf4da05b + ((0xbf45a35bf41a35bf85935ff45935bf81935ff41935bf4da15bf41a15df4d615 + ((0x2af14809c44a422f903077236618d0b1c4e82210e7062427a0ff06081f007c00 + ((0x8eab7d534a5c50f276530c93347022350747e73ca1d04df86b7335987cbc25a3 + ((0x93e6de9eefc7583991c4cde86e335cdaa2d2f66e32e98f8c536072f4174eb625 + ((0x1c041a30443050987011337975ca624d120e8f9c6822a910f85e42320650177e + ((0x28d0f0c16204c38089e2e304c6840e020d1823101e10380012608860b1026 + ((0x20447070202cc1116992c4088e0e040598a2be5a9888e0a0247860b10203c207 + ((0x526088e081c05185e2d32588111c1c080b30bc5a64b1022383810166088b4c96 + ((0x70b4c9622383810166089016992c447070202cd18222d325098e081c05985e2c + ((0x182c3078701064c0f0c141e1c040b4c9622383810102c4264b111c1c080930bc + ((0x860f081c000a3244305860f0e0228898d901e140008326078487840e0004981e + ((0x2cd181414243078701264c0a0b10203c3809303c5098d101e14000a2218284 + ((0xa1805981e25325490c1e14300b303c4a64a92183c28601668c98141a243c2070 + ((0xe14300b32607894c97203c300016618894c9524307850c02cc3112992a4860f0 + ((0x25490f0a1804090e992a487850c024c311825325490f0a1805981e344a64a921 + ((0xc305c98f0a02488f0c17223c3808223c4060b931a1c04911e182a4c787010253 + ((0x2607860a8c1e1c049822182a40987010683054810534608860a90261c04911e1 + ((0x30548104304430548101e10380016688a4082181e182a3078701064305460c53 + ((0xa8c1e1c041822182a40987010182a3062181e18284460f081c000b323d18310 + ((0x223c305080f081c08001660785088c1e103800146088548101e1038001460786 + ((0x40e00061a2218330282c4088c1e1c049a3216204460c73464c058811183c380a + ((0x5058811183c38093460344088c1e1038001668c91148c18c68c110b10263078 + ((0xb9024307840e0006191e18330182c4088c1e103800166088588101e103800146 + ((0x1c000b303c284860f081c000a3260324090c1e1038001668c8f149020c64c0f0 + (0x180c15204860f08 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g126H7 (_ : Nat) : Nat := (0xa71e10800000e50ce70a1484241070e0c180000408f222c0800000004062c001 + ((0x18002028000342eb5ea99b86aace271c78e275810bc000001df800f4600117c0 + ((0x8b64979b26fc57d77b60009038440ee2cceec86332638d214e4894f4f8003a63 + ((0xfc3c93c606c8005aa782003427acd310275260bb3e316006213450180050d68c + (0xb40406d2f38e3da5dc880036b40 <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g126D8 (_ : Nat) : Nat := (0x7f8d7fa6bfe15fe8affc17fc0bfd05fe02ef4d3fa27ff03fe81fb44bfe03fd01 + ((0x8300053089e30a2461c20c0019f5739aa60d5c4c908384c9294841804809c00 + ((0x70830005a230b2081c20c0014c1e30b2081c20c0016c2258918300e78c289187 + ((0x1ac2278c2c82461c20c001a89e30b2091870830006307932070803b079430a20 + ((0xc0016d3088c28918708300062278c2c82461c20c0018c2278c2c82461c20c00 + (0x3078c2c82070830005b2c1e30b2081c20c0018c2230a2461c2 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g126H8 (_ : Nat) : Nat := 0x9e98875de6dc0095fa9400d300e20000394b11a76100
def g126D9 (_ : Nat) : Nat := 0x4184023f
def g126L : Nat → Packing
  | 4 => (13,5,5,0,0,7,0,g126D4)
  | 5 => (87,4,5,0,0,10,0,g126D5)
  | 6 => (120,3,5,0,0,13,0,g126D6)
  | 7 => (73,2,5,0,0,13,0,g126D7)
  | 8 => (15,1,5,0,0,10,0,g126D8)
  | 9 => (1,0,5,0,0,1,0,g126D9)
  | _ => emptyPacking
def g126I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 5 16 3 8 4 0 g126H4 h
  | 6, h => lookupWord 30 104 6 11 7 0 g126H5 h
  | 7, h => lookupWord 45 147 7 11 7 0 g126H6 h
  | 8, h => lookupWord 25 87 7 11 7 0 g126H7 h
  | 9, h => lookupWord 6 19 4 8 4 0 g126H8 h
  | _, _ => none
def g126 : Forest := ⟨126,9,fun i => g126Y[i]?.getD (0,0),g126C,[[]],g126L,g126I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P4_0 : block g126 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P4_5 : block g126 4 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P4_10 : block g126 4 10 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126B4 : block g126 4 0 13 = true := (@block_merge g126 4 0 10 3 (@block_merge g126 4 0 5 5 g126P4_0 g126P4_5) g126P4_10)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_0 : block g126 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_5 : block g126 5 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_10 : block g126 5 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_15 : block g126 5 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_20 : block g126 5 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_25 : block g126 5 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_30 : block g126 5 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_35 : block g126 5 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_40 : block g126 5 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_45 : block g126 5 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_50 : block g126 5 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_55 : block g126 5 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_60 : block g126 5 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_65 : block g126 5 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_70 : block g126 5 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_75 : block g126 5 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_80 : block g126 5 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P5_85 : block g126 5 85 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126B5 : block g126 5 0 87 = true := (@block_merge g126 5 0 80 7 (@block_merge g126 5 0 40 40 (@block_merge g126 5 0 20 20 (@block_merge g126 5 0 10 10 (@block_merge g126 5 0 5 5 g126P5_0 g126P5_5) (@block_merge g126 5 10 5 5 g126P5_10 g126P5_15)) (@block_merge g126 5 20 10 10 (@block_merge g126 5 20 5 5 g126P5_20 g126P5_25) (@block_merge g126 5 30 5 5 g126P5_30 g126P5_35))) (@block_merge g126 5 40 20 20 (@block_merge g126 5 40 10 10 (@block_merge g126 5 40 5 5 g126P5_40 g126P5_45) (@block_merge g126 5 50 5 5 g126P5_50 g126P5_55)) (@block_merge g126 5 60 10 10 (@block_merge g126 5 60 5 5 g126P5_60 g126P5_65) (@block_merge g126 5 70 5 5 g126P5_70 g126P5_75)))) (@block_merge g126 5 80 5 2 g126P5_80 g126P5_85))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_0 : block g126 6 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_5 : block g126 6 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_10 : block g126 6 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_15 : block g126 6 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_20 : block g126 6 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_25 : block g126 6 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_30 : block g126 6 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_35 : block g126 6 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_40 : block g126 6 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_45 : block g126 6 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_50 : block g126 6 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_55 : block g126 6 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_60 : block g126 6 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_65 : block g126 6 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_70 : block g126 6 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_75 : block g126 6 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_80 : block g126 6 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_85 : block g126 6 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_90 : block g126 6 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_95 : block g126 6 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_100 : block g126 6 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_105 : block g126 6 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_110 : block g126 6 110 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P6_115 : block g126 6 115 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126B6 : block g126 6 0 120 = true := (@block_merge g126 6 0 80 40 (@block_merge g126 6 0 40 40 (@block_merge g126 6 0 20 20 (@block_merge g126 6 0 10 10 (@block_merge g126 6 0 5 5 g126P6_0 g126P6_5) (@block_merge g126 6 10 5 5 g126P6_10 g126P6_15)) (@block_merge g126 6 20 10 10 (@block_merge g126 6 20 5 5 g126P6_20 g126P6_25) (@block_merge g126 6 30 5 5 g126P6_30 g126P6_35))) (@block_merge g126 6 40 20 20 (@block_merge g126 6 40 10 10 (@block_merge g126 6 40 5 5 g126P6_40 g126P6_45) (@block_merge g126 6 50 5 5 g126P6_50 g126P6_55)) (@block_merge g126 6 60 10 10 (@block_merge g126 6 60 5 5 g126P6_60 g126P6_65) (@block_merge g126 6 70 5 5 g126P6_70 g126P6_75)))) (@block_merge g126 6 80 20 20 (@block_merge g126 6 80 10 10 (@block_merge g126 6 80 5 5 g126P6_80 g126P6_85) (@block_merge g126 6 90 5 5 g126P6_90 g126P6_95)) (@block_merge g126 6 100 10 10 (@block_merge g126 6 100 5 5 g126P6_100 g126P6_105) (@block_merge g126 6 110 5 5 g126P6_110 g126P6_115))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_0 : block g126 7 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_5 : block g126 7 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_10 : block g126 7 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_15 : block g126 7 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_20 : block g126 7 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_25 : block g126 7 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_30 : block g126 7 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_35 : block g126 7 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_40 : block g126 7 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_45 : block g126 7 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_50 : block g126 7 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_55 : block g126 7 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_60 : block g126 7 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_65 : block g126 7 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_70 : block g126 7 70 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126B7 : block g126 7 0 73 = true := (@block_merge g126 7 0 40 33 (@block_merge g126 7 0 20 20 (@block_merge g126 7 0 10 10 (@block_merge g126 7 0 5 5 g126P7_0 g126P7_5) (@block_merge g126 7 10 5 5 g126P7_10 g126P7_15)) (@block_merge g126 7 20 10 10 (@block_merge g126 7 20 5 5 g126P7_20 g126P7_25) (@block_merge g126 7 30 5 5 g126P7_30 g126P7_35))) (@block_merge g126 7 40 20 13 (@block_merge g126 7 40 10 10 (@block_merge g126 7 40 5 5 g126P7_40 g126P7_45) (@block_merge g126 7 50 5 5 g126P7_50 g126P7_55)) (@block_merge g126 7 60 10 3 (@block_merge g126 7 60 5 5 g126P7_60 g126P7_65) g126P7_70)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P8_0 : block g126 8 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P8_5 : block g126 8 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P8_10 : block g126 8 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126B8 : block g126 8 0 15 = true := (@block_merge g126 8 0 10 5 (@block_merge g126 8 0 5 5 g126P8_0 g126P8_5) g126P8_10)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P9_0 : block g126 9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126B9 : block g126 9 0 1 = true := g126P9_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g126B4
  · exact g126B5
  · exact g126B6
  · exact g126B7
  · exact g126B8
  · exact g126B9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 10 := lower_forest (g:=g126) (i:=0) (hints:=18956576) (before_sound K95 V95) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K95 10 [(126,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V95 low126 (by decide +kernel)

def g127Y : Array (Bits × Bits) := #[ (0x5d1b5a87147a1ae0a256d788b6bd1b1529539872078d4fded98959c2c105a28d,0x5503c00408e699400015c0e896ad001029118a62c3814184d98949c24101a288), (0xab96106ea2d18cc634b7fac7f50048b0b26f818c0702fa998127570262584761,0x881410641000844238b172c3370048302248458400402a108023570022100761), (0xbe102015a7055196015f0131d1d032cd3d0df35500a369259218a2b1e1412852,0x12002001810c718001020130800010c1100490501823010110188031c0412002), (0x96fd7930d87970aa3820e5099164bf5ad2d81c1258fd10832849103882a295e2,0x8294112091196480210024000100324080481410186800032000103082201462), (0x24e49be18d822c6944080afa61ff00fa6db0b0e0a629c4c85f64a0640b3a020c,0x24604e000c800021840008084054000a05a020208410c4c80f442040090a000c), (0xc32e274c60065233bf8074906e179c2dc6a6482b34702f2420c62b411c950137,0x680400200000229e0018006012c82c4402408d04100c00004622000c940115), (0x112084ba4020cb4556f8b00e0cabe16205492f79e98295744492449e1c00fc08,0x4101809a40000a040048800000a1010000010a00608010244080008e1000c800), (0x0,0x0), (0x0,0x0) ]
def g127C : List ColumnInfo := [(16,0,111,0,10), (4,0,123,0,10), (32,0,95,0,10), (8,0,119,0,10), (1,0,126,0,10), (64,0,63,0,9), (2,0,125,0,9), (33,0,94,0,8), (9,0,118,0,8), (41,0,86,0,7), (36,0,91,0,7), (34,0,93,0,7), (24,0,103,0,7), (20,0,107,0,7), (10,0,117,0,7), (96,0,31,0,7), (80,0,47,0,7), (72,0,55,0,7), (68,0,59,0,7), (48,0,79,0,7), (12,0,115,0,7), (18,0,109,0,7), (17,0,110,0,7), (6,0,121,0,7), (5,0,122,0,7), (66,0,61,0,6), (65,0,62,0,6), (3,0,124,0,6), (97,0,30,0,5), (82,0,45,0,5), (73,0,54,0,5), (70,0,57,0,5), (49,0,78,0,5), (38,0,89,0,5), (26,0,101,0,5), (21,0,106,0,5), (13,0,114,0,5), (37,0,90,0,5), (35,0,92,0,5), (25,0,102,0,5), (22,0,105,0,5), (19,0,108,0,5), (11,0,116,0,5), (7,0,120,0,5), (105,0,22,0,4), (86,0,41,0,4), (57,0,70,0,4), (45,0,82,0,4), (43,0,84,0,4), (39,0,88,0,4), (27,0,100,0,4), (23,0,104,0,4), (100,0,27,0,4), (98,0,29,0,4), (88,0,39,0,4), (81,0,46,0,4), (74,0,53,0,4), (69,0,58,0,4), (52,0,75,0,4), (50,0,77,0,4), (28,0,99,0,4), (14,0,113,0,4)]
def g127D8 (_ : Nat) : Nat := 0x3546c221387c2e0f01804028354642e1009c3e170780402b000efa6845d06afa6845d06
def g127H8 (_ : Nat) : Nat := 0x11b02
def g127D9 (_ : Nat) : Nat := 0x1a4685058404c343c242c141c04038691a16130d0f090b05070100ccc03fd0ba0dfe45d06
def g127H9 (_ : Nat) : Nat := 0xd060
def g127D10 (_ : Nat) : Nat := 0x182c4090c1c205040c0006460a121c283007dc0ff45bf906
def g127H10 (_ : Nat) : Nat := 0x1ca80
def g127D11 (_ : Nat) : Nat := 0x1851030810077f
def g127L : Nat → Packing
  | 8 => (2,3,6,0,0,7,0,g127D8)
  | 9 => (2,2,6,0,0,7,0,g127D9)
  | 10 => (2,1,6,0,0,6,0,g127D10)
  | 11 => (1,0,6,0,0,1,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 9, h => lookupWord 2 3 1 5 1 0 g127H8 h
  | 10, h => lookupWord 2 3 1 5 1 0 g127H9 h
  | 11, h => lookupWord 2 3 1 5 1 0 g127H10 h
  | _, _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,[[]],g127L,g127I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127B8 : block g127 8 0 2 = true := g127P8_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127B9 : block g127 9 0 2 = true := g127P9_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127B10 : block g127 10 0 2 = true := g127P10_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P11_0 : block g127 11 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127B11 : block g127 11 0 1 = true := g127P11_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g127B8
  · exact g127B9
  · exact g127B10
  · exact g127B11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=16843043) (before_sound K126 V126) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
end PEqualNP.Outside.L_meta_34206.Certificate30704

namespace PEqualNP.Outside.L_meta_34206
/- Restriction and projection lemmas adapted from Max Guillabert, project PR 42591. -/

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


private theorem signed_av {s : Set F} (point : Certificate30704.Row → X)
    {bank : List (Certificate30704.Wire Certificate30704.Row)}
    (hs : ∀ v ∈ s, Certificate30704.Available true bank (fun r => v (point r)))
    {f : F} (h : Av s f) :
    Certificate30704.Available true bank (fun r => f (point r)) := by
  rcases h with ⟨b,rfl⟩ | ⟨a,ha,rfl | rfl⟩
  · exact Or.inr (Or.inl ⟨b,rfl⟩)
  · exact hs _ ha
  · exact Certificate30704.avail_inv rfl (hs _ ha)

private theorem signed_prog {s : Set F} {f : F} {k : Nat} (p : Prog s f k)
    (point : Certificate30704.Row → X) (roots : List (Certificate30704.Wire Certificate30704.Row)) :
    ∀ m bank, Certificate30704.Reach true roots m bank →
      (∀ v ∈ s, Certificate30704.Available true bank (fun r => v (point r))) →
      ∃ pool, Certificate30704.Reach true roots (m+k) pool ∧
        Certificate30704.Available true pool (fun r => f (point r)) := by
  induction p with
  | done h => intro m bank hm hs; exact ⟨bank,hm,signed_av point hs h⟩
  | @gate s f a b k tag ha hb tail ih =>
    intro m bank hm hs
    let a' := fun r => a (point r)
    let b' := fun r => b (point r)
    let w := Certificate30704.combine (!tag) a' b'
    have hl : (fun r => comb tag a b (point r)) = w := by
      cases tag <;> rfl
    have hr : Certificate30704.Reach true roots (m+1) (w :: bank) :=
      Certificate30704.Reach.two (!tag) hm (signed_av point hs ha) (signed_av point hs hb)
    obtain ⟨pool,hp,hv⟩ := ih (m+1) (w :: bank) hr (by
      intro v h
      rcases Set.mem_insert_iff.mp h with rfl | h
      · rw [hl]
        exact Or.inl (List.mem_cons_self)
      · exact Certificate30704.available_cons w (hs _ h))
    exact ⟨pool,by simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hp,hv⟩

private theorem from_signed_L_meta_30704 {f : F} {L : Nat}
    {roots : List Certificate30704.Sig} {targetWord : Certificate30704.Sig}
    (cols : Fin 8 → Certificate30704.Sig)
    (hcols : ∀ i, cols i ∈ roots ∨ cols i = Certificate30704.zero)
    (he : ∀ r : Certificate30704.Row, Certificate30704.bit r targetWord =
      f (fun i => Certificate30704.bit r (cols i)))
    (h : Certificate30704.Lower true roots targetWord L) : Low L f := by
  intro k p
  let point := fun r i => Certificate30704.bit r (cols i)
  obtain ⟨pool,hp,hv⟩ := signed_prog p point (roots.map Certificate30704.observe) 0
    (roots.map Certificate30704.observe) Certificate30704.Reach.start (by
      rintro _ ⟨i,rfl⟩
      rcases hcols i with hmem | hz
      · exact Or.inl (List.mem_map.mpr ⟨cols i,hmem,rfl⟩)
      · apply Or.inr; apply Or.inl
        exact ⟨false,by funext r; change Certificate30704.bit r (cols i) = false
                        rw [hz]; simp [Certificate30704.bit,Certificate30704.zero]⟩)
  have eq : Certificate30704.observe targetWord = fun r => f (point r) := funext he
  rw [← eq] at hv
  exact h k pool (by simpa using hp) hv


def target : F := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem lower : Low 13 target := (one 2 false (good_at 32 9 0 (by decide +kernel)) (from_signed_L_meta_30704 (f := (rs 2 false target)) ![(Certificate30704.inputs.getD 6 Certificate30704.zero), (Certificate30704.inputs.getD 0 Certificate30704.zero), Certificate30704.zero, (Certificate30704.inputs.getD 1 Certificate30704.zero), (Certificate30704.inputs.getD 3 Certificate30704.zero), (Certificate30704.inputs.getD 2 Certificate30704.zero), (Certificate30704.inputs.getD 5 Certificate30704.zero), (Certificate30704.inputs.getD 4 Certificate30704.zero)] (by decide +kernel) (by decide +kernel) Certificate30704.low127))

def witness : List Gate := [⟨.or, [7, 5]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [2, 0]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [3, 12]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [1, 19]⟩, ⟨.or, [18, 20]⟩]

theorem witness_ok : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : X, Circuit.eval ⟨witness, 21⟩ (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem target_eq : ∀ x : X, target x = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_34206

open PEqualNP.Outside.L_meta_34206 in
theorem PEqualNP.Outside.L_meta_34206 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hg _ he
  by_cases hs : 14 ≤ gates.length
  · exact ⟨witness, 21, witness_ok, hs, fun x => (witness_eval x).trans (target_eq x)⟩
  · exact ⟨gates, o, all_not_not_of_guillabert_pr42591 lower gates o hg (by omega)
      (fun x => (he x).trans (target_eq x).symm), le_rfl, he⟩
