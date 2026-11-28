import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30282

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
  (x 0 &&& x 1) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) ||| (x 4 &&& x 5) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)

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
  (x 0 &&& x 1) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) ||| (x 4 &&& x 5) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)

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

def g28Y : Array (Bits × Bits) := #[ (0x0,0x0), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ef5,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8091), (0xbf9e,0x480c), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffebeb,0x1222), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g28C : List ColumnInfo := []
def g28D3 (_ : Nat) : Nat := 0x7
def g28L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,g28D3)
  | _ => emptyPacking
def g28I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g28 : Forest := ⟨28,3,fun i => g28Y[i]?.getD (0,0),g28C,[[]],g28L,g28I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g28P3_0 : block g28 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g28B3 : block g28 3 0 1 = true := g28P3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g28T : checkedTables g28 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g28B3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g28G : graphValid g28 (boundsBefore K0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low28 : Lower true (varsX 28) (graphGoal 28) 4 := lower_forest (g:=g28) (i:=0) (hints:=140032) (before_sound K0 V0) g28G g28T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K28 := extendKnown K0 4 [(28,[]),(44,[84]),(52,[83, 84]),(56,[82, 83, 84]),(67,[32, 49, 84, 101]),(112,[82, 99, 84, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V28 : Known true K28 := extend_ok (m:=28) V0 low28 (by decide +kernel)

def g85Y : Array (Bits × Bits) := #[ (0xffffffffffffffffffffffffffffffffffffffffffffffff3e1b6fd7dfc313e5,0xffffffffffffffffffffffffffffffffffffffffffffffffc1858495c0c4c361), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffff775fd51a7cfe8877,0x893042e0cc370874), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffedfedfb97f7cee3b,0xffffffffffffffffffffffffffffffffffffffffffffffff1001a1141108c20b), (0x0,0x0), (0xdfb3bfffc79b7fcc,0x2042422a06210c84), (0x0,0x0), (0x0,0x0) ]
def g85C : List ColumnInfo := []
def g85D3 (_ : Nat) : Nat := 0xf
def g85L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,g85D3)
  | _ => emptyPacking
def g85I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g85 : Forest := ⟨85,3,fun i => g85Y[i]?.getD (0,0),g85C,[[]],g85L,g85I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g85P3_0 : block g85 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g85B3 : block g85 3 0 1 = true := g85P3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g85T : checkedTables g85 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g85B3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g85G : graphValid g85 (boundsBefore K28) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low85 : Lower true (varsX 85) (graphGoal 85) 4 := lower_forest (g:=g85) (i:=0) (hints:=132102) (before_sound K28 V28) g85G g85T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K85 := extendKnown K28 4 [(85,[]),(86,[16]),(89,[50]),(90,[16, 50]),(101,[84]),(102,[16, 84]),(105,[50, 84]),(106,[16, 50, 84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V85 : Known true K85 := extend_ok (m:=85) V28 low85 (by decide +kernel)

def g83Y : Array (Bits × Bits) := #[ (0xffffffffffffffffffffffffffffffffffffffffffffffffded9dbb4f7f9993d,0x213680042b090924), (0xffffffffffffffffffffffffffffffffffffffffffffffffbd979fdfc5ebcaf1,0xffffffffffffffffffffffffffffffffffffffffffffffffc240628884a44291), (0x0,0x0), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffae7a359ab9c73d83,0xffffffffffffffffffffffffffffffffffffffffffffffffd1c292660ec55983), (0x0,0x0), (0x777efefb7abf77ce,0x801001050020448), (0x0,0x0), (0x0,0x0) ]
def g83C : List ColumnInfo := [(16,0,67,0,4)]
def g83D4 (_ : Nat) : Nat := 0x2f
def g83L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g83D4)
  | _ => emptyPacking
def g83I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g83 : Forest := ⟨83,4,fun i => g83Y[i]?.getD (0,0),g83C,[[]],g83L,g83I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g83P4_0 : block g83 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g83B4 : block g83 4 0 1 = true := g83P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g83T : checkedTables g83 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g83B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g83G : graphValid g83 (boundsBefore K85) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low83 : Lower true (varsX 83) (graphGoal 83) 5 := lower_forest (g:=g83) (i:=0) (hints:=393217) (before_sound K85 V85) g83G g83T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K83 := extendKnown K85 5 [(83,[]),(92,[32, 49, 100]),(99,[84]),(108,[32, 49, 84, 101]),(113,[64, 33, 50, 83]),(114,[32, 65, 50, 83, 84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V83 : Known true K83 := extend_ok (m:=83) V85 low83 (by decide +kernel)

def g116Y : Array (Bits × Bits) := #[ (0x0,0x0), (0x0,0x0), (0xfffffffffffffffffffffffffffffffffffffffffffffffffb7ba4e5bfa4e85d,0xfffffffffffffffffffffffffffffffffffffffffffffffff4804ab00186f055), (0x0,0x0), (0xfffffffffffffffffffffffffffffffffffffffffffffffff7d79eff6df74799,0x800a10160000488), (0xeedefaef6dcbd66,0x103100014100920), (0x9ddd73152fb72f2,0x62006c803e29252), (0x0,0x0), (0x0,0x0) ]
def g116C : List ColumnInfo := [(64,0,52,0,4), (4,0,112,0,4)]
def g116D4 (_ : Nat) : Nat := 0x2f
def g116L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g116D4)
  | _ => emptyPacking
def g116I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g116 : Forest := ⟨116,4,fun i => g116Y[i]?.getD (0,0),g116C,[[]],g116L,g116I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g116P4_0 : block g116 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g116B4 : block g116 4 0 1 = true := g116P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g116T : checkedTables g116 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g116B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g116G : graphValid g116 (boundsBefore K83) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low116 : Lower true (varsX 116) (graphGoal 116) 5 := lower_forest (g:=g116) (i:=0) (hints:=69338112) (before_sound K83 V83) g116G g116T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K116 := extendKnown K83 5 [(116,[]),(120,[50])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V116 : Known true K116 := extend_ok (m:=116) V83 low116 (by decide +kernel)

def g60Y : Array (Bits × Bits) := #[ (0x0,0x0), (0x0,0x0), (0x77aad7567bd1ea,0x81501040280e0), (0xffffffffffffffffffffffffffffffffffffffffffffffffffedd97f3fee0b91,0x102004d1200310), (0x3f05bfd99fbe4c,0x40c21000980c08), (0xfffffffffffffffffffffffffffffffffffffffffffffffffffa7e37adf0f437,0xffffffffffffffffffffffffffffffffffffffffffffffffff8400ca08401007), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g60C : List ColumnInfo := [(32,0,28,0,4), (16,0,44,0,4), (8,0,52,0,4), (4,0,56,0,4)]
def g60D3 (_ : Nat) : Nat := 0x20080080200010021042a509e2c4c808009d02a68897144d3244a6c2a9a205c9034c9029712a6880c78d524407a20698a03e10248501
def g60H3 (_ : Nat) : Nat := 0xec0240057922f23fa46
def g60D4 (_ : Nat) : Nat := (0xd3240bb44902be34406f4d101be24406f49101f930407e48101f531407d48501 + ((0x1340ef8d112bd3444af81112f53144bb4c912be3440af4d102be1440be4c102e + ((0x8150701c00be1448ef81123be2444ef81113dd2344ef89103be1440f748d03dd + ((0x88423008c42894320d00793b1ccd86531174b4532612488411d0cc5829120843 + (0x2108000c4232080304010088020081004023008c8200410001200 <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g60H4 (_ : Nat) : Nat := 0x400f3f98035600001e7b91683b5e001c5540109442c599d775c9436c3880cad420ca6e988000045e100400184c4
def g60D5 (_ : Nat) : Nat := 0x68811a20468811a20468811a204b521b242403e91fd13fa07f44be817d01
def g60H5 (_ : Nat) : Nat := 0x28f01476e33000004
def g60D6 (_ : Nat) : Nat := 0x7208f
def g60L : Nat → Packing
  | 3 => (8,3,2,0,0,7,0,g60D3)
  | 4 => (28,2,2,0,0,9,0,g60D4)
  | 5 => (6,1,2,0,0,7,0,g60D5)
  | 6 => (1,0,2,0,0,1,0,g60D6)
  | _ => emptyPacking
def g60I : Nat → Nat → Option (Nat × Nat)
  | 4, h => lookupWord 3 10 2 7 3 0 g60H3 h
  | 5, h => lookupWord 11 35 5 9 5 0 g60H4 h
  | 6, h => lookupWord 3 9 1 7 3 0 g60H5 h
  | _, _ => none
def g60 : Forest := ⟨60,6,fun i => g60Y[i]?.getD (0,0),g60C,[[]],g60L,g60I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60P3_0 : block g60 3 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60P3_5 : block g60 3 5 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60B3 : block g60 3 0 8 = true := (@block_merge g60 3 0 5 3 g60P3_0 g60P3_5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60P4_0 : block g60 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60P4_5 : block g60 4 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60P4_10 : block g60 4 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60P4_15 : block g60 4 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60P4_20 : block g60 4 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60P4_25 : block g60 4 25 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60B4 : block g60 4 0 28 = true := (@block_merge g60 4 0 20 8 (@block_merge g60 4 0 10 10 (@block_merge g60 4 0 5 5 g60P4_0 g60P4_5) (@block_merge g60 4 10 5 5 g60P4_10 g60P4_15)) (@block_merge g60 4 20 5 3 g60P4_20 g60P4_25))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60P5_0 : block g60 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60P5_5 : block g60 5 5 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60B5 : block g60 5 0 6 = true := (@block_merge g60 5 0 5 1 g60P5_0 g60P5_5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60P6_0 : block g60 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60B6 : block g60 6 0 1 = true := g60P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60T : checkedTables g60 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g60B3
  · exact g60B4
  · exact g60B5
  · exact g60B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g60G : graphValid g60 (boundsBefore K116) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low60 : Lower true (varsX 60) (graphGoal 60) 7 := lower_forest (g:=g60) (i:=0) (hints:=2237184) (before_sound K116 V116) g60G g60T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K60 := extendKnown K116 7 [(60,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V60 : Known true K60 := extend_ok (m:=60) V116 low60 (by decide +kernel)

def g31Y : Array (Bits × Bits) := #[ (0xffff97d7fff9e320b47bf3a931abe4d7ec3eccf74bc3c34d7cb3fd33976d980f,0x682820804c720b8b635262c05248281130060f4d81098c7530018345980c), (0xffff78fdfbcec4347af7d88ff7af4cdba99d657662e35f6a7f31847b9caa786f,0xffff87078c111089840488a889388584d288c82840b244f26008827a30aa6063), (0x77efb6a5574ffff677facfddbdea4bf25d9d3f66e8e7a98f27dcebb53370,0x88101842aca0040818620804404be0024220120608812184072982a43210), (0xbe7eff567ff8d7999bffccd6b764b5ffe31fdd7a3ddb42e6f84cefdac6a4,0x418902a80007a0062410742a84000020a01c04511042406228043d1a8424), (0xffffddbbbbbbbdb7cf3c2e5d2ff74e4e5eebfbeffabcd737eb787b8c4047edd1,0xffff2246400442480251c10982d100b400010901682843148e084002404149c1), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g31C : List ColumnInfo := [(3,0,28,0,4)]
def g31D5 (_ : Nat) : Nat := 0x5f
def g31L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,g31D5)
  | _ => emptyPacking
def g31I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g31 : Forest := ⟨31,5,fun i => g31Y[i]?.getD (0,0),g31C,[[]],g31L,g31I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31B5 : block g31 5 0 1 = true := g31P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g31B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K60) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 6 := lower_forest (g:=g31) (i:=0) (hints:=140033) (before_sound K60 V60) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K60 6 [(31,[]),(47,[84]),(55,[83, 84]),(59,[82, 83, 84]),(79,[32, 49, 84, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V60 low31 (by decide +kernel)

def g117Y : Array (Bits × Bits) := #[ (0x9d5c8037deda77ed8a8add2aa6a2acbefcb89f2424b9f77343d4d32,0x62a26ae9a1298060bd020451924eb97c0ca4d228443e23a1c3c4532), (0x0,0x0), (0xfffffffff5eede7bdec9574cef5a76a54eef02fdcda72354bef7457aa68b55e1,0xa11038005328194f0dc41480000241839b78210a2104360038b44c0), (0x0,0x0), (0xfffffffffedebfd6efeeb1d7e2ba7cff571f97b2f3f253f337a5f896ca3ea06d,0xfffffffff120002090094c200801008784a28880000008c21481200648148029), (0xf757fb9bf59e9f7755ffe5b1cf6edec4e6774aec9de11ba7be4d386,0x8a8c4600040200010004303044122340486400010e101820201306), (0xfad2f5f99beff6e59e7cb96fd58fcbbf5fdae0b5b2baee555512eda,0x505000650000c1f4020800000904002c3180006a300c80014128c0), (0x0,0x0), (0x0,0x0) ]
def g117C : List ColumnInfo := [(4,0,113,0,5), (1,0,116,0,5), (65,0,52,0,4), (5,0,112,0,4), (32,0,85,0,4), (16,0,101,0,4)]
def g117D4 (_ : Nat) : Nat := 0x81bc560bb0aa477a2540ef46a815e4d502
def g117H4 (_ : Nat) : Nat := 0x1378cc4
def g117D5 (_ : Nat) : Nat := 0x4100c86032180e4480fd23f903f902
def g117H5 (_ : Nat) : Nat := 0x2d02e10
def g117D6 (_ : Nat) : Nat := 0x588815f
def g117L : Nat → Packing
  | 4 => (4,2,3,0,0,5,0,g117D4)
  | 5 => (3,1,3,0,0,6,0,g117D5)
  | 6 => (1,0,3,0,0,1,0,g117D6)
  | _ => emptyPacking
def g117I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 2 5 1 6 2 0 g117H4 h
  | 6, h => lookupWord 2 4 1 6 2 0 g117H5 h
  | _, _ => none
def g117 : Forest := ⟨117,6,fun i => g117Y[i]?.getD (0,0),g117C,[[]],g117L,g117I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g117P4_0 : block g117 4 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g117B4 : block g117 4 0 4 = true := g117P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g117P5_0 : block g117 5 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g117B5 : block g117 5 0 3 = true := g117P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g117P6_0 : block g117 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g117B6 : block g117 6 0 1 = true := g117P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g117T : checkedTables g117 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g117B4
  · exact g117B5
  · exact g117B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g117G : graphValid g117 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low117 : Lower true (varsX 117) (graphGoal 117) 7 := lower_forest (g:=g117) (i:=0) (hints:=2229254) (before_sound K31 V31) g117G g117T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K117 := extendKnown K31 7 [(117,[]),(118,[16]),(121,[50]),(122,[16, 50])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V117 : Known true K117 := extend_ok (m:=117) V31 low117 (by decide +kernel)

def g87Y : Array (Bits × Bits) := #[ (0x6f9bbfaf7836e5fdfb4fd9ce6f07f3bf6219edc3e74a3d9d3e50b474d6,0x1064c0188581028890262408220c4642046d6401a5180c012804b04096), (0xffffffd77bcd9b37f5baf7defda0637b77d72af54b75be8bebb3b234630e99d3,0xffffffa8801446580a4100088801640583b9100980012a0a83109094ab0e1141), (0xffffffc9ffa0271f59f7a873bc5f197fea197b3d443f2075eb0be6db975c4c3d,0xffffffb60806c889a68841062710a08477827d28465808614e1728d3020c4c3d), (0x0,0x0), (0x37def7eaad49f97411765ff8f1feed59bfbca314ffb76a75c38fd9132e,0x48200811520105ba99908500438034800408a1051231280424add01302), (0x0,0x0), (0xfffffffafefe5efbbb1ffabddf74ff9db366e6abfb98ff7a5dcc6b583aa3ef09,0x5030120004480400241428018500001601200904044006a011001ac08), (0x0,0x0), (0x0,0x0) ]
def g87C : List ColumnInfo := [(4,0,83,0,5), (20,0,67,0,4), (2,0,85,0,4), (1,0,86,0,4)]
def g87D4 (_ : Nat) : Nat := 0x822080208102c80c0738d524b692c297a05452da4b025d85504
def g87H4 (_ : Nat) : Nat := 0x1e1480570864
def g87D5 (_ : Nat) : Nat := 0x40401608050281b646d2240ed24fe14fd14fe04fd04fd01
def g87H5 (_ : Nat) : Nat := 0x86354197969c
def g87D6 (_ : Nat) : Nat := 0xe411f
def g87L : Nat → Packing
  | 4 => (5,2,2,0,0,6,0,g87D4)
  | 5 => (6,1,2,0,0,6,0,g87D5)
  | 6 => (1,0,2,0,0,1,0,g87D6)
  | _ => emptyPacking
def g87I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 3 7 1 7 3 0 g87H4 h
  | 6, h => lookupWord 3 9 2 7 3 0 g87H5 h
  | _, _ => none
def g87 : Forest := ⟨87,6,fun i => g87Y[i]?.getD (0,0),g87C,[[]],g87L,g87I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87P4_0 : block g87 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87B4 : block g87 4 0 5 = true := g87P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87P5_0 : block g87 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87P5_5 : block g87 5 5 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87B5 : block g87 5 0 6 = true := (@block_merge g87 5 0 5 1 g87P5_0 g87P5_5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87P6_0 : block g87 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87B6 : block g87 6 0 1 = true := g87P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87T : checkedTables g87 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g87B4
  · exact g87B5
  · exact g87B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K117) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 7 := lower_forest (g:=g87) (i:=0) (hints:=132097) (before_sound K117 V117) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K117 7 [(87,[]),(91,[50]),(93,[32, 49, 100]),(94,[48, 33, 50, 100]),(103,[84]),(107,[50, 84]),(109,[32, 49, 84, 101]),(110,[48, 33, 50, 84, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V117 low87 (by decide +kernel)

def g115Y : Array (Bits × Bits) := #[ (0xffffffffff1cbfebf71b9076ff86cdcd38aae7e35ed649e81fdc7a655db3e20d,0xe1c0040e64250100e0e110b0c021d488100a2803c4f86092936204), (0xfffffffff3eddfb01fcaaf7bb2dadf4e0e42f3cfddaff1cc62ee4c666d755859,0xfffffffffc1228435009508c900a18e4410c8c22408c24d3602804024d641059), (0x0,0x0), (0x0,0x0), (0xb76b197f2dca7f115bf32fdeedf2ec8ce431afbd3b3c593f15625ec,0x4880e490c204948c112680a104c0501ac0230594013e04195562428), (0xfffffffffdceeb1fa5ebe95b857f27e4fb7cc1f82f5c86ef45870f9fba0d2757,0xfffffffff2310122125412a128c090c0ca8150a242c0068625c415042a010357), (0xffbcdffde7f5fdc5b5fff5bf7a7fcb6ab39fc14fd3df7a81bca9ab2,0x410002180001000040600001200001001c0001000028000088880), (0x0,0x0), (0x0,0x0) ]
def g115C : List ColumnInfo := [(32,0,83,0,5), (16,0,99,0,5), (2,0,113,0,5), (1,0,114,0,5), (48,0,67,0,4), (3,0,112,0,4)]
def g115D4 (_ : Nat) : Nat := (0x651512974d84544a790611512978d94540a761651502974d84540a751611502 + ((0x4544e7906115139b8994540e7616515039b4984540e751611503978d94544a7a + ((0x249b899358525e36496149b899358125e36496049b8994544e7a06515139b498 + ((0x4e48423c36302a241e18120c06009e819158d27616416349e819158927616416 + (0x8a847e78726c66605a54 <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g115H4 (_ : Nat) : Nat := 0x41c33a14664b04246ab2002969e16a6ab000001769feef4951c00011001ace6c2004a40d60
def g115D5 (_ : Nat) : Nat := (0xa895f11512faa0a25ed4244afe8a815f91502bea2a057c4540bf280817b50902 + ((0xdd4344efe8a81df91503bea2a077c4540ff28081f750d03bfa2a257e4544afa8 + ((0x504bf12a09f615412ec2a827ed0104bfa2a277e4544efa8a89df11513faa0a27 + ((0xfa6b0a5f49614bf1aa297e25453f40a8a5e81514fba0a297d35812fa4b025f8d + ((0xa697e054d3be869a5f45624be82c49de35492bc6a925f85524bf02a49ef42492 + ((0xac298a024076198561404a0e82004000be8ac697d058d3dc4a9a5b89534bf0a + ((0xde74dc8709bc6c5ab66d906157f5e56e5a1585494c4f122449023f0f6398cc2f + ((0x1161084808000400862080450421a029664e90e3d8de318861682e007e9f47b9 + ((0x204090020001842188201160084908000410862080450021a42000180218820 + (0x18220420800011004304408010000200082080100018204c0104100200 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g115H5 (_ : Nat) : Nat := (0xa31e0027300000f98000539af93cb0000097d0610004088280582018c0010800 + ((0xa83cb30f097899a52f003d3a2221d01c43a800002f03ac00a9f052568ae5cc7c + ((0x92c6400a05e3002319756e002d85080063186b830dfb45c13b56244f286cd0f8 + (0x2 <<< 256)) <<< 256)) <<< 256))
def g115D6 (_ : Nat) : Nat := (0x3416498391304c00fe34fd34fe24fd24fe14fd14fe04fd04fd13fd03fd12fd02 + ((0x553a210194c840554b329102150e8a440854b321802150e886008ad502450875 + (0x432910190c8405432180190c84055b3210194c840 <<< 256)) <<< 256))
def g115H6 (_ : Nat) : Nat := 0x31b2c03494228c662cc9dd3e6d48c8
def g115D7 (_ : Nat) : Nat := 0x2c68819f
def g115L : Nat → Packing
  | 4 => (24,3,3,0,0,8,0,g115D4)
  | 5 => (52,2,3,0,0,10,0,g115D5)
  | 6 => (12,1,3,0,0,9,0,g115D6)
  | 7 => (1,0,3,0,0,1,0,g115D7)
  | _ => emptyPacking
def g115I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 9 30 3 9 5 0 g115H4 h
  | 6, h => lookupWord 22 66 5 10 6 0 g115H5 h
  | 7, h => lookupWord 7 18 2 8 4 0 g115H6 h
  | _, _ => none
def g115 : Forest := ⟨115,7,fun i => g115Y[i]?.getD (0,0),g115C,[[]],g115L,g115I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P4_0 : block g115 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P4_5 : block g115 4 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P4_10 : block g115 4 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P4_15 : block g115 4 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P4_20 : block g115 4 20 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115B4 : block g115 4 0 24 = true := (@block_merge g115 4 0 20 4 (@block_merge g115 4 0 10 10 (@block_merge g115 4 0 5 5 g115P4_0 g115P4_5) (@block_merge g115 4 10 5 5 g115P4_10 g115P4_15)) g115P4_20)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P5_0 : block g115 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P5_5 : block g115 5 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P5_10 : block g115 5 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P5_15 : block g115 5 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P5_20 : block g115 5 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P5_25 : block g115 5 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P5_30 : block g115 5 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P5_35 : block g115 5 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P5_40 : block g115 5 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P5_45 : block g115 5 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P5_50 : block g115 5 50 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115B5 : block g115 5 0 52 = true := (@block_merge g115 5 0 40 12 (@block_merge g115 5 0 20 20 (@block_merge g115 5 0 10 10 (@block_merge g115 5 0 5 5 g115P5_0 g115P5_5) (@block_merge g115 5 10 5 5 g115P5_10 g115P5_15)) (@block_merge g115 5 20 10 10 (@block_merge g115 5 20 5 5 g115P5_20 g115P5_25) (@block_merge g115 5 30 5 5 g115P5_30 g115P5_35))) (@block_merge g115 5 40 10 2 (@block_merge g115 5 40 5 5 g115P5_40 g115P5_45) g115P5_50))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P6_0 : block g115 6 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P6_5 : block g115 6 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P6_10 : block g115 6 10 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115B6 : block g115 6 0 12 = true := (@block_merge g115 6 0 10 2 (@block_merge g115 6 0 5 5 g115P6_0 g115P6_5) g115P6_10)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115P7_0 : block g115 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115B7 : block g115 7 0 1 = true := g115P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g115B4
  · exact g115B5
  · exact g115B6
  · exact g115B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 8 := lower_forest (g:=g115) (i:=0) (hints:=4521985) (before_sound K87 V87) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K87 8 [(115,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V87 low115 (by decide +kernel)

def g124Y : Array (Bits × Bits) := #[ (0x0,0x0), (0x0,0x0), (0xaf70f2d6d9fff3d794917d39e9fd0f63ec2db9ce26199b82,0x50460d0122021008012c2810d1128541089da80400091182), (0xffffffffffffffff7bdfcf571d5656fd3867f4d279f45306fb4bc31f7553c4c5,0x840020e8c0a400a176904020228022125100400964d2c044), (0xf7f9efe9ab6f95f2ebea6b65fdae7beb93e61c6591e8672c,0x81010021400094400020002000500a08040100010000628), (0xfffffffffffffffffe7fd96cf7b77babf45f88dea73fbcfd74196690df46385b,0xffffffffffffffff018000100908060000401201002808042000040003002811), (0xcbd39adfe509ebdb674a2eb41388d39d4ad83cf36ae5c172,0x342cac2082d640ba5c08c128d5501719439cc0da00e5c142), (0x0,0x0), (0x0,0x0) ]
def g124C : List ColumnInfo := [(64,0,60,0,7), (32,0,92,0,5), (16,0,108,0,5), (8,0,116,0,5), (4,0,120,0,5), (96,0,28,0,4), (80,0,44,0,4), (72,0,52,0,4), (68,0,56,0,4), (12,0,112,0,4)]
def g124D7 (_ : Nat) : Nat := 0x5f
def g124L : Nat → Packing
  | 7 => (1,0,4,0,0,1,0,g124D7)
  | _ => emptyPacking
def g124I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g124 : Forest := ⟨124,7,fun i => g124Y[i]?.getD (0,0),g124C,[[]],g124L,g124I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g124P7_0 : block g124 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g124B7 : block g124 7 0 1 = true := g124P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g124T : checkedTables g124 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g124B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g124G : graphValid g124 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low124 : Lower true (varsX 124) (graphGoal 124) 8 := lower_forest (g:=g124) (i:=0) (hints:=69346048) (before_sound K115 V115) g124G g124T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K124 := extendKnown K115 8 [(124,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V124 : Known true K124 := extend_ok (m:=124) V115 low124 (by decide +kernel)

def g95Y : Array (Bits × Bits) := #[ (0x2bf3f9df2fe45ad4d68f8b0c236651abc2f50aaea7a3d96b1694cbc4aab90da4,0x2b441035c27281808d898600014c418b8241002403029c4a841609c42aa90104), (0x3e2a1351145d7db660b830a0f7412ad9ce16ea82eddbe88f4fe0e1109346bd76,0x40a014a00094840402060a1720000504c0a2ac2a8dd62110220601091442c72), (0xc1ee6f7c99bc88f8e553eff18a41d87fab86215970714e40f85d5c186679a613,0x142541b9892404184102fa4181020868a044110850b14c00482c001046398613), (0xec84472f753d7b29a58602bb74b993f6b388a2e55d1f1124e31ff6726ce41948,0x28a1e042210012120a8003e042510060288eec105081024a012f66020c41908), (0xb30da456ebab8a4d0ec1ef4a3ed86e163c2b373c881edfb52c43292f0981626b,0x50004200c848440c41050022480210102200228a0623980441090e09006060), (0x0,0x0), (0x9dd1fdf487eb25aa7a77b02ec036254c55f7d5b99f6830d65d3406e5151ed091,0xd0212a002d0000092216105c0012200401945418040000045908062104129081), (0x0,0x0), (0x0,0x0) ]
def g95C : List ColumnInfo := [(8,0,87,0,7), (4,0,91,0,7), (2,0,93,0,7), (1,0,94,0,7), (64,0,31,0,6), (16,0,79,0,6), (12,0,83,0,5), (3,0,92,0,5), (67,0,28,0,4), (28,0,67,0,4), (10,0,85,0,4), (9,0,86,0,4), (6,0,89,0,4), (5,0,90,0,4)]
def g95D5 (_ : Nat) : Nat := (0x61f961674d1018ee2859d344061f961678910187e5859d24406378e16749101 + ((0x5028f61859d3540bd240d254d502fa1214111440bf04850344d0287e5859e344 + ((0x3544bd144d254d5128de3859d4540a3d8616751502f29044954540a2f921674d + ((0x4451038de3859d4544a3e8216751512f25144954544a2f921674d5128fa0859d + ((0x59d4544fc545135515138ee2859d4540e3d8616751503f19044d54540fe44c50 + ((0xa137959048de3849e564122f92167855238be4859e0548e3b8a167515138fa08 + ((0x6178d905492bc8615741a148ee284de56452378e12795914af20855d168123b8 + ((0x3e82167456248f61859d05892378e16785524cda078d915492378e16781524cd + ((0x48f61859d058d23b8a16785534cea07899154d23b8a16781534ce617899054d2 + ((0x4d63d8610791935ace2851d368963e82117919258f61841e464963e821674563 + ((0x43f1e0e4642f160a44c230e054240f060240c03002b38e14749a358fa0845e46 + ((0x34974a2451c8b44215047f3e1e4ec73381b4d46732184bc5b2c154a44f241148 + (0x8408000000080080000000800a1020000000000562a54ca350275 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g95H5 (_ : Nat) : Nat := (0x6f48ec0911cc4960253ba5a007b74eaaddc046700100904cd0114700c6f134a9 + ((0xc004bf6e9724f1664300186000005cb50f98d4b6b6d434e3f12073c46837e159 + (0xb0000011663aa10ad8c895ca0908b708e214800a604575 <<< 256)) <<< 256))
def g95D6 : Nat → Nat
  | 0 => (0xe344067eb3a6880dee274d1019facf122033f59d24406ef1ba4880cfd6748d01 + ((0xcfe37519019fc4ea32033f91d364067f13a6c80cfe47499019fc6e932033f59 + ((0x88a205f94851340bec81a26816fa0751901dec2ea32039f95d464063f2ba8c8 + ((0x40b6fb1a6a817d9034d502eda4a9aa053f99d1440b7bb0a28817e52145102f72 + ((0x930449029fccea2a053f59d4540bdc8228a8176d25515029fcce9aa053f59d35 + ((0x205fa81d5240b77232a4816ed4654902fd280a9205fa4c15240bf4a0224817e + ((0x7f2ba6c814fe174d9029fa8f0b2053f4de1640bf513a80816fa5650102df2aca + ((0x519029fcaea3205b78dd4640a6f1ba8c814fe17519029faaf1b2053f45e3640a + ((0x5bd85d5640a7b0baac814fd57919029fa2f232057b89d4640aef1ba8c816ee27 + ((0x3cac814fd3795902bf40eab2057d85d5640b7d03aac814fe47559029fc6eab20 + ((0x12faa269aa25db4953544a7f33a08896fb6041112f6a2882225f544d0344a7ea + ((0x99d4544a7eb3a8a897b51451512eda4aa2a253f99d3544a7eb3a6a896df634d5 + ((0x2896f55650512fcc2ea9225bb9195244b76a32a4897e54154912fca62a92253f + ((0xfa0f1b2253f95d3644a7f03a6c894fd47819129fa6f03225f989d4144b7b2b28 + ((0x4644b7713a8c894fe5751912dbc6ea3225378dd4644a7f03a8c894fd578d9129 + ((0x4fe3755912df40eab2253e81d5644a7eabc8c894fd0791912bdc4ea3225778dd + ((0x88a2073f51e5644a7e9bcac895f61755912bf40eab225bd85d5644a7f23aac89 + ((0xe7f33a4a81eef6249503eba6a92a073f99d1440f7bb0a2881fd53145103f720 + ((0x4654d03fb280a9a07f65011340e7f33a8a81cfd6751503f7208a2a07d74d5454 + ((0x2073f49e1640fed1ba8081efa5650103df2aca0207f681d5340f6f232a681edd + ((0xf2ba8c81eee27519039dc4ea32073f85d4640e7eabc4c81cfd17899039fa8f0b + ((0x59039ec2eab2073f55e4640e7e8bc8c81dde3751903bdc4ea3207b78dd4640e7 + ((0x3f49e5640efd03aac81df61755903df40eab2073f91d5640e7f13aac81ef6175 + ((0xa4a89eef6249513eba6a92a273f99d0444f7db020889fb514411139fa8f2b207 + ((0x3dba8ca9a27f55055344e7f33a8a89cfd6751513f6a28a2a27d74d54544e7f33 + ((0x1e0644e7e93c0c89fd63750513decaca0a27bd5594144feb0baa689ede4654d1 + ((0x89cfe5751913ddc4ea32273b89d4644e7f03a8c89cfd57899139fa0f132273f5 + ((0x40eab2273e81d5644e7eabc8c89cfd0791913bbc6ea32277b89d4644f6f1ba8c + ((0x644e7e93cac89df61755913bf40eab227bd85d5644e7f23aac89cfe2755913df + ((0xfe17559239fc0eab2473f59e1548efd03a2a91cfd6781523bec2e82a473f51e5 + ((0x92a093f19d254139ea2a4a826ee2755923dbc6eab247af91d5648e5f23aac91c + (0x3dbb0a28824ff674d5049fcce9aa093f19d354139ea2a6a824ff67495049fcce <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0x755104cfecaaa209ee81d544139fb2aa8825fa0745104deec28a209ee81d1441 + ((0x93f45e26412ef1ba4c824fd37859049fa4f0b2095f95d16413bdb2aa0825fa0 + ((0x13aac826f617559049ec2eab2093f55e364127e8bc6c825ee274d9049faaf132 + ((0x2049fa6f2b2093f49e56412fb0baac8267e5755904df40eab2093f8dd564127f + ((0xfd9d254527f33a4a8a4fc6749514e7a8a92a29bd95d168137aaba2d026b51655 + ((0xa88a7b61755114e7ecaaa2293fd9d354527f33a6a8a4fc674d514e7a8a9aa293 + ((0xbbc6e932293f4de064527e93c0c8a57e5741914eeecaa8a297d85d544533fb2a + ((0xd564527d03aac8a4fd578d9149fa0f1b2297b89d364527eabc4c8a4fd0789914 + ((0xa4fd2795914bf40eab2299f95d564537b0baac8a4fe37559149fc4eab229be81 + ((0x6d02a497d85d054936f1b20a926fa5741a14df2ae83429ae419548527e9bcac8 + ((0x492f693c2a926de3685524bf40e8aa49b78d9154927eb3c0a925ed2781524dbc + ((0xe4755924dbc6eab249378dd564927f0baac924fe0755924f5c8ea92493f59e15 + ((0xac49bd585158927eb3c0b124fd6741624bec2e82c49be581058937713aac926b + ((0x7f2ba2d124fe0745a249fcae834493f85d068927eb3c2b124fd6745624bf40e8 + ((0x81534bba6f02a69bb89a054d2fb0ba0a9a6ee26415349fc2eab4493f81d56892 + ((0x9e791d534d27eb3c2a9a5dd3785534ddc4d0aa697e81d154d3771322a9a4fd67 + ((0x20b1a6de3755934d7c8eab269bb89d564d27713aac9a4fe17559349fc0eab26 + ((0x349face8ac697e81d158d37ab0a2b1a4fd67816349face82c697d85d058d37cb + ((0x85d568d27f03aad1a4fe5745a349fc0e8b4693f95d068d27f0ba0d1a4fd67856 + ((0xd0acfe3751a059fc4ea340b3f91d368167f13a6d02cfe4749a059fc6e9340b3f + ((0xbec69aa4b3f8dd468567f13a8d0acfe474da159fc4e9b42b3f91d268567f1ba4 + ((0x454975fb228a92f6e2751525e7ec8a2a4b7b89d354976fb1a6a92f6e274d525e + ((0xcfd47859259fa6f0b24b7e81d164967ea3c0c92cfd3781925bec2e8324b7b89d + ((0xca2c4b3f45e464967e83c8c92dde37519259fa2f1b24b3f41e36496df23a6c92 + ((0xd6ef1ba8a9aebf6451535ebc6ea2a6bcfd91454d76f23a6d12edd474da25cba6 + ((0x47499359fa8f0b26b3f49e164d6fd03a2c9acfd47819359fa4f0326b7d85d064 + ((0x46b9b499458d67e8bc8c9acfd0791935bdc4ea326b3f45e264d67e83c4c9adbe + ((0xe93c2ca2dfa07459459fa6f0328b3f49e06516fb0ba0ca2eee4749a35dda8e93 + ((0xd9459fa0f1b28b7b89d365167e8bc4ca2cfd0789945bbc6e9328b3f4de165167 + ((0xe406482b8134094047022010407c03b01c00b804801d809c0260060004fd178 + ((0xcc0dc06c834a1980c906302f01720b6057c29613e098849022e10a07e83c01d4 + (0x513789884aa24f11d88d445022210e085842020a10207f83f01f20f607603a41 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 2 => (0x1a48d0c66c32218a8c205f62ee1708b5059c2c815d8ab85502941470a204f627 + ((0xfc8fb07cc3e01ed0f5079c3c81e10ef076c3b01ce0e5872037c1bb0da46c634f + ((0x993189724ac24f924891847f23911b08b045222610fc87243321310648263ff1 + ((0x1610afc5782b915b0acc5602ad1518a8053a2931480a2650d27c93cc9da4e026 + ((0x95cc9463d31818a8c3a61030517d8be05ea2ee975cba25c42db96c4b3a5972c5 + ((0x38e1070237e1bd8de06ea3721b78d946c435f1aa8d4869e3451a10cfc6713321 + ((0x8fc47d53e09ed0f5c7a13ca1e38ef47743b71d84eb67553a41cece6a72138d9c + ((0x1b08d2462a2e115689e44c22490fc87843921b10b085241ba0710108023fe1fd + ((0x1e9894baa5852b69554a4250927893649824a924891e48c24492188f8475a379 + ((0xa6a5322941486a3651828a9448a1e50528113fc9f84f227793b09c44d4a6713 + ((0xb365982c71602af4573ab8559aab9559aab5540a9a54a2a39510a8253e29d94e + ((0x4861db0d5842c0d5fcafb17ccbe05ed2f19772b9e5cc2e2d6fcb715ab2d41686 + ((0x68ab43da04cf5674333598ecba656b29d942c9b64732218f6c75634318989cc + ((0x7093815bfedf26f6377dbb2dc56dfb6c9b58d986c235c1ac6d5d6abb545a7ad3 + ((0x613af1d5eea274aba21d04e7c73b39a5cc6e567283929c88e37718b891c3ce18 + ((0x93db1eccf607a63ce1e56f1e78c3c49e18f067803be9de8eee7743b89daaec87 + ((0x407202d0108053fd9fc4fd57e43f09f78fb67d83ea9f48f9e7cc3e49f18f7f7b + ((0x988208042c4084c410400162040829413208d04081d40d205d028811 + ((0x40020000808504104040030010a085041030810001088006211000c26208000 + ((0x408000304002009001000010000000000000000a8820000880201003081000 + ((0x88020100200300100004042830820200180085042830c1000020800401000200 + ((0x2080040100020000608000204002009001000010000000000000000a8c20000 + ((0x40000000000002a2080002210808408008084000101080c104282141040c2040 + ((0x800020210182085042830c10000200100400080001020000c100080240040010 + ((0x400080001820000810008024004001040000000000002a308000221080001810 + ((0x840800000a102004a000189400030b802000002e00b002170058010000200100 + ((0x200042000400008100000000000000009482000800400000200124092040002 + ((0x94c200080040000002840800000a102000108c212202860410008 + ((0xd304002142600c0c00d20401088212202860410008020004200040000c100000 + ((0x640800c10025308004080129042400424004001000002e008002142600c0c00 + ((0x21200202080000170840410a13086061069820410a130860610690200003304 + (0x10000188203004000062080c0100001982032040060801298400204009482120 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 3 => 0x4a008404081820810000000000000000008004000012842101020608204000000000000000002001000000800480240
  | _ => 0
def g95H6 (_ : Nat) : Nat := (0x1038582022460b0e053810004f9004002814000088160840b00381800200001 + ((0x8f001c101060c8811a10003003000c1814380009c7860a04000021402c0e04a0 + ((0x44c104020c30b7000a9d0200000280c00e1e0918a122000004880000411c + ((0xd9d8ed4740eab382e6d82458202181083cf47840a080000e0008c82042181c38 + ((0x29c30843c606dc1150b531b8db257985e8917f485f229cfa6addc7ee2dc54e86 + ((0xf8e31aeabacac542f45618486976c2c78880dc1046bccb351df59986e6cd04ff + ((0xb21e048e4d1e151ffd7f0bab338896952543f26702691300038ccae748b33a0c + ((0xdea00096433dd922f4d000000110546292cb9e000045b4a58d3995b62fa94add + ((0xa584ef973d1429f6e438142bf2160004a08000cd0c03472800210ce55b5d8001 + ((0xbb1a106592a545e470007c7a2f293f000495fcd8a9d47d80000010eef8e0a539 + ((0x768caba1991ad723f3500029f2077cb2800246c98ac95187e2a388f984308967 + ((0x49d4c5aaa87da1cb217ad800026100029c34fa00077b48c583373450859255d9 + ((0x22a4ee42df71e9102e0f346a2c00009aa4d45a538509b20003717b064895 + ((0x2bf34da9a69697c683a617542ba68a61800036429d7ab1451d03000000166006 + ((0xaed3a0b1d26ff51bc49289d37784d917317c21a388b1f1cfa81cb8759f93787a + ((0x5083d1e8e63095e8cb5bc4d751719724f6189bc163f371800069acc752a887f8 + ((0x309ac02b26f6863f714196330718b4ef817b908e318001ea80001a864a170000 + ((0xa0c53800006d75222191621b8d581ed6c4d24bb9cf677f3200034f0000000588 + ((0x6800004c9bc540698b0b2aa9b1d40000f216c0000000c18558d484001f2f0006 + ((0x70fc720000481598000476ac18c1225200008c0000000000609ff00284e6d91 + ((0xedca02e161894b214b70afcc918344395a3ab10698000daa81ac001ee074b2dd + ((0x66b400005b69e152c00000021d708eeae38a8000000f4524958748c3914e97a + ((0xdeefa29a8d091b812236e91800000733cac14000000000000000000000022953 + ((0xb42b0300015e362358cfa0166606770283e31806bf0003ce6cf96643ad349f15 + ((0xbc56e643970375857185f40000000000001f1e6dd02b0a78000b2d45aa329809 + ((0xf46589fb14c6c9da18000001020c49e056471cf3f5f38930100b0c44642b0010 + ((0xe0f145c149a43c91019400000001af2f71196b80000a48e71869ebbb384001c4 + (0xe5cfca0cbf43f3b7800095726e000000259f3111a82b9883b251 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g95D7 : Nat → Nat
  | 0 => (0x2ff44d02bf51901bf4d901bf49901ff8d101ff4d101ff89101ff49101ff48d01 + ((0x2bf85902ff45902fe50102fe4c102fb54902fb44902ff51502ff4d502ff4510 + ((0xd12bf95902ff55902bf55902bf91902ff51902bf51902bf8d902ff4d902bf4d9 + ((0xd912bf81912ff41912fd50512fd4c512fb54912ff51512ff4d512ff41112ff40 + ((0x45103bf95912ff55912bf55912bf91912ff51912bf51912bf8d912ff4d912bf4 + ((0xf89903ff49903bf85903ff45903fe50103f754d03f744d03ff51503ff49503ff + ((0xff51513ff49513ff41113bf95903ff55903bf55903bf91903ff51903bf51903b + ((0x3bf91913ff51913bf51913bf89913ff49913bf81913ff41913fd50513f754d13 + ((0x4ff49504bf55923ff85523ff45523ff81523ff41523bf95913ff55913bf5591 + ((0x904ff45904fe54104ef95104ff55104ef55104ef85104ff45104ef45104ff4d5 + ((0x5904bf55904ff8d904bf8d904ff4d904ff89904bf89904ff49904ff85904bf85 + ((0x4d514ff49514bf55a04bf45a04bd45a04ef55204ef45204ff95904bf95904ff5 + ((0xf89914ff49914ff81914bf81914ff41914fd54514ef95114ff55114ef55114ff + ((0xef55214ff95914bf95914ff55914bf55914ff8d914bf8d914ff4d914ff89914b + ((0x4b78d924fb54924ff85524ff45524ff81524ff41524bf55a14bf41a14be41a14 + ((0x34ff41534bf55a24bf45a24bf41a24ff85624ff45624ff81624ff41624bf5592 + ((0x634ff45634ff81634ff41634bf55934bb89934f754d34ff85534ff45534ff815 + ((0x9a15be81915bf51a05bf4da05bf49a05bd85905bf55a34bf45a34bf41a34ff85 + ((0x41925df91525ff51525df51525df8d525ff4d525df4d525bf51a15bf4da15bf4 + ((0xf51925ff8d925bf8d925ff4d925ff85925bf85925ff45925ff81925bf81925ff + ((0xff51535df51535bf51a25bf4da25b74da25df51625df4d625ff91925bf91925f + ((0x5bf89935ff49935ff85935bf85935ff45935ff81935bf81935ff41935df91535 + ((0x45be41845bf51a35bf49a35bb49a35df51635ff91935bf91935ff51935ff8993 + ((0x945ff85945bf85945ff45945ff81945bf81945ff41945b74d845bb49845bd458 + ((0x1b45bf51a45bf4da45bf49a45ff8d945bf8d945ff4d945ff89945bf89945ff49 + ((0x701e606d818005d0162054013e04380cc0228072015003c0078000bf45b45bf4 + ((0x4584e012c04a4124848011b843210503e40ea038a0d683180bd02b209c024c08 + ((0x20b87fe1f387981e3077a1da072c1c386de1a88684195061217b85ac15a85461 + ((0xa2ca0b042b08a9e29b8a3e28c8a2028389d226d0984252092a23e88b82250852 + ((0x43798dbc3618d6834f8d2c3468cea3348cb43270c7e3108c242fd0bb82e68b6 + ((0xda42a908041290263fc0fd83ed0f9c3d80f3c3c90ee83b10eac39d8e5838d0e + (0x13b04e313744ce13144bf12c04a7127e492122448011d046c918845d916444a1 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0x4965058f962058395f057315a255f9560550952454194ca51f144c50893fe4f2 + ((0x61994464698de627185a612182a60617fa5f597ac5e2176a5d3172e5c416d45a + ((0x7351cb671e9c5670e1bfc6f61ba86e29b606ca9b0c6b89aac69a9a2867f99c86 + ((0xc7f81fbc7e79f627cf9f0e7bc1ec67a41e427849de876c9d8e7561d4074a1cf2 + ((0x4c8cd22f88b6a2a489ba238880a1cc85fa14e8492100832a0b2825205e80ea01 + ((0x832478901071a24049662556946a4de928a48a913a43090623dc8efa3a68daa3 + ((0x881c48e20401cb2881c512388140a34c2071448e24402871620c91e24441c58 + ((0x91438a104734b24384140020d2048c30601cd3088c348204834134008d08234a + ((0x230a105000a34b19000534b2461448c285028d20512348284100a34c1d208534 + ((0x4024d2044843481630a10073491230c284100934915010d2448c28401cd2451 + ((0xc2458c28411cc2890a105000830812208180730130008c0c230b08d2058c30a1 + ((0x440e284140028c28640014c2891851038a140a3081444e20a104028d3074c314 + ((0x84100930811310c2050e28401cc2440e20a104024c2454043091038a10073091 + ((0x748214b2450e28001cb2048c38401cb2888c34820082c12c108b082308143882 + ((0xc915110b2448c20601cb24512309106000a34b1910452c81448d208180028b28 + ((0x1ca04a04228308b2058c308180024b2044842c81630818072c91230c20600092 + ((0x106000a30a1910452881444e208180028b2874c314a2458c28001ca204882840 + ((0x4a2044c428814388180728910388206000928915110a2440e20601ca24510389 + ((0x1830020c10891850c28601c61200c81938041848032064a010a2050e20818002 + ((0x34852481448c3c871448c31081448c3c862481c58c34822050d20842058c3482 + ((0x51510432448c30910700093494414050d20832048c34820402081d208420510 + ((0x1448c31481230f20810082044832230810051500032448c30b10500092c94500 + ((0x30810092481448c3482c41c003092058d2c701c92051230c62481c58c3482208 + ((0x74c3885205113085248144ce2087144882108144ce20860800820422481448c + ((0x92894500051510432440e20910700093094414054c38821081130e20810082 + ((0x81448821881448821481330e20810082044c32038810051500032440e20b1050 + ((0x91018042484a01092051038820402492051130e20b107000c2481538b1c0724 + ((0x881530841440881434842430a1005265cf28501891440601491018042484e01 + ((0x48401092128442451030a10700092451330d20a10402891444c3c8284100a144 + ((0x54c21051022050d21090c2060149973c9180624512100524484010921384424 + ((0x2248d2c701891440c2c41800249144cc348206000a2451130f20818002851022 + (0x107000a2244e2c701881230f20810082051230c2c414002881448c309107000a <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 2 => (0x414002040500042448414001881330e2081008205103882c414002881440e209 + ((0x442054c3c828410093484c3485248144841c07144841109144841c062481848 + ((0x30500032450c28414002091900041120811081730d20a104024c2134821444c3 + ((0x9204cf28501c92051210462481848414002091448411491030a107000824540 + ((0x1492051318001c51200042451318001892040c2841008248144cc3c828414003 + ((0x144482004205cc34820600092884d20851130c01081530f208180024b2130d2 + ((0x51200062451200052440c2c418002091510d10600042450c244180020919106 + ((0xc082481444f2c702092040c2060008248144cc3c82441800309204cf24601c92 + ((0x30c32051130f20810092130d2109205133cb1408248144cf24702092051334b1 + ((0x500041510432451030910700092510501044820c8144cc34820402484d208411 + ((0x1030814002492040c2c414002492040c2441c002454000c91440c2c414002494 + (0x92051330d208100a2481444c3c82040289205 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g95H7 (_ : Nat) : Nat := (0x106500800840001001c00a0c10604040000910042801c0000004000011210085 + ((0x882200701360040e0624a020200000226650e0a380050c18280020c40c002000 + ((0x4b6d940b39bbd52a194c0a300005e42f8007db2da269194ce802026410004cc7 + ((0x5c0765a352e1620ac9ed2269c448d16853cf98c015ff101a9e0739088cb39803 + ((0xf4166ee4931e0cad3cbdb37ce2058000007c2936ad8daa5a756d4c804ed9a33e + ((0xa590910ee1053b22a950888000535a1dc8244a5bf380d45b204b7b91c2dc571c + ((0xa3afec48f39813ff27c1e0000000cd00042e800000134422d8e6a9196b0d0007 + ((0x18dcf28506c546792f2146f02c16b623222b8000004251e3f866a4ed81435df + ((0x4408a63cd8400000063980031d2954635bc592b1100000016ad66b6ca5c00000 + ((0x52c9dd8000006179839dce8bc6a55d7d44b109b1492b2e64e5b81ca4df68c0cf + ((0x7f59bd35bdddee06c26f54e420002010003558000001c08006879caf56428800 + ((0x676f0a87051c9fd90937389d9ecef93890a8240176467b4e305662298ebd99c4 + ((0xe1cc38004938005e2a1c0005ed8001e50005c732803eac8800731800771bb86 + ((0x17c186eda200023bd6f0578006daddf6ae000012582da608f80000000074c800 + ((0x18fd3b3d000556a9933a601e9f6726ab0007c692c0000001b0e832d2fe4504c2 + (0x4e25a3eeb4 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g95D8 (_ : Nat) : Nat := (0xff417fc69fd34ff127f493fc29fd14ff027f413fa47fd13fe81ff44bfa05fd01 + ((0x42583bc59075070003fe8bfe45fea2ff117fc6bfd35ff12ff497fc2bfd15ff02 + ((0x418a21800aba5642a750c99f24a2ac187c0ea1b8338600b2148258436778d096 + ((0x250524c6288405ad2829072144202d894149318830016d4a0a41c841800b41ca + ((0x5a50524c62886002d28290721443001694148390a21800b498a498e42080a5 + ((0x31c851080a494931c851080a494931c841800a494931c841800a4a0a498c510c + ((0x800b4149318a21800a4149318a21800a4148390a21800a4148390a21800a4949 + ((0xa21800c4a0a498e4288405a50524c72144202d2829263908300169414931c841 + (0x4a0a498e428860031282926390a21800c4a0a498e428860031282926390 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g95H8 (_ : Nat) : Nat := 0x45a200c30797da2b000009200875c83000004655e3488c8894d3818de0dc4d3e84d055402de207e
def g95D9 (_ : Nat) : Nat := 0x642023f
def g95L : Nat → Packing
  | 5 => (53,4,4,0,0,9,0,g95D5)
  | 6 => (401,3,4,0,0,13,0,g95D6)
  | 7 => (230,2,4,0,0,14,0,g95D7)
  | 8 => (26,1,4,0,0,11,0,g95D8)
  | 9 => (1,0,4,0,0,1,0,g95D9)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 6, h => lookupWord 18 63 5 10 6 0 g95H5 h
  | 7, h => lookupWord 135 475 7 13 9 0 g95H6 h
  | 8, h => lookupWord 81 276 7 12 8 0 g95H7 h
  | 9, h => lookupWord 9 31 4 9 5 0 g95H8 h
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
theorem g95P5_50 : block g95 5 50 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B5 : block g95 5 0 53 = true := (@block_merge g95 5 0 40 13 (@block_merge g95 5 0 20 20 (@block_merge g95 5 0 10 10 (@block_merge g95 5 0 5 5 g95P5_0 g95P5_5) (@block_merge g95 5 10 5 5 g95P5_10 g95P5_15)) (@block_merge g95 5 20 10 10 (@block_merge g95 5 20 5 5 g95P5_20 g95P5_25) (@block_merge g95 5 30 5 5 g95P5_30 g95P5_35))) (@block_merge g95 5 40 10 3 (@block_merge g95 5 40 5 5 g95P5_40 g95P5_45) g95P5_50))
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
theorem g95P6_150 : block g95 6 150 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_155 : block g95 6 155 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_160 : block g95 6 160 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_165 : block g95 6 165 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_170 : block g95 6 170 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_175 : block g95 6 175 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_180 : block g95 6 180 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_185 : block g95 6 185 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_190 : block g95 6 190 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_195 : block g95 6 195 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_200 : block g95 6 200 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_205 : block g95 6 205 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_210 : block g95 6 210 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_215 : block g95 6 215 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_220 : block g95 6 220 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_225 : block g95 6 225 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_230 : block g95 6 230 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_235 : block g95 6 235 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_240 : block g95 6 240 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_245 : block g95 6 245 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_250 : block g95 6 250 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_255 : block g95 6 255 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_260 : block g95 6 260 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_265 : block g95 6 265 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_270 : block g95 6 270 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_275 : block g95 6 275 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_280 : block g95 6 280 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_285 : block g95 6 285 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_290 : block g95 6 290 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_295 : block g95 6 295 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_300 : block g95 6 300 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_305 : block g95 6 305 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_310 : block g95 6 310 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_315 : block g95 6 315 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_320 : block g95 6 320 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_325 : block g95 6 325 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_330 : block g95 6 330 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_335 : block g95 6 335 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_340 : block g95 6 340 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_345 : block g95 6 345 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_350 : block g95 6 350 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_355 : block g95 6 355 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_360 : block g95 6 360 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_365 : block g95 6 365 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_370 : block g95 6 370 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_375 : block g95 6 375 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_380 : block g95 6 380 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_385 : block g95 6 385 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_390 : block g95 6 390 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_395 : block g95 6 395 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_400 : block g95 6 400 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B6 : block g95 6 0 401 = true := (@block_merge g95 6 0 320 81 (@block_merge g95 6 0 160 160 (@block_merge g95 6 0 80 80 (@block_merge g95 6 0 40 40 (@block_merge g95 6 0 20 20 (@block_merge g95 6 0 10 10 (@block_merge g95 6 0 5 5 g95P6_0 g95P6_5) (@block_merge g95 6 10 5 5 g95P6_10 g95P6_15)) (@block_merge g95 6 20 10 10 (@block_merge g95 6 20 5 5 g95P6_20 g95P6_25) (@block_merge g95 6 30 5 5 g95P6_30 g95P6_35))) (@block_merge g95 6 40 20 20 (@block_merge g95 6 40 10 10 (@block_merge g95 6 40 5 5 g95P6_40 g95P6_45) (@block_merge g95 6 50 5 5 g95P6_50 g95P6_55)) (@block_merge g95 6 60 10 10 (@block_merge g95 6 60 5 5 g95P6_60 g95P6_65) (@block_merge g95 6 70 5 5 g95P6_70 g95P6_75)))) (@block_merge g95 6 80 40 40 (@block_merge g95 6 80 20 20 (@block_merge g95 6 80 10 10 (@block_merge g95 6 80 5 5 g95P6_80 g95P6_85) (@block_merge g95 6 90 5 5 g95P6_90 g95P6_95)) (@block_merge g95 6 100 10 10 (@block_merge g95 6 100 5 5 g95P6_100 g95P6_105) (@block_merge g95 6 110 5 5 g95P6_110 g95P6_115))) (@block_merge g95 6 120 20 20 (@block_merge g95 6 120 10 10 (@block_merge g95 6 120 5 5 g95P6_120 g95P6_125) (@block_merge g95 6 130 5 5 g95P6_130 g95P6_135)) (@block_merge g95 6 140 10 10 (@block_merge g95 6 140 5 5 g95P6_140 g95P6_145) (@block_merge g95 6 150 5 5 g95P6_150 g95P6_155))))) (@block_merge g95 6 160 80 80 (@block_merge g95 6 160 40 40 (@block_merge g95 6 160 20 20 (@block_merge g95 6 160 10 10 (@block_merge g95 6 160 5 5 g95P6_160 g95P6_165) (@block_merge g95 6 170 5 5 g95P6_170 g95P6_175)) (@block_merge g95 6 180 10 10 (@block_merge g95 6 180 5 5 g95P6_180 g95P6_185) (@block_merge g95 6 190 5 5 g95P6_190 g95P6_195))) (@block_merge g95 6 200 20 20 (@block_merge g95 6 200 10 10 (@block_merge g95 6 200 5 5 g95P6_200 g95P6_205) (@block_merge g95 6 210 5 5 g95P6_210 g95P6_215)) (@block_merge g95 6 220 10 10 (@block_merge g95 6 220 5 5 g95P6_220 g95P6_225) (@block_merge g95 6 230 5 5 g95P6_230 g95P6_235)))) (@block_merge g95 6 240 40 40 (@block_merge g95 6 240 20 20 (@block_merge g95 6 240 10 10 (@block_merge g95 6 240 5 5 g95P6_240 g95P6_245) (@block_merge g95 6 250 5 5 g95P6_250 g95P6_255)) (@block_merge g95 6 260 10 10 (@block_merge g95 6 260 5 5 g95P6_260 g95P6_265) (@block_merge g95 6 270 5 5 g95P6_270 g95P6_275))) (@block_merge g95 6 280 20 20 (@block_merge g95 6 280 10 10 (@block_merge g95 6 280 5 5 g95P6_280 g95P6_285) (@block_merge g95 6 290 5 5 g95P6_290 g95P6_295)) (@block_merge g95 6 300 10 10 (@block_merge g95 6 300 5 5 g95P6_300 g95P6_305) (@block_merge g95 6 310 5 5 g95P6_310 g95P6_315)))))) (@block_merge g95 6 320 80 1 (@block_merge g95 6 320 40 40 (@block_merge g95 6 320 20 20 (@block_merge g95 6 320 10 10 (@block_merge g95 6 320 5 5 g95P6_320 g95P6_325) (@block_merge g95 6 330 5 5 g95P6_330 g95P6_335)) (@block_merge g95 6 340 10 10 (@block_merge g95 6 340 5 5 g95P6_340 g95P6_345) (@block_merge g95 6 350 5 5 g95P6_350 g95P6_355))) (@block_merge g95 6 360 20 20 (@block_merge g95 6 360 10 10 (@block_merge g95 6 360 5 5 g95P6_360 g95P6_365) (@block_merge g95 6 370 5 5 g95P6_370 g95P6_375)) (@block_merge g95 6 380 10 10 (@block_merge g95 6 380 5 5 g95P6_380 g95P6_385) (@block_merge g95 6 390 5 5 g95P6_390 g95P6_395)))) g95P6_400))
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
theorem g95P7_55 : block g95 7 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_60 : block g95 7 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_65 : block g95 7 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_70 : block g95 7 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_75 : block g95 7 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_80 : block g95 7 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_85 : block g95 7 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_90 : block g95 7 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_95 : block g95 7 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_100 : block g95 7 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_105 : block g95 7 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_110 : block g95 7 110 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_115 : block g95 7 115 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_120 : block g95 7 120 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_125 : block g95 7 125 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_130 : block g95 7 130 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_135 : block g95 7 135 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_140 : block g95 7 140 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_145 : block g95 7 145 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_150 : block g95 7 150 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_155 : block g95 7 155 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_160 : block g95 7 160 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_165 : block g95 7 165 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_170 : block g95 7 170 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_175 : block g95 7 175 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_180 : block g95 7 180 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_185 : block g95 7 185 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_190 : block g95 7 190 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_195 : block g95 7 195 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_200 : block g95 7 200 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_205 : block g95 7 205 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_210 : block g95 7 210 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_215 : block g95 7 215 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_220 : block g95 7 220 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_225 : block g95 7 225 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B7 : block g95 7 0 230 = true := (@block_merge g95 7 0 160 70 (@block_merge g95 7 0 80 80 (@block_merge g95 7 0 40 40 (@block_merge g95 7 0 20 20 (@block_merge g95 7 0 10 10 (@block_merge g95 7 0 5 5 g95P7_0 g95P7_5) (@block_merge g95 7 10 5 5 g95P7_10 g95P7_15)) (@block_merge g95 7 20 10 10 (@block_merge g95 7 20 5 5 g95P7_20 g95P7_25) (@block_merge g95 7 30 5 5 g95P7_30 g95P7_35))) (@block_merge g95 7 40 20 20 (@block_merge g95 7 40 10 10 (@block_merge g95 7 40 5 5 g95P7_40 g95P7_45) (@block_merge g95 7 50 5 5 g95P7_50 g95P7_55)) (@block_merge g95 7 60 10 10 (@block_merge g95 7 60 5 5 g95P7_60 g95P7_65) (@block_merge g95 7 70 5 5 g95P7_70 g95P7_75)))) (@block_merge g95 7 80 40 40 (@block_merge g95 7 80 20 20 (@block_merge g95 7 80 10 10 (@block_merge g95 7 80 5 5 g95P7_80 g95P7_85) (@block_merge g95 7 90 5 5 g95P7_90 g95P7_95)) (@block_merge g95 7 100 10 10 (@block_merge g95 7 100 5 5 g95P7_100 g95P7_105) (@block_merge g95 7 110 5 5 g95P7_110 g95P7_115))) (@block_merge g95 7 120 20 20 (@block_merge g95 7 120 10 10 (@block_merge g95 7 120 5 5 g95P7_120 g95P7_125) (@block_merge g95 7 130 5 5 g95P7_130 g95P7_135)) (@block_merge g95 7 140 10 10 (@block_merge g95 7 140 5 5 g95P7_140 g95P7_145) (@block_merge g95 7 150 5 5 g95P7_150 g95P7_155))))) (@block_merge g95 7 160 40 30 (@block_merge g95 7 160 20 20 (@block_merge g95 7 160 10 10 (@block_merge g95 7 160 5 5 g95P7_160 g95P7_165) (@block_merge g95 7 170 5 5 g95P7_170 g95P7_175)) (@block_merge g95 7 180 10 10 (@block_merge g95 7 180 5 5 g95P7_180 g95P7_185) (@block_merge g95 7 190 5 5 g95P7_190 g95P7_195))) (@block_merge g95 7 200 20 10 (@block_merge g95 7 200 10 10 (@block_merge g95 7 200 5 5 g95P7_200 g95P7_205) (@block_merge g95 7 210 5 5 g95P7_210 g95P7_215)) (@block_merge g95 7 220 5 5 g95P7_220 g95P7_225))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P8_0 : block g95 8 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P8_5 : block g95 8 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P8_10 : block g95 8 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P8_15 : block g95 8 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P8_20 : block g95 8 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P8_25 : block g95 8 25 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B8 : block g95 8 0 26 = true := (@block_merge g95 8 0 20 6 (@block_merge g95 8 0 10 10 (@block_merge g95 8 0 5 5 g95P8_0 g95P8_5) (@block_merge g95 8 10 5 5 g95P8_10 g95P8_15)) (@block_merge g95 8 20 5 1 g95P8_20 g95P8_25))
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
theorem g95G : graphValid g95 (boundsBefore K124) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 10 := lower_forest (g:=g95) (i:=0) (hints:=140033) (before_sound K124 V124) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K124 10 [(95,[]),(111,[84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V124 low95 (by decide +kernel)

def g119Y : Array (Bits × Bits) := #[ (0x4a7e88f2a4db4f2f0cc97e7072a25d08ec23f0b1a544acb47f8dd3147623a3a9,0x205412c70a85410109038f0062011800e42050b18d7008046085531032238381), (0xc293b98a5e33a1a7bed172711ffc506f6706268855839d58b1cf218ccb987a49,0x9402640880209008469050e81550406802062602128186511172008cc8187848), (0xe781f16eabb9d297c3349ca4add5128085cc9afee29cbdee752c80f2089f90bd,0x260c9104a0000801100096200881020110cd93ca60c1b0be202c0062089f00a9), (0x0,0x0), (0x1f11663d37d87c998fe681412316bdd802dcd175bb8ad64dac3362c1e255cd12,0x88400041469010c08f43000121065148001040140a08060104413280c2008d12), (0xb95db997a9af666afc1a3dcfbf19a7c2d2725e4f84b249a30316cf36b84050c6,0x10230008080b811a400821cc561884a0e0002000803209000112c91430405044), (0x3fee0fe174e7bdc5720c443e544aaa7fd93d4fd8786d222ccacb7c0b15ae0d60,0x308082020002c041004001000002003118109482004002a8a08040305840020), (0x0,0x0), (0x0,0x0) ]
def g119C : List ColumnInfo := [(4,0,115,0,8), (2,0,117,0,7), (1,0,118,0,7), (32,0,87,0,7), (16,0,103,0,7), (64,0,55,0,6), (36,0,83,0,5), (20,0,99,0,5), (6,0,113,0,5), (5,0,114,0,5), (3,0,116,0,5), (67,0,52,0,4), (52,0,67,0,4), (7,0,112,0,4), (34,0,85,0,4), (33,0,86,0,4), (18,0,101,0,4), (17,0,102,0,4)]
def g119D4 (_ : Nat) : Nat := 0x930c099504a31b228a92cc986508d9145496694128c6c69aa4b34619423634d525
def g119H4 (_ : Nat) : Nat := 0x3f840aa02
def g119D5 : Nat → Nat
  | 0 => (0xfca5514049503f49355012540fe44c5044510387e5859d344063b8a1674d101 + ((0x503e4d359192540e3b9e146495038ec785192540f8b5514649503e4d35519254 + ((0x2540eb98616749503f4a084d52540f9399d3549503e4c674d52540fd241d3549 + ((0x751503e1d644d54540fc64113551503a6d58d9d2540e9b9616749503aae4859d + ((0x5052544fd14d541495138ee2851e5640e3b56227519038ee2859d4540e3d8616 + ((0xd646495138ee785192544e3b1e14649513e2d545192544f934d54649513f2554 + ((0xa0859d2544fd18613549513e4e674d52544f9319d3549513f45174d52544f934 + ((0x875913551513f15144d54544e9b5636749513a6e5859d2544eab9216749513ae + ((0x4e2d458d9254123b8a147959138ed5889d4644e3b8a167515138fa0859d4544f + ((0x412b98616749504f2a08515254138b99d4549504e2c6751525413ca41d454950 + ((0x9514e2d458d9254523b8a13795904a6d58d9d254129b9616749504ace3859d25 + ((0xd25452ba8216749514f2618515254538b99d4549514e2c6751525453c945d454 + ((0x2681534ce617899054d23b8a13795914a6d58d9d254529b9616749514ace3859 + ((0x7515254d23b8a167855348ed7889a154d33a81e26455348ee2859e054d23b5e2 + ((0x99d3549534f0d474d5254d3c34d54549534f0e38515254d38b99d4549534f0d3 + ((0xae4859d254d3634dd4749534e4e38595254d38b9216549534f0e484d5254d393 + ((0x6b38e14749a15aae484dd26856b38e14749a05aae484dd26816b38e16749534a + ((0x25e4e3651935496d38e1164d525b6a0845935496d38e1064d525b66184193549 + ((0x5496d3463634d525b4d08d8d354974bdd2464d525e4e3691935496d38e1464d5 + ((0x8d525d2f7451535496d38e1474d525b6a0845d35496d9861074d525b4d48d8d3 + ((0x5945496da8211651525b2e4841945496d98610651525d2d7491a35496d38e146 + ((0x36451525d4f738d9454978b91a3651525b2e484d9454978b9193651525b2e484 + ((0x484da45496da8211751525b661841d45496cb4e36451525b2d18d9145496cb42 + ((0x391c37519259ea0845e3649679861078d925d8e3711d36497535ce3691525b2e + ((0x8fa0845e464d63d8610791935d4e3849e454d67a82117919259e61841e464976 + ((0x2ab9213749a458fa0845e365163d861078d945ace3851d268d78b9212651635 + ((0x5b8b11562944f899126234438810f61d43304e0901081e0360600a81200c00c0 + ((0x15c2ac540a514427c4e09912c24c4808d11421c3fc738e11b6354678c91862f4 + ((0x24388590820a4087f8fc1f23d8798f01da3966ccd69a734266cca98f31260cba + ((0x1ec257d2f45dcba1712dc5acb41652c457ca994ba885049f13224c48c9011422 + ((0xe89ce396720e29c237e6f0da5b1b5d6aed45a5b4567ece599b2d64ec858db156 + (0x81108400105207408804ff1fb3f07d4f91ef3cf792f0dda3ae750 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0x110122388200000000000000000000000000000880911c21 + ((0x40000c2184000000000000000000010c121b8820000000000002182437084000 + ((0x4808000000000000001108616801d0020000c22040c218 + (0x28c100052020000000000000002304000000 <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g119H5 (_ : Nat) : Nat := (0xac029818b0080e89800c816e11c2501c43b807b20a40108401110d108842881a + ((0x5398a2c13309837c86bb7536525b0db2f40109aa1bbb380069f0000aa8c08007 + ((0xb00200000051751e9a6f1d00068bbbd0002159a4d4218a98ca33099dc1cad2a2 + ((0xc07a00004aed067123a9000180eb95872179ba8007250006bdc2fc0d1bed2a19 + ((0x93428382d8301a39883b50a1a963989b82143bbe8e28c799032f9d8004100003 + ((0x56abfb138361103083b12c893d91c3f2a830a6a7534ca8a14d20cbce908b5bbf + ((0x8fe36eb23800000000002ae6ba31cc04000312b8b40f7a1000709000101f84d8 + ((0x29e48291870ea3c000507b85fa780019c4b1896938e9509fd2b0000005a40006 + (0x74179a208d3e6a6523 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g119D6 : Nat → Nat
  | 0 => (0x51440fea98a2881fb904451039fc6ea32033f91d364067eb3a6880dee274d101 + ((0x1f4d3549503eda8a92a07bb9192540f76a324a81fe94049503bf40e8a207bdd8 + ((0x8a2a07d74d54540f77b3a4a81eee6749503ddace92a07bb19d2540ff483a4a8 + ((0x40feca02a681fd94044d039fccea2a073f59d4540efc83a8a81ebd6451503f72 + ((0x94654103bf4aea0207be9594040f7cab28081fda0754d03dbc8ca9a07b751953 + ((0x32073f95d4640f7713a8c81cee27519039fc2ea32073f51e1640f7d232a081ef + ((0x7d03aac81cfe4755903dec2eab2073d85d5640e7eabc8c81cfd1791903bdc4ea + ((0x49513bec2e82227bed810444fda8a20889cfd4795903bf40eab2077d85d5640f + ((0x7bb19d2544ff28ba4a89f4d3549513eda8a92a27bb9192544f76a324a89fe541 + ((0xba8a89ebd6451513f6a28a2a27d74d54544f77b3a4a89eee6749513ddace92a2 + ((0x13fac2ea9a27b79195344f6ea32a689fd54154d139fccea2a273f59d4544efa8 + ((0x81d4644e7ea3c0c89ef64654513dea8ca8a277d95d4144f7b2b28289ef556505 + ((0xc89cfd57919139fa0f232277b89d4644e7f2ba8c89eee27519139dc4ea32273f + ((0xfa8f2b2277d85d5644efd03aac89ef617559139fc8eab227be81d5644e7d03aa + ((0x2541376b3a4a826ec6749504fd20e92a09cb51525413b69aa4a826ee36495049 + ((0x6fa3654104f740eaa209af8d9544127f33a6a8273d454d504ddece92a09bb99d + ((0xeab209bd85d564127b0baac824fd578d9049fa2f1b2097b89d364127e9bc2c82 + ((0x53b69aa4a8a6ee36495149fa6f2b2097e81d56412fb0baac826fa07559049fc6 + ((0x454d514ddece92a29bb99d2545376b3a4a8a6ec6749514fca2e92a29cb515254 + ((0x2297b89d364527e9bc0c8a6f63654514f6c2eaa229af8d9544527f33a6a8a73d + ((0xd03aac8a6f617559149fc6eab229be81d564527d03aac8a4fd578d9149fa0f1b + ((0x1534bda4f02a69bb89a054d2fb0ba0a9a6ee26415349fa6f2b2297d85d56452f + ((0x7b49e154d3771342a9a5fa0745534ddc4c8aa693f59e054d2ee9bc0a9a5bd478 + ((0xa4a9a74d3549534f5a8a92a69cb515254d27eb3c2a9a5dd3785534b7a8f0aa69 + ((0x4ddcce92a69bb59d254d3e69ba4a9a7ad4749534ddaca92a699b595254d3e69a + ((0x5d564d27f03aac9a4ed5789934f3c8ea9a69e78dd544d3ce9aaa89a71d355513 + ((0x2eee3749a05dda6e9340bb78dd564d35f23aac9a6ee27559349dc4eab2693f8 + ((0xa8e9342bbb8dd26857769ba4d0acfe3751a059fc8e9b40bbb91d2681776a3a4d + ((0x5497b68b26a92f6e064d525eda0c9aa4b3f8dd468567f23a6d0aeee4749a15dd + ((0x6d174d525edc0e9aa4bdb41d35497a7b1a6a92f6e464d525eda8c9aa4bdb8593 + ((0x9aa4bf3d8d35497b6a2a6a92f6e474d525adc8e9aa4bdb51d35497b70ba6a92f + (0x7b68b28a92f6e0651525eda0ca2a4b5b51e35497b72346a92f6d468d525bdc8e <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0x751525edc0ea2a4bdb41d4549797b228a92f6e3651525eda6ca2a4bdb8594549 + ((0x4b7b8dd45497d7b228a92f6e3751525adc6ea2a4bdb4dd45497b70ba8a92f6d1 + ((0x1ba0c92fe61741925bcc2e8324bfad8106496b69bc8a92f6e3691525eda6d22a + ((0x925fd40e8b24b7a81d16497f3b0a2c92ded4781925bda6f0324b7b91d06496f7 + ((0x3d8d36497772326c92eed464d925bda8f0b24b7b4de16496f723a2c92dee3745 + ((0x6c92dee474d925f5c8e9b24b6b91d36497d623a6c92dee174d925bdc0e9b24bf + ((0xbdc0ea324bebd9146496f6a3c6c92ded178d925bda0f1b24bbb91a3649776a34 + ((0xe46496f683c8c92dee3751925f9c6ea324b738dd46497e61ba8c92dee1751925 + ((0xad6d2791535bbc6ea2a6bafd91454d7af1ba8a9af3f6451535bda6f2324b7b45 + ((0x2f2326b3f41e464d6f713a8c9acfd4785935bf40e8b26b3f51e064d6fb0ba0c9 + ((0x516fd03a2ca2cfd3781945bec2e8328bbb91d268d776a3a4d1ae6d26516359fa + ((0xb001c000ddc6e9348bbb4dd269167e8bc6ca2cfd078d945bdc4e9b28b3f4de16 + ((0x29c14009d04d025c12808904101cc0b8055029013c09004101d00bc04801d00 + ((0x49c238119089042c21010107f03dc1d80e9073036c1b00d5067032c1800bd059 + ((0xc3801b50d7067c3101810bf05ec2e816d0b3056c2a814d0a504fc2781350950 + ((0xc458229111087c43020d105081c3f81f90fb07bc3d81e90ef074c3981c90e307 + ((0x5882c115f0acc55829d14309fc4f827513709ac4c025d12b092c49023d11d08c + ((0x9833d1930c7c6383151870c2c6002fd17b0bac5d02dd16d0b5c5a02cd1650b1c + ((0x83b51d70eac74039d1cb0e2c71037d1bd0ddc6e036d1b50d9c6c83611af0d4c6 + ((0x49123d119c8a8441217109c840419207101c7f83f51f70f9c7c03d51e70f0c77 + ((0x712b7158cac05552a514fca68529293148ca3851128313cc9a84c125d12ac938 + ((0x5315187cc206052fb179cba85c52df16bcb505992cb164cb205852c115dcae85 + ((0x3991c9ce3070d37f1bbcdb86cd3631adcd606a134519fcce066532d193cc8863 + ((0xd203d0087f93f71f7cfb87d93e71f0cf707ad3cf1e1cef876d3b11d5ce9873d + ((0xd23bd1d88e946b231d1708a944f222d100871431215d0a885141f20ad04081d4 + ((0x26cd3409994c9262d3109854c125fd2d89654af255d2a0941499248d23090947 + ((0xc182010a04842c10704105c1000f0419ed4f1276d3a89cd4e5271d3889c14df + ((0x40020421081410000004341091010944610c2c15130b84543040010c10404 + ((0x8001042f8020009842000010004061040a104168420000341080001410204842 + ((0x4342091010844620c2c15138b04543040010c104040c1820108001000400b000 + ((0x800004001018810288105a2080000d082000050400008002042208141000000 + (0x4441090c10943610c2c150f0b845440400004001002c002000810be0080c101 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 2 => (0xc2c150f8b045440400004001002c002000410be008002610800284100000000 + ((0x410004001002c002000810be0080c101080028810000000004442090c1084362 + ((0x3017110c400040c10404330c20c070f002a20400103041010cc308301c3c00a8 + ((0x3010c07430c30191030c000833130e800050c05c343103015130c40c05c44410 + ((0x8300020c6008000301040308100c2050403e010301510120c0f8070cc3a00010 + ((0x10824620c9010924610c000064630806463080000646308064630b80002e0000 + ((0xa4630c310020561082d898430562082d8984324c0400e9092000040624630c90 + ((0x3620c8c10923610c2c1c16918c507630830918c363230b00002632308158c206 + ((0xc310020561082d898430562082d8984323c0400e8c8e000040764230c8c1082 + ((0x48420bc00826840030b060564a314199020c64230e8c8c2c00008148c20764a3 + ((0x40ca4242310908c2000082308209028822082f00208a2000c000248c209240a2 + ((0x8830924210d8c8c20c246323101c8c287a4230e1e9300387a4080001c928c00 + ((0x208c8830923210c189028624a30e1a8f00386a3080001a908c0040624630c209 + ((0x4463082c17128c402040410c040000002c17128c4000400105041410764230c + (0x1910c202040410c04000000 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g119H6 (_ : Nat) : Nat := (0x63810108020090206142820000300163c6001c28001200000404000060a20086 + ((0x1c10603001a18002000051e0c1822e1800800080805a284020008101020401 + ((0x1b5f71a385927211280005010618a07060068f7e0008122804211008e0004204 + ((0x419a3b1d72e9a0001114d484f5d0e80029afa628366be400008b41a0b57df142 + ((0x25c3b4000a1fa6fe9771290db57f095be1a0303288001d5f9156551c010b54f2 + ((0x698e6048b0a128002c001260b77a9cf025a7158253a4c8d102b5012d9c6ce4fb + ((0x699e070000001ee4f0b68098cdaa30000001cd62b5406f9fa595463b3 + ((0xaffa068f7c83eaadd228310007831c4149c5474b080002c000022795cbc98000 + ((0x4f87bc179537311c506c704dec7a8d4000000489cc398a53428000126267a208 + ((0x309b8cb000000357164c77e73d1142000d85d23d8f38b416f00000014dd00038 + ((0x124710000780414fa5ca56f053628708769da229090b7e30800018b207587b1d + ((0x667b32753f2430002340dc1ae8b41a8f14f700a721206d21cf05775da59 + ((0x340530032bb4b0e8ab3e345d553c47a6c38aa1c563a908f4738b669d05d1b700 + ((0xe54013621c8dfe4072c8000001c7d5467c240006f10002c77d45cf323b702283 + ((0xea10d1b584a6000771a8ac977eda28c6404000000e3d52341780003021bc3635 + ((0x10000002dfb23235820f8001c95b773a5e06fd19a642826237c78c3868fe05c2 + ((0x7b4945bc8223a8002d8d02fc0c493a9fe89006a0002c0d48002bd384c448d + ((0x4080a5c70a64459617a43dc7f0000000000000a862b0c00000020ab00d222000 + ((0x2312586bec1b7b5aa1047eb305eb12a99ba55d087920cd2f12232cb640a5c868 + ((0xe3e90bfeb1d89d227cdc00057da39fe0c03b0004b3ae3fe0fa66545b5584e602 + (0x3b <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g119D7 : Nat → Nat
  | 0 => (0x3fe50103f754d03f744d03ff51503fb49503ff45103bf51901bf4d901ff4d101 + ((0x13bf95903ff55903bf55903bf91903ff51903bf51903bf85903ff45903fe5410 + ((0x913bf51913bf81913ff41913fd54513fd50513f754d13ff51513fb49513ff411 + ((0x4104ef55104ef45104ff4d504fb49504bf95913ff55913bf55913bf91913ff51 + ((0x4d514fb49514bf95904ff55904bf55904bf8d904ff4d904bf85904ff45904fe5 + ((0xf95914ff55914bf55914bf8d914ff4d914bf81914ff41914fd54514ef55114ff + ((0xbf55934bb89934f754d34ef55134fb49534ff85534ff45534ff81534ff41534b + ((0x5db4d525bf51a15bf4da15bb49a15be81915bf51a05bf4da05bb49a05bd85905 + ((0x25fb85925fb45925fb81925fb41925db91525fb51525db51525db8d525fb4d52 + ((0x935bf81935ff41935df91535ff51535df51535fb91925fb51925fb8d925fb4d9 + ((0x1a35bb49a35df51635ff91935bf91935ff51935ff85935bf85935ff45935ff81 + ((0x8d945bf8d945ff4d945ff85945bf85945ff45945ff81945bf81945ff41945bf5 + ((0xd7465a2da14389784401d40cb054426c0f806781f0052000bf4da45bb49a45ff + ((0x10fd27ab3af9cf4dfe6ac33e18a4bac5a62b414709bc4c324291708203ee1d80 + ((0xd912c4b5fc2f216eab45583ab2555ca7051228093889714a0a3b918a887424a0 + ((0x26f0f9853414e02afde7c5bce1df4ec37463971c58dfc6e2b639abcd2767bb2a + ((0x4d57dab1545a9db4afa3fd13e8313e89d8ce0668730c9674a5e4b32068e4462a + ((0x2805c9f64031af899c3be1730217e7be65e02eaf70bb66da3ecdb62fb06d7cab + ((0x18280822381210228f1c2c505088e141c000b224058a0a901c28380016305238 + ((0x204460c1414380a222c284840b0e02089016121024207012441820c585890e16 + ((0x111c2c2070002c88b0b101c204840e00059120290811488b0b1020243808223e + ((0x222c2a11088b880e101c00082216223070816103800164478c460d00c4478c0b + ((0xc284c5040e0208030218b0b121e285050104078282045222e2040708101c000a + ((0x80d10282070002c89014881411880b0b1022203808203a204460e1220380a202 + ((0x4100b11183c40a081c000b2038623068062038605888f1028380016405858 + ((0x8091e101062c2c4870b0c140410171020305040e0005101615108405c4060a0e + ((0x42070002c78e148408a3c585860c121c040f16141c205870103c70b070812103 + ((0xa11078b090e101c00081e15243070816103800164478c481100c3c585090e102 + ((0x40e16141e28207010382010c585890f142828081e2c2430708101c000a1e2c2 + ((0x1c000b2038624088061c2c284868814103800163c70a440a08c38585860d101c + ((0x1218030e161218305040e00050e161510838584860a0e00040e0a92183c40a08 + (0x78061816243850500e30284860e0201c60b86880c018605090c1c04038c170c <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0x5000205c5c98e121c038c890c101c000719121e2c28061814243078061816204 + ((0xe2e4c68a0e01c585088c1c205840e00058b0a90203840b081c000b1617263858 + ((0x3000102c284460f10282070002c58548101e205040e00058b0b931e282800102 + ((0x2c585c88f16180008161c2a4c78b0c020585498d1e245850c00058b0a931e2c + ((0x716911a2c28600020589488d1218038b0c17223c5860102c2e4488f122c28600 + ((0x911a243006498d1a2430000e1d223448600c2d223c4890c00040b10911a24300 + ((0x8b440908a305858811183c04058811183c03058811183c0364488d121800070c + ((0x8150810c5c4080f10242070002880b448408a151020c5c4080d102c207000288 + ((0x50b0b131e2c280010305858811183c0405088c1891022306080e00040c460d00 + ((0x1c2d12102285440831612183440b081c000a1e2d1024228b0b1022306080e000 + ((0x80a90243062a4090c18203800103120440205420431612183c409081c000a + (0x5854812183040700028585c90f1614 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g119H7 (_ : Nat) : Nat := (0x504e4c320b0000000813000600011407420400810422c40400082432c5407002 + ((0xea200114d950007c91b0746820000026158cdb0600af0003113441aa8ed8f7a5 + ((0xe474e05000042de54d281314e0022a71ffa400330144934003c3399b24f382d + ((0xadb279833b40b8b399acbe82b22283664126f303e8d72909257183e370851580 + ((0xca0cbd6d0000000031d4ae6b4b2b43775a1366532faa42cc088fed5c709f8c0c + ((0xee2800000000000e3001b6945000c94003b0dcf321cd0007dd722af60c137b3c + (0xefa58ab659a3be33dc68b9ea535800f5e78adc8002dc000003a63b297 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g119D8 (_ : Nat) : Nat := (0x7f917fa8bfe35fe9afb497fc2bfd15ff02ff417fa69fd14fe827f44ffa07fd01 + ((0x1420c00165942c82461840c0017e9715a15f5655051d3e4d52d0901b04809000 + ((0x47162c82071040c00167962c82061420c00168162891871040c0016896289186 + ((0x461c41030005962c82461850830005962c82461850830005982881c41420c001 + ((0x1050830005962891871050830005962c91c50803962c82461c41030005962c82 + (0x162c82071050830005962c8207105083000596289187 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g119H8 (_ : Nat) : Nat := 0x33d8b0007c3d82000b4e001d3c8a99f906cf7880
def g119D9 (_ : Nat) : Nat := 0x8310402bf
def g119L : Nat → Packing
  | 4 => (4,5,5,0,0,5,0,g119D4)
  | 5 => (133,4,5,0,0,11,0,g119D5)
  | 6 => (288,3,5,0,0,13,0,g119D6)
  | 7 => (112,2,5,0,0,13,0,g119D7)
  | 8 => (15,1,5,0,0,10,0,g119D8)
  | 9 => (1,0,5,0,0,1,0,g119D9)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 2 5 2 6 2 0 g119H4 h
  | 6, h => lookupWord 47 159 5 12 8 0 g119H5 h
  | 7, h => lookupWord 98 342 7 13 9 0 g119H6 h
  | 8, h => lookupWord 43 138 6 11 7 0 g119H7 h
  | 9, h => lookupWord 5 18 3 8 4 0 g119H8 h
  | _, _ => none
def g119 : Forest := ⟨119,9,fun i => g119Y[i]?.getD (0,0),g119C,[[]],g119L,g119I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P4_0 : block g119 4 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119B4 : block g119 4 0 4 = true := g119P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_5 : block g119 5 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_10 : block g119 5 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_15 : block g119 5 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_20 : block g119 5 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_25 : block g119 5 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_30 : block g119 5 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_35 : block g119 5 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_40 : block g119 5 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_45 : block g119 5 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_50 : block g119 5 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_55 : block g119 5 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_60 : block g119 5 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_65 : block g119 5 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_70 : block g119 5 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_75 : block g119 5 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_80 : block g119 5 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_85 : block g119 5 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_90 : block g119 5 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_95 : block g119 5 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_100 : block g119 5 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_105 : block g119 5 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_110 : block g119 5 110 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_115 : block g119 5 115 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_120 : block g119 5 120 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_125 : block g119 5 125 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P5_130 : block g119 5 130 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119B5 : block g119 5 0 133 = true := (@block_merge g119 5 0 80 53 (@block_merge g119 5 0 40 40 (@block_merge g119 5 0 20 20 (@block_merge g119 5 0 10 10 (@block_merge g119 5 0 5 5 g119P5_0 g119P5_5) (@block_merge g119 5 10 5 5 g119P5_10 g119P5_15)) (@block_merge g119 5 20 10 10 (@block_merge g119 5 20 5 5 g119P5_20 g119P5_25) (@block_merge g119 5 30 5 5 g119P5_30 g119P5_35))) (@block_merge g119 5 40 20 20 (@block_merge g119 5 40 10 10 (@block_merge g119 5 40 5 5 g119P5_40 g119P5_45) (@block_merge g119 5 50 5 5 g119P5_50 g119P5_55)) (@block_merge g119 5 60 10 10 (@block_merge g119 5 60 5 5 g119P5_60 g119P5_65) (@block_merge g119 5 70 5 5 g119P5_70 g119P5_75)))) (@block_merge g119 5 80 40 13 (@block_merge g119 5 80 20 20 (@block_merge g119 5 80 10 10 (@block_merge g119 5 80 5 5 g119P5_80 g119P5_85) (@block_merge g119 5 90 5 5 g119P5_90 g119P5_95)) (@block_merge g119 5 100 10 10 (@block_merge g119 5 100 5 5 g119P5_100 g119P5_105) (@block_merge g119 5 110 5 5 g119P5_110 g119P5_115))) (@block_merge g119 5 120 10 3 (@block_merge g119 5 120 5 5 g119P5_120 g119P5_125) g119P5_130)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_5 : block g119 6 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_10 : block g119 6 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_15 : block g119 6 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_20 : block g119 6 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_25 : block g119 6 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_30 : block g119 6 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_35 : block g119 6 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_40 : block g119 6 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_45 : block g119 6 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_50 : block g119 6 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_55 : block g119 6 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_60 : block g119 6 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_65 : block g119 6 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_70 : block g119 6 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_75 : block g119 6 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_80 : block g119 6 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_85 : block g119 6 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_90 : block g119 6 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_95 : block g119 6 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_100 : block g119 6 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_105 : block g119 6 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_110 : block g119 6 110 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_115 : block g119 6 115 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_120 : block g119 6 120 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_125 : block g119 6 125 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_130 : block g119 6 130 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_135 : block g119 6 135 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_140 : block g119 6 140 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_145 : block g119 6 145 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_150 : block g119 6 150 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_155 : block g119 6 155 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_160 : block g119 6 160 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_165 : block g119 6 165 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_170 : block g119 6 170 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_175 : block g119 6 175 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_180 : block g119 6 180 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_185 : block g119 6 185 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_190 : block g119 6 190 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_195 : block g119 6 195 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_200 : block g119 6 200 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_205 : block g119 6 205 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_210 : block g119 6 210 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_215 : block g119 6 215 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_220 : block g119 6 220 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_225 : block g119 6 225 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_230 : block g119 6 230 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_235 : block g119 6 235 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_240 : block g119 6 240 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_245 : block g119 6 245 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_250 : block g119 6 250 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_255 : block g119 6 255 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_260 : block g119 6 260 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_265 : block g119 6 265 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_270 : block g119 6 270 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_275 : block g119 6 275 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_280 : block g119 6 280 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_285 : block g119 6 285 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119B6 : block g119 6 0 288 = true := (@block_merge g119 6 0 160 128 (@block_merge g119 6 0 80 80 (@block_merge g119 6 0 40 40 (@block_merge g119 6 0 20 20 (@block_merge g119 6 0 10 10 (@block_merge g119 6 0 5 5 g119P6_0 g119P6_5) (@block_merge g119 6 10 5 5 g119P6_10 g119P6_15)) (@block_merge g119 6 20 10 10 (@block_merge g119 6 20 5 5 g119P6_20 g119P6_25) (@block_merge g119 6 30 5 5 g119P6_30 g119P6_35))) (@block_merge g119 6 40 20 20 (@block_merge g119 6 40 10 10 (@block_merge g119 6 40 5 5 g119P6_40 g119P6_45) (@block_merge g119 6 50 5 5 g119P6_50 g119P6_55)) (@block_merge g119 6 60 10 10 (@block_merge g119 6 60 5 5 g119P6_60 g119P6_65) (@block_merge g119 6 70 5 5 g119P6_70 g119P6_75)))) (@block_merge g119 6 80 40 40 (@block_merge g119 6 80 20 20 (@block_merge g119 6 80 10 10 (@block_merge g119 6 80 5 5 g119P6_80 g119P6_85) (@block_merge g119 6 90 5 5 g119P6_90 g119P6_95)) (@block_merge g119 6 100 10 10 (@block_merge g119 6 100 5 5 g119P6_100 g119P6_105) (@block_merge g119 6 110 5 5 g119P6_110 g119P6_115))) (@block_merge g119 6 120 20 20 (@block_merge g119 6 120 10 10 (@block_merge g119 6 120 5 5 g119P6_120 g119P6_125) (@block_merge g119 6 130 5 5 g119P6_130 g119P6_135)) (@block_merge g119 6 140 10 10 (@block_merge g119 6 140 5 5 g119P6_140 g119P6_145) (@block_merge g119 6 150 5 5 g119P6_150 g119P6_155))))) (@block_merge g119 6 160 80 48 (@block_merge g119 6 160 40 40 (@block_merge g119 6 160 20 20 (@block_merge g119 6 160 10 10 (@block_merge g119 6 160 5 5 g119P6_160 g119P6_165) (@block_merge g119 6 170 5 5 g119P6_170 g119P6_175)) (@block_merge g119 6 180 10 10 (@block_merge g119 6 180 5 5 g119P6_180 g119P6_185) (@block_merge g119 6 190 5 5 g119P6_190 g119P6_195))) (@block_merge g119 6 200 20 20 (@block_merge g119 6 200 10 10 (@block_merge g119 6 200 5 5 g119P6_200 g119P6_205) (@block_merge g119 6 210 5 5 g119P6_210 g119P6_215)) (@block_merge g119 6 220 10 10 (@block_merge g119 6 220 5 5 g119P6_220 g119P6_225) (@block_merge g119 6 230 5 5 g119P6_230 g119P6_235)))) (@block_merge g119 6 240 40 8 (@block_merge g119 6 240 20 20 (@block_merge g119 6 240 10 10 (@block_merge g119 6 240 5 5 g119P6_240 g119P6_245) (@block_merge g119 6 250 5 5 g119P6_250 g119P6_255)) (@block_merge g119 6 260 10 10 (@block_merge g119 6 260 5 5 g119P6_260 g119P6_265) (@block_merge g119 6 270 5 5 g119P6_270 g119P6_275))) (@block_merge g119 6 280 5 3 g119P6_280 g119P6_285))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : block g119 7 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_5 : block g119 7 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_10 : block g119 7 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_15 : block g119 7 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_20 : block g119 7 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_25 : block g119 7 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_30 : block g119 7 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_35 : block g119 7 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_40 : block g119 7 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_45 : block g119 7 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_50 : block g119 7 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_55 : block g119 7 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_60 : block g119 7 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_65 : block g119 7 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_70 : block g119 7 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_75 : block g119 7 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_80 : block g119 7 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_85 : block g119 7 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_90 : block g119 7 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_95 : block g119 7 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_100 : block g119 7 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_105 : block g119 7 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P7_110 : block g119 7 110 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119B7 : block g119 7 0 112 = true := (@block_merge g119 7 0 80 32 (@block_merge g119 7 0 40 40 (@block_merge g119 7 0 20 20 (@block_merge g119 7 0 10 10 (@block_merge g119 7 0 5 5 g119P7_0 g119P7_5) (@block_merge g119 7 10 5 5 g119P7_10 g119P7_15)) (@block_merge g119 7 20 10 10 (@block_merge g119 7 20 5 5 g119P7_20 g119P7_25) (@block_merge g119 7 30 5 5 g119P7_30 g119P7_35))) (@block_merge g119 7 40 20 20 (@block_merge g119 7 40 10 10 (@block_merge g119 7 40 5 5 g119P7_40 g119P7_45) (@block_merge g119 7 50 5 5 g119P7_50 g119P7_55)) (@block_merge g119 7 60 10 10 (@block_merge g119 7 60 5 5 g119P7_60 g119P7_65) (@block_merge g119 7 70 5 5 g119P7_70 g119P7_75)))) (@block_merge g119 7 80 20 12 (@block_merge g119 7 80 10 10 (@block_merge g119 7 80 5 5 g119P7_80 g119P7_85) (@block_merge g119 7 90 5 5 g119P7_90 g119P7_95)) (@block_merge g119 7 100 10 2 (@block_merge g119 7 100 5 5 g119P7_100 g119P7_105) g119P7_110)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P8_0 : block g119 8 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P8_5 : block g119 8 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P8_10 : block g119 8 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119B8 : block g119 8 0 15 = true := (@block_merge g119 8 0 10 5 (@block_merge g119 8 0 5 5 g119P8_0 g119P8_5) g119P8_10)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P9_0 : block g119 9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119B9 : block g119 9 0 1 = true := g119P9_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g119B4
  · exact g119B5
  · exact g119B6
  · exact g119B7
  · exact g119B8
  · exact g119B9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 10 := lower_forest (g:=g119) (i:=0) (hints:=2229249) (before_sound K95 V95) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K95 10 [(119,[]),(123,[50])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V95 low119 (by decide +kernel)

def g125Y : Array (Bits × Bits) := #[ (0x2c106d1e49bd67f0665df8ea31b8aa43522cd9bee83a6368469ca84b9d02f72c,0x38c0be1f0b140284e54e48f2098f884209bc1874c812734ac630a00b8d02772c), (0x0,0x0), (0xd477222d9d90721c17eb3d2c43eeb01c2e0de0059678fcdfca1a7243628e2399,0x21150806200040302833090ce080341422004001443878068000624242062098), (0xd17d9d9f5e97eac79a04159600c2a1d272fa36c1a3d5a3e996cfdc9bfad14402,0x202116952f02041400010010442010050da0f0002418389068c0891b0d04400), (0xcbec51fe6b2e3b19673d0ed319f554af6153463da904ce167f90869c05282dc6,0x8040040009081a0003c40410102508820101000ca80004001110800c01080906), (0x24bbc2ddf3db9b47b8ee6be4de0153098cec34d61ead3fc07165a9240c75423d,0x8a0e01004020484040020e00a000009080030c200060040602100200c210221), (0xaf8cfc70697ebdb05117c369e6580ff6b3019f2a593249b925fd33e0d1c69860,0x5090160f020614b10310301a450060022028500156108b400cc53c050c48040), (0x0,0x0), (0x0,0x0) ]
def g125C : List ColumnInfo := [(1,0,124,0,8), (65,0,60,0,7), (8,0,117,0,7), (4,0,121,0,7), (32,0,93,0,7), (16,0,109,0,7), (33,0,92,0,5), (17,0,108,0,5), (12,0,113,0,5), (9,0,116,0,5), (5,0,120,0,5), (97,0,28,0,4), (81,0,44,0,4), (73,0,52,0,4), (69,0,56,0,4), (13,0,112,0,4), (40,0,85,0,4), (36,0,89,0,4), (24,0,101,0,4), (20,0,105,0,4)]
def g125D5 (_ : Nat) : Nat := (0x4be144d244d112aba484d90444bf044d3241112ada385190344be84514240d12 + ((0x112da5274513444ba558d144d112f85234513444b6945d244d112e8d63491344 + ((0x3444a3b8a1674d112dc52744d3444b7145d234d112e95135913444ba348d644d + ((0x650912bc64844d3244b7191d134c912ec5135193244a3e422674d1128f61859d + ((0x59d1440e5e96167451039ea2859d1440ee98e11450912da6374514244ba94513 + ((0xe267491039da3859d2440e5e96167491039f21859d2440e764e267451039da38 + ((0xa3845d4640e9e9611751903aea2845d4640f2edd14649903cbb745191640e764 + ((0x9e9616741113aea2859d0444eb68e12751903a7a5849d4640ebc8612751903ad + ((0x3e8d325912444f654dd1449113f85324512444eae5236741113aba4859d0444e + ((0x48f3985c2751913b96284514344f6589d1450d13f91074514344fa54522650d1 + ((0xd23e8d248594348eae5236741123aba4859d0448e9e9616741123af21859d04 + ((0x9064d2ba8a11641934ce62705d4648ee38612450d23d8e174914348fe241d245 + ((0xa224c841d46615c480e42a0901503c00c7a5841e264d31e9610785934af21849 + ((0xd5b95f5654a4ed354bd2948d1d45d1142d053fcf93cced39ce136ccc318c02c4 + ((0x9925591a378c62b896047f9f87c9ec799e0769d46cdad69da166d9563d8960d7 + ((0x41000018202040a08141018204042208081020210040210201081 + ((0x8250dc21800000000000000107820800107820800000000000000 + (0x410083a1074208000104a138430 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g125H5 (_ : Nat) : Nat := (0xb91f440c000d88601de5c340114000001c046040040460c11c0000100000004 + ((0xd69c86001f440d6c95000a5773bbb4f502f257ec894d5d003fbbe400c6000e3a + ((0x5a00000003428ac00745b11a696ab4ea0000000268f4b2f4e9a6dd4f67f64 + (0x516a51fd6385e618f0243327ef6f8af0578464003241e00000a4000 <<< 256)) <<< 256)) <<< 256))
def g125D6 : Nat → Nat
  | 0 => (0x90444b7cb3a06895fa4740d12bf28e81a25be5190344bf8a0a06897e94240d12 + ((0x97b5144d112f5a489a225be59d0444afd1ba08896f93641112fe26282225fa4c + ((0xce9a2257d45d3444af693a68896dd634d112faa269a225f348d3444b5eb22688 + ((0x44bf298a84895ee474c912f8a2699225bb5193244bf2a0a64894fe674d1129fa + ((0x63750512dea6ca0a257d91d3144b7aa3262895ee3750912f4a28a1225bb4d942 + ((0x22077e99d1440efcb3a2881dfa2745103f72488a2073f8dd4644a7f23a6c895f + ((0xfd23a2c81dfa2745903df28c8b207be4991640efd33a4881df96749103bf42e9 + ((0x51903df24ea3207be85d4640f7c8ba8c81dfa4749903bf42e93207be5192640e + ((0x7f648d0444fbd2ba8c81d7a5751903bf44ea32077e85d4640f3d2ba8c81efa27 + ((0x924889ebd6449113f6a2892227e74d12444f7db3a0889ef96741113df44c8222 + ((0x13dbc4ca1a277791d2344f6f2324689edd4648d13faa8291a27774dd2444fe69 + ((0x51e2644efb13a8289ef62650513fac2ea1a277789d4344fec83a8689f951450d + ((0xc89dee2751913dec2ea32273f89d4644f7713a8c89cee2751913dd84ea32273f + ((0x5a488a247e74d11448f7db3a0891ef96741123df42c822473f49e4644efb0ba8 + ((0x4248fe713a8691dde1750d23fb20ea1a47e34914348f6f0b28691ebd6445123f + ((0xcfe1751923dec2ea32473d85d4648f7a0ba8c91cfd4785923bdc2ea1247bb859 + ((0xe8b209be4d9164137c9322c824fd1791923bdc4ea32477d85d4648f7713a8c91 + ((0x12fd13a6c825fa174d904bf46e932097e85d264137c9b24c825fa3745904bf44 + ((0x274d114f720e9a229af89934452df1ba488a6be3649114ef4ae9b2095e95d364 + ((0x249af859344927e93c6c8a5f6174d914bdc4e9b2293f4de26453db0ba688a5be + ((0xe8bc6c925ee274d924bec2e9b2493f4de16493d713a68925be174d124f720e9a + ((0x5934bdc4e8b269de95d064d37d1320c9a6f92641934df42c83269be459064d27 + ((0xbe41e264d27c83c4c9a5f61749934bf20f0b2693f49e164d37c83c2c9a4f9078 + ((0x5e05705405104a04303c03502e02702001500e0070005f907899349fa2f13269 + ((0x11911611310c1050fe0f70f00cd0c60bf0b809508e08707c07907206b0640610 + ((0xb1c81c11ba19f19818918217316c16915e15715414914213f13413112e123120 + ((0x8627f27827126a25723822d22a22722021d21621320c2092021ff1f41f11ea1d + ((0x33532e32732030d2ee2e32dc2d92d22cf2c42c12be2b72b42ad2aa2a329028d2 + ((0xb3d83c93b63af3a83a139e39338c38937e37737436d36a36336035934634333c + ((0x8a47f47446945e45b45445144a44343c42941e41b41441140a4033fc3e93de3d + ((0x80a1028608783840e110840a0a102860d2451d5124fb4f04d54ce4c34ac4a14 + (0x20608402a181c10170f0100a088838400100040818208080002820001e0e102 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0x8046021000110084011020000408202040828206084022181c10170f01008088 + ((0x2c60c3c362d220808d820b1e0a087820b160a08744080448215182011a084440 + ((0xc3c03d20204000040800608004080200808402100840c3c300870d4883802310 + ((0x200002001038b49c3c0200c80e283480828386083c261b0880a48088607 + ((0xc80e283480828384083c26130880a48088405c3c03d202040608022080860210 + ((0xa838023102c60d1020112085460804682111020000200002001838b49c3c0200 + ((0x8408342e130894a0a10000080ca082038608342e1b0894a0a100043c300870f4 + ((0x8b8946c2022e270050f0d884340284d084c7421055084c54210000080ca08203 + (0xe0d8842400033182c200162e25130808b89c010383621090000cc40b08005 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g125H6 (_ : Nat) : Nat := (0xb060018b0a1010d0000400021008b4208080120010f0000008040000f0808000 + ((0x72ea990dfc28a1a215e37ab8e8fa1e0a8e4d6a28e0800c0070e4a30311245810 + ((0xf4d7211eddefb5024a462e00145c0002bde59e312cd61629a00163872c85f90b + ((0xf58f0c62a46e8286e609d04290b17a50405ea7c9287048a000efcaab878001f0 + ((0x1e066b640d89411b2240006aeb0c001e22000a860000012198bfec1cd00d20 + ((0x1ed4cb3c6000169c001ce400002c676e014f600000146c000000001f1f244000 + ((0x9e331a210ef514e130a008dc0a888267c722cbce100f835f1c1070fe8b587c00 + ((0x43f8410f8918a0267544e0e2cc4eb0c3b31184885a72682706bced27fceaacfe + ((0x32ad9208e9453900ebb0d8001e7a7080010f30c6085adac1d4c952a25706824b + (0x1ee7322c42c3c001c64000ec2f12001254001080324000497f2862b63 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g125D7 (_ : Nat) : Nat := (0x3bf51912bf4d912fd50512fd4c512fb50912fb4c912ff4d112fe41112fe40d12 + ((0x13ff49113fe41113be91903fe51903be51903fe49903fe45903fe49103fe4510 + ((0x123fe41123bf91913ff51913bf51913bf89913ff49913fd50513f750d13f748d + ((0x9904fe45904bf91923ff51923bf51923bf85923ff45923fb50923f750d23ff45 + ((0x4d124bf8d914ff4d914bf89914ff49914ef4d114ef49114be8d904fe4d904fe4 + ((0xf49934ff85934bf85934ff45934fe41934bf8d924ff4d924bf85924ff45924ef + ((0x143c3e93a435f31a2d529023d1ea1a516011b0d609804c000ff89934bf89934f + ((0xd699194c8f98d088482a8017bc77e74e7096b668d6415e75be57953b4f64c648 + ((0x10280aebde6ae33dfcda9d72d2dcdacb1c57c2ebf0b9db74b1aaf1ab3a6ea299 + ((0x210942c3060b0e02440548101c204808901a2a4090e1210280a901d285890e12 + ((0x1c2c2070002c88848101c205870124c4250a0e102c38092021204860c161c049 + ((0x3c50a911a282060121e285488d141030092240405490e16103800164c9084a12 + ((0x8f12282060161c345498f14103009121e2a4468a0818048a0f1522345040c024 + ((0x440b0e0249900a101821834548121c242050121e2a4c78a081800090e1a2a4c6 + ((0xa205840e0006132421102149918a1520407870124c2a4090c1e1c04132416183 + ((0x50124e2a4090c182c2070002c991481110a4c8c5490c16103800144e2e4090c1 + ((0x8c18a488450a90202c38092415204840b0e0209110a101821834548121c2420 + ((0x1038001648824088c524422a4070b081c000a2517204460e102c207000309921 + ((0x5898d1e245040c02c4864b111a2820601228325888d141030092515204070816 + ((0x890108810a45285090c1e1c04112012183440b0e024325898f14103000121c32 + ((0x12102c38082296204860c16103800164c8a50a88523942c4860d102c20700030 + ((0x80e102c2070002c9104a1518a43285888c1c205840e0006112021183148250a + ((0x83c08078b10223078816103800164c8c4460d1601c3868b131e24280012412c4 + (0xb10222058100f16204c60d102c2070002c910888d102c038588111 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g125H7 (_ : Nat) : Nat := (0x3336e0e34805200245d9c000024e9a414e6000d90101406900d211840000861 + ((0x640f0e5a002d3643261272f964d16d80032a5de711b000000006a5b321c13010 + ((0x3295cf7a5b4f003f589182002a237b2b92c1562230b1e8dcb68c61ae5c7f740c + (0x2a8abb <<< 256)) <<< 256)) <<< 256))
def g125D8 (_ : Nat) : Nat := (0x1030a106000be46027108601e09000fe9a7f493fa29f904fe91ff44ff207fd12 + ((0x51238810074859048c30a106000b4c59040e20a106000b1c5923881007225164 + (0x51230e20a106000a4251448c30a106000b4651440e20a106000b1a <<< 256)) <<< 256))
def g125H8 (_ : Nat) : Nat := 0x24a6d75c46200536c
def g125D9 (_ : Nat) : Nat := 0x1483104033f
def g125L : Nat → Packing
  | 5 => (64,4,5,0,0,10,0,g125D5)
  | 6 => (153,3,5,0,0,12,0,g125D6)
  | 7 => (57,2,5,0,0,12,0,g125D7)
  | 8 => (8,1,5,0,0,9,0,g125D8)
  | 9 => (1,0,5,0,0,1,0,g125D9)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 6, h => lookupWord 28 82 6 10 6 0 g125H5 h
  | 7, h => lookupWord 51 181 7 12 8 0 g125H6 h
  | 8, h => lookupWord 20 69 5 10 6 0 g125H7 h
  | 9, h => lookupWord 3 10 1 7 3 0 g125H8 h
  | _, _ => none
def g125 : Forest := ⟨125,9,fun i => g125Y[i]?.getD (0,0),g125C,[[]],g125L,g125I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_0 : block g125 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_5 : block g125 5 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_10 : block g125 5 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_15 : block g125 5 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_20 : block g125 5 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_25 : block g125 5 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_30 : block g125 5 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_35 : block g125 5 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_40 : block g125 5 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_45 : block g125 5 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_50 : block g125 5 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_55 : block g125 5 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P5_60 : block g125 5 60 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125B5 : block g125 5 0 64 = true := (@block_merge g125 5 0 40 24 (@block_merge g125 5 0 20 20 (@block_merge g125 5 0 10 10 (@block_merge g125 5 0 5 5 g125P5_0 g125P5_5) (@block_merge g125 5 10 5 5 g125P5_10 g125P5_15)) (@block_merge g125 5 20 10 10 (@block_merge g125 5 20 5 5 g125P5_20 g125P5_25) (@block_merge g125 5 30 5 5 g125P5_30 g125P5_35))) (@block_merge g125 5 40 20 4 (@block_merge g125 5 40 10 10 (@block_merge g125 5 40 5 5 g125P5_40 g125P5_45) (@block_merge g125 5 50 5 5 g125P5_50 g125P5_55)) g125P5_60))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : block g125 6 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_5 : block g125 6 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_10 : block g125 6 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_15 : block g125 6 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_20 : block g125 6 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_25 : block g125 6 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_30 : block g125 6 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_35 : block g125 6 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_40 : block g125 6 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_45 : block g125 6 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_50 : block g125 6 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_55 : block g125 6 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_60 : block g125 6 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_65 : block g125 6 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_70 : block g125 6 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_75 : block g125 6 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_80 : block g125 6 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_85 : block g125 6 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_90 : block g125 6 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_95 : block g125 6 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_100 : block g125 6 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_105 : block g125 6 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_110 : block g125 6 110 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_115 : block g125 6 115 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_120 : block g125 6 120 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_125 : block g125 6 125 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_130 : block g125 6 130 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_135 : block g125 6 135 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_140 : block g125 6 140 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_145 : block g125 6 145 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P6_150 : block g125 6 150 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125B6 : block g125 6 0 153 = true := (@block_merge g125 6 0 80 73 (@block_merge g125 6 0 40 40 (@block_merge g125 6 0 20 20 (@block_merge g125 6 0 10 10 (@block_merge g125 6 0 5 5 g125P6_0 g125P6_5) (@block_merge g125 6 10 5 5 g125P6_10 g125P6_15)) (@block_merge g125 6 20 10 10 (@block_merge g125 6 20 5 5 g125P6_20 g125P6_25) (@block_merge g125 6 30 5 5 g125P6_30 g125P6_35))) (@block_merge g125 6 40 20 20 (@block_merge g125 6 40 10 10 (@block_merge g125 6 40 5 5 g125P6_40 g125P6_45) (@block_merge g125 6 50 5 5 g125P6_50 g125P6_55)) (@block_merge g125 6 60 10 10 (@block_merge g125 6 60 5 5 g125P6_60 g125P6_65) (@block_merge g125 6 70 5 5 g125P6_70 g125P6_75)))) (@block_merge g125 6 80 40 33 (@block_merge g125 6 80 20 20 (@block_merge g125 6 80 10 10 (@block_merge g125 6 80 5 5 g125P6_80 g125P6_85) (@block_merge g125 6 90 5 5 g125P6_90 g125P6_95)) (@block_merge g125 6 100 10 10 (@block_merge g125 6 100 5 5 g125P6_100 g125P6_105) (@block_merge g125 6 110 5 5 g125P6_110 g125P6_115))) (@block_merge g125 6 120 20 13 (@block_merge g125 6 120 10 10 (@block_merge g125 6 120 5 5 g125P6_120 g125P6_125) (@block_merge g125 6 130 5 5 g125P6_130 g125P6_135)) (@block_merge g125 6 140 10 3 (@block_merge g125 6 140 5 5 g125P6_140 g125P6_145) g125P6_150))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : block g125 7 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_5 : block g125 7 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_10 : block g125 7 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_15 : block g125 7 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_20 : block g125 7 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_25 : block g125 7 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_30 : block g125 7 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_35 : block g125 7 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_40 : block g125 7 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_45 : block g125 7 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_50 : block g125 7 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P7_55 : block g125 7 55 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125B7 : block g125 7 0 57 = true := (@block_merge g125 7 0 40 17 (@block_merge g125 7 0 20 20 (@block_merge g125 7 0 10 10 (@block_merge g125 7 0 5 5 g125P7_0 g125P7_5) (@block_merge g125 7 10 5 5 g125P7_10 g125P7_15)) (@block_merge g125 7 20 10 10 (@block_merge g125 7 20 5 5 g125P7_20 g125P7_25) (@block_merge g125 7 30 5 5 g125P7_30 g125P7_35))) (@block_merge g125 7 40 10 7 (@block_merge g125 7 40 5 5 g125P7_40 g125P7_45) (@block_merge g125 7 50 5 2 g125P7_50 g125P7_55)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P8_0 : block g125 8 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P8_5 : block g125 8 5 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125B8 : block g125 8 0 8 = true := (@block_merge g125 8 0 5 3 g125P8_0 g125P8_5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125P9_0 : block g125 9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125B9 : block g125 9 0 1 = true := g125P9_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125T : checkedTables g125 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g125B5
  · exact g125B6
  · exact g125B7
  · exact g125B8
  · exact g125B9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 10 := lower_forest (g:=g125) (i:=0) (hints:=2237190) (before_sound K119 V119) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K119 10 [(125,[]),(126,[16])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V119 low125 (by decide +kernel)

def g127Y : Array (Bits × Bits) := #[ (0x4a4c2821269f43c3ae52759f24205437230628e068b6a060e208433ef2b8416a,0x48080431269241019e50050404a00022031220a0409482606208033ad0b04062), (0x12f6e828246494d98da63a79311897e416215783f5b91506006396c4b5294f1d,0xf5a04000049cd0408e30794001960054a1160294081100006394c424090f1d), (0x6dfb3158545650c2d0c28c44c046a75ca0038fb71372f80b56e085938acc1244,0xc020501062144350000c040642845d804009b51022080a12a080838a881044), (0xe9c0d65f7391e91ea4e7afa948294a8843218449b74c0478809704b201772d82,0xe100908ca00161188063018840394a80022104002b4000508004043001652d82), (0x9720c726df931110606c644213e79c42ef9a34b8928a1391096d316958130058,0x200452047900000280c204011800000709a0000808011010141314850120008), (0x1c1d32a52b4eeb3c14155305b848e91004fbe81644195be0741aba006080b691,0x1c15020000040a0006004201a00001200000a000441902a0641a020020008211), (0x4096818a88e8166c031909fe87b64a83186c7b74eee7e50eab0448480f4098a7,0xa002008a8868200c0000080202144809804048502a226c0e880448000b401080), (0x0,0x0), (0x0,0x0) ]
def g127C : List ColumnInfo := [(32,0,95,0,10), (16,0,111,0,10), (8,0,119,0,10), (4,0,123,0,10), (2,0,125,0,10), (1,0,126,0,10), (12,0,115,0,8), (3,0,124,0,8), (67,0,60,0,7), (10,0,117,0,7), (9,0,118,0,7), (6,0,121,0,7), (5,0,122,0,7), (40,0,87,0,7), (36,0,91,0,7), (34,0,93,0,7), (33,0,94,0,7), (24,0,103,0,7), (20,0,107,0,7), (18,0,109,0,7), (17,0,110,0,7), (96,0,31,0,6), (80,0,47,0,6), (72,0,55,0,6), (68,0,59,0,6), (48,0,79,0,6), (44,0,83,0,5), (35,0,92,0,5), (28,0,99,0,5), (19,0,108,0,5), (14,0,113,0,5), (13,0,114,0,5), (11,0,116,0,5), (7,0,120,0,5), (99,0,28,0,4), (83,0,44,0,4), (75,0,52,0,4), (71,0,56,0,4), (60,0,67,0,4), (15,0,112,0,4), (42,0,85,0,4), (41,0,86,0,4), (38,0,89,0,4), (37,0,90,0,4), (26,0,101,0,4), (25,0,102,0,4), (22,0,105,0,4), (21,0,106,0,4)]
def g127D11 (_ : Nat) : Nat := 0x51030810067f
def g127L : Nat → Packing
  | 11 => (1,0,6,0,0,1,0,g127D11)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g127 : Forest := ⟨127,11,fun i => g127Y[i]?.getD (0,0),g127C,[[]],g127L,g127I⟩
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
  · rfl
  · rfl
  · rfl
  · exact g127B11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 12 := lower_forest (g:=g127) (i:=0) (hints:=2237185) (before_sound K125 V125) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def postedGraph : Sig := 0xfffffffffffffffffffffffffffffefcfffffffefffffefcffeeffeeeeccaa00fffffffffffffffffffffffffffffefcfffffffefffffefcffeeffeeeeccaa00
theorem postedGraphProper : proper postedGraph := by unfold proper; decide +kernel

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [1, 7]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.or, [1, 11]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.and, [5, 13]⟩,
    ⟨.and, [14, 8]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [19, 17]⟩,
    ⟨.or, [20, 18]⟩], 21⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 14 := rfl

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

def eightInputs : List Sig := vars 255
def sampleEight (r : Row) (i : Fin 8) : Bool := bit r (eightInputs.getD i.val zero)
theorem eightList : List.ofFn (fun i : Fin 8 => eightInputs.getD i.val zero) = eightInputs := rfl
theorem eightSampled (r : Row) : List.ofFn (sampleEight r) = eightInputs.map (bit r) := by
  rw [←eightList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem eightTable : ∀ r : Row, bit r postedGraph = target (sampleEight r) := by decide +kernel

theorem eightEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sampleEight r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),eightSampled]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (([8, 16, 64, 1, 2, 1, 2, 2] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((([8, 16, 64, 1, 2, 1, 2, 2] : List Nat).getD i.val 0) ||| (1 <<< i.val))

set_option maxHeartbeats 0 in
theorem allEightRequired :
    (∀ i : Fin 8, bit (lowRow i) postedGraph ≠ bit (highRow i) postedGraph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true postedGraph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = postedGraph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eightEval C legal C.output r).trans ((computes (sampleEight r)).trans (eightTable r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 postedGraph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) postedGraphProper
    (out.resolve_right (fun h => h postedGraphProper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←eightList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allEightRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allEightRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true postedGraph 12 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 14 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by rw [witnessSize]; omega),witnessCorrect⟩
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

def coreMoves : List Move := ([65, 114, 67, 116, 101, 118].map swapRows) ++ fixRows 4 0
def removed : List (Sig × Row × Row) := [(eightInputs.getD 2 zero, 64, 68)]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem restricted : Lower true eightInputs postedGraph 13 := by
  have h := lift_ok (u:=true) (ms:=coreMoves) (T:=postedGraph) (raw:=eightInputs)
    (base:=varsX 127) (G:=graphGoal 127) (xs:=removed)
    (by decide +kernel) postedGraphProper (proper_of _ (by decide +kernel)) low127
  exact h

theorem excluded : Impossible true postedGraph 12 eightInputs.toFinset := by
  intro k small run
  have steps := list_run run eightInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper postedGraphProper)
    steps (eightInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := restricted q bank built hit
  omega

end PEqualNP.Outside.L_meta_30282

theorem PEqualNP.Outside.L_meta_30282 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_30282.replaceShort PEqualNP.Outside.L_meta_30282.excluded gates o fit correct
