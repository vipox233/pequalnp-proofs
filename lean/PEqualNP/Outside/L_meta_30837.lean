import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30837

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
  (x 0 &&& x 3) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7)

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

def graphCutPairs (G : Sig) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let p := (1 : Nat) <<< i
    let witness := (List.range 9).find? fun j =>
      !G.getLsbD (1 <<< j) && G.getLsbD ((1 <<< j) ||| p)
    let r := if G.getLsbD p then 0 else (witness.map fun j => (1 : Nat) <<< j).getD 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| p))

def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)

def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := graphCutPairs (movedWord ms (chartGoal m)) s
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
  let xs := graphCutPairs (movedWord ms (chartGoal m)) s
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
  (x 0 &&& x 3) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 6) ||| (x 5 &&& x 7)

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

def g97Y : Array (Bits × Bits) := #[ (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff77f5,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8085), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbbeb,0x4062), (0xeede,0x1218), (0x0,0x0), (0x0,0x0) ]
def g97C : List ColumnInfo := []
set_option maxRecDepth 100000 in
def g97D3 (_ : Nat) : Nat := 0x7
def g97L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,g97D3)
  | _ => emptyPacking
def g97I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g97 : Forest := ⟨97,3,fun i => g97Y[i]?.getD (0,0),g97C,[[]],g97L,g97I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g97P3_0 : block g97 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g97B3 : block g97 3 0 1 = true := g97P3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g97T : checkedTables g97 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g97B3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g97G : graphValid g97 (boundsBefore K0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low97 : Lower true (varsX 97) (graphGoal 97) 4 := lower_forest (g:=g97) (i:=0) (hints:=5) (before_sound K0 V0) g97G g97T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K97 := extendKnown K0 4 [(97,[]),(98,[16]),(100,[16, 33]),(137,[83, 84, 118]),(146,[16, 84, 118]),(161,[118]),(162,[16, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V97 : Known true K97 := extend_ok (m:=97) V0 low97 (by decide +kernel)

def g43Y : Array (Bits × Bits) := #[ (0xf79fbef7df8bdfe4,0x868200418990624), (0xffffffffffffffffffffffffffffffffffffffffffffffff5f72f70f697e60bf,0xa02982d401d360bc), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffff3eb8fcd5d72f35f1,0xffffffffffffffffffffffffffffffffffffffffffffffffc0160771674401d1), (0x0,0x0), (0xfffffffffffffffffffffffffffffffffffffffffffffffff97ffb6f3bf4fb1f,0xffffffffffffffffffffffffffffffffffffffffffffffff0482142324201903), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g43C : List ColumnInfo := []
set_option maxRecDepth 100000 in
def g43D3 (_ : Nat) : Nat := 0xf
def g43L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,g43D3)
  | _ => emptyPacking
def g43I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g43 : Forest := ⟨43,3,fun i => g43Y[i]?.getD (0,0),g43C,[[]],g43L,g43I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g43P3_0 : block g43 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g43B3 : block g43 3 0 1 = true := g43P3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g43B3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K97) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K97 V97) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K97 4 [(43,[]),(45,[33]),(51,[16, 67]),(75,[101]),(77,[33, 101]),(172,[32, 65, 66, 100, 118]),(197,[33, 67, 100, 117, 118]),(232,[32, 65, 98, 67, 116, 101, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V97 low43 (by decide +kernel)

def g105Y : Array (Bits × Bits) := #[ (0x5ff7affde7eebcf6,0x2000410020480064), (0x0,0x0), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffb3603df0af9eea87,0xffffffffffffffffffffffffffffffffffffffffffffffffcc8a8e8e95864a83), (0x0,0x0), (0xfffffffffffffffffffffffffffffffffffffffffffffffffaf9db975edd535b,0xffffffffffffffffffffffffffffffffffffffffffffffff854484464b80001b), (0xffffffffffffffffffffffffffffffffffffffffffffffffbd6ff78af8f577a9,0x42300a2810163780), (0x0,0x0), (0x0,0x0) ]
def g105C : List ColumnInfo := [(8,0,97,0,4)]
set_option maxRecDepth 100000 in
def g105D4 (_ : Nat) : Nat := 0x2f
def g105L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g105D4)
  | _ => emptyPacking
def g105I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g105 : Forest := ⟨105,4,fun i => g105Y[i]?.getD (0,0),g105C,[[]],g105L,g105I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g105P4_0 : block g105 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g105B4 : block g105 4 0 1 = true := g105P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g105T : checkedTables g105 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g105B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g105G : graphValid g105 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low105 : Lower true (varsX 105) (graphGoal 105) 5 := lower_forest (g:=g105) (i:=0) (hints:=3) (before_sound K43 V43) g105G g105T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K105 := extendKnown K43 5 [(105,[]),(139,[80, 49, 50, 99, 100, 101, 118]),(147,[48, 81, 82, 83, 100, 101, 118]),(153,[80, 99, 100, 101, 118]),(154,[16, 81, 100, 101, 118]),(165,[80, 50, 118]),(170,[16, 81, 101, 118]),(177,[80, 67, 101, 118]),(201,[83, 117, 118]),(228,[16, 33, 82, 67, 116])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V105 : Known true K105 := extend_ok (m:=105) V43 low105 (by decide +kernel)

def g99Y : Array (Bits × Bits) := #[ (0xfffffffffffffffffffffffffffffffffffffffffffffffffcd9cdb9f3fa28a7,0x323201431613886), (0x9ed67c5fc55df44,0x620583080753944), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0xfb7f5f2df4eb27e,0x40060840088228), (0xfffffffffffffffffffffffffffffffffffffffffffffffff7efdf1f2bfdcd99,0xfffffffffffffffffffffffffffffffffffffffffffffffff81001410a000411), (0x0,0x0), (0x0,0x0) ]
def g99C : List ColumnInfo := [(2,0,97,0,4)]
set_option maxRecDepth 100000 in
def g99D4 (_ : Nat) : Nat := 0x2f
def g99L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g99D4)
  | _ => emptyPacking
def g99I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g99 : Forest := ⟨99,4,fun i => g99Y[i]?.getD (0,0),g99C,[[]],g99L,g99I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g99P4_0 : block g99 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g99B4 : block g99 4 0 1 = true := g99P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g99T : checkedTables g99 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g99B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g99G : graphValid g99 (boundsBefore K105) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low99 : Lower true (varsX 99) (graphGoal 99) 5 := lower_forest (g:=g99) (i:=0) (hints:=85) (before_sound K105 V105) g99G g99T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K99 := extendKnown K105 5 [(99,[]),(101,[33]),(163,[118]),(169,[80, 33, 50, 83, 118]),(178,[32, 81, 50, 67, 118]),(225,[80, 33, 50, 67, 116, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V99 : Known true K99 := extend_ok (m:=99) V105 low99 (by decide +kernel)

def g59Y : Array (Bits × Bits) := #[ (0x5df9e5df76bfef7e1d7577d83fefce7fede1ff9bd4c7bced7b7d8f912fe0fa,0x220c0800d9400003701120808402516040040018664516a11200030003c0d8), (0xffeef61faffdfd77dbf7fbd93fd5953bbfd3be48ed3fbf7b92aece716fd35f45,0x11098090010248004c000c8094235012000218943606702000047809930640), (0x0,0x0), (0xffba7bd941f37fc39fcd3f382a367edc47f7c956b251c5bd84c9ab6edf5e8533,0xffc58126a004a83d6c03c8920842f0209f98c2fe241990e840c9990c7b5c0523), (0xffb5b975f7cd4b55d3f7ba79a3efbf261e8456a44fed75221b29bf354e496e1f,0xffca460309b630a06d2133524e40cca6e83028c06bc819061079bb801648681f), (0xfff3dfef9ad995f9e8b27cbfd7de41d7ef5f2aff2ade0a597ff7dad268b431cf,0xff8c20146506392204836243000018a08c05f964620808894e605b8062243107), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g59C : List ColumnInfo := []
set_option maxRecDepth 100000 in
def g59D4 (_ : Nat) : Nat := 0x1f
def g59L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g59D4)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g59 : Forest := ⟨59,4,fun i => g59Y[i]?.getD (0,0),g59C,[[]],g59L,g59I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59B4 : block g59 4 0 1 = true := g59P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g59B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K99) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 5 := lower_forest (g:=g59) (i:=0) (hints:=65603) (before_sound K99 V99) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K99 5 [(59,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V99 low59 (by decide +kernel)

def g167Y : Array (Bits × Bits) := #[ (0x3d669bbb437a5b3bb6a7fd0fe8e89ece561ae9f73817fece33485b229a,0x429960409b82a1c1244a8841b664d123b04820a6342e6d4ab04859208a), (0xfffffff93d0def27b9aae3cd38f6fa0ef4f1f0ab9aa26a87d96b7cfe07bdc903,0xffffff86c3d04218460539440b4c03b6836586622000e07618612eba07394803), (0x68ee67d52918657f39f02ac9dca53b8c62ecf751557444c3f4774f6864,0x1711d123c6079aca45d4e96e3304d8167a23a56157f2a4c3d80a4f6860), (0x0,0x0), (0x0,0x0), (0xffffffffd7ebf7fff7b76dffff3cff7573faf176e53c9dc9746fbb9fbb58557d,0x20048800004000802000800008020001000810800002000410000514), (0x0,0x0), (0x76fd7cdf97ce5ffbeedaff84cbde371fbb3fdb67bf8b947d70d6a7bec2,0x90403006021020409003014480008100403d601098180100000069240), (0x0,0x0) ]
def g167C : List ColumnInfo := [(2,0,165,0,5)]
set_option maxRecDepth 100000 in
def g167D5 (_ : Nat) : Nat := 0x5f
def g167L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,g167D5)
  | _ => emptyPacking
def g167I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g167 : Forest := ⟨167,5,fun i => g167Y[i]?.getD (0,0),g167C,[[]],g167L,g167I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g167P5_0 : block g167 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g167B5 : block g167 5 0 1 = true := g167P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g167T : checkedTables g167 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g167B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g167G : graphValid g167 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (graphGoal 167) 6 := lower_forest (g:=g167) (i:=0) (hints:=1365) (before_sound K59 V59) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K59 6 [(185,[112, 49, 66, 115, 117]),(186,[48, 113, 66, 67, 117])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V59 low167 (by decide +kernel)

def g107Y : Array (Bits × Bits) := #[ (0xfffffffffd7fef207dedbef0636751fffedbf45f6f8b776f93f92f099b6e4e13,0xfffffffff28018c5041000021128010103840808020827028cc0000013204413), (0x9be987dd3e7daddb9af2dc76d6c2fb2f13cc5f8fdc7992764b1fc48,0x6418342341005200689c04322dc8860020c639a1da0012024215c48), (0x0,0x0), (0xfffffffff6b8bbf9c5cdad08a8a3d7b9ea77b90a7ac2311d50ef89bf8f3e286d,0x94745027a23c28ce057cc5288103623c486980c4033cd1d6c1e286c), (0x0,0x0), (0xeeedff6b67bb9e3bdd9ef1fe6ae666f9d7f4bd8ca0a56df5d9817bc,0x1102008480448980840000450011682481300440008448740980304), (0xff1adcfdd737fbfefff826d91d85bbbbbfb8ca36794e9fc3645e1e6,0xc401002e880402004341808000005b1609821421408080044a0a0), (0x0,0x0), (0x0,0x0) ]
def g107C : List ColumnInfo := [(2,0,105,0,5), (8,0,99,0,5), (0,8,98,1,5), (9,0,98,0,4), (64,0,43,0,4), (32,0,75,0,4)]
set_option maxRecDepth 100000 in
def g107D4 (_ : Nat) : Nat := 0x5d85534
set_option maxRecDepth 100000 in
def g107H4 (_ : Nat) : Nat := 0xb00
set_option maxRecDepth 100000 in
def g107D5 (_ : Nat) : Nat := 0x210808fd34
set_option maxRecDepth 100000 in
def g107H5 (_ : Nat) : Nat := 0x48
set_option maxRecDepth 100000 in
def g107D6 (_ : Nat) : Nat := 0x2c68819f
def g107L : Nat → Packing
  | 4 => (1,2,3,0,0,1,0,g107D4)
  | 5 => (1,1,3,0,0,1,0,g107D5)
  | 6 => (1,0,3,0,0,1,0,g107D6)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 2 2 1 5 1 0 g107H4 h
  | 6, h => lookupWord 2 2 1 5 1 0 g107H5 h
  | _, _ => none
def g107 : Forest := ⟨107,6,fun i => g107Y[i]?.getD (0,0),g107C,[[]],g107L,g107I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107P4_0 : block g107 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107B4 : block g107 4 0 1 = true := g107P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107B5 : block g107 5 0 1 = true := g107P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107P6_0 : block g107 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107B6 : block g107 6 0 1 = true := g107P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g107B4
  · exact g107B5
  · exact g107B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=83) (before_sound K167 V167) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K167 7 [(109,[33]),(118,[32, 33, 67]),(173,[80, 33, 50, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V167 low107 (by decide +kernel)

def g205Y : Array (Bits × Bits) := #[ (0x7e77c7dff5dbff57b6b957458fbf1ffff9b3ef69ea73e674497b7e1aa2,0x18420200a0080a020002804206800000ba52028c00284440800580222), (0x0,0x0), (0x66bd3b878f5f52747b853bead2f5ecd547c459f184fb5fc9af8580777a,0x1942808870a8a8f02061887d08ca90d5aa054b5061609f432a01005772), (0xffffffbbb73dfe3d678be9a9f79e37ebabc7af46eaeedf599e06933e7535865d,0x4448c20221183402404450c88993444210080e450b1010880635258418), (0x0,0x0), (0x0,0x0), (0x3fcc76e5f3eeba7efbc8f5ee16d3f1b38bf495ff06a5bdcce3ec8f6d2c,0x40300b1204404701ce96410243150500000884830e8100a851c887280c), (0xffffffcfecdfbb3bbbc6bde446cb1befedf86f3d69ec06b5ec68f7ff1241f8d7,0xffffffb0130140d04601450a098221520413310040c00020ac6132b1880078c5), (0x0,0x0) ]
def g205C : List ColumnInfo := [(4,0,201,0,5), (0,4,137,64,5), (68,0,137,0,4), (128,0,77,0,4), (8,0,197,0,4)]
set_option maxRecDepth 100000 in
def g205D4 (_ : Nat) : Nat := 0xc2dc4a824f91502
set_option maxRecDepth 100000 in
def g205H4 (_ : Nat) : Nat := 0xd018
set_option maxRecDepth 100000 in
def g205D5 (_ : Nat) : Nat := 0x3044024044023070898280fd24ff04fd04ff02fd02
set_option maxRecDepth 100000 in
def g205H5 (_ : Nat) : Nat := 0x24cc44011c
set_option maxRecDepth 100000 in
def g205D6 (_ : Nat) : Nat := 0x468815f
def g205L : Nat → Packing
  | 4 => (2,2,3,0,0,3,0,g205D4)
  | 5 => (5,1,3,0,0,6,0,g205D5)
  | 6 => (1,0,3,0,0,1,0,g205D6)
  | _ => emptyPacking
def g205I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 2 3 1 5 1 0 g205H4 h
  | 6, h => lookupWord 3 7 1 7 3 0 g205H5 h
  | _, _ => none
def g205 : Forest := ⟨205,6,fun i => g205Y[i]?.getD (0,0),g205C,[[]],g205L,g205I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g205P4_0 : block g205 4 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g205B4 : block g205 4 0 2 = true := g205P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g205P5_0 : block g205 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g205B5 : block g205 5 0 5 = true := g205P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g205P6_0 : block g205 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g205B6 : block g205 6 0 1 = true := g205P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g205T : checkedTables g205 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g205B4
  · exact g205B5
  · exact g205B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g205G : graphValid g205 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low205 : Lower true (varsX 205) (graphGoal 205) 7 := lower_forest (g:=g205) (i:=0) (hints:=1539) (before_sound K107 V107) g205G g205T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K205 := extendKnown K107 7 [(205,[]),(236,[16, 65, 50, 84, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V205 : Known true K205 := extend_ok (m:=205) V107 low205 (by decide +kernel)

def g171Y : Array (Bits × Bits) := #[ (0x76edfc5f8f71eddf33df7d28651bb6f463cf15ffce125a970f58,0x9000260708441a8083420848c08000040490506611200920c50), (0xffffffffffffdaf4dcf65a5e3e6d45a4d6e73dab5cabcc22fe79f13b44ba61c5,0xffffffffffffa50ac101b1a140aea11b24641a040423042a95e3219800926145), (0x0,0x0), (0x4f76565e55b7d1e9cacf2e7e47c1bc9a6e57d3d01cd4d7d8433e,0x30a9a182826822449083410351309d213a96909014a8c408432e), (0x0,0x0), (0xfffffffffffffd4eebef7c73773ed732ee53fd1f171f99afcc1d5d35a92bd829,0x2b500100008aa0040c048002151c840b8944018082408291028), (0x0,0x0), (0x3ff7efe7b7aeebd9ed1519fefbfecd7c9e74be26a2cebdc4b4e6,0x4000100c08001001000080000002221c00000a00800011448080), (0x0,0x0) ]
def g171C : List ColumnInfo := [(32,0,139,0,5), (1,0,170,0,5), (8,0,163,0,5), (2,0,169,0,5)]
set_option maxRecDepth 100000 in
def g171D6 (_ : Nat) : Nat := 0xe411f
def g171L : Nat → Packing
  | 6 => (1,0,2,0,0,1,0,g171D6)
  | _ => emptyPacking
def g171I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g171 : Forest := ⟨171,6,fun i => g171Y[i]?.getD (0,0),g171C,[[]],g171L,g171I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g171P6_0 : block g171 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g171B6 : block g171 6 0 1 = true := g171P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g171B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K205) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := lower_forest (g:=g171) (i:=0) (hints:=83) (before_sound K205 V205) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K205 7 [(171,[]),(179,[16, 67]),(229,[33, 67, 100, 117, 118]),(233,[112, 33, 66, 67, 100, 117])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V205 low171 (by decide +kernel)

def g155Y : Array (Bits × Bits) := #[ (0xfffffffff3bc319467bffdfa3d4b73b7acfc25fcd99121f9e566c6fdbad34359,0xc434642880043143a83802441016244a15182a0016800ed92d10158), (0x75f6bf874ccfbafcaa6ac3caf6dfdadc2a68a2571ff7d5e43195cf2,0x8a18011883104d01499c000144180a8cf838840613a1951041958c0), (0x0,0x0), (0xd6d7edf2d4d4d73fdd1f69d291626ffae3b34d0ef35d03a7fa3fa28,0x2908020769220c2402054428ad494804c207844c60558104c22da20), (0xfabdc55f26df0fd68c509e8f7fdd69f8f52cf269ee737fa60bc0b36,0x54412a05022b2301021480a1a67a44104052840cc5062aa8a40332), (0x0,0x0), (0x0,0x0), (0xfffffffffefff73bbff6e7f1f23ed7fe5cbfdbf6f7ec750b5fd99be59564b5c5,0xfffffffff1000884000410000000081900080010000005011000800001002405), (0x0,0x0) ]
def g155C : List ColumnInfo := [(16,0,139,0,5), (8,0,147,0,5), (2,0,153,0,5), (1,0,154,0,5), (18,0,137,0,4), (9,0,146,0,4)]
set_option maxRecDepth 100000 in
def g155D4 (_ : Nat) : Nat := (0x4e48423c36302a241e18120c06009e819258d26e26416349d859358925e36456249e819258526e26416149d859358125e36456049d8594548e7a06515239d4584548e7906115239b8994540e7616515039b4984540e751611503978d94544a7a0651512974d84544a790611512978d9454066e2651501974d8454066d2611501 + (0x8a847e78726c66605a54 <<< 1024))
set_option maxRecDepth 100000 in
def g155H4 (_ : Nat) : Nat := 0xb60021d2100415c40000000e4ef0072d6c083ac29c02971a4c00044be461a86aa5c001870c8408718
set_option maxRecDepth 100000 in
def g155D5 (_ : Nat) : Nat := (0xfa4b0a5f41614ef1aa295e35452fc4a8a5f81514fba0a297d35812fa2b025f8d504f712a096e25412fc2a827ed0104bfa2a477e4548efa8a91df11523f6a1247dd4348efe8a81df91503bea2a077c4540ff28081f750d03bfa2a257e4544afa8a895f11512faa0a25ed4244afe8a80df91501bea2a037c45407f28080fd50501 + ((0x1028096208000200862080412421a029664e9223d8de318861682e057fdf47b9de74dc86f5b76c5ab66d906157f5d16e5a1585494c4f122449023f0f6398cc2f0ac298a024076198561404a0e82004000be92c697d058d2fc4a9a7d85534bb0aa697e054d3be869a5f4d624be8ac497e35492fc2a927e81524bd02a49ef42492 + (0x18210401020012004204008000c10260086084100200004001081002004100088020001882188201160094108000410862080448021a82000180218820 <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g155H5 (_ : Nat) : Nat := 0x319dfda8004bdec502cf88fc194c004892b355d0d4800372b016ae79978e0035792400d901b0000000000531822b800c219ebb40095a0781345081b1799c3764149cf8d7cb0a761cb6472900268386dd8f0406040c90800c9008040a0
set_option maxRecDepth 100000 in
def g155D6 (_ : Nat) : Nat := 0x43a210190c84055b3210194c8405432180190c8405532910194c840554b3a2102150e8a440854b321802150ca46008ad5024508753416498391304c00fe34fd34fe24fd24fe14fd14fe04fd04fd23fd03fd12fd01
set_option maxRecDepth 100000 in
def g155H6 (_ : Nat) : Nat := 0x398160005a000485230000646b858af8f084
set_option maxRecDepth 100000 in
def g155D7 (_ : Nat) : Nat := 0x2c68819f
def g155L : Nat → Packing
  | 4 => (24,3,3,0,0,8,0,g155D4)
  | 5 => (52,2,3,0,0,10,0,g155D5)
  | 6 => (12,1,3,0,0,9,0,g155D6)
  | 7 => (1,0,3,0,0,1,0,g155D7)
  | _ => emptyPacking
def g155I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 12 33 3 9 5 0 g155H4 h
  | 6, h => lookupWord 20 64 5 10 6 0 g155H5 h
  | 7, h => lookupWord 5 16 3 8 4 0 g155H6 h
  | _, _ => none
def g155 : Forest := ⟨155,7,fun i => g155Y[i]?.getD (0,0),g155C,[[]],g155L,g155I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155P4_0 : block g155 4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155P4_16 : block g155 4 16 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155B4 : block g155 4 0 24 = true := (@block_merge g155 4 0 16 8 g155P4_0 g155P4_16)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155P5_0 : block g155 5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155P5_16 : block g155 5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155P5_32 : block g155 5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155P5_48 : block g155 5 48 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155B5 : block g155 5 0 52 = true := (@block_merge g155 5 0 32 20 (@block_merge g155 5 0 16 16 g155P5_0 g155P5_16) (@block_merge g155 5 32 16 4 g155P5_32 g155P5_48))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155P6_0 : block g155 6 0 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155B6 : block g155 6 0 12 = true := g155P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155P7_0 : block g155 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155B7 : block g155 7 0 1 = true := g155P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g155B4
  · exact g155B5
  · exact g155B6
  · exact g155B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 8 := lower_forest (g:=g155) (i:=0) (hints:=65603) (before_sound K171 V171) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K171 8 [(155,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V171 low155 (by decide +kernel)

def g207Y : Array (Bits × Bits) := #[ (0x36dbd34920b74da1038dcf2b24dad2687fb92a4d97bd67241ec4d10d8d7391e4,0x72e402102250d00038845094011420008b822489128043146005101842091e0), (0xd5f2e8bef688ba16fe01f3adf41142f0f0497bd23066985bbfed49a0f4982bb6,0xa72e44c9240080145000d789d51122c0f49929ca11243499b1a24920d41821b6), (0xbd1d6679abd6d97d20c259d437fc6bd5dc346432f552451b54d2149a121e75f1,0x500735f08265dcb171501a45b5706ec5cc144050b500441554ea5488101e75f1), (0xb0d34e93710ee08fa3f8b297aa30aece579aa8b0cef470e03c37a67d8198342f,0x30d10680844a028ca0029286b2022444d70481000cd470c08837067c01982406), (0x0,0x0), (0x0,0x0), (0xde3db6dedf6d3278cc0639ec4b3e79bfea24162b7cfd1d63e9a0e17273cdc740,0x50000210002240882220200a0a11380340802040510b020800a05223c10200), (0x47a35da24df8fd56b07ddc5a9ec99e6e0a4bd5f4990ada9e035b3ec02e23689b,0x4800300451807002083508100088892b0040143000030206004820802a034809), (0x0,0x0) ]
def g207C : List ColumnInfo := [(2,0,205,0,7)]
set_option maxRecDepth 100000 in
def g207D7 (_ : Nat) : Nat := 0xbf
def g207L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,g207D7)
  | _ => emptyPacking
def g207I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g207 : Forest := ⟨207,7,fun i => g207Y[i]?.getD (0,0),g207C,[[]],g207L,g207I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g207P7_0 : block g207 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g207B7 : block g207 7 0 1 = true := g207P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g207T : checkedTables g207 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g207B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 8 := lower_forest (g:=g207) (i:=0) (hints:=1635) (before_sound K155 V155) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K155 8 [(207,[]),(215,[16, 67])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V155 low207 (by decide +kernel)

def g237Y : Array (Bits × Bits) := #[ (0xac5393ec6adfd3a0c2e2c3f78f08a2b6628c91ca611db6aaf62b2a4650932db0,0x10064c800020960000004110040082046204804040204008060a204450100c20), (0x0,0x0), (0x11858765dd647c93b808ec5da852fcd4b452293b9d22537c1b9e27b8fc221624,0x141384c4680cde0848102054887206c4a608a9828320403c1f0216b85c220424), (0xbf49399012d94f453bfc8fa0daf004bdf973b68065871cd178d23c96994682dd,0x6b61000d1852200104e0a6a0c8e000b89822689428db144140900882884682dc), (0x0,0x0), (0xe1e5f79b6513b09fbc6b34ec76df319307c66225caf3011d02ebc8cb068cd60a,0xa40010814032000950a04802288211101624000085001004000080302809208), (0x5bd232588c751879042d8eb2d0cfd946d9144b5f108cef062f954520e364698e,0x218812320210001602809a225001180a1011021d300c0a02a0814100a1446182), (0x37b4c76741af75cffd75b176db34f29b8ab366b8644286999419a112d79e061,0x908020a18c082c22051805001240400489122b160420029841521025296001), (0x0,0x0) ]
def g237C : List ColumnInfo := [(128,0,109,0,7), (64,0,173,0,7), (32,0,205,0,7), (1,0,236,0,7), (8,0,229,0,7), (4,0,233,0,7), (0,4,137,96,6), (0,8,100,129,6), (132,0,105,0,5), (72,0,165,0,5), (36,0,201,0,5), (9,0,228,0,5), (136,0,101,0,5), (68,0,169,0,5), (12,0,225,0,5), (1,8,100,128,5), (32,4,137,64,5), (64,4,137,32,5), (128,8,100,1,5), (140,0,97,0,4), (137,0,100,0,4), (100,0,137,0,4), (76,0,161,0,4), (192,0,45,0,4), (160,0,77,0,4), (65,0,172,0,4), (40,0,197,0,4), (5,0,232,0,4), (96,4,137,0,4), (129,8,100,0,4)]
set_option maxRecDepth 100000 in
def g237D5 (_ : Nat) : Nat := 0x4080c10b82000057a32e2bf608490c0c033989e1641534d5a474155340ee69610450d03f8b645012340f664dd0451503d99074d14540f564dd0551503f19344154540f5641d3551503f19044d54540fd4961034d501
set_option maxRecDepth 100000 in
def g237H5 (_ : Nat) : Nat := 0x22b5a0802a7a0039e9402904cc4000428
set_option maxRecDepth 100000 in
def g237D6 (_ : Nat) : Nat := (0x40e7fb3a8a81cfd6751503bf20ea2a07774dd4540f5eb228a81fb90451503f3a68a2a079f5954540fbc82a8a81f5d3551503bec2e9a2053f51e564067e9bcac80ef93095901dea632b2037d51e56406fa9bcac80ef53695901fe2aea0203fc95940407f92ba6080ff1574c101fe4ac98203ec41145407e881a6a80fc10348d01 + ((0x91923bda0f23247bb41a4648fe6a3aa691fce4654d23e9a6aa2a477b89d0544e7ea3cac81e7e57559039fc8eab2073f55e4640f5f23a8c81cfe5751903ef6caa82077e95d4040fddb228081dde4754d03ebecaa9a07d64155340feca02a681f9f6450d03f3208a1a07f65414340fe723a4681fce4648d03f9a8c91a07f250123 + ((0x8dd45416bf23a6a82cfe07559349ea0f0b2696f81d544d37b0b24a9a5ee2741534cfaca82a69cf515054d37b0b20a9a5ee27415149fa6f2b2093f8dd564127eabc6c825be474d904b7c6eaa209af8d9544135f2b268826bd564d104b7a8e9aa099f595354139ea2a6a824fd57919239fa0f23247bb40a4648f6e81c8c91ded57 + ((0xa8c7cc60c54c48c1cc00bf4bd8b8cb50a74a68a3ca009f49c898c98095493891c9008e484883c81077476872c6f06946085fc5b058455851c5004d449846c45044442841c3f03e43b83ac3903443082cc2702341680dc0013f41e365167e9bc0ca2cfd07919359fa8f0326b5f95d064d6bf03a8a9ae7e06515359da6f1320b5f + ((0x388a0018e82382e10ea200863a2e10e020000200ed004030900403082281ec8c020dd090863a06c018e8a07b2300a3a364418e0d8c8a08d3e322f20190d0183836214f8c06454040e8e596887d3e362d2219170f01b03900d000fd4fa8f8cf70f34f18f0cee0ea4e88e7ce60e44e18dfcdf0de4db8d8cd60d44d28d1cd00cd4c + ((0x808e0200102380610e81043a3810082000394213002030022a20cac220d5010063a3834302a258f4dca880542406800c0a10e8a00060038204382a001803a0610e820608e020408a63d3b301c10110001200e01042b4f8ccc070404420248038348618e013086382a20cac228e8d07d3b321813090003830282083a0410e0184 + (0x382040c0a1000c0a10e80043a08e820f86c41818200302840cc7841810206282060e2d2054808000382040e0810e00043 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g237H6 (_ : Nat) : Nat := (0x960400112ad7b86432ad21292075a11e1e298e12453dff2ea56e930530312eb04c07cbd3600287c480008cad46d070267c2b000000d3283f3500000829ac3a85cb000440910c488b000e0aed99bb1ce3d157caa11000aa4007bb0012752a2a2d7c2cc0044567be9b860ceb8c000e2382aa01c0028c810400e21c03600c10840f + (0x2200061b486d3b1aa2000166a0ed60001a8bb9d162c40061379e4a99d123a70526e <<< 1024))
set_option maxRecDepth 100000 in
def g237D7 (_ : Nat) : Nat := (0xd504fb51723fb41323bf91923fb91923f354d23fb51523fb41123ff41513ff95903bf95903ff55903bf55903ff91903bf91903ff51903bf51903fe54103fe50103f754d03f750d03f348d03ff51503ff4d102ff44d02fd51601fd4d601f9c8e01f948e01bf95901fd95901fc50101fc4c101fd51501fd4d501f9c8d01f948d01 + ((0x39e9b70d4a64b2ff96e8aea52926792608ec45b1fd0e806d231d15709343d819208e02b40c2000bf8d945ff4d945bf81945ff41945bf91935ff51935bf81935ff41935df51535bb89905df51505df4d505bf55934bd85934ef55134ff49534ff41534ff41514bf95904ff55904bf55904bf8d904ff4d904ef55104ef4d104ff4 + ((0x407890e034e51203e3450b901a2c380c386ca119e9e3068b9124306890a040e9c36427a78c1a2a4860d1214079c2946345490d161c051d38ca88f4f1a2a4868b0e03659729491647d631b15687ac2fa0ad0267df3d91e06ed3735b941c40e056ceb599a0aca4636b015756b7b58d2b014a29f04c7a44914688142c1fdcf80766 + ((0x80014647c64c0e1024204930423a7860c1200049c2a413c6860c1210251d64407a7ca90243058701874e1706080801c5874a104141c306549cf4f142e4490c1a24280d3a567a78a1524306890a0309c5490d161c039d2ac93c5490d161c051d364e7878d14243060b0814000f3a6ca4f4f1a2a4868b0a14069c324680f8d142e + ((0x848702034e9824427c7cb10263058501a74e1a2a4a8470e9b2a5888e102428113a70d501f1c3a64b111c2048501e283054821d060900014ecf0e182e4090e102028001a74c141e910001ce98293c3860a121c20280c380c1210229ca01c3650a121c2048408034e192a412a10239c32568070c14243848401874a0f8e981c204 + ((0x4819d32527870c1424305040a0007192e507a4400073a64b949e1c305090c1414069c32c03860a121a2050408034e192a452a20439d325ca118e9e2e4860c0a00071c32548b04f1a183440809874e19300400c509d04d952c4088e1024280d38528264b1022384090a030e1a2b423860b101c204840e00079c34568474c96223 + ((0x92230639c30568070c1420384840c0007182e54825420473a617870c1422384080c00069d3050924460c73860b95251936589081210200e0f961e2c30063a5ca129e9e365890c1a10200e3a60a129e9e343068810030e182e568070c14203850501a1b263850700c70b9523423a68b92102028001c303c50ca948a9008018686 + (0x70b95601c305080d141030001c60b9522951021ce9728bc3860a11182820600038c97284 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g237H7 (_ : Nat) : Nat := 0x1bc5d0310010295c003a8ee7431b86d8b3a6fa43f3561a46014119646c70fedb3a00a4dc324a0000000000000008babcf27aa003a00900077dfa67d6b21996a0790005b23e59200474ed5763ca61364ce88ae770788c13d6f48da3881ce88d25064b0195510044120021
set_option maxRecDepth 100000 in
def g237D8 (_ : Nat) : Nat := (0x9459040c284180039140f3871851230e20a10600105922c71a51440e20a106000f54f1640e286021b4503c71859040e20a106001071140f1859038a180bccd81ad35409b51d2073a8690c49562644086a8a20e415c120007f517fa6bfd25fe8aff417fa69fd24fe8a7f413de47fd23f691ff44ffa07fd12fe817d807fa03f501 + ((0x69451230e20a10403d24502071859048c388284101075448f1c69459040e20a104041c5514071a51641230c20600104913c91c69451230e20818004164d03471859048c38820600106513c71a516410388206000f5109448c286021a4903c71a51448c30a106001075240f1e51230a180b4d12871859048c30a106000f40f1c6 + (0x174911c69459048c38820403d84901c69459048c30a10403d33cc1c <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g237H8 (_ : Nat) : Nat := 0x2981b8b00427d4d184514000000583656450e3e210e9108cceac0ee1303
set_option maxRecDepth 100000 in
def g237D9 (_ : Nat) : Nat := 0x1483104033f
def g237L : Nat → Packing
  | 5 => (11,4,5,0,0,7,0,g237D5)
  | 6 => (87,3,5,0,0,12,0,g237D6)
  | 7 => (62,2,5,0,0,13,0,g237D7)
  | 8 => (19,1,5,0,0,11,0,g237D8)
  | 9 => (1,0,5,0,0,1,0,g237D9)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 6, h => lookupWord 6 15 3 8 4 0 g237H5 h
  | 7, h => lookupWord 30 104 5 11 7 0 g237H6 h
  | 8, h => lookupWord 21 74 5 10 6 0 g237H7 h
  | 9, h => lookupWord 7 23 4 9 5 0 g237H8 h
  | _, _ => none
def g237 : Forest := ⟨237,9,fun i => g237Y[i]?.getD (0,0),g237C,[[]],g237L,g237I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P5_0 : block g237 5 0 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237B5 : block g237 5 0 11 = true := g237P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P6_16 : block g237 6 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P6_32 : block g237 6 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P6_48 : block g237 6 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P6_64 : block g237 6 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P6_80 : block g237 6 80 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237B6 : block g237 6 0 87 = true := (@block_merge g237 6 0 64 23 (@block_merge g237 6 0 32 32 (@block_merge g237 6 0 16 16 g237P6_0 g237P6_16) (@block_merge g237 6 32 16 16 g237P6_32 g237P6_48)) (@block_merge g237 6 64 16 7 g237P6_64 g237P6_80))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P7_16 : block g237 7 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P7_32 : block g237 7 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P7_48 : block g237 7 48 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237B7 : block g237 7 0 62 = true := (@block_merge g237 7 0 32 30 (@block_merge g237 7 0 16 16 g237P7_0 g237P7_16) (@block_merge g237 7 32 16 14 g237P7_32 g237P7_48))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P8_16 : block g237 8 16 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237B8 : block g237 8 0 19 = true := (@block_merge g237 8 0 16 3 g237P8_0 g237P8_16)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P9_0 : block g237 9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237B9 : block g237 9 0 1 = true := g237P9_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g237B5
  · exact g237B6
  · exact g237B7
  · exact g237B8
  · exact g237B9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 10 := lower_forest (g:=g237) (i:=0) (hints:=1283) (before_sound K207 V207) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K207 10 [(237,[]),(246,[16, 67])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V207 low237 (by decide +kernel)

def g187Y : Array (Bits × Bits) := #[ (0xbdda459fefe2c50ca32bb68d8bc4fa7b1648b5222698ce5f74ac905c8413eda9,0x103830570101440030a1108500048060126930090618441800a880088410e189), (0xe28f7a737d4b7ee321c57ff04689e5a4c578e0cff5282d82ca91ed2be0651197,0x2c0b0540c58000140c015110281812010580009f0024c825a000108e0610103), (0x0,0x0), (0x9c3bd6304af8c664f801d254af073833dfc62762eaf639e4f8766116b08d4e5a,0xc583c3285ed4923704108b128a033116c5860d6241223a64f2527116300d0e52), (0x93a0f7ddfb6b77f7a77408f6c423f739a02b235e1f258817a9ee7ef2420ca5ce,0x852940aa31a55a7ea13888e69408661180a7317609348009a1f416f2000ca4cc), (0x6a110d6ac357b86ba3ae91ba3c9c2e45e498cdc05145e7ac657bd37319308871,0xa807078840a61a5c0b0e80023c082e17048289d0012533040012567318000870), (0x0,0x0), (0x3f75e89d3d1cdb7c5c726407ba7386c82bd71bd5c8cf347187c30a883fca3240,0x8000006000000000082000020000c000000401080003821000), (0x0,0x0) ]
def g187C : List ColumnInfo := [(32,0,155,0,8), (16,0,171,0,7), (8,0,179,0,7), (2,0,185,0,6), (1,0,186,0,6), (34,0,153,0,5), (33,0,154,0,5), (17,0,170,0,5), (10,0,177,0,5), (24,0,163,0,5), (18,0,169,0,5), (9,0,178,0,5), (128,0,59,0,5), (50,0,137,0,4), (41,0,146,0,4), (26,0,161,0,4), (25,0,162,0,4), (144,0,43,0,4), (136,0,51,0,4)]
set_option maxRecDepth 100000 in
def g187D4 (_ : Nat) : Nat := 0x36c2a91e6123060213d132386c8322b88d4889c364191585744c8e1322c82e23522370991641613c92b446ea8e030ae495a22754201c471c45123aac80e234e12851c56407342910b84ea82039914881c3754501
set_option maxRecDepth 100000 in
def g187H4 (_ : Nat) : Nat := 0x534654e000b1004527d9a2f800a5
set_option maxRecDepth 100000 in
def g187D5 : Nat → Nat
  | 0 => (0x754501b354819551406d54e065545019f3788c1514067c9e150885018be4859e354063b8a1678d501e576345635406378e1674d5018be4859d354063b8a1674d501e556345535407d440d154d5018be4859e25406378e16789501e6b62416254063b8a167495018be4859d25406378e16749501e696241525407d84490549501 + ((0x338de2755901ccc3789d564072b91c2755901cce3709d564061f9e16515901c3d4759456407274e14715901cad2851c564068f5206554101a6d28195504073a19e2754101ba94809d504077885c2754101b394819550406da4a065541018be4859d514068f5206554501a5d38195514073519e3754501b95480dd514077481c3 + ((0xe0544a378e117d5b029ce3845f52c0a2f92167457028de3859d15c0a378e117d5902eca274d950c073641d36d47018dd688dd51c073945d26d42018ed6889d50807b18dd26546018ee2841f56406378e117d5901c9e3891d56407270e24755901cae2891d564072b0a24755901c9e478dd564072791c3755901cae4789d56407 + ((0xdf784d915017338dd26454058ee2841f56c4e738a107d4f138be4859d05c4e3b8a167417138ee2841f5644eb58e15745b03ad53815d16c0ead5205745b03ae52815d16c0fb889d1654303cf10758615c0e3b8a16785503aea2855d06c4aba4a05741b12ab94815d06c4ab64e05741b12ed23741951c4b3c45d60817128de3859 + ((0x89905aad4809a164172b91e2645905cce37899164163bde02645905aad48099164172b91c2645905cce37099164163d9e161059059da3845f50417338de26455058ee78898154172b51e2605505ccd37898154173a8a26754005cea6789d50017aa89d4654005eca274d950016bade12654005ee22745950017278dd46454058 + ((0x791e3641915cce278d90645637de03641915a9d480d9064572791c3641915cce270d9064563e9e160019159e62841f51457358e26754415cd6678dd51057a58dd4654415ad7784d951057b18dd2654415ed23741951056a75203745a05ada3845a508162f92117899058de3845e26416ab9211789905ace3845e26416ba42017 + ((0x1a4510e421023f0f63c0ea390de360c930cbd2dcb12aca527c90228841f8781c86c1986016854138480e4330b4270841b0540f0023b8a107859359ce2841f534d6378e117819259ce3845f52496ab5202741a15ae62841a518562f921078d9158ee2841e36456a7921078d915ace2841e36456b5460078d915a9d480da064572 + (0x108200000000000881dfb78dcb6cd9b60d6b54d3b48d0b33cb727c8709c0efdbdef1baee5b7ed9b4ecdb1ec1aeeb5abea9a8e94a3a88a0a6a9925e96252932469023a8d22e8a222872168420a811fe7e1f27b1e6781da751ce721c26f1b66c1aa6919e66192631866017a5d16e5a162571565414a5113e4e1324b126481 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 1 => 0x306080001a25004000000000000000000000000061010000342a00800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000402000000000001c10000000000000
  | _ => 0
set_option maxRecDepth 100000 in
def g187H5 (_ : Nat) : Nat := (0x1d1b08c42ecf50e000105598f5a80000021ec5f08bede1895cebcfc0035fea1a138000003480d2acd35c2da64a28d6d701300000014fa17d09c513033c7a1029c517b20ec8b039207d0641ad758418b4001d140039400000211cf86a014d99aec400400010e1880140400180410800880054a404515d00001600704e240000 + ((0x20af8df1dcca80036080031580000010b1d931f800395c4454c0860c4c9bd934001156e17203473969c750cd1d5d4e5b183540ac28d0dc85c9b14543ed635e84e7467cda8a6c7e5266108f35b449354a052581db9922598000dc8d87551da0000000404000002cc756e5d045f4260591dbcb891c84b16653d4c800159f5f4000 + (0xc0f410d2f5e60ec41dd09dadd8b99406c00 <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g187D6 : Nat → Nat
  | 0 => (0x4067fb3c6a80cfd678d501bf20f1aa037d45e354076fb1c6a80f75158d5019fece9aa033f59d35406fc83a6a80df6174d501dbac69aa03f640d35407ba8aa6a80cff67895019facf12a037e41e25406fa8bc4a80eef6289501ef20b12a033fd9d254067eb3a4a80dfa0749501bea2e92a03bb58925407f28924a80f790549501 + ((0x54501cfecaa8a039f195514077a33aa280ff20754501fe00ea8a03f58dd51407ea1baa280df62754501eeecaa8a03dd19551407f982aa280ff10554501dec6ca8a03bd4d9514077b132a280ef52654501fe460a8a03fc4c151406faabc4280ef65688501deaad10a03fc54221407f3b124280ef65648501deaac90a03fc54121 + ((0x19d50407f90baa080ff01754101bf46ea8203fa89d50407f413aa080f7b6554101ef0caa8203be8d9504077c9b2a080efa2654101df24ca82037e55e304077d2b46080ef9568c101fb6c698203be959304077cab26080df907d4501cfecba8a037d55e51406fbb3ca280ff30594501fe20b28a033f59d51406fd03aa280dde37 + ((0xcfe2755901ddc4eab2033b89d564077613aac80cff6715901b7a8e2b203774dc56406f6938ac80e7d651590197a8e2b203374dc5640676938ac80cfd578d901dbc6e9b2033f95d364067eabc4c80eee27499019fcae932037d45f504073fb2ea080df95794101bf6cf282037d85d50406f713aa080e7f6554101cf8caa8203be + ((0x4037b89d508073f32aa100e7d6554201dda4ca8403bd99d51807eb1baa300ee526546019fa0fab2033f45f564073f32cac80cfd37959019fa4f2b2036f91d56406ef1baac80dee2755901cfcaeab2033f81d564077d03aac80cfe1755901dec2eab203af91d564065f23aac80cfe3755901dbc6eab203378dd564076e1baac80 + ((0xeac816ee27559029dc4eab2053f85d5640bf513aa0817e90554902ed20aa92053f59e1540afc83c2a815ed27855029fcce8aa05778dd1540b7d33aa180fea2754301db26ca86037e41f51c073eb2ea380edd36d4701bf40ea8e03778dd51c073f32aa380e7d6554701dba6ca8e037d45f508073eb2ea100eed26d4201bec2ea8 + ((0xcce82a257b89d0544bb692a0a894fd17d5b02ddc4eab6053f85d56c0a7f2ba2d817ea2754302df22ca8605bb59f52c0bf483ea5815ed17d4b02ddacba9605fa41752c0bb482ea5816ed5644b02fd2a0896053f59e15c0afc83c2b815ee27857029fcce8ae053f59d15c0af713a2b815de3745702deac28ae05f948515c0a7e8b + (0xb7caba0d896f85741b12fac6ea8e257d81d51c4b7a832a3896f106547129facf02e257d45e05c4b7cb040b894fe67417129face82e257b89d05c4b7cb020b894fd07d5912ddc4eab225b78dd5644a6f1baac894fe0755912fcc4ea8a25f58dd5144afb03aa2897e515549129facf02a257d45e0544af693c0a8976d25815129f <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 1 => (0x703deac28ae073f45f5640f6f1baac81eee27559039dc4eab2073f85d5640fed1baa081fea2754103bf42ea8207f64155340eeeabe2681edf56c4d03fb2a189a073f59e1540efc83c2a81ddd3785503eba6b0aa073f99d1540eef1ba2a81fd63145503eba6a8aa073f41f56c4a7f03aad894fe5741b12df6ae83625be95d06c4 + ((0xd5644e7f03aac89fd63754513faa2aa9a27d54555344e7eb3c0a89df51781513bba6f02a273f99d0544ef713a0a89cfd17d5b039fc2eab6073f95d16c0f7baba2d81ef65745b03deaae8b607bd15d16c0ff513aa181dfa1754303df22ca8607bc45950c0e7eb3c2b81df90785703deac30ae073f99d15c0e7eb3a2b81dde3745 + ((0xe3745405d7a8c8a80bb74d915017769322a02fcd2554d239fa0fab627b78dd56c4e7f03aad89cfe5741b13fac6ea8e27bd41951c4f6eb3ea789fd517d4f13bba0fa9e27b759753c4fea8aea789f5515d4f139facf02e277d45e05c4e7f33a0b89cfd6741713bbc6e82e277b89d05c4f7cb020b89cfd07d5913dbc6eab227378d + ((0xbbb89b154167fb3c2a82eee2685505bf40e8aa0b778dd154177bb0a2a82eee26455059fece0aa0b6f51c15416ee9b82a82ded2705505ddc4c0aa0bbe99d500167d33aa002fea2754005d728ca800bb64d95001774932a002ef91654005de22ca800b3f59f150177ab0e2a02ebd46c5405dba6d8a80bbb49b150167f33a2a02dd + ((0xc82ded27c5905ddc4d8b20bbd98616417771342c82eec26859059fa6f0b20b3f49e16416df23a2c82dde3745905bdc4e8b20bbb89916417761322c82ef56105905ddc4c0b20bbb89b50416fc8bea082fea26d4105ddc4d1aa0bb7d8d35417771326a82f6f6289505ddec492a0bdb89d25417b7b124a82df907c5505deec38aa0 + ((0xe0ae0b774dc15c16f69382b82dde3745a059fc6e8b40bb78dd168166f1ba2d02edc3745a059fc4e8b40bbe45a50816ef1ba2b02cfd178d905bdc4e9b20b3f45e26417f503c4c82eee3689905dda6d1320bbb81e264177683c4c82eee3789905dda6f1320bbbc5e26417770bc4c82eed1789905dd82f1320b7bd9c26416d6a384 + ((0xcb000c8aede3601915dbc6da8a2b7d41f51457eb1b6a28af5f638d515dbec69aa2bd78dd35457afb1a6a8aede3689515ddec492a2bb78d9254577b33aa20acf66754415fac6ea882bad519510576a9b2a20aee52654415dea0ca882bbc41951056fc83e2b82ef561c5705bf40e8ae0b778dd15c177ab0a2b82df90705705b7a8 + (0x5dbc2f1b22bb745e364576f13c6c8aedd278d915dbe0f1b22bb781e364576e83c6c8aedc078d915bbece1b22b6751c364576f1b44c8acfd0789915bbc6e9322bb78d926456ee9be0c8aede36c1915df4c10322bb78da064576e1b40c8acfd37819159fa4f0322b6f91d06456ef1ba0c8adee2741915dbc6c8322bb70d9064577 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 2 => (0x68d67713a0d1acfe1741a359fa0f0b26b3f45e064d6f713a0c9addd17d4d35bba0fa9a6b778dd168976f1ba2d12cde3745a259fc0e8b44b3f85d068967e83c2c92dde37459259fa2f0324b7b45f52496f683ea492dee2741a159fc6e8342b3f89d068577713a0d0acee2741a15dd84e8342bbd41a518567e83c6c8afd6178d91 + ((0x8183f61f40f687983c61dc0ea87483961c00de86c83561a80ce863830e1840be85e82e61700b685982be1540a8853828612c092847822e10c08283f81ee0f407683981be0dc06a83381960c005882a814e0a004c823810607c03a81b80ce06402c814808604001c80c804e02000a803800e0004fe0745a35bdc4e8346bbb89d0 + ((0xa63cc1e48f187863bc1d68e9874639c1cc8e5872638c1c28df86f63741b88db86d63641ae8d686a634419e8cd86663301968ca864e32418e8c686263101848c085fe2fc1788ba85be2dc1688b2857e2bc15a8ac855e2ac14e8a4850e28413e89e84ee27013689884be254126891848623c11c88c845e22c11088684262101068 + ((0x830097c8bde5ec2f09768ba65cc2e49718b7e5b82d896a8b4e5a02cc9658b1e5782ba95c8ade5602ac9558a9e54429e94d8a565282909468a2651028694189fe4f027493889b64d826a933898e4c025e92e896e4a8250927892e49424692188e647023491988be45c22c913889644821e90c885642420e906881e3fc1ee8f687 + ((0xa1890b6854420a0e905e82c40ca028ff67f83f49f88fbe7dc3ec9f58f967b83d89ea8f467983c89e38f167883bc9dc8ede7683b29d78eae7443a09ce8e6e72c3949c98e367143869c18e066f83749b28d8e6c035c9ad8d666ac3549a88d3669834899e8cee6743389988cb66583289918c7e63831698a8c4661c30a9848c1e60 + ((0x4eea74536a9a94c6a5852aa909466a24510a84941ea0c504a8193f69f84faa7c93de9ec4f4a7893b69d84e8a7393969c84dea6c934e9a44cea6593269904c6a62930e97c4baa5b929694049ea4e926e930496a49924692048aa4191f68f847aa3c91de8e8472a3791b68cc460a2d91568a044ea269126890444a2090f6874434 + ((0x100080c104a2210c022040c10100080c10421083018404881c2c614b08982ec10604b0097febf05f6afa97c6bd85e8af3978ebc45deaee9756ba85d0ae7972eb905c6ae296feb745b6ada96ceb645b0ad796a6b4c5a2ac8963eb1c588ac295feafc57cabd95deae8572ab895aead4562aae956eab4558aab954ea98546aa09 + (0x2000c8822204001000010020100003610888108040018410c0a0888108040c1000412104001048800200108422104003620808040030004000040070400084107041188200004a10830100d8a84521041c16204302c2210484104040020488122040020488100080020322a10c101008410404080020322081010c060c12104 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 3 => (0x2040000400200004a1080c0820104001e0040044208302c10084100c0b048202e01c00204101000008810b04e00c88100101000000010704841000c100000001080402104280f80302040410000000000004000040000400100001e00b80109e008002e00b80109e00800c04000012110c0c338020ce0080000400000100840 + ((0x30304004040c04201060c104810800004081e00400304101041c10043000040108081010410100004041c10104081000c14204042042c0d098580500000280f8030304003040c082020610103820800004041e0040030810204200c083010408103040000c1020404100000490808382040820400b042c1120b44e010008040 + ((0x81c2050818422a1a0102c10be00800b060460102c138030b04e00c00b04e00c10100000003010a0f0907004a104841a10408042020400001141010e04102041002810a0444290f80400041000800200003a2080810007801000d0420c03010c3c30280e04078070004103040000410010141040410428118905805000002c138 + ((0x42b8020028140d8040a03e00c280f80300280f803000000a10008000000000041e00400304000002a10804002442208009042c10000000185802440580112100e0b08c4e160208808200002101000c10002202082286803a1a00800000280100001002c88083840008300820c220b08002000030400007081000684103020b0 + (0x81c1e008041020404100310c04300001070b8020204002040010400c44020c00304002078010000200090c8420a0400000006260090c16004443c34281f0f89808000210108241210108000083040c1000210108007a2a00e8a802000000a0042884043830008300420c21080000400a <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | _ => 0
set_option maxRecDepth 100000 in
def g187H6 (_ : Nat) : Nat := (0x8b830008d0914242022c6c39a0a0c0050214405041420000867000800208001c006601c1000008a0208081190400d81022049104341114210181022410e142ce86004018000180000400481021018002001070c080000000800040800c0a0010b00401865204380062452104000020a0418010000000e1c003062c6800804080 + ((0x8d0006da09630693d4122b474000f6090239a3369ccc8002c9e0cd272b4362078660000000001f9a0002bc0095b1449a521ba9a000769ec9c0000001c9d6729332770c5fbe4dee21c53980035f7578248aeaf9d6132d4f0002670c3434ec80b8dbcbd6092d216ae42ee5fd4ed8fe0925bbb8ac8c23a949bac5811b001011d184 + ((0xee1edae43bc12c25636e91c0c8000067bb2fa988000000000e124e16b79aea00020188160f458522c0000776c7d5ba4000000304d300001574eb7836c001a42465f80784398dc54946ea3b94b24fd280ab5d3045262200006636bcbaeb1205b0c2dd8d93423b880a1dcc99f70800076549a06e004c0d381358d8ea2ad861082 + ((0x4acfeb658bd8a355135beb58000a7c81948f8000001faa262f8d716ba2de5954ffc2734900779a900f1a7b18537291cf568cddaedc9c7840000060000000079a1bd55520d044920b2cdcfcbcc7a9f04596da29450835d6c3ca00e7a4912008daba6df740a3d1995aae3dccc8694426ed921e1a8f0f096743d9260001cbcd1092 + ((0xa7b891196b2ba000ed18d916b3ef2b18fb088fa9811c3695d82be60b831881b5e00092b5d0c000653000000174000053c80020bbcb811511b99c88af0677c45192b709388af1b7768b9a34b9e0ec000950906d201d18876e098a75b7b834737dea6554f47b041d024c78b76365901f4c9ac2abbf7b78af2a1aad7698da699929 + ((0x7365040017290000003e5c8ddcd2cbf800063982f80bc000c720003845f280004360000000000991e924000000000608c0014409650b108b80003df8e74b5bf2df5f01c31fa13c8863cb3afa050d907d7f26a865826e351015736ebf529801e0006839c84c4e0679b1cb87cb0000a56d693b05c44bc91eda45204363a33c610a + ((0x32f2fb28502e413e4c00081f357aee3f15f3d520f25425928d005f00837c37f800246e00043c191f1d90c8719306800174a17400022c529c085867ed59d759b90944001ad6e22a6b1e88003f71d63adec0002920000000000000098a9abd8900000029680005510000000000000057000141622ace036cadb293206cc0001130 + (0x277fd4af2cd05e498d1d03ed55e3f325c307ab96c8ab88001b7f0000002ef4ba2992e439c71eee00006f8000f010006a1ed2963ffd32cac4f800096f012da7269650e8b18310000e812918058cf8edc803229f275335a2dd9ea9192462700b1f9128b00ec4e1e000ea846 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g187D7 : Nat → Nat
  | 0 => (0x4201ff54201fd54601ffd5901bfd5901ff95901bf95901ff55901bf55901ff15901bf15901ff8d901bf8d901ff4d901bf4d901ff89901bf89901ff49901bf49901ffd4101fe94101ff54101fe54101fe8c101fe4c101ffd4501fd94501ff54501fd54501fd88501fd48501ff8d501ff4d501ff89501ff49501bfd5801bf55801 + ((0x2bec1b12bf41b12be41b12fd54712ff81712ff41712bfd5912bf55912fd54512fb54912ff81512ff41512bfd5b02bf55b02bf45b02fe54302fbd4b02fb44b02ff85702ff45702bfd5902bf55902fe54102fb54902ff85502ff45502bfd5b01bf55b01b74db01fe54301ffd4701ff54701bf41a01bfd5a01bf55a01bb49a01ffd + ((0x54005ffc5405ff45405bfd5923bf55923fb54923f754d23bfd5b13bf55b13bf41b13fd54713f7d4f13ff81713ff41713bfd5913bf55913fd54513f754d13ff81513ff41513bfd5b03bf55b03bdc5b03bf45b03bd45b03fe54303ff85703ff45703bfd5903bf55903fe54103f754d03f7c4d03ff85503ff45503bfd5b12bf55b1 + ((0x5df49605ffc5605ff45605ff8d905bf8d905ff4d905ff89905bf89905fb89905bb89905ff49905fb09905ffc5905ff85905bf85905ff45905ff05905ffd4105fed4105ff8d505ff4d505ff89505df89505ff49505df49505ffc5505ff85505ff45505ff05505bfd5805af51805b74d805bb49805bdc5805bf45805bd45805fe + ((0xf89915bf89915ff49915ffc1915ff81915bf81915ff41915ff01915ffd4515fdd4515ff8d515df8d515ff4d515df4d515ff89515ff49515bfd5815af51815b74d815bb49815bec1815bf41815be41815fd54415bf45b05ffc5705ff85705ff45705ff05705bf41a05bf4da05bf49a05ffc5a05ff45a05bf45a05fe94205df896 + ((0xa35bf89935ff49935bf85935ff45935bf81935ff41935f7d4d35bf4da25ff45a25bf45a25ff41a25bf41a25bf8d925ff4d925bf85925ff45925bf81925ff41925fbd4925ff4d525bf41b15bf45a15bf4da15bf49a15ffc1a15ff41a15bf41a15fd94615df8d615df4d615ff8d915bf8d915f78d915b78d915ff4d915f70d915f + ((0x30c8c102fb8ba92dacb182b84abf2a3ca742948a0d273c998258493f24908df228486320b08111fd879c1d5c7191b6c6c01a9466e198462a183c5df16f459b15ac526142c4b8125845110d83e30f0437c0da032a0c202d80a6824e08e81fc07681aa05b012003dc0ce029407c00f8000bf49a35ff45a35bf45a35ff41a35bf41 + (0x5ab46a49a5468e5a1e679d9c566a9996656193664358eb62b58846135832605d7f55f317805d0970b5b5169d592961357a95c8567d54553c949f51314074f2537d4d193244c252e74a8926448b51f647511b945d113644190b3422905340e101d3f7cfa13da8f2c3bf0eda3ae0e7338d4e0536e4d903564d3e348cce5329cc70 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 1 => (0xca3c28c7a1d281a9fc67a59e0e7379c726de9ad667098ae5d89616571955a51f93da4bf920645f90323e38eea3988d6a3388bce2c38aa228d895a2348866205871e1a5859e13e841e0e582f207080c9ffb7f11f8d7ce9f037b69e957a05e6d7949e3077add987515d317459cdf72d9c7f7105c2d7049bf06eadb7b6d65b066b7 + ((0xb0e0206040688418101a2c3806162820344840e02078a0e1218344840e0286040860a10101e24380818101a11060407890e01858a080d102438081e2c444080d1024380a18101a102291080d08114604068810a4820344085101c203040700020407080c101c0008b0fec16af0eba1ad56afbab4aa86a9aea1fa7f69bfa57a93 + ((0x182038001028447880d161c040c07083070910630508080d0e01c6024888c04070001c6040618406080e00030c4485008080e00020c080d1214031222302030407000241a10218f18283840609081c000b141d0811078c141e1824380012111020c78c162020344080e00058b10881083c60b1111101c0009180c2182c384068 + ((0xb081c000b2430384840b00f1e202c02088f10182c030c08083080c1211080c17101c203800124880b07080e000410182c24205807244060b080b00e305840420b06843182c38406080e00048b0e1018203800102e407090f121c040c161c203458071812086120a10c6080e101e205840e04000c182840406080e00048a1010 + ((0x3808501c22303806181c2011038406044182820384080e00048a080e10203800101c203858700c3058a07081610380014281c2c38052430503840b00e302030c2030418f182024203800104878809080e00040f18201c205807243c608480c1602060806084101018210607080e10203800121c20384080e00040c101c20384 + ((0x4303804180c086101a20220f182824305070002488f1410141c00081e30503820700e4478c140c0e01c60a06044141110630584060a081c00091610182820700020404078a0e01860b14101e205040e00058b098a0e01488c1612081c038c080c3080c08640607060a0e000411201c18283800104060709040e01c890181c223 + ((0x60b0e13121c038c161c222c3807101c203c58700e30587080f102c2070002c60b0e13161c038c161c260141c283004070a0a1802901e304c88e101c28380018488901e2420385070002c9101e30488480a081c0591203c6090e8e1020380b182020305040e000488080c141038001030407078814103800144460807040e01e4 + (0x80d102c2070002e222058700b1e222c3805242d102109101622222c3808100d106302030c60406080e0003834485008202030c24208911181304040008181c24210884848408a3058404210182e204440b01048584440852440584440b00e101c20c6048418407090881212242805182c38406080e04000a182c386098b0a020 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 2 => (0x2c60a100f161c038c14201e014587080c16103800121018430204101a10c22242804161c20304070200049120303840609081c000b244060b080d102038001630184301a10c60406080e00038c161c2601460b8811102c03922030584440b01030184301a10c80c42044201c20304840e000491201d1210230c0888108405c40 + ((0x841e2020344080e0004921e21102423070884318101863020304070001c222428040e101860e0844888c07820200040c140c0883c60a860d081c0411140d0811488f140d081c038c100e088481a205045182840406080e04000a1828405078b0a02060a100f121c038c14201a2c3807101c203c58700e30508080f102c207000 + ((0x512161032232202c10100020911048408a284040788101c000914202030407020004911e305040609081c000b243c608080d102038001630204302220c60406080e00038c14201e01460a860d081c03911e305034207010301a10220f1412183c409081c000b8789081c02c887890e01488a42044223c50787890e02078c440 + ((0x8e101a205040e00061222251021488f141018282070002888a06191201c20305040e0005110e1110848643038202000411203c627080e102420700034608068441e304040708101c000a182c24204290182d2040708101c000b24407c8080e102420700030911128408a48788080e10203800144840342212202c20384080e00 + (0x244078c50101a205040e00068c140e0811478c141118305040e00058c0e1110840607080c14103800144480f <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | _ => 0
set_option maxRecDepth 100000 in
def g187H7 (_ : Nat) : Nat := (0x900094a0003a4000a8d000484134d8cda3490000aae917a99737f662ba1b37250aac96f5dd28c203c78bdd64960ece8b5547000fdea46000348000718c8900037b0000001003a9dc988420400b30200004419904c0550441431a40060004403c201324202104064200018404100e0401810050011400112c40ca1c30040800c3 + ((0xdddca171abe1af912a53d6c1b1f7539c9cb99d263ad7c78ca7786d9435ce4d96e6b484c000000e16677000d5b1d3000859000000000000000000550f51413d2accfd8f00000090bc7de85c830007981c42c385f86200000033f85e000000588772e688a92db3bb630f04c3d11caa14d8035224033fa0e082cce564c24437d66d + ((0xd7e5da36f3b811e014d03061542c49a26000119632cb0c8b000c07f1b406958538000a920050009ab000000000b3b50155a87a0000000000007d500014ee7f29b74b39eea612d576000000b93000000b0200089166bc299806b9c11ea82cd5df3b680906a6bf8d2d45165b15181f27540a2352fbd4ec01ac000c1fc9a13932eb + (0x882000500000000787b1d36940a036cb241aebcd0d84f6b71c8174cd0a54ac648a76d65747033eac1ec983132218ec95b446977d1fad467a3a079a41610d2bdc5a7cb0c42c40f62190e3555a5ea289f952f3c6735dc <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g187D8 (_ : Nat) : Nat := (0x84180030b2071038828418002ca2071038828418002cf2ca2071038828418003481c40e20a106000ad8d9e3125d6b294ea794aa8d1039e337e66cbe95927645c7c8d817424c3784b042001fe35fe9aff897fa4bff15ff0aff457f82bff05ff02ff417f80bfd23ff89ff44ffe07fd03ff897f44bfe05fd02ff80ff807fa03fc01 + ((0x38f2881038828418002cc2881038828418002cb1c40e20a106000a49140c2c71038828418003902c71038828418002cc2c71038828418002d03c92071030818002c81c40e208180024f2881c40e20818002cb2840e20818002503ca1c40e20818002cb2840c284180024f2c81030a106000a2071030a106000940f2c81c40c2 + (0x1240f30a1c40e208180035140f28710388206000c4503cc2c81030a106000d4903cb2040c284180030a2040e20a106000a4913cc28810388284180 <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g187H8 (_ : Nat) : Nat := 0x70d844f79d016accb3ec001294c247a9560000000eb690009425c36219d811bdb400c41e24000034
set_option maxRecDepth 100000 in
def g187D9 (_ : Nat) : Nat := 0x10401bf
def g187L : Nat → Packing
  | 4 => (10,5,5,0,0,6,0,g187D4)
  | 5 => (135,4,5,0,0,10,0,g187D5)
  | 6 => (449,3,5,0,0,13,0,g187D6)
  | 7 => (224,2,5,0,0,14,0,g187D7)
  | 8 => (25,1,5,0,0,11,0,g187D8)
  | 9 => (1,0,5,0,0,1,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 4 12 4 8 4 0 g187H4 h
  | 6, h => lookupWord 45 160 6 12 8 0 g187H5 h
  | 7, h => lookupWord 154 534 7 13 9 0 g187H6 h
  | 8, h => lookupWord 82 272 6 12 8 0 g187H7 h
  | 9, h => lookupWord 10 31 4 9 5 0 g187H8 h
  | _, _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,[[]],g187L,g187I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P4_0 : block g187 4 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187B4 : block g187 4 0 10 = true := g187P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P5_16 : block g187 5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P5_32 : block g187 5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P5_48 : block g187 5 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P5_64 : block g187 5 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P5_80 : block g187 5 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P5_96 : block g187 5 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P5_112 : block g187 5 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P5_128 : block g187 5 128 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187B5 : block g187 5 0 135 = true := (@block_merge g187 5 0 128 7 (@block_merge g187 5 0 64 64 (@block_merge g187 5 0 32 32 (@block_merge g187 5 0 16 16 g187P5_0 g187P5_16) (@block_merge g187 5 32 16 16 g187P5_32 g187P5_48)) (@block_merge g187 5 64 32 32 (@block_merge g187 5 64 16 16 g187P5_64 g187P5_80) (@block_merge g187 5 96 16 16 g187P5_96 g187P5_112))) g187P5_128)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_16 : block g187 6 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_32 : block g187 6 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_48 : block g187 6 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_64 : block g187 6 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_80 : block g187 6 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_96 : block g187 6 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_112 : block g187 6 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_128 : block g187 6 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_144 : block g187 6 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_160 : block g187 6 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_176 : block g187 6 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_192 : block g187 6 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_208 : block g187 6 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_224 : block g187 6 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_240 : block g187 6 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_256 : block g187 6 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_272 : block g187 6 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_288 : block g187 6 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_304 : block g187 6 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_320 : block g187 6 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_336 : block g187 6 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_352 : block g187 6 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_368 : block g187 6 368 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_384 : block g187 6 384 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_400 : block g187 6 400 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_416 : block g187 6 416 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_432 : block g187 6 432 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P6_448 : block g187 6 448 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187B6 : block g187 6 0 449 = true := (@block_merge g187 6 0 256 193 (@block_merge g187 6 0 128 128 (@block_merge g187 6 0 64 64 (@block_merge g187 6 0 32 32 (@block_merge g187 6 0 16 16 g187P6_0 g187P6_16) (@block_merge g187 6 32 16 16 g187P6_32 g187P6_48)) (@block_merge g187 6 64 32 32 (@block_merge g187 6 64 16 16 g187P6_64 g187P6_80) (@block_merge g187 6 96 16 16 g187P6_96 g187P6_112))) (@block_merge g187 6 128 64 64 (@block_merge g187 6 128 32 32 (@block_merge g187 6 128 16 16 g187P6_128 g187P6_144) (@block_merge g187 6 160 16 16 g187P6_160 g187P6_176)) (@block_merge g187 6 192 32 32 (@block_merge g187 6 192 16 16 g187P6_192 g187P6_208) (@block_merge g187 6 224 16 16 g187P6_224 g187P6_240)))) (@block_merge g187 6 256 128 65 (@block_merge g187 6 256 64 64 (@block_merge g187 6 256 32 32 (@block_merge g187 6 256 16 16 g187P6_256 g187P6_272) (@block_merge g187 6 288 16 16 g187P6_288 g187P6_304)) (@block_merge g187 6 320 32 32 (@block_merge g187 6 320 16 16 g187P6_320 g187P6_336) (@block_merge g187 6 352 16 16 g187P6_352 g187P6_368))) (@block_merge g187 6 384 64 1 (@block_merge g187 6 384 32 32 (@block_merge g187 6 384 16 16 g187P6_384 g187P6_400) (@block_merge g187 6 416 16 16 g187P6_416 g187P6_432)) g187P6_448)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_16 : block g187 7 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_32 : block g187 7 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_48 : block g187 7 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_64 : block g187 7 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_80 : block g187 7 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_96 : block g187 7 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_112 : block g187 7 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_128 : block g187 7 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_144 : block g187 7 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_160 : block g187 7 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_176 : block g187 7 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_192 : block g187 7 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P7_208 : block g187 7 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187B7 : block g187 7 0 224 = true := (@block_merge g187 7 0 128 96 (@block_merge g187 7 0 64 64 (@block_merge g187 7 0 32 32 (@block_merge g187 7 0 16 16 g187P7_0 g187P7_16) (@block_merge g187 7 32 16 16 g187P7_32 g187P7_48)) (@block_merge g187 7 64 32 32 (@block_merge g187 7 64 16 16 g187P7_64 g187P7_80) (@block_merge g187 7 96 16 16 g187P7_96 g187P7_112))) (@block_merge g187 7 128 64 32 (@block_merge g187 7 128 32 32 (@block_merge g187 7 128 16 16 g187P7_128 g187P7_144) (@block_merge g187 7 160 16 16 g187P7_160 g187P7_176)) (@block_merge g187 7 192 16 16 g187P7_192 g187P7_208)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P8_16 : block g187 8 16 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187B8 : block g187 8 0 25 = true := (@block_merge g187 8 0 16 9 g187P8_0 g187P8_16)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P9_0 : block g187 9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187B9 : block g187 9 0 1 = true := g187P9_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g187B4
  · exact g187B5
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=65603) (before_sound K237 V237) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K237 10 [(187,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V237 low187 (by decide +kernel)

def g255Y : Array (Bits × Bits) := #[ (0x2a22e8c5084077017342c00af51cf3b0a9e2a960040a192da4333cd03100434a,0x2000c8000102200052404000fabc019001c080200402190ca4211cd031004200), (0xb001400b55ce200f2df153a0ded300cea50c44891532a796c4b608e043158480,0xb4442000c49c053208e9940822108440911228584841608c003140080), (0x44b84c299a552a1bb1c4eab5bec20f065a950357b19195d024638d483f985031,0xa85c215a452883a0c44b251ed2181208850353919195d024238d4833905030), (0x8de974e18ae18b4507177f8a000be02332b273db53cc6071a016d374c22d0005,0x9d6931e78ee08a25019337a20043e82a123273d951cc60710016c324c20d0005), (0x4e118c3039ac24f0bcd828d95165adda148a71309410685156e863be74da6261,0x4f7d8c603b3064f03400048a51648978148231308410685152e0633674ca4261), (0x4dc6a75c04308c44da2d12340087288d026216818845e9445b054003ac089940,0x4c45214400108440000800100000204c02221080000460004a0000028c088940), (0x9d108a33ca82fa6a044af605271080235511b00461e810821340612581a76e1b,0x11000290208052200400a440000000214410200460480002114060250023240b), (0x62cc3b30306185b680208d45d82417118805083e4a06460a08088e0f126230ac,0x800010000011028020884500001601c80508060a0002020008000900203008), (0x0,0x0) ]
def g255C : List ColumnInfo := [(1,0,246,8,11), (2,0,237,16,11), (4,0,187,64,11), (8,0,246,1,11), (16,0,237,2,11), (64,0,187,4,11), (32,0,155,68,10), (0,8,118,129,9), (0,16,109,130,9), (128,0,118,9,9), (48,0,207,0,8), (40,0,215,0,8)]
set_option maxRecDepth 100000 in
def g255D10 (_ : Nat) : Nat := 0xa6681b5904cf2c702cb6671b5d230f2c702e400f3d75517d75d535
set_option maxRecDepth 100000 in
def g255H10 (_ : Nat) : Nat := 0xee8
set_option maxRecDepth 100000 in
def g255D11 (_ : Nat) : Nat := 0x126a968498e42886003926a968498e428860039483549394604ace6ad0728c09b2663300ffcafff55fdea2fdd35
set_option maxRecDepth 100000 in
def g255H11 (_ : Nat) : Nat := 0x10fb30004400
set_option maxRecDepth 100000 in
def g255D12 (_ : Nat) : Nat := 0x32a19080eff
def g255L : Nat → Packing
  | 10 => (2,2,4,0,0,7,0,g255D10)
  | 11 => (4,1,4,0,0,8,0,g255D11)
  | 12 => (1,0,4,0,0,1,0,g255D12)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 11, h => lookupWord 2 3 1 5 1 0 g255H10 h
  | 12, h => lookupWord 4 7 1 6 2 0 g255H11 h
  | _, _ => none
def g255 : Forest := ⟨255,12,fun i => g255Y[i]?.getD (0,0),g255C,[[]],g255L,g255I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B10 : block g255 10 0 2 = true := g255P10_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B11 : block g255 11 0 4 = true := g255P11_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B12 : block g255 12 0 1 = true := g255P12_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 12 := by
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
  · exact g255B10
  · exact g255B11
  · exact g255B12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (varsX 255) (graphGoal 255) 13 := lower_forest (g:=g255) (i:=0) (hints:=66883) (before_sound K187 V187) g255G g255T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def postedGraph : Sig := 0xfffffffffffffffeffffffffffffffeefffffffffefefefefefefefeeeccaa00fffffffffffffffeffffffffffffffeefffffffffefefefefefefefeeeccaa00
theorem postedGraphProper : proper postedGraph := by unfold proper; decide +kernel

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [1, 7]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [12, 5]⟩,
    ⟨.or, [12, 2]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.and, [4, 10]⟩,
    ⟨.and, [14, 8]⟩,
    ⟨.and, [13, 11]⟩,
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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (([8, 16, 32, 1, 2, 1, 1, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((([8, 16, 32, 1, 2, 1, 1, 1] : List Nat).getD i.val 0) ||| (1 <<< i.val))

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

def coreMoves : List Move := ([].map swapRows) ++ fixRows 0 0
def removed : List (Sig × Row × Row) := []

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem restricted : Lower true eightInputs postedGraph 13 := by
  have h := lift_ok (u:=true) (ms:=coreMoves) (T:=postedGraph) (raw:=eightInputs)
    (base:=varsX 255) (G:=graphGoal 255) (xs:=removed)
    (by decide +kernel) postedGraphProper (proper_of _ (by decide +kernel)) low255
  exact h

theorem excluded : Impossible true postedGraph 12 eightInputs.toFinset := by
  intro k small run
  have steps := list_run run eightInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper postedGraphProper)
    steps (eightInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := restricted q bank built hit
  omega

end PEqualNP.Outside.L_meta_30837

theorem PEqualNP.Outside.L_meta_30837 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_30837.replaceShort PEqualNP.Outside.L_meta_30837.excluded gates o fit correct
