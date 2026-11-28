import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28866

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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 4) ||| (x 1 &&& x 6) ||| (x 2 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 5)

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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 4) ||| (x 1 &&& x 6) ||| (x 2 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 5)

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

def g49Y : Array (Bits × Bits) := #[ (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbde7,0x4062), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0xd7fc,0x208c), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7edb,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8411), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g49C : List ColumnInfo := []
def g49D3 (_ : Nat) : Nat := 0x7
def g49L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,g49D3)
  | _ => emptyPacking
def g49I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g49 : Forest := ⟨49,3,fun i => g49Y[i]?.getD (0,0),g49C,[[]],g49L,g49I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g49P3_0 : block g49 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g49B3 : block g49 3 0 1 = true := g49P3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g49T : checkedTables g49 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g49B3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g49G : graphValid g49 (boundsBefore K0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low49 : Lower true (varsX 49) (graphGoal 49) 4 := lower_forest (g:=g49) (i:=0) (hints:=4) (before_sound K0 V0) g49G g49T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K49 := extendKnown K0 4 [(49,[]),(73,[67, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V49 : Known true K49 := extend_ok (m:=49) V0 low49 (by decide +kernel)

def g27Y : Array (Bits × Bits) := #[ (0xffffffffffffffffffffffffffffffffffffffffffffffffdfafafebc7ff6c7b,0xffffffffffffffffffffffffffffffffffffffffffffffff22502011c2012823), (0xadfa79bfb8e0bbb4,0x521302fd024158b4), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffe73d37abe33cda5d,0x18a2c30e142cc25c), (0x7edefbdf7dcbb7e6,0x80a8040235840740), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
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
theorem g27G : graphValid g27 (boundsBefore K49) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := lower_forest (g:=g27) (i:=0) (hints:=67) (before_sound K49 V49) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K49 4 [(27,[]),(45,[33, 84]),(54,[32, 50, 83]),(85,[33, 83, 84, 101]),(86,[32, 33, 83, 84, 101]),(90,[32, 33, 82, 83, 84, 101]),(99,[83, 100]),(102,[32, 83, 100]),(108,[32, 81, 83, 100]),(114,[32, 33, 82, 99]),(116,[32, 81, 99, 84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V49 low27 (by decide +kernel)

def g51Y : Array (Bits × Bits) := #[ (0xfffffffffffffffffffffffffffffffffffffffffffffffff999faf9ddb5d25f,0xffffffffffffffffffffffffffffffffffffffffffffffff86601c0041c1c01b), (0xffffffffffffffffffffffffffffffffffffffffffffffffbcf5c9433be8b6b1,0xffffffffffffffffffffffffffffffffffffffffffffffffc3a230d5eb604691), (0x0,0x0), (0x0,0x0), (0x5ff79ffe3f7bedbc,0x2009000014002124), (0xffffffffffffffffffffffffffffffffffffffffffffffffee3b7de7ed973f43,0x119402868a101e40), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g51C : List ColumnInfo := [(2,0,49,0,4)]
def g51D4 (_ : Nat) : Nat := 0x2f
def g51L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g51D4)
  | _ => emptyPacking
def g51I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g51 : Forest := ⟨51,4,fun i => g51Y[i]?.getD (0,0),g51C,[[]],g51L,g51I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g51P4_0 : block g51 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g51B4 : block g51 4 0 1 = true := g51P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g51T : checkedTables g51 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g51B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 5 := lower_forest (g:=g51) (i:=0) (hints:=68) (before_sound K27 V27) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K27 5 [(51,[]),(53,[33, 84]),(57,[64, 33, 50]),(75,[83, 84, 101]),(77,[33, 83, 84, 101]),(89,[64, 33, 50, 67, 101]),(105,[64, 33, 50, 67, 100, 101]),(113,[64, 33, 50, 99])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V27 low51 (by decide +kernel)

def g122Y : Array (Bits × Bits) := #[ (0x0,0x0), (0x1fe1e3fceea6fff19b5c5c9ef7fd1fd57a76dbbfab1dc4779e932de5d54966,0x601a28028559008d5100c2180c01440374b136aea018c02209852511554140), (0x0,0x0), (0xffde5f9fc6f7ae920fec8fc7f31996e96052fcff679d61aba923a1d3d61ec4f9,0xffa1a0605b081983f011a0beb8c98b014d24a4662bf849a08101b0a2d814c4f1), (0x7dd77bf7b67fe5be9832fc7d7df7b77fdfab9b7777d37e13ecdee1b927b2f6,0x221c50040000a400aa31d00320080000046890105002c50a07a108822a036), (0x3b37dd9d05fbea964de22de7feb5ab1bc5b3369654dbf2bc704e60fea977d0,0x44ca22e29a12143770046215c1961ea36c804634c0df032c080466748957c0), (0xffebfaf56bfffadbd96fefb7fba6fa5ee373fc6ec98d7ea9eed7e3de66dafd0b,0x140580800224240208140146023090208242804005840540560a50268a380a), (0x0,0x0), (0x0,0x0) ]
def g122C : List ColumnInfo := [(32,0,90,0,4), (8,0,114,0,4)]
def g122D4 (_ : Nat) : Nat := 0x1f
def g122L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g122D4)
  | _ => emptyPacking
def g122I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g122 : Forest := ⟨122,4,fun i => g122Y[i]?.getD (0,0),g122C,[[]],g122L,g122I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g122P4_0 : block g122 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g122B4 : block g122 4 0 1 = true := g122P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g122T : checkedTables g122 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g122B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g122G : graphValid g122 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low122 : Lower true (varsX 122) (graphGoal 122) 5 := lower_forest (g:=g122) (i:=0) (hints:=21061696) (before_sound K51 V51) g122G g122T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K122 := extendKnown K51 5 [(122,[]),(124,[33, 84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V122 : Known true K122 := extend_ok (m:=122) V51 low122 (by decide +kernel)

def g87Y : Array (Bits × Bits) := #[ (0xffffef3d7d819f7dcd95df34aa5e3bae72d45fbf7f833e5944b1e6ff86248ecf,0xffff10e2a05a28821160b81e694c89500846807071422e09443747100820064f), (0xffff7d9be3ee6d79f0fd21d3776fadb6872babe74b38cd9dfa4f8fe178d16273,0xffff82625c0901820f32a827487440821a46848453080880017f8f9128406263), (0xffffa5d341317ab77fe20ede0ffb4a6fbb1b425da1cc126e6b1b7bb9534f1569,0xffff5a2c2ece812a582073113f1454ee9844b0e080e20a8e455b05bd52470569), (0x0,0x0), (0xbef7f9be4f7e1f7cddd3ddfc75fe4515c73f75317e76dec989fe6b15d3fc,0x411002809011e00507c000011421a0a0020b842051501a80106447159190), (0x0,0x0), (0xffffdffff6fdbbe3fbb7b67deee7df6bbfea79d1cacfb3abb3bf7641f7eabd13,0x20010000441500090080000300006100410b0c015120a200304004889810), (0x0,0x0), (0x0,0x0) ]
def g87C : List ColumnInfo := [(2,0,85,0,4), (1,0,86,0,4)]
def g87D4 (_ : Nat) : Nat := 0x5f
def g87L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g87D4)
  | _ => emptyPacking
def g87I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g87 : Forest := ⟨87,4,fun i => g87Y[i]?.getD (0,0),g87C,[[]],g87L,g87I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87P4_0 : block g87 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87B4 : block g87 4 0 1 = true := g87P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87T : checkedTables g87 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g87B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g87G : graphValid g87 (boundsBefore K122) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 5 := lower_forest (g:=g87) (i:=0) (hints:=1604) (before_sound K122 V122) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K122 5 [(87,[]),(103,[33, 84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V122 low87 (by decide +kernel)

def g94Y : Array (Bits × Bits) := #[ (0x0,0x0), (0xf7de7ffdcdee93c7bfdd9dfed6f9df9e771de40eaba179efd73ece5d4fbd7435,0xf8218402321928408409038708c60e003021494092b120c25c304a10032d2411), (0xf17bf8db311fd709e6d7cf422a83cafa8abbbfb1c4fba9e02be295fb52ea921b,0xfe8404bee8a038f2142ade9090e3349f307288c860d70de01ef4053951a8921b), (0xa7cbb93c68f697b19a1e0a7bfc6f97f95d82ac43c0776b96f916d9eb228bde8,0x5838c6939e03404f5af8da8f82e4084a07370623a0474602f700f32f228b568), (0xe73e68fafbc6757ad555fdc37fedf3d2256e236a5c1d57f519f9e3b7ad954fa,0x18c0910894691a85a36b82812219071ce0020a66408471d8186952ac8d050ea), (0x0,0x0), (0xffbfbffffbdbfffcdfbbfaeffd97a6f3ddfbfff95efeef9eaeeb7df6b566ebcf,0x406000040600000200004004008040060c020404088208800b00c408424884), (0x0,0x0), (0x0,0x0) ]
def g94C : List ColumnInfo := [(8,0,86,0,4), (4,0,90,0,4)]
def g94D4 (_ : Nat) : Nat := 0x5f
def g94L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g94D4)
  | _ => emptyPacking
def g94I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g94 : Forest := ⟨94,4,fun i => g94Y[i]?.getD (0,0),g94C,[[]],g94L,g94I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g94P4_0 : block g94 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g94B4 : block g94 4 0 1 = true := g94P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g94T : checkedTables g94 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g94B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g94G : graphValid g94 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low94 : Lower true (varsX 94) (graphGoal 94) 5 := lower_forest (g:=g94) (i:=0) (hints:=16868928) (before_sound K87 V87) g94G g94T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K94 := extendKnown K87 5 [(94,[]),(110,[33, 84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V94 : Known true K94 := extend_ok (m:=94) V87 low94 (by decide +kernel)

def g91Y : Array (Bits × Bits) := #[ (0xfffffffffebe5c7fcfebbdff1c131ff7fe53b5fc3e7c73e399b96a794b49972d,0x141b29000040000850809400481688000006281508000710649002c), (0xfffffffffbadad5d5c5ddf873bee7a7869cceb85ff61863ecad6bce7a68a68dd,0xfffffffff45294802122245148001f8014d1c802c22024acf08098c1058a480d), (0x0,0x0), (0xffffffffffcbd3fb2ccf5e7fccc1ed3516ace6ef7ba6cde527b825a7593e0ba3,0xfffffffff0340c44d31030544074260ca040801ca82104282339a10651120b83), (0x5fbf6157aa87fc976dddc6ae651ff0dddedde5ad3f313da80b386d4,0xa04016f8050882410962024232a0445154d9852063f4000103086d0), (0x0,0x0), (0x7f4bfdfb7bed572dff7bbc64baf8abef1d23c752e24df55fe747c1a,0x808402800090aa2200300014008160115c800400c06460088243410), (0x0,0x0), (0x0,0x0) ]
def g91C : List ColumnInfo := [(16,0,75,0,5), (2,0,89,0,5), (18,0,73,0,4), (64,0,27,0,4), (1,0,90,0,4)]
def g91D5 (_ : Nat) : Nat := 0x5f
def g91L : Nat → Packing
  | 5 => (1,0,3,0,0,1,0,g91D5)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g91 : Forest := ⟨91,5,fun i => g91Y[i]?.getD (0,0),g91C,[[]],g91L,g91I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : block g91 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g91B5 : block g91 5 0 1 = true := g91P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g91B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K94) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 6 := lower_forest (g:=g91) (i:=0) (hints:=67) (before_sound K94 V94) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K94 6 [(91,[]),(109,[33, 84]),(115,[83, 100]),(117,[33, 83, 84, 101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V94 low91 (by decide +kernel)

def g55Y : Array (Bits × Bits) := #[ (0xe4f0d6e5edde2dfd8edf77ff673b8ea702a77d1e75c274b9fb44cd9e6670,0x1b0329183201b01440a6d708008eb1a80370191e2640009789408e1c4630), (0xffffb2de5ee87d3192ba7a31cfc658677fa5ec6179d3aba1df46cd19492cf817,0xffff4d21689780816d4c4d97d4a2aa19d101505d3bbf9b4494468041410c7817), (0xe71d2ae8fadc570f3243c212bbcfffca921fed2588463317cebf3fd0cb1e,0x18e3d50259232c509aca1d987607343870505506086e11e64c16afd0c21e), (0x0,0x0), (0xffff7fb7cff7f3e5f6fe5dbe4f3f4f6f575fffeb5fddefb9a9eb603c7da9d2ed,0x804804200c0a000000482800500002048002c04040a82020403e00a18048), (0xffffbfedfdfbfe7bed95f35ffcfcb1d3f8fcd7bfe3f2dd5f561c9ff7b6572d9b,0xffff40100044800402280000002509400801080d22209101c208020010022981), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g55C : List ColumnInfo := [(4,0,51,0,5), (2,0,53,0,5), (6,0,49,0,4), (1,0,54,0,4)]
def g55D5 (_ : Nat) : Nat := 0x5f
def g55L : Nat → Packing
  | 5 => (1,0,2,0,0,1,0,g55D5)
  | _ => emptyPacking
def g55I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g55 : Forest := ⟨55,5,fun i => g55Y[i]?.getD (0,0),g55C,[[]],g55L,g55I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g55P5_0 : block g55 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g55B5 : block g55 5 0 1 = true := g55P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g55B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 6 := lower_forest (g:=g55) (i:=0) (hints:=1348) (before_sound K91 V91) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K91 6 [(55,[]),(59,[80, 50]),(61,[80, 49, 50, 84]),(93,[80, 49, 50, 83, 84, 101]),(107,[80, 50, 83, 100])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V91 low55 (by decide +kernel)

def g79Y : Array (Bits × Bits) := #[ (0x3bb7efecd42df5dd9179caef5967d2ff5fd58bb7a9d7e5b5d623a1fef654bc,0x4449111520921a02304085200b02558c60a050f301c7201517702024265424), (0x728c766e8612fb38efa83b8a56da65b57c81e5a6fa27b09b50fc7dc85c1f06,0xd7329d199ce20c530dc59a8fb8403a9c60efa05f74aa04150fd2d9c541f06), (0xbcee913c5549d7b2342c093fafa27c98d7c3ded9511b9dcb5b5cb21b0ac6e,0x74334ccd2e33628444805b2f4d4c9d26c49e1d6d0793f9dc0b9d2108b08c6e), (0xffdcdd19afeefaf54fbbf5c69b7daffbf2c2c7c17de87e66dfaaab09bbf78d89,0x2322e2c011014068412a32423424a220061e240488384cc8a80d0c98518988), (0x0,0x0), (0x0,0x0), (0xffff7ffff7bffffefa7eafbd77fef8fdedff3ffefe57b9bf6f7ddcfec709fb77,0xff8080000040008000820000000001004008010000000000020000c043082011), (0x0,0x0), (0x0,0x0) ]
def g79C : List ColumnInfo := [(4,0,75,0,5), (2,0,77,0,5), (6,0,73,0,4)]
def g79D5 (_ : Nat) : Nat := 0x5f
def g79L : Nat → Packing
  | 5 => (1,0,2,0,0,1,0,g79D5)
  | _ => emptyPacking
def g79I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g79 : Forest := ⟨79,5,fun i => g79Y[i]?.getD (0,0),g79C,[[]],g79L,g79I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g79P5_0 : block g79 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g79B5 : block g79 5 0 1 = true := g79P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g79T : checkedTables g79 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g79B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 6 := lower_forest (g:=g79) (i:=0) (hints:=1635) (before_sound K55 V55) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K55 6 [(79,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V55 low79 (by decide +kernel)

def g118Y : Array (Bits × Bits) := #[ (0x0,0x0), (0xffffffe77d7e5c7e8df79747ecf4efec6fcaff24def88fb9a343fc32ca5e591b,0xffffff988001a1c0308c00001a04441153a1980d4a0040988a005c7a801a5901), (0x3f5befe7ef2b46f9fbafbd578db02fca9f6d3672ec4b7ec265bdb276b0,0x40a41a900054a0404e0a008a07331811006e204820888ec00504b05230), (0x0,0x0), (0xffffffbfab479dd95eff8eacddae5fb75edfb370ee1d8dea74d1b79f13958177,0x405da842028020481680a031022c0845820450094230d8a20427850072), (0x72fbbedbb5f8ee6bdddb9a747fef1f0ae9750d64d775a643fe8ec3cfc4,0xd000020c8035395811045402000870235918e048041200dea08428d84), (0x5be71fe6fae7fc786b7be3e2ea59ecdf9798eeb3519e7cd9277b6838ee,0x2418c4480d0003118041803188840062f081cea243044020803b4020ce), (0x0,0x0), (0x0,0x0) ]
def g118C : List ColumnInfo := [(64,0,54,0,4), (32,0,86,0,4), (16,0,102,0,4), (4,0,114,0,4), (2,0,116,0,4)]
def g118D4 (_ : Nat) : Nat := 0xc498605d85534bd02a496e2540ebc6a894f91501
def g118H4 (_ : Nat) : Nat := 0xc40320046640288
def g118D5 (_ : Nat) : Nat := 0xc140400000081104000633c6cc15243440500fd34fd24fd14fd04fd23fd13fd03fd12fd02fd01
def g118H5 (_ : Nat) : Nat := 0xb723780064a200913900c500f600108
def g118D6 (_ : Nat) : Nat := 0x468815f
def g118L : Nat → Packing
  | 4 => (5,2,3,0,0,5,0,g118D4)
  | 5 => (10,1,3,0,0,7,0,g118D5)
  | 6 => (1,0,3,0,0,1,0,g118D6)
  | _ => emptyPacking
def g118I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 4 8 1 7 3 0 g118H4 h
  | 6, h => lookupWord 5 13 4 8 4 0 g118H5 h
  | _, _ => none
def g118 : Forest := ⟨118,6,fun i => g118Y[i]?.getD (0,0),g118C,[[]],g118L,g118I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g118P4_0 : block g118 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g118B4 : block g118 4 0 5 = true := g118P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g118P5_0 : block g118 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g118P5_5 : block g118 5 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g118B5 : block g118 5 0 10 = true := (@block_merge g118 5 0 5 5 g118P5_0 g118P5_5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g118P6_0 : block g118 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g118B6 : block g118 6 0 1 = true := g118P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g118T : checkedTables g118 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g118B4
  · exact g118B5
  · exact g118B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g118G : graphValid g118 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low118 : Lower true (varsX 118) (graphGoal 118) 7 := lower_forest (g:=g118) (i:=0) (hints:=18941248) (before_sound K79 V79) g118G g118T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K118 := extendKnown K79 7 [(118,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V118 : Known true K118 := extend_ok (m:=118) V79 low118 (by decide +kernel)

def g121Y : Array (Bits × Bits) := #[ (0xffffffffffefebfebeff5faffd7becfcdf49ed6b76fe9de3d9c9f5322954dc55,0x1004000102a0000000060010002000a00810800800002200508040), (0x0,0x0), (0x0,0x0), (0xf5b57b75bdb331aa9bbef8bb3e69f952399ae2fb62712f6bc3a46ae,0xa40910a8244ccf160d0880075402824080890e30055211cc0a46a4), (0xfffffffffadcb7af383fae75c634d99f7f776c9cbc62ff3c0fb22e1bcbcd21ad,0xfffffffff5214870c43011010e3981440060566003024d2027a092810b0d012d), (0x73cdf7877b3cb59d21ed5a5a6fdf376bc814ad78fde6f79c28937d2,0x8c22003384c02a2e0c468830c01818e00040257901a645054803692), (0x3f46399ff7af4da8fc7a6eb79e7f6a2592d349ee36fa2cc3fa68b3a,0xc0bd26400880220c822b11e28081125102764408352a08830a4091a), (0x0,0x0), (0x0,0x0) ]
def g121C : List ColumnInfo := [(64,0,57,0,5), (32,0,89,0,5), (16,0,105,0,5), (8,0,113,0,5), (72,0,49,0,4), (48,0,73,0,4)]
def g121D4 (_ : Nat) : Nat := (0x16515029b89935c065e36497018f919354066e264d5018f919254065e3649501 + ((0x4540e7616515038f5180544a5d36015129d85945c0a3e4645702978d94540a76 + ((0x249b89935c125e36497048f5180544e6d26015139d85945c0e3e46457039b899 + ((0x4e48423c36302a241e18120c06009b498054d2751601534974d8054927516015 + (0x8a847e78726c66605a54 <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g121H4 (_ : Nat) : Nat := 0xf1a70006e00000b2874fd0801ebb674701446b682cd92060024a554dc3b922805483902103
def g121D5 (_ : Nat) : Nat := (0xb80ef915019f22a037e35406fa6a80df89501be92a03f610407ea6280fd48501 + ((0xde3540abc6a815f85502f710205ed4240bda24815f8d701be9ae037e25c06fa4 + ((0x103eea1a07dd1340efc0a895f01512bf22e057d45c0afa2b815f91502bea2a05 + ((0xf80a89df91703bea2e077d15c0efc8a81df51503f712a076e2540efc2a81f78c + ((0xe097d25c12fc6a825f89504fb0aa0976154137c80826f4d104de922097e0544e + ((0xc891f8781b46217056118400c02004000bf02a697c054d2fc0a925f01524be9a + ((0xbb6859b641855fd6f5915e561484e12848908408f73b0e6358cb314bf2bc9f23 + ((0x8200400040080080220022042208297a448fa248660e822027ddf1785d1705 + ((0xc410810002802280228c20062080400608010061082080014011401146100204 + (0x62080400620804102104000608040044084410400c4100800c100200 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g121H5 (_ : Nat) : Nat := (0x9bfcf00059d5ba9eb48500000e951f26c2400000e05714204151111461000700 + ((0x4c1722c660001071a0766be14c00029e04d800060c007c89c70400727a2028ac + (0x214a329104800a78001082a0237136000c76a8dad8eb8fcdab800000c0dcf55e <<< 256)) <<< 256))
def g121D6 (_ : Nat) : Nat := (0x2810c68270d03400fd34fd24ff04fd04fd13ff03fd03fd12ff02fd02ff01fd01 + ((0x43210194c8405532101550c840653210154c840543210150c840595431e4d85d + (0x5432101950c840643210150c84055 <<< 256)) <<< 256))
def g121H6 (_ : Nat) : Nat := 0x50940800000000398054807b959a0122b500000b5080001
def g121D7 (_ : Nat) : Nat := 0x2c68819f
def g121L : Nat → Packing
  | 4 => (24,3,3,0,0,8,0,g121D4)
  | 5 => (52,2,3,0,0,10,0,g121D5)
  | 6 => (12,1,3,0,0,9,0,g121D6)
  | 7 => (1,0,3,0,0,1,0,g121D7)
  | _ => emptyPacking
def g121I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 9 30 4 9 5 0 g121H4 h
  | 6, h => lookupWord 24 68 4 10 6 0 g121H5 h
  | 7, h => lookupWord 9 20 3 8 4 0 g121H6 h
  | _, _ => none
def g121 : Forest := ⟨121,7,fun i => g121Y[i]?.getD (0,0),g121C,[[]],g121L,g121I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P4_0 : block g121 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P4_5 : block g121 4 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P4_10 : block g121 4 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P4_15 : block g121 4 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P4_20 : block g121 4 20 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121B4 : block g121 4 0 24 = true := (@block_merge g121 4 0 20 4 (@block_merge g121 4 0 10 10 (@block_merge g121 4 0 5 5 g121P4_0 g121P4_5) (@block_merge g121 4 10 5 5 g121P4_10 g121P4_15)) g121P4_20)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P5_0 : block g121 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P5_5 : block g121 5 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P5_10 : block g121 5 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P5_15 : block g121 5 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P5_20 : block g121 5 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P5_25 : block g121 5 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P5_30 : block g121 5 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P5_35 : block g121 5 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P5_40 : block g121 5 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P5_45 : block g121 5 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P5_50 : block g121 5 50 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121B5 : block g121 5 0 52 = true := (@block_merge g121 5 0 40 12 (@block_merge g121 5 0 20 20 (@block_merge g121 5 0 10 10 (@block_merge g121 5 0 5 5 g121P5_0 g121P5_5) (@block_merge g121 5 10 5 5 g121P5_10 g121P5_15)) (@block_merge g121 5 20 10 10 (@block_merge g121 5 20 5 5 g121P5_20 g121P5_25) (@block_merge g121 5 30 5 5 g121P5_30 g121P5_35))) (@block_merge g121 5 40 10 2 (@block_merge g121 5 40 5 5 g121P5_40 g121P5_45) g121P5_50))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P6_0 : block g121 6 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P6_5 : block g121 6 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P6_10 : block g121 6 10 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121B6 : block g121 6 0 12 = true := (@block_merge g121 6 0 10 2 (@block_merge g121 6 0 5 5 g121P6_0 g121P6_5) g121P6_10)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121P7_0 : block g121 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121B7 : block g121 7 0 1 = true := g121P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121T : checkedTables g121 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g121B4
  · exact g121B5
  · exact g121B6
  · exact g121B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g121G : graphValid g121 (boundsBefore K118) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low121 : Lower true (varsX 121) (graphGoal 121) 8 := lower_forest (g:=g121) (i:=0) (hints:=3) (before_sound K118 V118) g121G g121T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K121 := extendKnown K118 8 [(121,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V121 : Known true K121 := extend_ok (m:=121) V118 low121 (by decide +kernel)

def g126Y : Array (Bits × Bits) := #[ (0x0,0x0), (0xe6fdd7d81b3206fdbafa6893f76a03024e7f3f147bef97f980407893256eca4c,0x2118d9980922c0fca8166800a0da070640763c0c014a025990486893010e8a48), (0xfdf351fefff10e4cc59484e8369e8dffb266002d22f17f4daba7acb256908ce7,0x418004882a50ac8068404a0979801cf0232880106a12a41e8a62c1256908047), (0x8135de7b896cfbc74cf70b257b6ca81c75c26c59e688617142fc2312ba8c3b9d,0x8102325c0165e1e608d489213320cb8516c63c09ef886322c2fe2112ba8c2b8d), (0x5a59e6bdd464435136f03dd7ad615bd253a9ffe6eae2b0075cc7825cefdbe00c,0x44050025d48c020116e014de09001890128880016a24180240b28248e6d06004), (0xeefaf66fea407d5cb09bdc6218efdc65ade6d19fc128cd06f5cf09efd9ad18a2,0xe2e78028424406a91b8a0000654400a504711c9102c504140901a5092d18a0), (0x7146bf7965bfb4aeed6f6fbe4215309a1c9344f0971df2fc2bb8f72902357751,0x40c40421401814004120120a40040010880940f0100490040500922800215410), (0x0,0x0), (0x0,0x0) ]
def g126C : List ColumnInfo := [(8,0,118,0,7), (4,0,122,0,5), (2,0,124,0,5), (32,0,94,0,5), (16,0,110,0,5), (72,0,54,0,4), (40,0,86,0,4), (36,0,90,0,4), (24,0,102,0,4), (18,0,108,0,4), (12,0,114,0,4), (10,0,116,0,4)]
def g126D7 (_ : Nat) : Nat := 0xbf
def g126L : Nat → Packing
  | 7 => (1,0,4,0,0,1,0,g126D7)
  | _ => emptyPacking
def g126I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g126 : Forest := ⟨126,7,fun i => g126Y[i]?.getD (0,0),g126C,[[]],g126L,g126I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126P7_0 : block g126 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126B7 : block g126 7 0 1 = true := g126P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126T : checkedTables g126 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g126B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K121) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 8 := lower_forest (g:=g126) (i:=0) (hints:=18965824) (before_sound K121 V121) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K121 8 [(126,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V121 low126 (by decide +kernel)

def g95Y : Array (Bits × Bits) := #[ (0xbd1ee755424605f6f3eaa3586ff8cbe2a9eb2877f5c3f64281a258823ca16f6e,0xb005060014401a442e222100a72800000202834724182106022080018216e24), (0xe70f1138889df6e50d65f4f226765a0ade04cfade70e02d74e198c7c037217b6,0x2047561251d20e401c67a9220128003ca00952de788c05246380c44033207a6), (0x8c799c8f63ebfd7430f902db986739dbaa59161f4c09c82974878a4dc45b654d,0x85989e0873ea6dc01ae832d8306618c7aa11f7670060ec297493884cc45b654d), (0xd0ca9463dc0a6519412c6a97f690be6cbdc0f1d7f5b85d0d99cf3964c7e5890a,0xda8983241a0c1101080c06f4883a0c0941d7c305b84c210f891064c7c4810a), (0x5a4dcb781eecd5973edc95fc8dc8540a7fa94bca3b2c29a2d62dd7fa9158a658,0x30a102029882d611a8088548d508541835994240083420a0904413ba80488058), (0x0,0x0), (0x6ff6fa8efffd3a6bc55b490f903775b553be942508778b7d39de2395ea0ed0a5,0x7001000080001202841100010100413010880000000201840044239120001000), (0x0,0x0), (0x0,0x0) ]
def g95C : List ColumnInfo := [(4,0,91,0,6), (2,0,93,0,6), (16,0,79,0,6), (20,0,75,0,5), (18,0,77,0,5), (6,0,89,0,5), (8,0,87,0,5), (1,0,94,0,5), (22,0,73,0,4), (68,0,27,0,4), (10,0,85,0,4), (9,0,86,0,4), (5,0,90,0,4)]
def g95D4 (_ : Nat) : Nat := 0xc498604ce3741a25e520aa2a052d19d454079882a8a80de10789501
def g95H4 (_ : Nat) : Nat := 0xd34e238008804
def g95D5 (_ : Nat) : Nat := (0x5f354d23eb51523fa54102eb51502ed91901f949901fc54101ed51501f989501 + ((0xa180c0600eb89945ed85945bb89935bb4da25bb41a25b78d905bb89905cf5150 + (0x49040040008142281000847e78726c66605a4e4236302 <<< 256)) <<< 256))
def g95H5 (_ : Nat) : Nat := 0x62e833bc200258021f87f1db31206e05370a4a94090009840d
def g95D6 (_ : Nat) : Nat := 0x1241884002928c0218012d2628c032d2728c032d472902350cb3e362412006f517fa6bee25fe82fb48fda05f501
def g95H6 (_ : Nat) : Nat := 0xf0815333801a00cdc
def g95D7 (_ : Nat) : Nat := 0x172ec4203bf
def g95L : Nat → Packing
  | 4 => (5,3,4,0,0,5,0,g95D4)
  | 5 => (17,2,4,0,0,8,0,g95D5)
  | 6 => (7,1,4,0,0,8,0,g95D6)
  | 7 => (1,0,4,0,0,1,0,g95D7)
  | _ => emptyPacking
def g95I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 3 7 1 7 3 0 g95H4 h
  | 6, h => lookupWord 6 21 5 9 5 0 g95H5 h
  | 7, h => lookupWord 3 9 2 7 3 0 g95H6 h
  | _, _ => none
def g95 : Forest := ⟨95,7,fun i => g95Y[i]?.getD (0,0),g95C,[[]],g95L,g95I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P4_0 : block g95 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B4 : block g95 4 0 5 = true := g95P4_0
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
theorem g95P5_15 : block g95 5 15 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B5 : block g95 5 0 17 = true := (@block_merge g95 5 0 10 7 (@block_merge g95 5 0 5 5 g95P5_0 g95P5_5) (@block_merge g95 5 10 5 2 g95P5_10 g95P5_15))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_0 : block g95 6 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P6_5 : block g95 6 5 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B6 : block g95 6 0 7 = true := (@block_merge g95 6 0 5 2 g95P6_0 g95P6_5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : block g95 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95B7 : block g95 7 0 1 = true := g95P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95T : checkedTables g95 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g95B4
  · exact g95B5
  · exact g95B6
  · exact g95B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 8 := lower_forest (g:=g95) (i:=0) (hints:=1603) (before_sound K126 V126) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K126 8 [(95,[]),(111,[33, 84])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V126 low95 (by decide +kernel)

def g63Y : Array (Bits × Bits) := #[ (0x6f7ef6996f20a630817f0a7f4b747f632a71eecefd8f78cde03fcfe0ad525989,0x22b64820200020006d803400414e002a402000c18a38168031cb2000520181), (0x5fd5f986d1ff39e33217829486c419bcc24a26e5d8684fdffbdc0a1f619c8beb,0xc162990171a853ea2831806c86045dbcd04a26d1d028c41ba15d0a0f61908bab), (0x17006cda2cf549c7cc0ffa682af2b8feb69750020249a6fd65f7b5907759232,0x4d3a8eda2c3009d6109d72010b5a31da2636542a008ab46d42f5b5007759222), (0x3efbdf2f9f888e3a7d2a5b89af4c99276046f856715b5fe130cb2c73c569ec8a,0xd49140b7948a0e18d9021a89aa0c904b85a2db57302145e13dc82453c529ec0a), (0xf8957bf6dcfe39c7428662a774b0a6df3ce610bbf7d14736cdee5016dc9f3467,0x815009088462801000276831010a04200a0582a205003004c0210108c0d3044), (0xd155d57ae0f9cfbefcd1f551b20fe2a0d79db73d3eb7a428b610b38972a1ef14,0xc00840025018c6429c8000400a0010a0550402151c2500280200208970804c10), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g63C : List ColumnInfo := [(8,0,55,0,6), (4,0,59,0,6), (2,0,61,0,6), (12,0,51,0,5), (10,0,53,0,5), (6,0,57,0,5), (14,0,49,0,4), (36,0,27,0,4), (18,0,45,0,4), (9,0,54,0,4)]
def g63D3 (_ : Nat) : Nat := 0x31830919d4545524c48674153540b2419d044d101
def g63H3 (_ : Nat) : Nat := 0x168030
def g63D4 (_ : Nat) : Nat := 0x185523cc2460c04e46745524e4a8a8aa493959e2585266b3c4b81cd56785303998ce9aa05d24153540a6a33a6880f91044d101
def g63H4 (_ : Nat) : Nat := 0xb5170300b8510470823600150
def g63D5 (_ : Nat) : Nat := (0x2f985102bd95901bd55901f58d901fc50101f54d501f989501f54d101f949101 + ((0x3f349303f585303bb91902bb51902f38d902fa54102f34d502f945502f34d10 + ((0xa14f54d614f989614b78d904bd85904e74d104b755b03b751b03f389703f5457 + ((0x5934f389534f545534f985924bb81924eb55124f34d524f945524bd55a14bd41 + ((0x41a25f989915bd81915dd51515b78d905bb89905d74d505b795934b755934f58 + ((0x331689c48210d860240c0481800bb89945bd85945b791935f389935bb51a25bb + ((0x49c4ca4d208d43a11027b3a9c8de6c34998c6602d15ca8512712c90451f8f06c + ((0x3820020803824820004020040920800100e1b017aba5bad162ae542954 + (0x4080000080482000402000082382000000000000080000 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g63H5 (_ : Nat) : Nat := (0x4c0833265312ad3bd91136256a3d64dd6a5861479ac53980200185d004101817 + ((0x54465042bfcaa22c94ebd00003426ed20075dc0c0600132ea33163ac2000012e + (0x4a4378000058a276220041039000e803e005b74500091b <<< 256)) <<< 256))
def g63D6 (_ : Nat) : Nat := (0xe6d2c0f83e00fea2f74d7dc4bf515fe82f74d3da49f614fe8277c0fda05f501 + ((0x6941060150728c22a0a41082080349060112728c22a50520859944df2da62a99 + (0x8200d2720c029ca3088839482144100 <<< 256)) <<< 256))
def g63H6 (_ : Nat) : Nat := 0xb9e5000000ca8b3600910000b0c8623703640002a000
def g63D7 (_ : Nat) : Nat := 0x130e42033f
def g63L : Nat → Packing
  | 3 => (3,4,4,0,0,4,0,g63D3)
  | 4 => (9,3,4,0,0,6,0,g63D4)
  | 5 => (51,2,4,0,0,9,0,g63D5)
  | 6 => (12,1,4,0,0,9,0,g63D6)
  | 7 => (1,0,4,0,0,1,0,g63D7)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 4, h => lookupWord 2 4 1 6 2 0 g63H3 h
  | 5, h => lookupWord 4 12 3 8 4 0 g63H4 h
  | 6, h => lookupWord 17 61 5 10 6 0 g63H5 h
  | 7, h => lookupWord 8 19 3 8 4 0 g63H6 h
  | _, _ => none
def g63 : Forest := ⟨63,7,fun i => g63Y[i]?.getD (0,0),g63C,[[]],g63L,g63I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P3_0 : block g63 3 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63B3 : block g63 3 0 3 = true := g63P3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P4_0 : block g63 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P4_5 : block g63 4 5 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63B4 : block g63 4 0 9 = true := (@block_merge g63 4 0 5 4 g63P4_0 g63P4_5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P5_5 : block g63 5 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P5_10 : block g63 5 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P5_15 : block g63 5 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P5_20 : block g63 5 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P5_25 : block g63 5 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P5_30 : block g63 5 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P5_35 : block g63 5 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P5_40 : block g63 5 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P5_45 : block g63 5 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P5_50 : block g63 5 50 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63B5 : block g63 5 0 51 = true := (@block_merge g63 5 0 40 11 (@block_merge g63 5 0 20 20 (@block_merge g63 5 0 10 10 (@block_merge g63 5 0 5 5 g63P5_0 g63P5_5) (@block_merge g63 5 10 5 5 g63P5_10 g63P5_15)) (@block_merge g63 5 20 10 10 (@block_merge g63 5 20 5 5 g63P5_20 g63P5_25) (@block_merge g63 5 30 5 5 g63P5_30 g63P5_35))) (@block_merge g63 5 40 10 1 (@block_merge g63 5 40 5 5 g63P5_40 g63P5_45) g63P5_50))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P6_5 : block g63 6 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P6_10 : block g63 6 10 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63B6 : block g63 6 0 12 = true := (@block_merge g63 6 0 10 2 (@block_merge g63 6 0 5 5 g63P6_0 g63P6_5) g63P6_10)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63B7 : block g63 7 0 1 = true := g63P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g63B3
  · exact g63B4
  · exact g63B5
  · exact g63B6
  · exact g63B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := lower_forest (g:=g63) (i:=0) (hints:=1347) (before_sound K95 V95) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K95 8 [(63,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V95 low63 (by decide +kernel)

def g119Y : Array (Bits × Bits) := #[ (0x7eefbd4307cbeaae1398cddabee581e0df695346a0ddf129512959b1b818fc80,0x98c1227800008c0d1600ccd2220500201229630401499103103501303808e880), (0xdbf064bca985dcd28dbad27cc94c6a3f37be3f111548e1cebc050772bc860278,0xc6ac045003808c1c84b898448108402035736e104148f30e18858572b8840248), (0x20ce2fe35efd9d25c6b1fe232a1ead229293a2e38b716a742ed3e62d6ae82a43,0x386c402128810625d4b44e612b1580209a21a4418520a2402831a22568a82a42), (0x0,0x0), (0x6097445f71bb0870ef468e857d2270ab5e1059cddc9ead0ce8666a5f610131f4,0x100c00340082040010402010c1220c7080090c99496000082024a0d41001130), (0x90d39ba5dfbeb5d4f0ef53ff66f21d30a1d6008acbea5619d1d11540c9df4507,0x42020904132010000042300c40e01d0001d408126a00408840c0144080570405), (0xaf7bf1139d4ecf0b09733505824fe25471ada67f32a50de3de4bf8ac16668f2c,0x128804442e10020903210000c234d54080000220820ca0c640488806420524), (0x0,0x0), (0x0,0x0) ]
def g119C : List ColumnInfo := [(1,0,118,0,7), (4,0,115,0,6), (2,0,117,0,6), (64,0,55,0,6), (68,0,51,0,5), (66,0,53,0,5), (6,0,113,0,5), (32,0,87,0,5), (16,0,103,0,5), (70,0,49,0,4), (65,0,54,0,4), (34,0,85,0,4), (33,0,86,0,4), (20,0,99,0,4), (17,0,102,0,4), (5,0,114,0,4), (3,0,116,0,4)]
def g119D4 (_ : Nat) : Nat := 0x624c302b88222640545ce367481014d7834d52655034e1535459540d3864d50655034
def g119H4 (_ : Nat) : Nat := 0x10f1c9b44020
def g119D5 (_ : Nat) : Nat := (0x1024525f23a0c91ef16040523fc24080a47bcd810144f75b020489fe11040913 + ((0xa6b90655034dd6c081249bcd8101493f090202924de3741914dd2c081229f844 + ((0x4080a69b3499530d36a8b2a61a6d90654c34e3a6aaa069ab499540d35a8b2a81 + ((0x4d375b02049a7cb3040934f528081269bcd81014d3e8982029a7b34040534fc2 + ((0x120405359ec2eab6693b89d568d27713aac9a4f617559349f40eab269e64c104 + ((0x126bda541024d7730b2049acf76740535de2c080a6bf44c1014d7b8a82029afe + ((0xb8a8202a2fe12040545dcc4c80a8b3d41e164d67b0ba0c9aeeb6040935f96608 + ((0x419459dece8128bba58102517d4a0204a2f695040945de6c080a8becd0101517 + ((0x4f261248c43200f474371a0c45c271207434170803414070027683c4ca2cee27 + ((0x4c3602f574b3562a54ca3502752c9348225047f3c1d4e46f361a4cc6330164ac + ((0x4000040000000000000000000400d040002c100000001d76a3459 + (0x410f04000000043c1000000000010000204401004010000 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g119H5 (_ : Nat) : Nat := (0xed071b6c00331e921a54f4f0014c50ff297c298f440301087084280040200001 + ((0xae475e17d39b08a5640ba751000f9a00346471a088857f08a598d834dcaa2f45 + (0xc4b230651e92d45572c1b940063800001ed000eb8d40000000a27949cc00229 <<< 256)) <<< 256))
def g119D6 (_ : Nat) : Nat := (0x3fd40523bf51a13bf91913bf51913bf81913bf41913fd50513fd40513fb40913 + ((0x14fb409149f55a23bf51a23f750e23bf51923bf41923fb50923fb40923f750d2 + ((0x924bf41924fb40924fd405249f55a14bf4da14ef4d214bf41914fd40514ef4d1 + ((0x58349f55834bb49834bd45834be41834f754c34ef55034bf4da24bf8d924bf81 + ((0x41934f780d34f740d34ef81134ef41134fb80934fb40934fd80534fd40534bf5 + ((0xf55a34bf49a34f794e34f754e34bf95934bf55934bf89934bf85934bf81934bf + ((0xdf51535df41535fb40935fd40535bf55b34bf45b34ef95334ef55334bf4da34b + ((0x5bf51b35bb49b35bf91935fd85935bd85935bf81935bf41935f780d35f740d35 + ((0x45fb89945bb89945bf81945bf41945ef81145ef41145df41545fb40945fd4054 + ((0x61402684a0870f41982c84c08c1001d02d04e06806800bf4db45bd45b45bf8d9 + ((0x1280cfb1f03b86e8cc1762d2570ab1502864f4981232104087e0ef1b6338608a + ((0xbd570acd580ae95a2a7542a51472884f69d52d25449c9212123c45e8a50e2164 + ((0xc3d845056043fb7dcf85edbce782eb5ccb8c6e2d91abb4a67acc19531d604 + ((0x18000804580081020011c2420600000704382340040410008000000100382001 + ((0x10000200c1610c1620388305880e20c16203880c10608000004000080046090a + ((0x2060010c00220002040800030400208000304004040060000000000400008000 + ((0x8904082041000020011e0020c0020608e1a2430608204482081040800010e14 + (0xc1182c4860c102 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g119H6 (_ : Nat) : Nat := (0x7f35024259cf89ca35c5430cc7c600a105200e4014001015100a5c4082000441 + ((0xbae61c1c0058b81444e22ca0000a00d47ace4c843109cda926e1e77bed80f110 + ((0x14b44ef22b662470c1afd3c94393e86c8e001a8800e6d2f069800777a0e1a1 + ((0xecc95748e4298a40065258c6ac00797000003a18000013069260cb7206c004ca + ((0x209bc2ab1a00392a81b84f3067c8581166484a3187bc0b02523001f2dea000f7 + (0xd <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g119D7 (_ : Nat) : Nat := (0xff517fe6bfd35ff9a7f8d3fa69fc34ff127f493fc29fd14ff11ff48ffc27fd13 + ((0xc20402481c6143081008d3b18b72a69c23a841d466162498ea2b8720d800ffa2 + ((0x1850c204024b2071850c204024e2071840c204024d2071840c204024e2071850 + ((0x20402081c308100634c2c81c30810093081c61030810092071840c204020c207 + ((0x481c51030810083881c51030810092071440c204020e3481c308100830b2070c + (0xc2071440c20402 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g119H7 (_ : Nat) : Nat := 0x62f1bc00006a95f37d0f0840eb566eb40900000000000000c7e0c004
def g119D8 (_ : Nat) : Nat := 0x3148310403bf
def g119L : Nat → Packing
  | 4 => (5,4,5,0,0,5,0,g119D4)
  | 5 => (54,3,5,0,0,9,0,g119D5)
  | 6 => (85,2,5,0,0,11,0,g119D6)
  | 7 => (16,1,5,0,0,10,0,g119D7)
  | 8 => (1,0,5,0,0,1,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 2 6 3 7 3 0 g119H4 h
  | 6, h => lookupWord 19 65 6 10 6 0 g119H5 h
  | 7, h => lookupWord 29 101 6 11 7 0 g119H6 h
  | 8, h => lookupWord 12 25 2 8 4 0 g119H7 h
  | _, _ => none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,[[]],g119L,g119I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P4_0 : block g119 4 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119B4 : block g119 4 0 5 = true := g119P4_0
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
theorem g119P5_50 : block g119 5 50 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119B5 : block g119 5 0 54 = true := (@block_merge g119 5 0 40 14 (@block_merge g119 5 0 20 20 (@block_merge g119 5 0 10 10 (@block_merge g119 5 0 5 5 g119P5_0 g119P5_5) (@block_merge g119 5 10 5 5 g119P5_10 g119P5_15)) (@block_merge g119 5 20 10 10 (@block_merge g119 5 20 5 5 g119P5_20 g119P5_25) (@block_merge g119 5 30 5 5 g119P5_30 g119P5_35))) (@block_merge g119 5 40 10 4 (@block_merge g119 5 40 5 5 g119P5_40 g119P5_45) g119P5_50))
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
theorem g119B6 : block g119 6 0 85 = true := (@block_merge g119 6 0 80 5 (@block_merge g119 6 0 40 40 (@block_merge g119 6 0 20 20 (@block_merge g119 6 0 10 10 (@block_merge g119 6 0 5 5 g119P6_0 g119P6_5) (@block_merge g119 6 10 5 5 g119P6_10 g119P6_15)) (@block_merge g119 6 20 10 10 (@block_merge g119 6 20 5 5 g119P6_20 g119P6_25) (@block_merge g119 6 30 5 5 g119P6_30 g119P6_35))) (@block_merge g119 6 40 20 20 (@block_merge g119 6 40 10 10 (@block_merge g119 6 40 5 5 g119P6_40 g119P6_45) (@block_merge g119 6 50 5 5 g119P6_50 g119P6_55)) (@block_merge g119 6 60 10 10 (@block_merge g119 6 60 5 5 g119P6_60 g119P6_65) (@block_merge g119 6 70 5 5 g119P6_70 g119P6_75)))) g119P6_80)
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
theorem g119P7_15 : block g119 7 15 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119B7 : block g119 7 0 16 = true := (@block_merge g119 7 0 10 6 (@block_merge g119 7 0 5 5 g119P7_0 g119P7_5) (@block_merge g119 7 10 5 1 g119P7_10 g119P7_15))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P8_0 : block g119 8 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119B8 : block g119 8 0 1 = true := g119P8_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 8 := by
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := lower_forest (g:=g119) (i:=0) (hints:=1348) (before_sound K63 V63) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K63 9 [(119,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V63 low119 (by decide +kernel)

def g127Y : Array (Bits × Bits) := #[ (0xc22437f59803a818a76280b9820258b80a85a6acd6db9a28a6850ddd548118b0,0x4020410220000a44080190102101002118400d2919a00a6000185540000a0), (0x5db27223fe7355609892b20f7505c41d161bb4eea9bdd0d182aba1ab690a71ca,0x78315207a27145428c10820f63c254040618a49e899cd05082a9218b690871c2), (0xd43deb00f6ce1142748cc761797e1b33ea5ea517bfec5dbcf8d05086910946ca,0xc47d3900f14a50521d084038592e1932925085038e8c58a8f0d01084910946ca), (0x7a437867141c52e68313bf20d0885b6416ac79bfc20bf8fc01b03a58e6725406,0x6c53756124185407030377a610a00b22348c29bf080a40fc01b03858a2725402), (0x859ead0b07f9265507630e15bcbca3321d8dda02e4b0a0a34a780824a3d7c9a9,0x5002d8005882010430a08008c292a2218c45301242020a34850082082930809), (0x1aaa805a4b5a2dafa0fc2cea4fc8678aa3aa6c7b088c05562575919a0a4c8317,0x1282805a0a0005ad00b024c202c04048200a2038000005540125801a08448114), (0x6845cac0a08cdbac5a3579028c33046dcc7297c817766340d906e62198b0a445,0x100809800040a20402408408411204908221040006021000806c62000808005), (0x0,0x0), (0x0,0x0) ]
def g127C : List ColumnInfo := [(8,0,119,0,9), (6,0,121,0,8), (1,0,126,0,8), (32,0,95,0,8), (16,0,111,0,8), (64,0,63,0,8), (9,0,118,0,7), (36,0,91,0,6), (18,0,109,0,6), (12,0,115,0,6), (10,0,117,0,6), (72,0,55,0,6), (68,0,59,0,6), (66,0,61,0,6), (34,0,93,0,6), (20,0,107,0,6), (48,0,79,0,6), (76,0,51,0,5), (74,0,53,0,5), (70,0,57,0,5), (52,0,75,0,5), (50,0,77,0,5), (38,0,89,0,5), (22,0,105,0,5), (14,0,113,0,5), (5,0,122,0,5), (3,0,124,0,5), (40,0,87,0,5), (24,0,103,0,5), (33,0,94,0,5), (17,0,110,0,5), (78,0,49,0,4), (54,0,73,0,4), (100,0,27,0,4), (82,0,45,0,4), (73,0,54,0,4), (42,0,85,0,4), (41,0,86,0,4), (37,0,90,0,4), (28,0,99,0,4), (25,0,102,0,4), (19,0,108,0,4), (13,0,114,0,4), (11,0,116,0,4)]
def g127D5 (_ : Nat) : Nat := (0x1ea45193858045407a51564e16011501ea85192858045407a61564a16011501 + ((0x1501e855193859445407a25464a16511501e2c5197858045407871565e160115 + ((0x655901d9842752899564071d0798e50851901e0d5197859445407a3146421651 + ((0x16011502e98559185804540a6b24a56776581019e48e969dd140406e304a5d50 + ((0x5e16011502e1a559785804540ba89464e16011502e92559385804540baa14646 + ((0x465e16511502e8a519085944540ba0d464e16511502e89519185944540b8a946 + ((0x68784550655902b8a169744194640b6a109d061651902b1a1e9565834540b82d + ((0xacc93a19d47581029d28e969dd55040b1c8798e50855902e328e4784195640b8 + ((0x51b6292a4244555946d8c469091155651a66a5a5277658102b1a5686751d6040 + ((0xb45427120843c1b0c054240f060240c030032e1694650809d56cb85a52942017 + ((0x11085411fcf873b59a0ca622f970b256299409a4a238fa77389ac + (0x8410420800000000000000000021040000042080000000000 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g127H5 (_ : Nat) : Nat := (0x193066dbe42a3a5c8b049d577026597056465653e6000861980830202200c01 + ((0x2e2622e1c038651c0000364b2a0c30a9d00000003d40009ec680000000002180 + (0x33703426ce5071f21 <<< 256)) <<< 256))
def g127D6 : Nat → Nat
  | 0 => (0xf9c5596011501cf9bc2c022a039f178580454077a270b008a80ef84a16011501 + ((0x76aa70b288a80ed94a165115019f8c4ac022a03af18658045407d628cb008a80 + ((0x3b95385904540774a50b208a80f8d5196511501cbabc2ca22a03b71085944540 + ((0x1fd0a0240a2a03f6150481454075e212b408a80e6d5e16411501dd8842c822a0 + ((0xfcc4117551501f98a020aa2a037b149981454075e30cb028a80ef8601205150 + ((0x63ecf2b428a80cf98a568515019f904a70a2a03bb16841145407762708228a8 + ((0x35b47959245407a6c8ebac8a80ebc6196091501f58a32c122a033b6495e1454 + ((0x1f98822cba2a033f189583454075e30cb068a80f9c55960d15019f314ad122a + ((0x80fe85012051901f70b0240a32039e67848146407762d08268a80edc42165d15 + ((0x4077c3019028c80fe85032051901f70b0640a32039e678c81464077c3009028c + ((0x2036f109959464075e2112b28c80fac4125651901d78842aca3203eb10455946 + ((0x901f58ba20ca3203eb23441946407d62688328c80fac8910651901f589220ca3 + ((0xc80fb40e50651901d792c20ca3203af238419464075e2708328c80fac9d10651 + ((0x6407d62810328c80facd010651901f58a020ca32033f18941946407da4728328 + ((0x32036f1099d946407d62093b28c80fac4117651901bd8a4e0ca32036f1098194 + ((0x1901bd884c68a3203bb1088d146407762109a28c80dec4262451901cda3c248a + ((0x8c80dbc5a70451901bd884c08a3203bb25841146407764708228c80eec4e1045 + ((0x464067e2131c28c80c7d9e538519019f884c50a32031f6794a146406f62133a2 + ((0xa32033d639421464073e0f28428c80ef48e50851901de81ca10a32033f109961 + ((0x91901d38ac20d23203af10855a464067e2133c28c80c7d42678519019eb1caf0 + ((0x2ac80ee44e104d1901de89c20da3203be12841b464076e2b08248c80ebc56106 + ((0x156407dc2c1902ac80cf9e252055901df0c0240ab203f615048156407dc2c090 + ((0xcab203e675289956406de2d3202ac80ef88a24055901df114280ab2033e789c8 + ((0x655901f391aa0cab203e713541956407ce44a832ac80f9c4950655901b7884c4 + ((0x32ac80ebc4e10655901f711420cab203ee02841956407ce4ea832ac80f9c5d50 + ((0x1956406de492832ac80fb48e50655901f681ca0cab203af248419564075e4708 + ((0x6aab203be228c1956406de213032ac80f9cd410655901f38a820cab203be2284 + ((0x28559019f3c4850ab2037e1090a156406ee2133aaac80dcd1257555901bb904a + ((0xbc2ac80cf58e508559019f314a10ab2033f2094e1564067cc529c2ac80cf9426 + ((0x502564067e2133c2ac80cfc82578559019db24af0ab2033d6395e1564067cc52 + ((0x20dab203bb109522564075e290834ac80eac52106959019f8c4a812b203bb184 + (0x527501019f8c4c4ca02037b149899404073e6f0836ac80e7c5e106d5901de89c <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0x3b3a8080dec9256750101be91cacea02037b24955d40407b648eaba8080dec92 + ((0x91d140406d62d23a28080dcc5647450101bc89c8e8a02033f189d9d40406f629 + ((0xced0a02037d2395a140406ee4b29428080dec5a77450101bd8acee8a02037b16 + ((0x9d2758101b78b4c4ab02033f18989160406de2d3122c080dec5276850101bb8a + ((0xb223ac080ddc5644758101be89c88eb02037e12911d60406de4d293ac080f3c9 + ((0x6915d60406fa2722bac080cfc6274758101b78b4e8eb02036f16911d60406ee6 + ((0xb4eaeb02037e12995d60406de4d2abac080dec9255758101bd824aaeb02036f1 + ((0x5647658101b38ac8ecb02036b1491d960406da2723b2c080cfc6275758101b78 + ((0x2911c2c080df48e52858101b78aceecb0203ed238dd960406fa472bb2c080dbc + ((0x169d2160406fa273a42c080df84a74858101be91ca90b0203bd038521604077a + ((0x884ad023a036f169d6160406fa273ac2c080df48e55858101bf114ab0b02036f + ((0x99232055d01dd324240aba033d6395a2474067e4129c28e80cdd9652851d01d7 + ((0xaa7233aae80d794a46755d019f9c4cc0aba03bb2489815740776709202ae80ee + ((0xc638481674067ac72b44ae80ced9253855d019db24a50aba035b54919d57406b + ((0xebc4870b3a033d6394a1674077a471832ce80ef48e24059d01de31c640b3a03b + ((0x7a5e16011502de49c2c022a05be1185804540a7cc52ac6ce80ced9255899d019 + ((0x7d312b008a816ba6196011502f54a32c022a05e69565804540b3d6f0b008a816 + ((0xe2d465944540b2daf0b288a816da4216511502da69c2ca22a05b65185944540a + ((0xd7484ad022a059ad785904540b75210b208a816e34e16411502dd28c2c822a05 + ((0x6da5a10551502db49c20aa2a05f29744154540aed2b33028a816ba6196051502 + ((0xa6dcb2bc28a8147b9e568515029f30cad0a2a053ea094e14540be528082a8a81 + ((0x5b69684164540be52c882c8a814fa6256091502d74c32c122a05ea9465824540 + ((0x2e96a3eeba2a0556c795974540b5d30cb068a8179a55960d1502dd4842c922a0 + ((0x179a5955051902df10c2a0a32053e789c414640bdc2c18828c814f986568d150 + ((0xadd2130b28c817a9d061651902b74b4ca0a3205be2189414640add2d2a828c8 + ((0x5eaa344194640bd52688328c817aa8510651902f548a20ca32056e909959464 + ((0x2d749c20ca3205ee2184194640bdc0308328c817aa9d10651902f54ba20ca32 + ((0x815ba9650651902f651ca0ca3205ec8394194640b5d4b08328c816ba8e106519 + ((0x40b7c4318328c815ba4260651902f55a020ca3205ea9404194640b7c4308328c + ((0x2053e7890614640afc2120c28c815ea4267451902b962cae8a32057aa094d146 + ((0x9029e71ca10a32053e6194214640a7d4129c28c814f986538519029f284c30a3 + (0xc814fa42678519029f504af0a320536e595e14640a79c72bc28c814f98657851 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 2 => (0x640b5d210ab48c814fa6255091902b74b4aa123205b69855424640bcd2caa848 + ((0x32059e97841b4640b792708368c816da4255891902d74ac20d23205a695841a4 + ((0x5902df0c0620ab205f6150c415640bdc2c1882ac816799e31055902cf5bc20da + ((0xac8179a5d50655902f351aa0cab205e69354195640bcd42a832ac8179a455065 + ((0x5640b1d0f0832ac816ba9210655902d751c20cab205ae9384195640bcd4ea832 + ((0xab205e6b504195640bcd2a0832ac814fa6250655902f651ca0cab205ec839419 + ((0x55902f3482cecab205e69055d95640aed2b3832ac815ba4260655902f34a840c + ((0xaac816da4223555902db48426aab205769098555640b2d8f08aaac815ba42676 + ((0x55640b2d0f082aac816da9210555902db51c20aab205b69384155640aed2131a + ((0xab2053e9098615640a3dcf28c2ac815da4267555902b74b4e0aab2057690981 + ((0x855902de51ca10ab205bc8394215640a7d213242ac814fa42638559028f73ca7 + ((0x34ac814fa42678559028f684cf0ab2053ce395e15640a79c72842ac8167a1e50 + ((0x175640b79270836ac816f846106d5902dd4a420b2b205ae94841a5640b552908 + ((0x8ea8205d6a5751d5040aed4b28baa0814fa6261654102bb4acc2ca8205b49384 + ((0x75541029f4c4ecea820576959d9d5040aed4b2b3aa0815f28e56754102bb52ca + ((0xbaaa0815da5277554102bb4b48eaa8205669691d55040ae52923aaa0815d24e4 + ((0x8516040aed2b3b42a0815ea5276854102be51cad0a82057aa494615040aed2d3 + ((0x88eb02056ea6945d6040b9d4ce8bac0814fa6261558102b74b4c2ab02056e969 + ((0x54758102bb52ca8eb02057685951d6040b9d0cea3ac0815ba5a44758102be49c + ((0x22bac0815f846457581029f4c4e8eb02056e969d1d6040afc23323ac0815ba9a + ((0x9d5d6040add2d3abac0815ba5a45758102bd5a48aeb02057a94915d6040af927 + ((0xcaecb0205669591d96040add2923b2c0815aa5247658102b649c8ecb02053e98 + ((0x654858102de4ac470b02057ca394616040add293bb2c0817b28e37658102be51 + ((0x72ac2c0816f20e15858102b74b4e90b02057c939d216040af9472a42c0815f88 + ((0x58c414740b6ccb08828e815ba5a75858102be49ceb0b02057e119d616040af94 + ((0x9c8cea3a055e51919d4740a7d7133028e816da9626051d02db5c2ca0a3a05b66 + ((0x4256815d029e71cad123a0536e594e14740a6dcb28c28e8155b5646751d02ae6 + ((0xc71882ce816f18e11059d029e71cad12ba053ea094e15740a75c928c2ae816ba + ((0xe595226740a79f121c2ce814f38e51859d02de51c60cb3a05bca389416740b78 + ((0x880a8d0b2091f6195e1164123bc72bc22c827ac40546459049f30ca91b3a0536 + ((0x78e57885904a7ab4ee30b2099b548dc6164137629080c2c8272ddc54685904f5 + (0xbc72bc44c8247d86578899048bf2caf0932091de395e1264123ec32bc24c8247 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 3 => (0xde395e1564123dc52bc2ac8247d8657855904d9ca420aab209e3905519564123 + ((0xbb2c22093a097b10906164412f6233282c8824ede271059104d9c9c20aaa2091 + ((0x798632059d04ceb1c620b3a091de395a2574123ec32b44ae8245f9653849d04c + ((0x3bf121c2ce826758e21859d04cea1c430b3a099d6380616741339c71902ce826 + ((0x1ee295e21641637c92bc22c82c778e578459058f714af08b20b1f6194e167412 + ((0xf34812ad1320b1ee295e1264163bc72bc24c82f9a40956499058ef1caf10b20b + ((0xdda4a640595059b7c4e40b2a0b1de395e2264176d2b08144c82f1bdc95689905 + ((0x63bc72b448e82c7b8a56891d058df24a708ba0b9ae4848117416ed212142ca82 + ((0xb9cc388a16741739c70142ce82e738e32059d05ceb1c620b3a0b9e628c416741 + ((0x58f714af10328b1f6195e2065163dc529c2ce82c77e243859d05ce71c450b3a0 + ((0x2c7d865784d9458fd04af09b28b9cd285cc365173aa30b986ca2e76421730d94 + ((0x173cc510c2cea2c7d4261859d458f714af11b28b1f6195e2365163dc52bc26ca + ((0xdaf1684061441b96ee2b2428837ac4056485106f5880ac88a20d1ed098a1675 + ((0x6d74b42051220dea9025922441bd5204b2248834778e57885106c7ab46e30a2 + ((0x834778e57885506d78b42030aa0de71015961541bce202b2a2a834778e578891 + ((0x41a3bc72bc44a836ba5a10289506e37b92cb12a0de69025962541bcd204b2a4a + ((0xa0d1dd898dc4541b3b2111b88a836375a23711506ce69446e22a0d9d5188dc45 + ((0x506d5a8c2c822a0da79085944541b4ba70b288a8369b4a16511506d3a8c2ca22 + ((0xa8347b8a578915068ef1caf022a0dab9085904541b53a70b208a836ab4a16411 + ((0x641a5ef138828c835ba4a610519068ef1caf1a2a0d1f6195e34541a3bc72bc48 + ((0x320d6f1198c14641b5b7071828c836b660d3051906f4ca1a60a320d6f1198814 + ((0x5906977c4e40ab20d6f1198815641add253082ac835bc4241851906b7494c60a + ((0xac835ba4a63055906b788cc60ab20dadb838c15641b5b306982ac8379654d305 + ((0x3741a3ec32a444e836758e11049d068f714ab10ba0d9ce384811741add212142 + ((0x1ba0d5d519d5a3741ab9c52ab46e83477627468dd06ae694e8d1ba0d5d61951a + ((0x8dd06aea8ceb11ba0d5ce295623741ab9a53a446e83575865488dd068eec4ead + ((0xc6e83575467578dd06ae714aaf1ba0d1dd89d1e3741ab9a53a3c6e8357586547 + ((0x90251b1ead1b8e02a36794a371c0546ce71406eaba0d9d6180dd4741a3bb13ab + ((0xf81a8d9e52885f0351a3ec32bc604a347d62617c0946af284c2f0128d5e6195c + ((0x8c15468fb0caf182a8d1f58985f0551b3ca510be0aa347d86578c0d468fac4c2 + ((0x2aaca358d4644555946b1e8488aab28d639091155651bc3a86b2a6aa34778e57 + (0x5d0751a3ef120ba0ea36758e01741d46b1e9c88aab28d61d391155651ac5a522 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 4 => (0x2f83a8d1ee295620751a3ec32ac40ea347d8653881d468fb0ca5103a8d9d6388 + ((0x685d46af294e0d0ba8dbb1494201751b5e2d28402ea36f84a50805d46cf2944 + ((0x8442ea36750e50885d468fac4e090ba8d5e529c121751abcc52ab42ea347d627 + ((0x4221751abcc52abc2ea35798a55885d46af294e110ba8d5d6394221751b3ac72 + ((0xae280aad1ee295623751a3ea130c26ea34778e50889d468fa84c3093a8d1de39 + ((0x227c0d56cf28c6e5812ad1ee295e30155a3db1313e02ab5794262780556af314 + ((0x2bc608ab47b62627c1156cf28c44f822ad1ee295e30355a3db1313e06ab67946 + ((0x94620755b39c7113a0eab47be242741d56ce71c04e83aad1de395e30455a3dc5 + ((0x4c508baad9e51889f0755a3dc52a440eab47d8654881d568f714a7103aad1ee2 + ((0x670689d56db4aca1013aadae9694202755b7c2328404eab4778e50885d568f68 + ((0x728444eab6730e50889d568f6c4e0b13aad5e519c162755a3db138344eab5794 + ((0x394222755abcc32a3c4eab5798654889d56af28ce1113aad5ce394222755b39c + ((0xa004a02200f807002800c004801800600047d865488dd568f684c509baad1de + ((0x80fe07c03c81d80dc06603181800b0055029013c09804401e00e406202e0158 + ((0x81bc0d606983401860c005c02d41640af056029014209904b024c12008d04282 + ((0x270135096849424411f08b845022210e083040c2000fd07d03dc1e80ec074839 + ((0x61800be85e82ee1740b885b82d61630b005742b41520a7853029214109f04ec + ((0xe1e40eb873c38e1c40e086f83761b80d586a034a1a20cf86703281910c486183 + ((0x234116089044221910b084c42020810288083fe1fc0fc87d83e61f00f687a83c + ((0x7013689a84ce26413089784b625812a894849e24c124891848624011e88e846e + ((0x51610afc5782b915b0acc5562a81500a745342971478a3051227c13c89d84e62 + ((0x1818c005fa2f51790bbc5d82e91730b8c5c02dd16d0b5c5a82d11670b2c5902c + ((0xb88da46c235e1ad8d606aa3521a28ce06563281928c8863e31c18a0c44612306 + ((0x8ee47623a91d30e8c74039d1cd0e5c7283911c48e187063801be8de86ee3741 + ((0x902480c4031fd8fb87d63e81f28f887be3dc1ec8f587a63d01e68f2878e3c41e + ((0x1a08ca46222f91708b2451224910487c43621990c085a42a2139090838414208 + ((0xf49744b725a12c495c4ab254129494449f24e126492c48e245920c9004782381 + ((0x8a1e50c2849418a0650027e93d49da4ea271137c9b84d9266132498c4c326012 + ((0xaa054d2a5151ca7e53c29c94d8a6653029694a8a4e5242909478a3651828a944 + ((0x865bb2dc16c0b505a02ce9668b2458f2c395fcaee5742b895b8acc5632b0154c + ((0x464732218f0c7263631998acc5062030c1840c106002fc17c0bd05e02ee9754b + (0x6ab3541a94d306953491a3cd1868434099e4cec67333819b4cd466232d1948c9 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 5 => (0x2d3951c9ce4872138a1bf4dc26de36d9b60daa6d23679b1cd886bc35a1ac4d5c + ((0xc3c49df0ef27763b99dc0eda76a3b39d68ea474f3a39d10e8273e39d9ce0e607 + ((0x403200d0007f83fa9fc8fde7ec3f21f84fbc7db3ec1f04f7c7b13cd1e5cf2878 + ((0x2da1610aa852427a13109283c41ca0d906682b411a06d030815409203d018809 + ((0xe225112288e445a22110a88243fa1f10f2876439a1c10da86a433a1910c285e4 + ((0xa3691ae8d4468a3391968c8462a30917e8bc45ca2c515c8ab454229514489f44 + ((0x4a924e924490a479222909483240d2008fd47aa3c91de8ec474a3991c68e046e + ((0x992c69604aea5692ae9544a8a5392969484a2a50927e93c49ca4d9266930496a + ((0xd3489a14cf26593269904c6a62930e9844c0a5f92f69784baa5c92de96c4b4a5 + ((0x3c09dd4ed275d3a89d14e7272d3909c54e126fd3789b94db26cd3609ad4d5269 + ((0x60a2d515289d434a12507a831412a06501a8013fa9f54f927bd3d89e94f3278d + ((0x8a69533298d4c0a5d52d295d4a8a51527292d490a4552128fd478a3951b28cd4 + ((0xb04580aba95a6abc557aa61520a8d5452a1d508a8153f29ed4f0a7553929bd4d + ((0x4a5a3ad11682b3e59dace166ab32597ac9d63eb1c58cac59626b10586ac2960e + ((0x65c1ae016fab7a5bbadd16e2b6e5b5ada16cab625afad716b2b565a9ad4169ab + ((0x5e9af4179abca5e3af11782bbe5d8ae91742b9e5cdae6172ab925c7ae31712b8 + ((0x68100000008810881002204000000000008c108c1000000be25efaf717b2bd6 + ((0x106810000180108006810000000041000d040000000d04000000000810201000 + ((0x8810000008040000001a0401040000d04000003410000000000781000004 + ((0x8010819041904000000008c120800000000281000a040000000000000001a040 + ((0x18103410002040000034100000000000000000001 + ((0x8040004100000060400023048200000000000000 + ((0x8c120823048208c12080000000020100230400000008040000000000 + ((0x22042204220400000000000008040000000000000a041204 + ((0x190402040704006410000000000841084100210400023042308420000000 + ((0x190302000000000000000000000000000030100190400041064103010000 + ((0x8c11080000001d0400000000000000000000000000000000006040c04000810 + ((0x2a042a084190c0c04006410641030100008410001041904190400000181000 + ((0x64106410641000064100000210400641064101c1064106410641064106410041 + ((0x704000410641000000002304420000000241000904000000006410 + ((0x1c20841002304000000001c10000000021064209421064161025084190580714 + (0x8c210641110008c1108230841904440000641001901c200000000000210 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 6 => (0x1901c20000021042104210400000000000000241000000044100 + ((0xd040000000000040100000000000000000000000000 + ((0x640c08190400000019040000000000 + ((0x641000000000000000000000000000 + ((0x1901c206410000000000008040000000000 + ((0x541410220841505040541408220841505040401000000000000000000000000 + ((0xd0408040000000000000002208415050408821 + (0x640c081901c20000000000000000000000000000000000 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g127H6 : Nat → Nat
  | 0 => (0xc34602000420a2a002051e185020000086260c081400088102142050c28004 + ((0x80408407060c4001a2cb9a140000002042930e1018f000800032005042e1c20 + ((0x1a20e142843000883002c182125c0070800100021858100005a6001009100000 + ((0x28e00602880c080120c7008500003024a2cd002a10483002400b0010281361c + ((0x3400876080800aa8c800021791080418244442831000106160c08b0c64d823e1 + ((0xa3c600000c29f3050a00021c40f6211c000840a23ce04086001868a3455a0e00 + ((0x67d299353f84860003df70a7b63634ba4c618edc837015089003c020140cda33 + ((0xd878b0fc00034fbd60a40400000000000000f5be44cb2b6a5870ec5cd55c18d1 + ((0x176885861c9c505700000000000000e70c0009750000d1681864a54000f40da8 + ((0xd555646dbc55e96b3396c0a8b13c000033c000817d045828d0f851ff9ef00009 + ((0x715242bc00000000000000000506c0005589971b95998d320cd6d5a12987d49f + ((0xc2cf1c6dd025624ad3021e6e870000d3a88540000000000000295b429800054a + ((0x48d000100c75225214048608b0a7c410000000f239c0f89c8000000261e77 + ((0x55440000000000833886c00035a8000347400002c022fd5e4260d88cfaeb8020 + ((0x1780188442f491eaa4094132ca261d3d1e4890780007707a4c17395ea42688ae + ((0xa605619d773238e298bf65cf518190ca3fe1c41c1895496910ff51d53bf1f65f + ((0xdb35a06673953b64ae00406285430da54166b2f1725de18fb1af731e0a46941a + ((0xe4104a0219b341cc99391e89600034abb243d6437265a7d1b5c20855a84b19e3 + ((0x2800042cc000159e46963dda1fa4c70820633599f5285d5a8672af13a8000907 + ((0x7e2eae91ea64d66a9e051263522d99f8f9886f8d5988300359c292600029e3b1 + ((0x52c000a6900000990031339724b270207bb7ae81d65afc7563d9a46c0b4ea5f + ((0xf294466d080f86b903b90e2af410d000000000009be0003d9c00039d8c464416 + ((0xa04a23d23b034000e3fc0001aa8a260003c430877d7b0002e43459a5fae8d786 + ((0x6a330bc284c0000ab662c00000000524000000151059b8000000258985fc8 + ((0xed9814a8000689c00a884863100010b7a7176bc00000000000000c9eb4ed0000 + ((0xa4000f0b80009400e3d416409390f6c2a735b08f73ac64954f8960014000098f + ((0x3853f27163c6202d63711a052f77521081d8cf329d40005406d5f0001d4407 + ((0x898fc60397eab044588cb497bddb39d8e3b0604553c79d0d7e454954e61691a0 + ((0x912e71b0211c1eda8eacd9b2b30dea1e09bf1a2d197c32ad7450e443f3a800e4 + ((0x9a96994a1a9df07e473359f2721d38d6e71f2419462a54b750c46519fc89e456 + ((0x29f9a74000429ce9ba98880b73d64cda0c9d75834845ee0db5964895d5c9018d + (0x41783329281765888786aa570003a6848a720d0000000494ec63f7b30d01ab3 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0xcb1c4b1c8c3476136a20000a33b1900006a2a61700019ae8174822063caa3712 + ((0x9ee9fdd93ae96c207a5d708d968012400039516be41f3054b860000f38ec7308 + ((0xe5dc000f9a643a289027d688ee93f567a7e140bcdd24be91865ccd6c57fa5f95 + ((0x640529ca250a607336c0000000d3d9769e168085eb940232a4d0a397ce9f20b0 + ((0xee00031fbd744266a2d800093b000096cb5d2000306ad4d12b8000157673721d + ((0x48b0002d6a00000002a7008944954a5c678809e25feb600005b496d868654fed + ((0xe15ae531d4010929f500038ba963ae40809cda5c83e81199494aab073838c3cb + ((0x19826d594000c8de8e90000db5f7cc055da4400074b3a380795c137302ebbc19 + ((0x3885f014e977312a92621d8d8530b4400000cdf6575d350198e4222c5d1b84 + ((0x39c76afc000782c000d6540000000000c8e5c9d00020c55054000c49301a0 + ((0x44adf47708adcfa0003dc274cc00024af6113839d11a3f70be9228eb58622204 + ((0x4d0003508896486ed6764a2362c22d6246114b90400056015a956f4000f7724d + ((0xc195795a259d04c355b800029fdde00000442c81800000028e0d6e0000c26d5 + ((0x21cb00dcd439a0a622b8d2a850003cb5b8078a9fad0d8a0002572d9b31044aa0 + ((0x3a94f3515056a44bdba6824699255e53ca91706817a04946798e55f134c07f98 + ((0x39d1a093c1513c93e2a127d8ab1d0cee6b60f8c71527e90b47415e1ca684ef9a + ((0x28329dfc0c3a6a627bcb82aad42f65fa51f816ddffc429e3013991d380b04ee5 + ((0xbd585294e06791d45f5936680a5c6a8a14b43a27a6594ddd92e5e766f28b95a1 + ((0x2016c74e8882baa70003909c38583553252140003451fa605bbe1119a310ae8b + (0xc3c76ac458a34c9320000c4ef6b028334700001910d3985e36a980601cf16b71 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g127D7 : Nat → Nat
  | 0 => (0x1501af56811501bd53811501be52811501fb56411501f756511501ff16011501 + ((0x16051501fe520515019f778115019f57811501bf10811501af76811501bf5681 + ((0x1bf53851501fb50451501fb10451501f757551501f750551501ff26051501ff + ((0x491501fb56491501f757591501ff16091501bf57851501bf50851501bf568515 + ((0xbf568d1501fb104d1501f7565d1501ff160d1501bf57891501bf56891501fb77 + ((0x1901ef65651901ef55651901fe72051901fe52051901bf10811901bf108d1501 + ((0x67651901ef57651901ff30651901ef60651901ef50651901ff10651901ef1065 + ((0x1ff10451901fb10451901fb63451901fb53451901fb62451901fb52451901ef + ((0x851901bf52851901fb67451901fb57451901ff30451901fb60451901fb504519 + ((0xbf50851901ff10851901bf10851901bf65851901bf63851901bf53851901bf62 + ((0x1901bf678519019f67851901bf578519019f47851901ff30851901bf60851901 + ((0x75891901bf55891901b755891901ff10491901ef57691901ef10691901ef5569 + ((0x1be528d1901fb104d1901ff106d1901bf54891901bf57891901bf10891901b7 + ((0x55901fe72055901fe52055901bf57815901bf10815901bf108d1901bd538d19 + ((0xef50655901ff10655901ef10655901ef62655901ef52655901ff24055901ff14 + ((0x5901f763555901f753555901f762555901f752555901ff30655901ef60655901 + ((0x62855901bf52855901fe42855901f767555901f757555901f760555901f75055 + ((0x1bf50855901bf64855901bf63855901bf53855901bf62855901fe62855901be + ((0x895901bb54895901ef10695901ff14095901bf67855901bf57855901bf608559 + ((0xf7575d5901ff106d5901bf55895901bf57895901bf10895901bb74895901bf54 + ((0x101ff22650101ff126501019f778d5901bf578d59019f578d5901bd538d5901 + ((0x12850101fb37450101fb07450101ff36750101ff16750101ff15750101ff1275 + ((0x1ff22458101ff12458101ff36850101bf26850101ff16850101ff15850101ff + ((0x758101ff14758101ff04758101ff22758101ff12758101ff22558101ff125581 + ((0xef07658101ff35758101ff25758101ff15758101ff05758101ff34758101ff24 + ((0x8101ff14858101fd23858101ff12858101ff37658101ef37658101ff17658101 + ((0x55811d01bd53811d01be52811d01ff35858101ff15858101ff34858101bf2485 + ((0x1bf52851d01df55751d01af76811d01bf56811d01af56811d01b775811d01b7 + ((0x8d1d01bf56891d01bf55891d01bf52891d01fb52491d01df55791d01bf53851d + ((0xff24055d01fe72055d01fe52055d01bf56815d01bd53815d01bf108d1d01bf56 + ((0x5d01df46755d01df63755d01df53755d01df62755d01df52755d01ff26055d01 + (0x44855d01bb44855d01bf63855d01bf53855d01bf62855d01bf52855d01df7675 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0x1df76795d01df52795d01bf66855d01bf64855d01fb64855d01bb64855d01fb + ((0x819d01bf108d5d01bf568d5d01bf55895d01bf56895d01bf52895d01be52895d + ((0xb775819d01bf55819d01b755819d01bb74819d01bb54819d01bd53819d01be52 + ((0x9d01df53759d01df62759d01df52759d01ff24059d01fe72059d01fe52059d01 + ((0x63859d01bf53859d01fd43859d01bf62859d01bf52859d01ff30659d01df6375 + ((0x1bf52899d01df52799d01bf65859d01bf64859d01bf63859d01fd63859d01bd + ((0x511502fe96011502bf108d9d01bf558d9d01bf548d9d01bf56899d01bf55899d + ((0xaef6811502bed6811502aed6811502bcd3811502be51811502fad6411502f6d6 + ((0x1502f690551502fea6051502fe960515029ef78115029ed7811502be90811502 + ((0xd7851502bed0851502bed6851502bed3851502fad7451502fad0451502f6d055 + ((0x2fe960d1502be90891502bed6891502fad6491502f690591502fe96091502be + ((0x811902be90811902bed78d1502bed68d1502fad74d1502f6f75d1502f6d65d15 + ((0xeed5651902eee1651902eed1651902fea5051902fe95051902fe71051902bed7 + ((0x1902feb0651902eee0651902eed0651902fe90651902ee90651902eee5651902 + ((0xd7451902fae0451902fad0451902fae3451902fad3451902fae1451902fad145 + ((0x2bee1851902fe61851902be61851902bed1851902fe41851902fae7451902fa + ((0x851902bed7851902bee0851902bed0851902bee5851902bee3851902bed38519 + ((0xb6f5891902bed5891902b6d5891902ee90691902eed5691902fe95091902bee7 + ((0x1902bcd38d1902fad74d1902fe906d1902bed4891902bed7891902be90891902 + ((0x90655902ee90655902fe71055902be908159029ef78d1902bed78d19029ed78d + ((0x2f6d1555902eee7655902eed7655902feb0655902eee0655902eed0655902fe + ((0x555902f6d0555902fe90555902f690555902f6e3555902f6d3555902f6e15559 + ((0xbed3855902bee1855902bed1855902f6e7555902f6d7555902feb0555902f6e0 + ((0x5902bee0855902bed0855902fe90855902be90855902bee4855902bee3855902 + ((0xd7695902ee90695902bee78559029ee7855902bed78559029ec7855902feb085 + ((0x2bed7895902be90895902baf4895902bed4895902bad4895902fe90595902ee + ((0x654102be908d5902bcd38d5902be518d5902f6905d5902fe906d5902bed58959 + ((0xf687554102feb6754102fe96754102fe94754102fe91754102fea1654102fe91 + ((0x8102feb6854102bea6854102fe96854102fe94854102fe91854102f6b7554102 + ((0x84758102fea1758102fe91758102fea1558102fe91558102fea1458102fe9145 + ((0x2fea5758102fe95758102fe85758102feb4758102fea4758102fe94758102fe + (0x858102fe91858102feb7658102eeb7658102fe97658102ee87658102feb57581 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 2 => (0xbcd3811d02feb5858102bea5858102fe95858102feb4858102fe94858102fca3 + ((0x1d02ded1751d02fea6051d02fea5051d02fe71051d02fe51051d02bed6811d02 + ((0xf6751d02dec6751d02dee5751d02ded5751d02dee3751d02ded3751d02dee175 + ((0x2f6c5851d02b6c5851d02bee3851d02bed3851d02bee1851d02bed1851d02de + ((0x891d02def6791d02ded1791d02bee6851d02bee5851d02f6e5851d02b6e5851d + ((0xbe51815d02be908d1d02bed68d1d02bed4891d02bed6891d02bed1891d02be51 + ((0x5d02aef6815d02bed6815d02aed6815d02baf4815d02bad4815d02bcd3815d02 + ((0xd68d5d02bed6895d02bed4895d02bed1895d02f6d1595d02bed3855d02bed185 + ((0x2baf4819d02bed4819d02bad4819d02bcd3819d02be51819d02be908d5d02be + ((0x759d02ded1759d02fea5059d02fe71059d02fe51059d02b6f5819d02b6d5819d + ((0xfcc3859d02bee1859d02bed1859d02feb0659d02dee3759d02ded3759d02dee1 + ((0x9d02bee5859d02bee4859d02bee3859d02fce3859d02bce3859d02bed3859d02 + ((0x908d9d02bed58d9d02bed48d9d02bed6899d02bed4899d02bed1899d02ded179 + ((0x4df77185904ff10185904ebd46859049fd7845904ff10145904ebd4645904be + ((0x6559049fd7889904bbd4889904ded72899049fd78499049fd7885904bbd48859 + ((0xbbd4855904bee2855904d7f7555904f790555904f3f4555904cfd7655904ebd4 + ((0x5104f3905551049fd7895904bbd4895904cfd7695904ebd46959049fd7855904 + ((0x95059104faf2059104fb71059104fba1059104fb91059104bbd3855104f3d055 + ((0x4dbd3759104dbe2759104dbd2759104dbe1759104dbd1759104fba5059104fb + ((0x859104bbd3859104fb61859104fb41859104ebe0659104ebd0659104dbe37591 + ((0xded3249d04df51049d049fd6885d049fd3845d04df96744104bbe5859104bbe3 + ((0x9d04b7e5849d049fe6849d04d7e5849d0497e5849d049fe3849d049fd3849d04 + ((0xe3459d04dbd3459d049fd6895d049fe6855d049fe3855d049fd3855d049fd688 + ((0x4df61859d049f61859d04df41859d04def2059d04df71059d04dfa1059d04db + ((0x859d04dde3859d049de3859d049fd3859d04ddc3859d049fe2859d049fe1859d + ((0x9fd5899d049fd2899d049ed2899d04bde3859d04bf61859d049fe5859d049fe3 + ((0x5905df571859059fd7845905bf908d9d04bbd48d9d04b7d58d9d049fd6899d04 + ((0x90289905e7d56899059fd7849905fe90249905e7d56499059fd7885905b7d588 + ((0x5f3f5451905cfd7651905e7d56519059fd7889905b7d5889905def7289905fe + ((0x891905b7d5891905cfd7691905e7d5691905b7d5851905bf61851905dbf74519 + ((0xf7a4059505f6f2059505f7a2059505f792059505f771059505b7d38515059fd7 + (0x9505d7e3759505d7d3759505d7e2759505d7d2759505d7e1759505d7d1759505 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 3 => (0xe4859505b7e3859505b7d3859505f6e2859505f6c2859505e7e0659505e7d065 + ((0x59be4845d059fe3845d059fd3845d05df53145d05ded2045d05df96748105b7 + ((0x891d059fd6889d059fd3849d059fd6885d05bbe4845d059fe6845d05dbe4845d + ((0x9fe1859d05def2059d05dfa2059d05df71059d05d7e3559d05d7d3559d059fd6 + ((0x9d059fd3859d05ddc3859d059fe2859d05dee2859d059ee2859d05dec2859d05 + ((0x51899d05bde3859d05bee2859d059fe4859d059fe3859d05dde3859d059de385 + ((0x45bf908d9d05b7d58d9d05bbd48d9d059fd6899d059fd4899d059fd1899d059f + ((0x800d45bbd4800d45b7d5800d45aff6800d45afd6800d45bed2800d45bf51800d + ((0xb7d58c0d45bed28c0d45bf518c0d459fd7880d45ddd7380d45ddd7340d459fd7 + ((0x1945bdf3801945bdd3801945bed2801945bf518019459fd78c0d45bbd48c0d45 + ((0xd7681945bde3841945bdc3841945cfd76419459fd7801945bbd4801945b7d580 + ((0x459fd78c1945bbd48c1945b7d58c1945bed28c1945bf518c19459fd7881945cf + ((0x80d945b7d580d945bed280d945bf5180d945bfb080d945bf9080d945ddd730d9 + ((0x9fe084dd459fd78cd9459fd788d945ddd738d9459fd784d9459fd780d945bbd4 + ((0x9d45dee2859d459ee2859d45df61859d459f61859d459fe0859d459fe684dd45 + ((0x10185106ebd6485106dde3785106ff10145106ebd6445106dde37451069fe385 + ((0x6fe90249106ebd6449106dde37491069fd7885106afd6885106df77185106ff + ((0x7455069fd7889106afd6889106fe90289106ebd6489106dde3789106def72491 + ((0xff10185506e7d6585506dde3785506df77145506ff10145506e7d6545506dde3 + ((0x9506dde3789506fe90249506e7d6549506dde37495069fd7885506afd6885506 + ((0xd6511506dde37115069fd7889506afd6889506def7289506fe90289506e7d658 + ((0x6bf90811506afd6811506bdd3811506bed2811506bf51811506ebd6411506e7 + ((0x5d1506dde37d15069fd7891506afd6891506ebd6491506dde37915069fd78115 + ((0xef92051906ef71051906efa1051906ef910519069fd78d1506afd68d1506e7d6 + ((0x1906cfe1751906cfd1751906efa3051906ef93051906eef2051906efa2051906 + ((0x41851906ebe0451906ebe3451906ebd3451906cfe5751906ede3751906edc375 + ((0x6efa1055906ef91055906afe5851906afe3851906afd3851906ef61851906ef + ((0x755906efa3055906ef93055906eef2055906efa2055906ef92055906ef710559 + ((0xe7e3555906e7d3555906cfe4755906ede3755906edc3755906cfe2755906cfd2 + ((0x4106afe4855906afe3855906afd3855906eee2855906eec2855906e7e0555906 + ((0xe3845d069de3845d06ded2045d06dfa5748106fda3748106dfa4744106fda374 + (0x69fd5885d069fd4885d06bde3845d06dde3745d069fe5845d069fe4845d06dd <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 4 => (0x849d06dde3749d069fe5849d069fe4849d06dde3849d069de3849d06df51049d + ((0xddf568dd06ddd568dd06ddf468dd06ddd468dd069fd5889d069fd4889d06bde3 + ((0xdd06ddf588dd06ddd588dd06ddf488dd06ddd488dd06ddd288dd06ddd188dd06 + ((0xe3851d06bf61851d06ddc3751d06ddf578dd06ddd578dd06ddf478dd06ddd478 + ((0x6afd68d1d06bdd38d1d06bed28d1d069fd5891d069fd2891d069fd1891d06bd + ((0x895d069fd2895d069fd1895d06bde3855d06bee2855d06ddc3755d06bf908d1d + ((0xef76140546ef56140546bf908d5d06afd68d5d06bdd38d5d06bf518d5d069fd4 + ((0x546df771c05469f77880546df77140546df57140546fb74140546fb54140546 + ((0xf4240946fad4240946df617409469fd78c0546bbd48c0546afd68c0546bed28c + ((0x46df617c0946def7080946fe61780946de61780946def7240946ded7240946fa + ((0x340d46f9d4340d46df61740d469fd78c0946bbd48c0946afd68c0946bf518c09 + ((0xbbd48c0d46afd68c0d46bed28c0d46bf518c0d46ddf73c0d46df617c0d46ddd7 + ((0x1546bbd48c1546afd68c1546bed28c1546bf518c1546df617c15469fd78c0d46 + ((0xd3455946bbe484d546ddf734d546f9d434d546e7d654d546df6174d5469fd78c + ((0x46fb61749146eee2855946afe0855946e3c4555946ef61755946cfe0755946eb + ((0x741d46bbd38d5146bbd08d5146fb617d5146bbe084d146fb6174d146dbe074d1 + ((0x9fd5881d469fd3881d469fd2881d46bde3841d46bf61841d46df61741d46df41 + ((0x5d46bf10805d46bbd48c1d46afd68c1d46bed28c1d46bf518c1d46df617c1d46 + ((0x70485d46df50485d46df55685d46df70685d46df50685d469f77805d46bf5080 + ((0x46df53885d46df52885d46df70885d46df50885d469f50885d46df53485d46df + ((0x849d469fd0885d46bf50885d46df55785d46df53785d46df52785d46df55885d + ((0x9fe084dd46dbe044dd469fd0889d46bf61849d46df61849d469f61849d469fe0 + ((0x5d469fd588dd469fd088dd46bf6184dd469fe584dd46df6184dd469f6184dd46 + ((0x75140556f755140556dee27405569fd3895d469fd0895d46bee2855d46bf6185 + ((0x56dee27c0556df77080556fe62780556de62780556df77140556df57140556f7 + ((0x240956eef6240956eed62409569fd78c0556b7d58c0556afd68c0556bed28c05 + ((0xbf518c0956def72c09569ef7880956def7240956ded7240956f6f5240956f6d5 + ((0xd56ddd7340d56f5d5340d56dee2740d569fd78c0956b7d58c0956afd68c0956 + ((0xd78c0d56b7d58c0d56afd68c0d56bed28c0d56bf518c0d56ddf73c0d56dee27c + ((0x569fd78c1156b7d58c1156afd68c1156bed28c1156bf518c1156dee27c11569f + ((0x74d556d7e074d556f6e2745556b7e584d156ddf734d156f5d534d156dee274d1 + (0xdee2741d56dec2741d56b7d38d1556b7d08d1556f6e27d1556b7e084d556f6e2 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 5 => (0x1d56dee27c1d569fd4881d569fd3881d569fd1881d56bde3841d56bee2841d56 + ((0xe2845d569ee2845d569fe0845d56b7d58c1d56afd68c1d56bed28c1d56bf518c + ((0x569ef7809d56bed0809d56be90809d569fd0885d56bee2845d56dee2745d56de + ((0x889d56ded3589d56def0589d56ded0589d56ded4689d56def0689d56ded0689d + ((0xded3789d56ded4889d56ded3889d56ded1889d56def0889d56ded0889d569ed0 + ((0xdd569ee284dd569fe084dd56d7e054dd569fd0889d56bed0889d56ded4789d56 + ((0xe2851d56bf61851d569fd488dd569fd088dd56bee284dd569fe484dd56dee284 + ((0x606240ab011101ce033c057008400a200e401500009fd3891d569fd0891d56be + ((0x805b20b2816202b5053a0a3813f827904c2094811881fe03cc075c0e881c2036 + ((0x604d40978126c24604740894105c20403f007b00f001cb036306840c3c18002e + ((0xc832406300c42184830185f40bb817102d185940af8154828f85190a1413ec27 + ((0x9220e840807dd0fae1ed83ca87860ea61d1039f072f0e2e1bd836f06c60d4a19 + ((0x44146a28744f989e413aa27184d7099f130e25e04a2890911d0231c44a086a10 + ((0x868b0715de2ba456d0acb158a2afc55c8aa115362a305430a7714d029645250a + ((0x3b46618c9018de31806288c4218302fb85eb0bb517042da85b20b4316682c705 + ((0xd883ab07530e971cda38e87158e131bd236d86cf0d7d1aca353469a8d2f19f83 + ((0xd12160423c82e10321ffe3fc07e30fae1f2c3df87aa0f331e003bc476c8eca1 + ((0x98592fc25ec4b7896792a524f648fc90f11e2238246808bf915e228c44948791 + ((0x52f8a53149728ec519ca231437283e501c9f793e9276c4e0c9b5934a26644c68 + ((0x2c525844afc95f32b92570cada159c2b0855b0aae954e2a245430a7a14ee29ac + ((0x982d30185ff4bf717e82fb25f04bd497912ebc5d60b9717042da25a78b359638 + ((0xccc196e3264648cc8598f331a462e8c5a18ae312c6240c3c186930b4612cc22 + ((0x6f00dd89b9937146da4d9b1b3036426bdcd621a7f34aa68f4d0e19f2337e66c + ((0xe3a8c74dce941cf539cc735ce5f9cb93954726ce341c4738707014df69bde37b + ((0xc1e573ca27908f1e1e2d3c3c783cf001dfa3bd6774ced49d9a3b1675f0eb69d5 + ((0x90fc19f503e827ca4f919f023de67b6cf661ec63d5c7aa0f4c9e8a3d0879f8f3 + ((0x8686d10ce2172427e849d07ea0ca4176824502f203d405c807d0081fe63f787e + ((0x4946748cad18e230445d88b2d15e22a444f4891d120a232444688510fe21e443 + ((0x94a4f649e0933d257249f48d8919922ba43f483c90191f723cd47348dc11ac23 + ((0xe1d3b3273c4dee9b5935aa69d4cf8999132f26224c0297812d6a5834ac4954d2 + ((0x298a489480a8c5516ca23143a285c509aa0d540ea8175010a0093f9a7c94f2c9 + (0xba15712adc55acab535640ac21573aab45526a9c9528aa27540ca74d4d4a96d5 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 6 => (0x67d2ce259a6b3116442c8258d4b1916262c345838b0355ff2bef57aeaf215d82 + ((0xbc417732ebc5d00b97d711ae025bc2b6b96cfad875adeb5a569fad395a54b449 + ((0x625ec45d87fb0d56144c1bd834b03f6018bf657d32f8e5edabd5579eaf2e5e50 + ((0xb2406450c889905320463fcc7998ebb1c86372c6cd8cdb17a62d6c5718ab3147 + ((0x99d5b3936708cdb19a5b33c665acc9d983330065e2cb8996e32a06510c9e5930 + ((0x8d315a5fb4b96954d225a26b4476870d0c9a11b40b67f8cfd99ef33cf6792cee + ((0xf6b40d669aca35856adad579aa7b5406a74d4ada92b50d6a0ed3e1a7934e369a + ((0x5367b6cd8d951b2736486c84d8f1b1b36276c30d801afd35eb6ba6d6edadab5a + ((0xddbafb7596e94dd11b9f372f6e52dc69b85b7056dfedb9db6c36c96d62da65b4 + ((0x22e209c3e385b70aae119c1bb8317032e029bf4b7c86f72dea9bd2378c6efadd + ((0x6c72cce55dca8b9427266e491c8f390f7212e3e9c75b8e5719ae31dc5c38a071 + ((0x35ba5c7488e8b1d0eba177422e809cf539d27386e6d1cd7399f7332e629cc239 + ((0xd61da4bb3a7668ec71d86baf575cceb5dd5fbab97566eab5d53ba987512e9c5d + ((0x866f091e0abc0f77eeefa1df13bca7788eed5dd7bba97734ee51dc2bb7676e0e + ((0xcc67980f2e9e5a3ca5792cf241e453c8478fcf1bde34bc5a7896f115e1fbc397 + ((0xeb5bd5c7aacf541ea0bd327a58f499e8bbd117a16f415e7b3cf079c2f349e663 + ((0xf985f24be3a7c44f84df023df57bdef7a5eed3dcb7b66f6b5ecf3d8f7b00f5c5 + ((0x7e42fc49f863f067deefb7df6cbed37d88fad5f57be8e7d10fa09f39be6d7cce + ((0xc0057fc8ff79fec3fc97f86fef5fd73f967f0efe05fbdbf6c7ea8fd39fa43f39 + ((0x2098c12b8227041207ac0ef81c103220584098811301ea035c05c8053006a005 + ((0xf07c60f5c1dc839b06fa0dc41a9834706760c74188830505ce0b6c167829f050 + ((0x985750ad2152c29f85330a2a142427584cd0982128c242847908b610ac20683e + ((0x643dd878b0eb61cf438686ef0d7e1a8434a86770c8e185c2fc85ed0bc2170c2c + ((0x8a26544bb896b129a247447f88f311ce232444c8869109620fc40787f10fca1f + ((0xe717b62f3c5cf8b8116c62d1458a8af7158e2aa45458a5b147a28c451289f513 + ((0xfb8dc71b2e35e46ad8d2b1a1a340467a8ce91972326c63e8c5f188230445f98b + ((0x334857909120e6410c81b8ff51fae3ee47cd8f7d1ebe3c2c75b8e871cae389c6 + ((0x5ba4ab4947927124a648d490291f9239246ac8cf919322ea455c89c910921d64 + ((0x58f2abe54bca9194bd28f65174a1f942128064f4c9d1939726ce4d24995930d2 + ((0xbc6976f2ea25c84b7896d32d6a5a5cb45965b2c3257ecaf795e32b8a56e4acd9 + ((0x6b3cd589a93350e69ecd259a1b33fa67c4cd7999132e664c4c8098d130d65eac + (0x3a4e7424e7e9ccd3982728ce429c6738b670acdfd9bdd377e6e84db89b2f35da <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 7 => (0x9f373e327becf6e9ead3d1e79c4f299e353c2e779ceed9dab3b1a7604eba9d57 + ((0xd0f4a1dd435a863d0c1a17742b284ed08ea0ff4156815d0139ff73f8e7e5cfb3 + ((0x69075208a3f347aa8edd1c3a37b46968cb5187a2df45828a45139a255446e881 + ((0xb4c5a983d2f8a5c14b4695cd2aaa5374a32943526ea49b48fa91c5232a447487 + ((0xaa9a552eaa55d4a5a90951d6a335445a85b50569f15382a6d54d4a9a1d334a64 + ((0x955daab9756f2adb559eab315626abd556baacb5536a965514aa0b53daa7854e + ((0xe80820e8581018742c0e0408290e8581c0814440d081a088c260d030957e2af + ((0x81001a080810d058100110521d0b0381028a43a160702004011c3a13068204 + ((0xe04020800d041c08081a08541003401080408802a020c3c1a0a820042838101 + ((0x1041a01040d040080220782a08010045110680418a03a1a0a82050682230684 + ((0x20d040d0404220d00830d021a0104231103404208c441a06808504020e04041a + ((0xd040d0404220d00830d021a0104220f0200420883c1a040085000c0888100822 + ((0x410880210880c010c46220f02004288c441e00880d0104020434080810d02220 + ((0xd1401184c1a18782a020c1a088c3c1a090345070200881110182110680218883 + ((0x1e0b8203140783415040a230981804208834020c1a088c1a0200881d0a84c1c0 + ((0x201042e085c10100410c808206821507034040114501e0b8200401183c170406 + ((0x2084c1000001c0d08001020018100820104260800204260d08461a068084008 + ((0xc04108c260d0c461d0d0481a2878101000803004300820600840d04001004200 + ((0xa160a8384120742c15070a1a0a8383030201041a088c1a0200881e0983410208 + ((0x501e0d05410283410103410060c1c08081001083c080800d0582a0e008a0e043 + ((0x1081a08023068400541140781a021046220f0200c287410c854215868100210 + ((0x98381a20381a10340c10341010681a080088290682031184c1a08030a1a041a + ((0x24060c3e1903060d010043158a4340d010a1a068180220a4461a09034506821a + ((0x30682e080c34080086240681830e84c0c184c0c108c10020c46220f0340c288c + ((0xc102010d04c1a0810441a0680841408834170a82060d0581018a0441a0b85410 + ((0x481a0b0541c287834080100451100820681804183804100802100410402005c1 + ((0x81010881c10881c10a01140380c185c10b83802187810a82020b85820f058200 + ((0x682c0110000820e01040e010415040415042a08a0441e0b85410300240404005 + ((0x260d1452220d04c1a28a4441a0680450e8682a0e008a02041c08081c06080148 + ((0x1044406082606082606083415098381a280290d04c1a2068260d04082911068 + ((0x200418080210000340410012030412042408481002606081a06008606040c080 + (0x3a160781c5060221060423098300c208c3412068080230041110082068182070 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 8 => (0x42c0f038a260e8581e070100470e84c1807103a02083a1603861d0b03c0e2098 + ((0x808019008402041e070804088028020c3a190a01c042800c0432160380441307 + ((0x80410781c20018083010e8500e02008a210c80830602250e864280714460c082 + ((0x98302118641802101e081c1008201042c08580e10041060214078300401141e0 + ((0x420602000802100010426080000190783030004080060402080410982000810 + ((0x74260c038823010423098303118783211060a07043a07080038180218041030 + ((0xa03c02283c10f05c280f104e1e0b8501e2864280f0c0c0804106022306008022 + ((0x4210c80830c82190104231083004208c42190600850c80820601c04011032170 + ((0x10c80830c82190104210e81c0420843a19038085000c088410082210c840c038 + ((0x40c010c46210e81c04288c421d00880c0104020432080810c82210c840c03842 + ((0x983030e8500418301118743211060a008411081821086402188432108402108 + ((0x86250e8642807144613030084108640418301118300401103c140983c1828023 + ((0xe18300e060c1e07082c0700861d038400943a16038080230742c070c3a1603 + ((0x7418021046210e81c0c287810d0582818a832070108251087432160a01c71083 + ((0x8300e0618180864260f06080f06040c03041904180108460c080060200501128 + ((0x600850c8300c01104c2310864220c18420c0386190601c02209818070c461909 + ((0x118843a0c030a270601830f04c0c188c22060c3e1a098184060080218a84c190 + ((0x81820b021600841d042807082e16083a17080138642e14078a13030423038083 + ((0x105010a0225108742c14038c009c0e10017038421078421078407040e0894112 + ((0xc3c190a03c02280810781c2078182004c190b80440002083c04103c0410500e + ((0x84320c010825108642c14038c190b01c31288432160a01c60c8580e18640e01 + ((0x1143a19038080228840410300c020c1e02080401080208016078419098300e2 + ((0x807104c210c84c1828642813078305004c19098304130843213060a261086418 + ((0x4410882110400981820601802181810302000411081820981820981820c84c1 + ((0x80230c8441802008c21010401041806081e07010602008400300410000440c1 + ((0xa100c100060840100800201021e0384030080030002020400f0200218000041a + ((0x10102020400004085428020c2a14080100602180010200781008002010200500 + ((0x380020b838200000820000204440d081a0808101020014100200508002820010 + ((0x11020a040c01080c010802080010002010004000000007810182200a04000c10 + ((0x8010006000400080010004040400f03c2004408000001000208281000110042 + ((0x2a0508002021d08040004040801d038043000008301000200080408741c080c + (0x641810081010200141000a08010028400081003208081010200081003a080810 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 9 => (0x80010080020000000e8204044015080020208000416078401040000408841810 + ((0x741c10021040000008001041208021008421041208006008401040c0108000 + ((0x404080000000020404080000000810000080010000000002000400080020182 + ((0x208401010042000008001000200040000200002040408000041000000408002 + ((0x4200000020204011834021800020100000400108400880021080100821004000 + ((0x60000704000000848041034100001820e0084000000422020818080001010780 + ((0x21b01841b0104230d841b0436088c111822309044160614000808100460c008 + ((0x20206040c0800404000040800008100000800201020504000800201020504000 + ((0x44606080c0800304000040801904040801a040a080020444080810080810000 + ((0x43e120826060802084416100410902c20282000811081c20c81c2010200003 + ((0x10440c1048100020818001024100000021f08841303040104003000205020000 + ((0x3000211020a0424086c22104410e0482090211044611082408000480c104416 + ((0x2068042000200040c0008360800000600042104120800100020600041c040000 + ((0x82020404080411104c1a081044130682041100821100820d03420400420d020 + ((0x4020400002080810102220d04220402080410982020404010800c83c02184c10 + ((0x3610080008002010202042c08883410882610041010202043008883410022098 + ((0x800d0400983421081c20044210a8502028882a080c060840102820304080008 + ((0x12800080010d020800842209840104020804100100108441a09060a040001a + ((0x83431102130444130406220904220984220d04c1a0814441a0a84c240e068281 + ((0xc10082010004220400431104c1c1828100821304000441308441208440802209 + ((0xc01082608000801040042008200200210001043e080410002000810010802084 + ((0x20380420c81c2060042008202040408843210841008201042608081010042001 + ((0x426100810000082020404080411084c18071042130601c41080821080820c830 + ((0x1010180020002000804080811086420b82210984010404080811086420c02008 + ((0x84190442130802080410082001c02108432110c120800030100180800c040a08 + ((0x28843214098441e0c0481c02500400101c021004100821304020800100020700 + ((0x8426108422108410042130606210426088426070c4211084213084219098300e + ((0x2108010082001c0210001043e08041000200084207008613078409042608000 + (0x1c <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g127H7 : Nat → Nat
  | 0 => (0x4230314060224010502030002000204250e021d030501000704000d0401 + ((0x1000003050405010b02000a0a0321041c000611020007060202030600030802 + ((0x3070f0000000103070002020501010c00000003000000040f03080000001304 + ((0x552e181b000403000b1e03360d00000000010a0000091100250027000d070900 + ((0xe0400011d080715000923000000020001111600170709020002015e01011824 + ((0x31d0606080505080c100334070002311f1e0f0d001d0b040b000103030a0b + ((0x1f031b01010806000006150b0037100c140a072d0606011b03080603020015 + ((0x4030b07040015010005340f031a21000309031d003d1b220d000300000010 + ((0x1201060513080012233800088702000601004706050913010b01001200050200 + ((0x318030a5e001146040c02013a090406101c01000c030f001f14001203030801 + ((0x12010f0945000d081f0e001c0400000a0c12000c00006800093b130303070d05 + ((0xebbd70001af2645df185c344c5ae43fd92ee55e6b7ac6e1b7a001a0500281a2f + ((0x524306a03168a00000003a140826ca775373a985776eeb4dd2994c14ee00035a + ((0x16cab58692c4f4a990965f78b3f015ecab3013d875843ca6aada3b907b15481 + ((0x40a0cc03540f50c0915dbcbe09e54322f5ccc2c2971713203b72c05611889b00 + ((0xcd3a55027a2f0794d6a27737c84441eb71d9f5a74522132332e745e44a34bc09 + ((0x64099eca4601eee2f28cd3915542d80aca035b9b4295c58bdcbfba0e0374132d + ((0x98d04908c30806faaedc9ce01cdf4f821e1566f1c8936109beda88bedd185e + ((0xddf4266ad15ae6835443faf819c380f6d43922d1114d8e4a726e64f19948a75 + ((0xca699f510c8875cd1b59e7e241e1f4000618051fbe1f81d4c06866cf80700002 + ((0x8aee014033e13cb024c0004098000129d6128227600012ee55f8000070c367cf + ((0x53700bdbcb32b7246b390154c63031801746614c5b19727292cb04f8aa3a8857 + ((0x90f6c782479126a46eeaaca8c3b03fe0f2014243830d7a620abc4dcff235 + ((0x1cff0000960e00000000000a6d20001cda417200000002121db7ee0e24af0000 + ((0x7702111f8000524eed5cc1b6262083a6beddd4000000000002100ba730001651 + ((0x60001899f550800087ce60c986602c5e0bd4579da37b6e10ee00000007b8820b + ((0x1328000000063f5000000008088000e21a2a34dc00000566103e606b5b1 + ((0x49c9830f4000087b144ea3f40181cb5ed5c796d96c74a27606c222028ec07800 + ((0x946a540005aaa446800000006386b0d80000582e9ac95ddcf94000682fc09b2b + ((0xe9f2ec000004fc3acf3532f1c00063fe75940000000630364834147873d1c6b0 + ((0x7803e169d59800097ec00001ca9bbdb705e241d978abe514ae11000013 + (0xa15a07285201a40a0c0000000e36ae7149b443d4921e000247db1d5000000000 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0x22d8fdd9091182584c8812412a232000a6f01182236b235b68e287499d300012 + ((0x9de127845d604b505f42bb69e4000029c302e2cd9913389c36dee827846097b3 + ((0x4502146d7d6e346c835ac8152082640003aa98012608156653bef3c4cad656b7 + ((0x2834d90b836381f0000000004c104cf5f50000b5e84a2c0000000000080b1 + ((0x9536cb43d2e8000d5720003dee02f9768584e7171e1450000ea025cb4c27e756 + ((0xc0b7869f6a5ea0010c6f1a7a8e6d8e285992696af40004b980001ac2a4f70a6c + ((0x3156899da518a92199de3d20640c76a05f83e4a073e7d00005b39d4da0d84095 + ((0x20000ca948168208c3151b612590000e3e28cf80000000e3d45d780000001c90 + ((0xef4f781a814443b524308e4b4e1731852a6c4de9084a47471e2738907caaed5c + ((0xabcee2d4a7e35803354b3c368b2e160a535514edf0991a97d585049355035a0 + ((0x131813b4c82ca906b13589c1518fc22e9edc11923b08554d0cb0e271c7b00a46 + ((0xf4aba11ffa018311f869887d7131c11d04a94d02168a808030c4ab13ecb25e02 + ((0x3d9315c21c92f9c1265a8496dcb1f0e51395eaeb9c49ab730020d2c1ed00ec63 + ((0x6cab1d681c7a708a1199e351811f5c668b287634d598a86221022fc07d4d782 + ((0xde3c1683a6000000000005a96f206c7a0526391cd4cc82449b8b0fe63b88c985 + ((0x1de48756e209215f802875580177c19b4f0c000697ff79b2a988c1d3e2c1118 + ((0x5fcc0529e20000000000011758000a6e060ebdfd0000842ea34289d11a36 + ((0x837489e000124f88b4800003be882ec1a336af437488f1b30bc870a665c31ac0 + ((0x4f6119b9b65919e07dd01de35ae45c000186fc82200000000000000020154d12 + ((0xd1bd90a50c4a410b26b6593c176b55b3a0aad888c291e83f80000000231e0798 + ((0x8910336cc95c800699500000000000198f00000000000200fb27600000000000 + ((0x1188f62bc8f320e084097d00001c77c95a7484d05fc32980d63e58c939e5 + ((0x60001ce7cc1e778a2c94dbdc1d191050ec0000728ef4d000000005383c557ad4 + ((0xe30e6667b8eb2aa040dbc71cc1980000000000000012cee62e00031633a3bb38 + ((0x39bcf66c40003456800050d6a8689eea908000030808e91c2ec21da59dd3f09a + ((0x1dcc9909d0054672586789a27aa0001d2979f0504682568d97c194343618e9d + ((0x8430403432bd149c3538dd0000254600010810000f5cfc4b45318000000000 + ((0x291297505659980003622000000000eaa01800018bd0000a7f60000000000000 + ((0x899097c5e46d489c88000c09d0dce5150add00000000000340c000000020db83 + ((0x2b34e04aa5558302ae9515299a4660c2757be8d9e457e9e11c5d026a06fac749 + ((0xf40003503d85790ed48a201eb101f5b14ce00000949130dc2b85c87ad900006 + (0x12620e9e4e308001bb44e4097208d8364e53c0001025aaef43920002864bb43e <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 2 => (0x1a4b03c266aea9ec21e01a06bec1c800073d30001a9d2475e992d043a1711dc6 + ((0x3ff5eca089953e00000000000a405e362c923046d702c8c3d6fab8ac83f0428 + ((0xd23ae2d506deadb542a244fd1f71290000000100862e500018064c6581a58147 + ((0x415b128542db1dd491fe58481089bc8b28434eed2198d39cce48a00000000959 + ((0xb04538ca57dd4802c402251b10d24960419ae070b0000000059dd0001703c5f9 + ((0x18f980007b2dd2fc69850cb43b6e5fe6b2c000124f00016d6f854e29374d3cec + ((0x7b548ae7799a739e000082f799d7815e77e657ccc2608d00004830cbe2a92000 + ((0x70000664fc04887059fb07e60000d74a8a8b5fb45b20640b8d00004db48fff2c + ((0x1aa16e2c924ca67e69ef9b4e00000001d2521b3f642e6e6e01c353a1294e9212 + ((0x38a88000c8492e3b02ef3f9d29ccbb0cc768f00001cb0260d8000945aec + ((0xb334632c661100000037ead280916bf8508b6cc4c2b0000000186f000008a200 + ((0x334dd20a4bab8ac30290000f01c00021a4d090f059d7ac9abe2f348de5781b + ((0x79389ff2870001455c9da6055f172604d8a080be15f40001d2c10b873da00000 + ((0x1902c53f800087f882cf870c8fcd50c4b440000000049600000006bae76c1a + ((0xabfb5e665cfa111974d336236b4f1891ae5092959cae79d400000003d4a783e0 + ((0xc20a2cf661d23129ba11eb740b8b0c00181f6c550601c9fe80ed7011018ba152 + ((0x80914aa435ea3cd10501badb85c3884dd80895a25b7454913947e06724e18b90 + ((0x628a927d38e123143aa5ba92f027a732243bb00ee0b19061653fa0c13e11522 + ((0xebdeb397d0288b792d5d2c0e39b985b9bd33dec3a191213a3761e6ef0c78bba1 + ((0x702781fdb7a3a5c50a1f06f405544db1e8598de19dac495e35a0ad6782a0ac42 + ((0x388219bfb3f1263e6eaad3ef8a691e7a0e10248a5ac7c742046088adaa785108 + (0xc5d0281870866058964b1b22c <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g127D8 : Nat → Nat
  | 0 => (0xd15901fee8c80ff646407faa3203fd11901fee8a80ff645407faa2a03fd11501 + ((0xa3a03fd91d01fea8e80ff447407f8b0203fc50101feeac80ff656407faab203f + ((0x540bfbb3a03fd99d01feace80ff467407fbaba03fd95d01feaae80ff457407fb + ((0x817ec5640bf7a3205fb91902fda8c817ec4640bf7a2a05fb91502fda8a817ec4 + ((0x2fde8e817ee4740bf6a3a05fb11d02fd2c0817e95040bf7ab205fb95902fdaac + ((0xff45904fdece817ee6740bf6b3a05fb19d02fdeae817ee5740bf6aba05fb15d0 + ((0xca8209fe44104f7ac8827bd54413ff2b209ff55904ffc4c827fd26413ff0b209 + ((0x67412ff2ba09ff55d04bfaae825fe27413fe93a097f49d04bfc2e825fd17413f + ((0xc82ffd46417ff1320bff49905ffc2c82ffd16417ffb3a097f99d04fface825fd + ((0x5bfc4e82dfd27416ff0ba0bff45d05bfa2e82ff920417beb2a0bdf51505ffc8 + ((0xbff80d45ffa06a2ffc03517ffb3a0b7f99d05fface82dfd67416ff23a0bff51d + ((0xff9b28bff8d945ffa6ca2ffc36517ff8328bff81945ffa0ca2ffc06517ff81a8 + ((0xd2541bff0aa0dff45506ffc48837fd2441bff0a20dff45106bfacea2dfd37517 + ((0x2e837f92041bfc8820dbf55906dfa8c837ff4541bff22a0dff11506ffc4a837f + ((0xd06ffa8e837de3741aef1ba0d7f89d06ffa4e835fd2741aff0ba0dff45d06bfa + ((0x8dff40946ffe02a37f60151bfe80a8dffd5d06bfcae837fd5741bffa3a0d7f91 + ((0xbde8a28dbf55946dfa2ca37fd3551bff82a8dffc0d46ffa06a37ff0251bf7012 + ((0xf61751afe8ba8dfd05d46ffe0ea35fe0751bfe83a8defd5146f7a68a37bd2451 + ((0xaaea35fe3751bfe9ba8d7f4dd46bfc4ea37fd2751afe93a8d7f85d46fec2ea35 + ((0xd56ffa06ab7ff0255bf7012adff40956ffe02ab7f60155bfe80aad7f95d46ff + ((0xaadff41d56efe8aab77d3555bbe92aaddf45556dfa4cab7fd3455bff822adffc + ((0x5bf713aad7b89d56bfa4eab7ec2755aff0baadff45d56bfa2eab7ff0755aff03 + ((0xc075817004280ac0178000bfc8eab7fd4755aff1baadff4dd56bfa6eab5fe275 + ((0xc01e2872c1b5868819485fc165854814284ac11d84280f283740cd82d809c821 + ((0xd9c3598d103368c8c3098bd02e28b242b18a7028c89d425d8910230886420387 + ((0x9208474919445d9140446910443790c841c90243fb8f903ca8edc3a78e4037a8 + ((0x964c589961057a95d456d957054e9504529948050e93dc4eb93604c092ac497 + ((0xab9a9869e9a4468999e066a997464798f862698445f997b85da97145b796a05a + ((0x7649d747539d287409cdc72b9c907129c046fb9bd06ee9b846d39b386c69ae46 + ((0xc873a190856a12483ba098818a0147ef9f887ce9ef47ab9e807949e2c7819dc0 + ((0x8898ea5e4963a54893ea4cc923a448906a3e48e5a3688cca2dc8a7a27088ca1f + (0xb8cad7ab08ab2aa74a8fa9f8a64a95ca41a8a0a18a8149efa7689cea6fc9b1a6 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 1 => (0xb038bf8afb4bddaf40bc0aeb4b97ae08b6ead8cb53ad08b36aca4b13ac10af6a + ((0x124a494746858383420180804bce0b344cbbb2b8c9cb20cc73b180c4ab0d4c1b + ((0x281e1a17150e0d08060201309474685854383420180804b201a150e0d0806020 + ((0x684c48383420180804a221a0e0d0806020120a47868544c48383420180804c29 + ((0xe0d080602011c7468544c48383420180804b29281e1a17150e0d08060201308c + ((0x785c54201808049251d1a16150e0d080602012c8c684c48383420180804a1a0 + ((0x1808049291a0e0d0806011ca088685c54383420180804b23130d06020118a48 + ((0x6011894685854383420180804a2928221e1a17150e0d08060130aca46838342 + ((0x48383420180804b251d1a16150e0d08060128aca46838342018080491a0e0d08 + ((0xb23221a13120e0d08060128aca46838342018080491a0e0d08060118a488684c + ((0x4746458503c301c180804c2019140f0c070602012498947464583c301c180804 + ((0xf0c070602011c7864504c443c301c180804b281e1917140f0c070602012c989 + ((0x4c443c301c180804c281e1917140f0c070602012c8c644c443c301c180804a19 + ((0x6140f0c07060201308c644c443c301c180804a21190f0c070602012098746450 + ((0x8a0645c503c301c180804a23130c0602011898807458501c180804926251d191 + ((0x1c180804b281e1917140f0c07060128a898643c301c1808049190f0c0706011 + ((0x16140f0c07060130a898643c301c180804926190f0c0706011c94846458503c3 + ((0x98643c301c1808049190f0c070601189884644c443c301c180804b2625211d19 + ((0x83c14100c61e05040110783021e050401107834223211913110f0c07060128a8 + ((0x224a478685c542018100804a221e100504021878545040100c0871e05040c847 + ((0x9281e1715080504030201002ca478685c5420140c0400a1e1d1514100604030 + ((0x141005010020a0785c503c14100c080400b1e19100f011478645c503c140c040 + ((0x221e080605188c88780c04006281e1514100504030201002c7874400c41e1d15 + ((0x14100c61d05030110743021d05030110743421e10050ca4a078100c080400823 + ((0x98746458501c180c0804a211d100503021874545040100c0871d05030c887438 + ((0x14100400a251d16150e0504030201002c746840380451d1a16150e0504010024 + ((0xd151410050302010028787440104251d1614070504030201002c98746458501c + ((0x1c100c0061d10050c989474100c080400823211d070605188c84741004006251 + ((0x4030218401422310050c40201c100c08610080704030218400021006000c4020 + ((0x2010020706c54504014080481000084014003100b0840201c100c0061008070 + ((0xa0503108c382804423090504108c3c24044230a050401148c282032221151410 + (0x402148c7014104231b0503108c6c343018140c0882309050301148c241c3230 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | 2 => (0xd04030100248c644c30181408048231a130d06050201208c84140c085232205 + ((0x188c644c4430100c040092313120d050403020100288c68483418046231a1312 + ((0x4188c48442c18006231f12110b06188c4c443014100c080400a2319110c0601 + ((0x504030201001c8c847430180c6231c0c0604148c14100c080400723221e0d06 + ((0x220c050402011888544c48383420180804a221a08050402011c8c6c34180c523 + ((0x41008008220a0604001488201410080461413110f0c070602012488643010045 + ((0x14100c8221513120d0805040124886c2810005220e0c080504021c883028201 + ((0x100b0504002488504c44403c30141004a22151312100d0805040128888454504 + ((0x221a0c0802148814100c080400723221e0b080218888454504014107221c1211 + ((0x1c88807c5c544c4834209221513120d0803020100288868544c483834282004a + ((0x46221413110f0c030201002888544c48342014100c080400c221513120d0801 + ((0xc120b080018887048442c0c08048221413110f0c05040302010030884c3c3020 + ((0x1148854504014100c080400a222115100c08031c8848442c14100c080400a221 + ((0x602012884641c140c0804721070503020118544c483834201808049211a0d030 + ((0x503021c8434241c140c080082109060300148434140c08046211413110f0c070 + ((0x12884544c48403834140c04a211413110c07050301248470240c005210f0d070 + ((0x4742c1c086222115141005031c846c4844402c140c00921141311100c0705030 + ((0x44c38341c046211513120e0d04020100288464341c085210504030201001c8c8 + ((0x110c0704020100288464504c443c30241c04a211513120e0d050403020100308 + ((0x504c44301c14100c080400c211413110c07011c84807c58504c44301c9211413 + ((0x40341c1072112110b05040302010028846c442c1c006211b12110b0402012084 + (0x2115141005040302010028888450 <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
  | _ => 0
def g127H8 (_ : Nat) : Nat := (0x4023408606040000410c0006342031a0818000142821e00080040408a1400080 + ((0x93408502009c017000010804b42840318306042c1900a000090000304242408 + ((0xb289e000200d61274a46f2e85c421aa9d6648877d35a001c5f681b799302bc64 + ((0x41472329681e37e11000178d0b82d034a382001ca64556bab520ffa9a2a00322 + ((0xaadde318a383400155600121d47988ded8d09a8380e6f6001c8b617cd5c60001 + ((0x48e9966aceeee16922cf7476940000004f4f3b125b046d3333b8f8c981a67e4f + ((0x93d0c5718001585f54001f1de6ee43943070189a8e00000132933722d538c4aa + ((0xf26d67bd2600058b4c734510d7714518652e3776a0a27d373e622ec001f64e4e + ((0x1a03e00012c2ebf8136200000000156e000a07ee433e000ef22c054d52a45731 + ((0x822001f41c03cda4a55060002112d62090720000003200000001682fc0000009 + ((0x26666a0429c001a684be287d02113edf4f000003a0760002f80b0d4f16a001 + ((0x29d0ee4d4ab253685f59d87237845b0a56ce0d83cb00caeb17b740006e600000 + ((0x912b4825c2a000039b5e0001518e9059514a2e4cd0b600000121275da5b4c38 + (0x74977bc186cbeac <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256)) <<< 256))
def g127D9 (_ : Nat) : Nat := (0x186040438c1ba59d142943606c00ff55bfd46ff41bfd45ff417fd04fb40bf501 + ((0xb4c74b1528407070c14203040401ea4f172a5080f101828406080803c30202 + ((0xa13244480c16202840608080411931a30305080c1010059528404070a1018202 + (0x1095284c91120345870a10182020104454 <<< 256)) <<< 256)) <<< 256))
def g127H9 (_ : Nat) : Nat := 0x767ab0000000000060693c84
def g127D10 (_ : Nat) : Nat := 0x51030810067f
def g127L : Nat → Packing
  | 5 => (39,5,6,0,0,9,0,g127D5)
  | 6 => (705,4,6,0,0,13,0,g127D6)
  | 7 => (1071,3,6,0,0,15,0,g127D7)
  | 8 => (200,2,6,0,0,14,0,g127D8)
  | 9 => (8,1,6,0,0,10,0,g127D9)
  | 10 => (1,0,6,0,0,1,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6, h => lookupWord 16 50 5 10 6 0 g127H5 h
  | 7, h => lookupWord 236 833 7 14 10 0 g127H6 h
  | 8, h => lookupWord 359 1266 8 15 11 0 g127H7 h
  | 9, h => lookupWord 71 241 7 12 8 0 g127H8 h
  | 10, h => lookupWord 6 13 1 7 3 0 g127H9 h
  | _, _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,[[]],g127L,g127I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P5_0 : block g127 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P5_5 : block g127 5 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P5_10 : block g127 5 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P5_15 : block g127 5 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P5_20 : block g127 5 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P5_25 : block g127 5 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P5_30 : block g127 5 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P5_35 : block g127 5 35 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127B5 : block g127 5 0 39 = true := (@block_merge g127 5 0 20 19 (@block_merge g127 5 0 10 10 (@block_merge g127 5 0 5 5 g127P5_0 g127P5_5) (@block_merge g127 5 10 5 5 g127P5_10 g127P5_15)) (@block_merge g127 5 20 10 9 (@block_merge g127 5 20 5 5 g127P5_20 g127P5_25) (@block_merge g127 5 30 5 4 g127P5_30 g127P5_35)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_5 : block g127 6 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_10 : block g127 6 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_15 : block g127 6 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_20 : block g127 6 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_25 : block g127 6 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_30 : block g127 6 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_35 : block g127 6 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_40 : block g127 6 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_45 : block g127 6 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_50 : block g127 6 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_55 : block g127 6 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_60 : block g127 6 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_65 : block g127 6 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_70 : block g127 6 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_75 : block g127 6 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_80 : block g127 6 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_85 : block g127 6 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_90 : block g127 6 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_95 : block g127 6 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_100 : block g127 6 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_105 : block g127 6 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_110 : block g127 6 110 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_115 : block g127 6 115 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_120 : block g127 6 120 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_125 : block g127 6 125 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_130 : block g127 6 130 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_135 : block g127 6 135 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_140 : block g127 6 140 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_145 : block g127 6 145 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_150 : block g127 6 150 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_155 : block g127 6 155 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_160 : block g127 6 160 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_165 : block g127 6 165 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_170 : block g127 6 170 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_175 : block g127 6 175 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_180 : block g127 6 180 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_185 : block g127 6 185 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_190 : block g127 6 190 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_195 : block g127 6 195 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_200 : block g127 6 200 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_205 : block g127 6 205 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_210 : block g127 6 210 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_215 : block g127 6 215 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_220 : block g127 6 220 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_225 : block g127 6 225 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_230 : block g127 6 230 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_235 : block g127 6 235 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_240 : block g127 6 240 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_245 : block g127 6 245 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_250 : block g127 6 250 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_255 : block g127 6 255 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_260 : block g127 6 260 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_265 : block g127 6 265 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_270 : block g127 6 270 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_275 : block g127 6 275 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_280 : block g127 6 280 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_285 : block g127 6 285 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_290 : block g127 6 290 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_295 : block g127 6 295 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_300 : block g127 6 300 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_305 : block g127 6 305 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_310 : block g127 6 310 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_315 : block g127 6 315 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_320 : block g127 6 320 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_325 : block g127 6 325 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_330 : block g127 6 330 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_335 : block g127 6 335 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_340 : block g127 6 340 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_345 : block g127 6 345 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_350 : block g127 6 350 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_355 : block g127 6 355 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_360 : block g127 6 360 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_365 : block g127 6 365 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_370 : block g127 6 370 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_375 : block g127 6 375 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_380 : block g127 6 380 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_385 : block g127 6 385 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_390 : block g127 6 390 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_395 : block g127 6 395 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_400 : block g127 6 400 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_405 : block g127 6 405 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_410 : block g127 6 410 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_415 : block g127 6 415 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_420 : block g127 6 420 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_425 : block g127 6 425 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_430 : block g127 6 430 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_435 : block g127 6 435 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_440 : block g127 6 440 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_445 : block g127 6 445 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_450 : block g127 6 450 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_455 : block g127 6 455 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_460 : block g127 6 460 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_465 : block g127 6 465 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_470 : block g127 6 470 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_475 : block g127 6 475 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_480 : block g127 6 480 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_485 : block g127 6 485 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_490 : block g127 6 490 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_495 : block g127 6 495 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_500 : block g127 6 500 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_505 : block g127 6 505 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_510 : block g127 6 510 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_515 : block g127 6 515 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_520 : block g127 6 520 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_525 : block g127 6 525 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_530 : block g127 6 530 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_535 : block g127 6 535 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_540 : block g127 6 540 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_545 : block g127 6 545 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_550 : block g127 6 550 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_555 : block g127 6 555 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_560 : block g127 6 560 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_565 : block g127 6 565 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_570 : block g127 6 570 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_575 : block g127 6 575 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_580 : block g127 6 580 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_585 : block g127 6 585 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_590 : block g127 6 590 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_595 : block g127 6 595 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_600 : block g127 6 600 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_605 : block g127 6 605 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_610 : block g127 6 610 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_615 : block g127 6 615 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_620 : block g127 6 620 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_625 : block g127 6 625 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_630 : block g127 6 630 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_635 : block g127 6 635 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_640 : block g127 6 640 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_645 : block g127 6 645 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_650 : block g127 6 650 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_655 : block g127 6 655 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_660 : block g127 6 660 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_665 : block g127 6 665 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_670 : block g127 6 670 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_675 : block g127 6 675 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_680 : block g127 6 680 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_685 : block g127 6 685 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_690 : block g127 6 690 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_695 : block g127 6 695 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P6_700 : block g127 6 700 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127B6 : block g127 6 0 705 = true := (@block_merge g127 6 0 640 65 (@block_merge g127 6 0 320 320 (@block_merge g127 6 0 160 160 (@block_merge g127 6 0 80 80 (@block_merge g127 6 0 40 40 (@block_merge g127 6 0 20 20 (@block_merge g127 6 0 10 10 (@block_merge g127 6 0 5 5 g127P6_0 g127P6_5) (@block_merge g127 6 10 5 5 g127P6_10 g127P6_15)) (@block_merge g127 6 20 10 10 (@block_merge g127 6 20 5 5 g127P6_20 g127P6_25) (@block_merge g127 6 30 5 5 g127P6_30 g127P6_35))) (@block_merge g127 6 40 20 20 (@block_merge g127 6 40 10 10 (@block_merge g127 6 40 5 5 g127P6_40 g127P6_45) (@block_merge g127 6 50 5 5 g127P6_50 g127P6_55)) (@block_merge g127 6 60 10 10 (@block_merge g127 6 60 5 5 g127P6_60 g127P6_65) (@block_merge g127 6 70 5 5 g127P6_70 g127P6_75)))) (@block_merge g127 6 80 40 40 (@block_merge g127 6 80 20 20 (@block_merge g127 6 80 10 10 (@block_merge g127 6 80 5 5 g127P6_80 g127P6_85) (@block_merge g127 6 90 5 5 g127P6_90 g127P6_95)) (@block_merge g127 6 100 10 10 (@block_merge g127 6 100 5 5 g127P6_100 g127P6_105) (@block_merge g127 6 110 5 5 g127P6_110 g127P6_115))) (@block_merge g127 6 120 20 20 (@block_merge g127 6 120 10 10 (@block_merge g127 6 120 5 5 g127P6_120 g127P6_125) (@block_merge g127 6 130 5 5 g127P6_130 g127P6_135)) (@block_merge g127 6 140 10 10 (@block_merge g127 6 140 5 5 g127P6_140 g127P6_145) (@block_merge g127 6 150 5 5 g127P6_150 g127P6_155))))) (@block_merge g127 6 160 80 80 (@block_merge g127 6 160 40 40 (@block_merge g127 6 160 20 20 (@block_merge g127 6 160 10 10 (@block_merge g127 6 160 5 5 g127P6_160 g127P6_165) (@block_merge g127 6 170 5 5 g127P6_170 g127P6_175)) (@block_merge g127 6 180 10 10 (@block_merge g127 6 180 5 5 g127P6_180 g127P6_185) (@block_merge g127 6 190 5 5 g127P6_190 g127P6_195))) (@block_merge g127 6 200 20 20 (@block_merge g127 6 200 10 10 (@block_merge g127 6 200 5 5 g127P6_200 g127P6_205) (@block_merge g127 6 210 5 5 g127P6_210 g127P6_215)) (@block_merge g127 6 220 10 10 (@block_merge g127 6 220 5 5 g127P6_220 g127P6_225) (@block_merge g127 6 230 5 5 g127P6_230 g127P6_235)))) (@block_merge g127 6 240 40 40 (@block_merge g127 6 240 20 20 (@block_merge g127 6 240 10 10 (@block_merge g127 6 240 5 5 g127P6_240 g127P6_245) (@block_merge g127 6 250 5 5 g127P6_250 g127P6_255)) (@block_merge g127 6 260 10 10 (@block_merge g127 6 260 5 5 g127P6_260 g127P6_265) (@block_merge g127 6 270 5 5 g127P6_270 g127P6_275))) (@block_merge g127 6 280 20 20 (@block_merge g127 6 280 10 10 (@block_merge g127 6 280 5 5 g127P6_280 g127P6_285) (@block_merge g127 6 290 5 5 g127P6_290 g127P6_295)) (@block_merge g127 6 300 10 10 (@block_merge g127 6 300 5 5 g127P6_300 g127P6_305) (@block_merge g127 6 310 5 5 g127P6_310 g127P6_315)))))) (@block_merge g127 6 320 160 160 (@block_merge g127 6 320 80 80 (@block_merge g127 6 320 40 40 (@block_merge g127 6 320 20 20 (@block_merge g127 6 320 10 10 (@block_merge g127 6 320 5 5 g127P6_320 g127P6_325) (@block_merge g127 6 330 5 5 g127P6_330 g127P6_335)) (@block_merge g127 6 340 10 10 (@block_merge g127 6 340 5 5 g127P6_340 g127P6_345) (@block_merge g127 6 350 5 5 g127P6_350 g127P6_355))) (@block_merge g127 6 360 20 20 (@block_merge g127 6 360 10 10 (@block_merge g127 6 360 5 5 g127P6_360 g127P6_365) (@block_merge g127 6 370 5 5 g127P6_370 g127P6_375)) (@block_merge g127 6 380 10 10 (@block_merge g127 6 380 5 5 g127P6_380 g127P6_385) (@block_merge g127 6 390 5 5 g127P6_390 g127P6_395)))) (@block_merge g127 6 400 40 40 (@block_merge g127 6 400 20 20 (@block_merge g127 6 400 10 10 (@block_merge g127 6 400 5 5 g127P6_400 g127P6_405) (@block_merge g127 6 410 5 5 g127P6_410 g127P6_415)) (@block_merge g127 6 420 10 10 (@block_merge g127 6 420 5 5 g127P6_420 g127P6_425) (@block_merge g127 6 430 5 5 g127P6_430 g127P6_435))) (@block_merge g127 6 440 20 20 (@block_merge g127 6 440 10 10 (@block_merge g127 6 440 5 5 g127P6_440 g127P6_445) (@block_merge g127 6 450 5 5 g127P6_450 g127P6_455)) (@block_merge g127 6 460 10 10 (@block_merge g127 6 460 5 5 g127P6_460 g127P6_465) (@block_merge g127 6 470 5 5 g127P6_470 g127P6_475))))) (@block_merge g127 6 480 80 80 (@block_merge g127 6 480 40 40 (@block_merge g127 6 480 20 20 (@block_merge g127 6 480 10 10 (@block_merge g127 6 480 5 5 g127P6_480 g127P6_485) (@block_merge g127 6 490 5 5 g127P6_490 g127P6_495)) (@block_merge g127 6 500 10 10 (@block_merge g127 6 500 5 5 g127P6_500 g127P6_505) (@block_merge g127 6 510 5 5 g127P6_510 g127P6_515))) (@block_merge g127 6 520 20 20 (@block_merge g127 6 520 10 10 (@block_merge g127 6 520 5 5 g127P6_520 g127P6_525) (@block_merge g127 6 530 5 5 g127P6_530 g127P6_535)) (@block_merge g127 6 540 10 10 (@block_merge g127 6 540 5 5 g127P6_540 g127P6_545) (@block_merge g127 6 550 5 5 g127P6_550 g127P6_555)))) (@block_merge g127 6 560 40 40 (@block_merge g127 6 560 20 20 (@block_merge g127 6 560 10 10 (@block_merge g127 6 560 5 5 g127P6_560 g127P6_565) (@block_merge g127 6 570 5 5 g127P6_570 g127P6_575)) (@block_merge g127 6 580 10 10 (@block_merge g127 6 580 5 5 g127P6_580 g127P6_585) (@block_merge g127 6 590 5 5 g127P6_590 g127P6_595))) (@block_merge g127 6 600 20 20 (@block_merge g127 6 600 10 10 (@block_merge g127 6 600 5 5 g127P6_600 g127P6_605) (@block_merge g127 6 610 5 5 g127P6_610 g127P6_615)) (@block_merge g127 6 620 10 10 (@block_merge g127 6 620 5 5 g127P6_620 g127P6_625) (@block_merge g127 6 630 5 5 g127P6_630 g127P6_635))))))) (@block_merge g127 6 640 40 25 (@block_merge g127 6 640 20 20 (@block_merge g127 6 640 10 10 (@block_merge g127 6 640 5 5 g127P6_640 g127P6_645) (@block_merge g127 6 650 5 5 g127P6_650 g127P6_655)) (@block_merge g127 6 660 10 10 (@block_merge g127 6 660 5 5 g127P6_660 g127P6_665) (@block_merge g127 6 670 5 5 g127P6_670 g127P6_675))) (@block_merge g127 6 680 20 5 (@block_merge g127 6 680 10 10 (@block_merge g127 6 680 5 5 g127P6_680 g127P6_685) (@block_merge g127 6 690 5 5 g127P6_690 g127P6_695)) g127P6_700)))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_5 : block g127 7 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_10 : block g127 7 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_15 : block g127 7 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_20 : block g127 7 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_25 : block g127 7 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_30 : block g127 7 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_35 : block g127 7 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_40 : block g127 7 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_45 : block g127 7 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_50 : block g127 7 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_55 : block g127 7 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_60 : block g127 7 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_65 : block g127 7 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_70 : block g127 7 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_75 : block g127 7 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_80 : block g127 7 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_85 : block g127 7 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_90 : block g127 7 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_95 : block g127 7 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_100 : block g127 7 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_105 : block g127 7 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_110 : block g127 7 110 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_115 : block g127 7 115 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_120 : block g127 7 120 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_125 : block g127 7 125 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_130 : block g127 7 130 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_135 : block g127 7 135 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_140 : block g127 7 140 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_145 : block g127 7 145 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_150 : block g127 7 150 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_155 : block g127 7 155 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_160 : block g127 7 160 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_165 : block g127 7 165 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_170 : block g127 7 170 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_175 : block g127 7 175 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_180 : block g127 7 180 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_185 : block g127 7 185 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_190 : block g127 7 190 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_195 : block g127 7 195 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_200 : block g127 7 200 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_205 : block g127 7 205 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_210 : block g127 7 210 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_215 : block g127 7 215 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_220 : block g127 7 220 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_225 : block g127 7 225 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_230 : block g127 7 230 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_235 : block g127 7 235 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_240 : block g127 7 240 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_245 : block g127 7 245 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_250 : block g127 7 250 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_255 : block g127 7 255 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_260 : block g127 7 260 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_265 : block g127 7 265 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_270 : block g127 7 270 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_275 : block g127 7 275 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_280 : block g127 7 280 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_285 : block g127 7 285 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_290 : block g127 7 290 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_295 : block g127 7 295 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_300 : block g127 7 300 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_305 : block g127 7 305 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_310 : block g127 7 310 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_315 : block g127 7 315 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_320 : block g127 7 320 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_325 : block g127 7 325 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_330 : block g127 7 330 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_335 : block g127 7 335 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_340 : block g127 7 340 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_345 : block g127 7 345 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_350 : block g127 7 350 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_355 : block g127 7 355 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_360 : block g127 7 360 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_365 : block g127 7 365 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_370 : block g127 7 370 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_375 : block g127 7 375 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_380 : block g127 7 380 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_385 : block g127 7 385 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_390 : block g127 7 390 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_395 : block g127 7 395 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_400 : block g127 7 400 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_405 : block g127 7 405 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_410 : block g127 7 410 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_415 : block g127 7 415 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_420 : block g127 7 420 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_425 : block g127 7 425 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_430 : block g127 7 430 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_435 : block g127 7 435 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_440 : block g127 7 440 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_445 : block g127 7 445 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_450 : block g127 7 450 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_455 : block g127 7 455 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_460 : block g127 7 460 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_465 : block g127 7 465 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_470 : block g127 7 470 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_475 : block g127 7 475 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_480 : block g127 7 480 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_485 : block g127 7 485 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_490 : block g127 7 490 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_495 : block g127 7 495 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_500 : block g127 7 500 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_505 : block g127 7 505 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_510 : block g127 7 510 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_515 : block g127 7 515 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_520 : block g127 7 520 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_525 : block g127 7 525 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_530 : block g127 7 530 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_535 : block g127 7 535 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_540 : block g127 7 540 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_545 : block g127 7 545 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_550 : block g127 7 550 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_555 : block g127 7 555 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_560 : block g127 7 560 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_565 : block g127 7 565 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_570 : block g127 7 570 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_575 : block g127 7 575 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_580 : block g127 7 580 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_585 : block g127 7 585 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_590 : block g127 7 590 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_595 : block g127 7 595 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_600 : block g127 7 600 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_605 : block g127 7 605 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_610 : block g127 7 610 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_615 : block g127 7 615 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_620 : block g127 7 620 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_625 : block g127 7 625 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_630 : block g127 7 630 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_635 : block g127 7 635 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_640 : block g127 7 640 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_645 : block g127 7 645 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_650 : block g127 7 650 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_655 : block g127 7 655 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_660 : block g127 7 660 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_665 : block g127 7 665 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_670 : block g127 7 670 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_675 : block g127 7 675 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_680 : block g127 7 680 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_685 : block g127 7 685 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_690 : block g127 7 690 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_695 : block g127 7 695 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_700 : block g127 7 700 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_705 : block g127 7 705 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_710 : block g127 7 710 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_715 : block g127 7 715 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_720 : block g127 7 720 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_725 : block g127 7 725 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_730 : block g127 7 730 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_735 : block g127 7 735 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_740 : block g127 7 740 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_745 : block g127 7 745 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_750 : block g127 7 750 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_755 : block g127 7 755 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_760 : block g127 7 760 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_765 : block g127 7 765 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_770 : block g127 7 770 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_775 : block g127 7 775 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_780 : block g127 7 780 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_785 : block g127 7 785 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_790 : block g127 7 790 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_795 : block g127 7 795 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_800 : block g127 7 800 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_805 : block g127 7 805 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_810 : block g127 7 810 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_815 : block g127 7 815 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_820 : block g127 7 820 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_825 : block g127 7 825 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_830 : block g127 7 830 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_835 : block g127 7 835 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_840 : block g127 7 840 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_845 : block g127 7 845 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_850 : block g127 7 850 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_855 : block g127 7 855 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_860 : block g127 7 860 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_865 : block g127 7 865 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_870 : block g127 7 870 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_875 : block g127 7 875 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_880 : block g127 7 880 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_885 : block g127 7 885 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_890 : block g127 7 890 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_895 : block g127 7 895 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_900 : block g127 7 900 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_905 : block g127 7 905 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_910 : block g127 7 910 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_915 : block g127 7 915 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_920 : block g127 7 920 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_925 : block g127 7 925 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_930 : block g127 7 930 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_935 : block g127 7 935 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_940 : block g127 7 940 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_945 : block g127 7 945 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_950 : block g127 7 950 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_955 : block g127 7 955 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_960 : block g127 7 960 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_965 : block g127 7 965 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_970 : block g127 7 970 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_975 : block g127 7 975 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_980 : block g127 7 980 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_985 : block g127 7 985 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_990 : block g127 7 990 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_995 : block g127 7 995 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1000 : block g127 7 1000 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1005 : block g127 7 1005 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1010 : block g127 7 1010 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1015 : block g127 7 1015 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1020 : block g127 7 1020 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1025 : block g127 7 1025 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1030 : block g127 7 1030 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1035 : block g127 7 1035 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1040 : block g127 7 1040 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1045 : block g127 7 1045 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1050 : block g127 7 1050 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1055 : block g127 7 1055 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1060 : block g127 7 1060 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1065 : block g127 7 1065 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P7_1070 : block g127 7 1070 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127B7 : block g127 7 0 1071 = true := (@block_merge g127 7 0 640 431 (@block_merge g127 7 0 320 320 (@block_merge g127 7 0 160 160 (@block_merge g127 7 0 80 80 (@block_merge g127 7 0 40 40 (@block_merge g127 7 0 20 20 (@block_merge g127 7 0 10 10 (@block_merge g127 7 0 5 5 g127P7_0 g127P7_5) (@block_merge g127 7 10 5 5 g127P7_10 g127P7_15)) (@block_merge g127 7 20 10 10 (@block_merge g127 7 20 5 5 g127P7_20 g127P7_25) (@block_merge g127 7 30 5 5 g127P7_30 g127P7_35))) (@block_merge g127 7 40 20 20 (@block_merge g127 7 40 10 10 (@block_merge g127 7 40 5 5 g127P7_40 g127P7_45) (@block_merge g127 7 50 5 5 g127P7_50 g127P7_55)) (@block_merge g127 7 60 10 10 (@block_merge g127 7 60 5 5 g127P7_60 g127P7_65) (@block_merge g127 7 70 5 5 g127P7_70 g127P7_75)))) (@block_merge g127 7 80 40 40 (@block_merge g127 7 80 20 20 (@block_merge g127 7 80 10 10 (@block_merge g127 7 80 5 5 g127P7_80 g127P7_85) (@block_merge g127 7 90 5 5 g127P7_90 g127P7_95)) (@block_merge g127 7 100 10 10 (@block_merge g127 7 100 5 5 g127P7_100 g127P7_105) (@block_merge g127 7 110 5 5 g127P7_110 g127P7_115))) (@block_merge g127 7 120 20 20 (@block_merge g127 7 120 10 10 (@block_merge g127 7 120 5 5 g127P7_120 g127P7_125) (@block_merge g127 7 130 5 5 g127P7_130 g127P7_135)) (@block_merge g127 7 140 10 10 (@block_merge g127 7 140 5 5 g127P7_140 g127P7_145) (@block_merge g127 7 150 5 5 g127P7_150 g127P7_155))))) (@block_merge g127 7 160 80 80 (@block_merge g127 7 160 40 40 (@block_merge g127 7 160 20 20 (@block_merge g127 7 160 10 10 (@block_merge g127 7 160 5 5 g127P7_160 g127P7_165) (@block_merge g127 7 170 5 5 g127P7_170 g127P7_175)) (@block_merge g127 7 180 10 10 (@block_merge g127 7 180 5 5 g127P7_180 g127P7_185) (@block_merge g127 7 190 5 5 g127P7_190 g127P7_195))) (@block_merge g127 7 200 20 20 (@block_merge g127 7 200 10 10 (@block_merge g127 7 200 5 5 g127P7_200 g127P7_205) (@block_merge g127 7 210 5 5 g127P7_210 g127P7_215)) (@block_merge g127 7 220 10 10 (@block_merge g127 7 220 5 5 g127P7_220 g127P7_225) (@block_merge g127 7 230 5 5 g127P7_230 g127P7_235)))) (@block_merge g127 7 240 40 40 (@block_merge g127 7 240 20 20 (@block_merge g127 7 240 10 10 (@block_merge g127 7 240 5 5 g127P7_240 g127P7_245) (@block_merge g127 7 250 5 5 g127P7_250 g127P7_255)) (@block_merge g127 7 260 10 10 (@block_merge g127 7 260 5 5 g127P7_260 g127P7_265) (@block_merge g127 7 270 5 5 g127P7_270 g127P7_275))) (@block_merge g127 7 280 20 20 (@block_merge g127 7 280 10 10 (@block_merge g127 7 280 5 5 g127P7_280 g127P7_285) (@block_merge g127 7 290 5 5 g127P7_290 g127P7_295)) (@block_merge g127 7 300 10 10 (@block_merge g127 7 300 5 5 g127P7_300 g127P7_305) (@block_merge g127 7 310 5 5 g127P7_310 g127P7_315)))))) (@block_merge g127 7 320 160 160 (@block_merge g127 7 320 80 80 (@block_merge g127 7 320 40 40 (@block_merge g127 7 320 20 20 (@block_merge g127 7 320 10 10 (@block_merge g127 7 320 5 5 g127P7_320 g127P7_325) (@block_merge g127 7 330 5 5 g127P7_330 g127P7_335)) (@block_merge g127 7 340 10 10 (@block_merge g127 7 340 5 5 g127P7_340 g127P7_345) (@block_merge g127 7 350 5 5 g127P7_350 g127P7_355))) (@block_merge g127 7 360 20 20 (@block_merge g127 7 360 10 10 (@block_merge g127 7 360 5 5 g127P7_360 g127P7_365) (@block_merge g127 7 370 5 5 g127P7_370 g127P7_375)) (@block_merge g127 7 380 10 10 (@block_merge g127 7 380 5 5 g127P7_380 g127P7_385) (@block_merge g127 7 390 5 5 g127P7_390 g127P7_395)))) (@block_merge g127 7 400 40 40 (@block_merge g127 7 400 20 20 (@block_merge g127 7 400 10 10 (@block_merge g127 7 400 5 5 g127P7_400 g127P7_405) (@block_merge g127 7 410 5 5 g127P7_410 g127P7_415)) (@block_merge g127 7 420 10 10 (@block_merge g127 7 420 5 5 g127P7_420 g127P7_425) (@block_merge g127 7 430 5 5 g127P7_430 g127P7_435))) (@block_merge g127 7 440 20 20 (@block_merge g127 7 440 10 10 (@block_merge g127 7 440 5 5 g127P7_440 g127P7_445) (@block_merge g127 7 450 5 5 g127P7_450 g127P7_455)) (@block_merge g127 7 460 10 10 (@block_merge g127 7 460 5 5 g127P7_460 g127P7_465) (@block_merge g127 7 470 5 5 g127P7_470 g127P7_475))))) (@block_merge g127 7 480 80 80 (@block_merge g127 7 480 40 40 (@block_merge g127 7 480 20 20 (@block_merge g127 7 480 10 10 (@block_merge g127 7 480 5 5 g127P7_480 g127P7_485) (@block_merge g127 7 490 5 5 g127P7_490 g127P7_495)) (@block_merge g127 7 500 10 10 (@block_merge g127 7 500 5 5 g127P7_500 g127P7_505) (@block_merge g127 7 510 5 5 g127P7_510 g127P7_515))) (@block_merge g127 7 520 20 20 (@block_merge g127 7 520 10 10 (@block_merge g127 7 520 5 5 g127P7_520 g127P7_525) (@block_merge g127 7 530 5 5 g127P7_530 g127P7_535)) (@block_merge g127 7 540 10 10 (@block_merge g127 7 540 5 5 g127P7_540 g127P7_545) (@block_merge g127 7 550 5 5 g127P7_550 g127P7_555)))) (@block_merge g127 7 560 40 40 (@block_merge g127 7 560 20 20 (@block_merge g127 7 560 10 10 (@block_merge g127 7 560 5 5 g127P7_560 g127P7_565) (@block_merge g127 7 570 5 5 g127P7_570 g127P7_575)) (@block_merge g127 7 580 10 10 (@block_merge g127 7 580 5 5 g127P7_580 g127P7_585) (@block_merge g127 7 590 5 5 g127P7_590 g127P7_595))) (@block_merge g127 7 600 20 20 (@block_merge g127 7 600 10 10 (@block_merge g127 7 600 5 5 g127P7_600 g127P7_605) (@block_merge g127 7 610 5 5 g127P7_610 g127P7_615)) (@block_merge g127 7 620 10 10 (@block_merge g127 7 620 5 5 g127P7_620 g127P7_625) (@block_merge g127 7 630 5 5 g127P7_630 g127P7_635))))))) (@block_merge g127 7 640 320 111 (@block_merge g127 7 640 160 160 (@block_merge g127 7 640 80 80 (@block_merge g127 7 640 40 40 (@block_merge g127 7 640 20 20 (@block_merge g127 7 640 10 10 (@block_merge g127 7 640 5 5 g127P7_640 g127P7_645) (@block_merge g127 7 650 5 5 g127P7_650 g127P7_655)) (@block_merge g127 7 660 10 10 (@block_merge g127 7 660 5 5 g127P7_660 g127P7_665) (@block_merge g127 7 670 5 5 g127P7_670 g127P7_675))) (@block_merge g127 7 680 20 20 (@block_merge g127 7 680 10 10 (@block_merge g127 7 680 5 5 g127P7_680 g127P7_685) (@block_merge g127 7 690 5 5 g127P7_690 g127P7_695)) (@block_merge g127 7 700 10 10 (@block_merge g127 7 700 5 5 g127P7_700 g127P7_705) (@block_merge g127 7 710 5 5 g127P7_710 g127P7_715)))) (@block_merge g127 7 720 40 40 (@block_merge g127 7 720 20 20 (@block_merge g127 7 720 10 10 (@block_merge g127 7 720 5 5 g127P7_720 g127P7_725) (@block_merge g127 7 730 5 5 g127P7_730 g127P7_735)) (@block_merge g127 7 740 10 10 (@block_merge g127 7 740 5 5 g127P7_740 g127P7_745) (@block_merge g127 7 750 5 5 g127P7_750 g127P7_755))) (@block_merge g127 7 760 20 20 (@block_merge g127 7 760 10 10 (@block_merge g127 7 760 5 5 g127P7_760 g127P7_765) (@block_merge g127 7 770 5 5 g127P7_770 g127P7_775)) (@block_merge g127 7 780 10 10 (@block_merge g127 7 780 5 5 g127P7_780 g127P7_785) (@block_merge g127 7 790 5 5 g127P7_790 g127P7_795))))) (@block_merge g127 7 800 80 80 (@block_merge g127 7 800 40 40 (@block_merge g127 7 800 20 20 (@block_merge g127 7 800 10 10 (@block_merge g127 7 800 5 5 g127P7_800 g127P7_805) (@block_merge g127 7 810 5 5 g127P7_810 g127P7_815)) (@block_merge g127 7 820 10 10 (@block_merge g127 7 820 5 5 g127P7_820 g127P7_825) (@block_merge g127 7 830 5 5 g127P7_830 g127P7_835))) (@block_merge g127 7 840 20 20 (@block_merge g127 7 840 10 10 (@block_merge g127 7 840 5 5 g127P7_840 g127P7_845) (@block_merge g127 7 850 5 5 g127P7_850 g127P7_855)) (@block_merge g127 7 860 10 10 (@block_merge g127 7 860 5 5 g127P7_860 g127P7_865) (@block_merge g127 7 870 5 5 g127P7_870 g127P7_875)))) (@block_merge g127 7 880 40 40 (@block_merge g127 7 880 20 20 (@block_merge g127 7 880 10 10 (@block_merge g127 7 880 5 5 g127P7_880 g127P7_885) (@block_merge g127 7 890 5 5 g127P7_890 g127P7_895)) (@block_merge g127 7 900 10 10 (@block_merge g127 7 900 5 5 g127P7_900 g127P7_905) (@block_merge g127 7 910 5 5 g127P7_910 g127P7_915))) (@block_merge g127 7 920 20 20 (@block_merge g127 7 920 10 10 (@block_merge g127 7 920 5 5 g127P7_920 g127P7_925) (@block_merge g127 7 930 5 5 g127P7_930 g127P7_935)) (@block_merge g127 7 940 10 10 (@block_merge g127 7 940 5 5 g127P7_940 g127P7_945) (@block_merge g127 7 950 5 5 g127P7_950 g127P7_955)))))) (@block_merge g127 7 960 80 31 (@block_merge g127 7 960 40 40 (@block_merge g127 7 960 20 20 (@block_merge g127 7 960 10 10 (@block_merge g127 7 960 5 5 g127P7_960 g127P7_965) (@block_merge g127 7 970 5 5 g127P7_970 g127P7_975)) (@block_merge g127 7 980 10 10 (@block_merge g127 7 980 5 5 g127P7_980 g127P7_985) (@block_merge g127 7 990 5 5 g127P7_990 g127P7_995))) (@block_merge g127 7 1000 20 20 (@block_merge g127 7 1000 10 10 (@block_merge g127 7 1000 5 5 g127P7_1000 g127P7_1005) (@block_merge g127 7 1010 5 5 g127P7_1010 g127P7_1015)) (@block_merge g127 7 1020 10 10 (@block_merge g127 7 1020 5 5 g127P7_1020 g127P7_1025) (@block_merge g127 7 1030 5 5 g127P7_1030 g127P7_1035)))) (@block_merge g127 7 1040 20 11 (@block_merge g127 7 1040 10 10 (@block_merge g127 7 1040 5 5 g127P7_1040 g127P7_1045) (@block_merge g127 7 1050 5 5 g127P7_1050 g127P7_1055)) (@block_merge g127 7 1060 10 1 (@block_merge g127 7 1060 5 5 g127P7_1060 g127P7_1065) g127P7_1070)))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_5 : block g127 8 5 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_10 : block g127 8 10 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_15 : block g127 8 15 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_20 : block g127 8 20 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_25 : block g127 8 25 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_30 : block g127 8 30 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_35 : block g127 8 35 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_40 : block g127 8 40 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_45 : block g127 8 45 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_50 : block g127 8 50 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_55 : block g127 8 55 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_60 : block g127 8 60 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_65 : block g127 8 65 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_70 : block g127 8 70 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_75 : block g127 8 75 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_80 : block g127 8 80 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_85 : block g127 8 85 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_90 : block g127 8 90 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_95 : block g127 8 95 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_100 : block g127 8 100 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_105 : block g127 8 105 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_110 : block g127 8 110 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_115 : block g127 8 115 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_120 : block g127 8 120 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_125 : block g127 8 125 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_130 : block g127 8 130 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_135 : block g127 8 135 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_140 : block g127 8 140 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_145 : block g127 8 145 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_150 : block g127 8 150 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_155 : block g127 8 155 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_160 : block g127 8 160 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_165 : block g127 8 165 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_170 : block g127 8 170 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_175 : block g127 8 175 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_180 : block g127 8 180 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_185 : block g127 8 185 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_190 : block g127 8 190 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P8_195 : block g127 8 195 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127B8 : block g127 8 0 200 = true := (@block_merge g127 8 0 160 40 (@block_merge g127 8 0 80 80 (@block_merge g127 8 0 40 40 (@block_merge g127 8 0 20 20 (@block_merge g127 8 0 10 10 (@block_merge g127 8 0 5 5 g127P8_0 g127P8_5) (@block_merge g127 8 10 5 5 g127P8_10 g127P8_15)) (@block_merge g127 8 20 10 10 (@block_merge g127 8 20 5 5 g127P8_20 g127P8_25) (@block_merge g127 8 30 5 5 g127P8_30 g127P8_35))) (@block_merge g127 8 40 20 20 (@block_merge g127 8 40 10 10 (@block_merge g127 8 40 5 5 g127P8_40 g127P8_45) (@block_merge g127 8 50 5 5 g127P8_50 g127P8_55)) (@block_merge g127 8 60 10 10 (@block_merge g127 8 60 5 5 g127P8_60 g127P8_65) (@block_merge g127 8 70 5 5 g127P8_70 g127P8_75)))) (@block_merge g127 8 80 40 40 (@block_merge g127 8 80 20 20 (@block_merge g127 8 80 10 10 (@block_merge g127 8 80 5 5 g127P8_80 g127P8_85) (@block_merge g127 8 90 5 5 g127P8_90 g127P8_95)) (@block_merge g127 8 100 10 10 (@block_merge g127 8 100 5 5 g127P8_100 g127P8_105) (@block_merge g127 8 110 5 5 g127P8_110 g127P8_115))) (@block_merge g127 8 120 20 20 (@block_merge g127 8 120 10 10 (@block_merge g127 8 120 5 5 g127P8_120 g127P8_125) (@block_merge g127 8 130 5 5 g127P8_130 g127P8_135)) (@block_merge g127 8 140 10 10 (@block_merge g127 8 140 5 5 g127P8_140 g127P8_145) (@block_merge g127 8 150 5 5 g127P8_150 g127P8_155))))) (@block_merge g127 8 160 20 20 (@block_merge g127 8 160 10 10 (@block_merge g127 8 160 5 5 g127P8_160 g127P8_165) (@block_merge g127 8 170 5 5 g127P8_170 g127P8_175)) (@block_merge g127 8 180 10 10 (@block_merge g127 8 180 5 5 g127P8_180 g127P8_185) (@block_merge g127 8 190 5 5 g127P8_190 g127P8_195))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P9_5 : block g127 9 5 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127B9 : block g127 9 0 8 = true := (@block_merge g127 9 0 5 3 g127P9_0 g127P9_5)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127B10 : block g127 10 0 1 = true := g127P10_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g127B5
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=1347) (before_sound K119 V119) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def postedGraph : Sig := 0xfffffffffffffffefffffffefffffffeffffffffffeeffeefefefefeaaaa0000fffffffffffffffefffffffefffffffeffffffffffeeffeefefefefeaaaa0000
theorem postedGraphProper : proper postedGraph := by unfold proper; decide +kernel

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [5, 7]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [11, 2]⟩,
    ⟨.or, [11, 3]⟩,
    ⟨.and, [4, 9]⟩,
    ⟨.and, [12, 8]⟩,
    ⟨.and, [13, 10]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [18, 16]⟩,
    ⟨.or, [19, 17]⟩], 20⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (([16, 32, 32, 64, 1, 1, 1, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((([16, 32, 32, 64, 1, 1, 1, 1] : List Nat).getD i.val 0) ||| (1 <<< i.val))

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
    (lower : Impossible true postedGraph 11 eightInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 13 ≤ gates.length
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

def coreMoves : List Move := ([113, 114, 115, 116, 117, 118].map swapRows) ++ fixRows 2 0
def removed : List (Sig × Row × Row) := [(eightInputs.getD 1 zero, 32, 34)]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem restricted : Lower true eightInputs postedGraph 12 := by
  have h := lift_ok (u:=true) (ms:=coreMoves) (T:=postedGraph) (raw:=eightInputs)
    (base:=varsX 127) (G:=graphGoal 127) (xs:=removed)
    (by decide +kernel) postedGraphProper (proper_of _ (by decide +kernel)) low127
  exact h

theorem excluded : Impossible true postedGraph 11 eightInputs.toFinset := by
  intro k small run
  have steps := list_run run eightInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper postedGraphProper)
    steps (eightInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := restricted q bank built hit
  omega

end PEqualNP.Outside.L_meta_28866

theorem PEqualNP.Outside.L_meta_28866 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_28866.replaceShort PEqualNP.Outside.L_meta_28866.excluded gates o fit correct
