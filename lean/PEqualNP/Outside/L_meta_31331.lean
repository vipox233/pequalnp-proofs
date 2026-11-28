import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31331

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
  (x 0 &&& x 3) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)

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
  (x 0 &&& x 3) ||| (x 0 &&& x 5) ||| (x 0 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 4) ||| (x 1 &&& x 5) ||| (x 1 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 5) ||| (x 3 &&& x 6) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)

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

def g41Y : Array (Bits × Bits) := #[ (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbef5,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4405), (0x0,0x0), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fab,0x80a8), (0x0,0x0), (0xddde,0x2812), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g41C : List ColumnInfo := []
set_option maxRecDepth 100000 in
def g41D3 (_ : Nat) : Nat := 0x7
def g41L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,g41D3)
  | _ => emptyPacking
def g41I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g41 : Forest := ⟨41,3,fun i => g41Y[i]?.getD (0,0),g41C,[[]],g41L,g41I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g41P3_0 : block g41 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g41B3 : block g41 3 0 1 = true := g41P3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g41T : checkedTables g41 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g41B3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore K0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low41 : Lower true (varsX 41) (graphGoal 41) 4 := lower_forest (g:=g41) (i:=0) (hints:=3) (before_sound K0 V0) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown K0 4 [(41,[]),(146,[16, 67, 101, 118]),(161,[67, 100, 101, 118]),(162,[16, 67, 100, 101, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) V0 low41 (by decide +kernel)

def g51Y : Array (Bits × Bits) := #[ (0xe5fbc4f277cb93e6,0x1a075111621351e4), (0xffffffffffffffffffffffffffffffffffffffffffffffffbebf3fcfdb3dfd5d,0xffffffffffffffffffffffffffffffffffffffffffffffff4000c50321054505), (0x0,0x0), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffead15ffc5bbd4379,0x150a30e4163a2278), (0xdd7ff77fa6cfbeae,0x2018088804a8aa0a), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g51C : List ColumnInfo := []
set_option maxRecDepth 100000 in
def g51D3 (_ : Nat) : Nat := 0xf
def g51L : Nat → Packing
  | 3 => (1,0,1,0,0,1,0,g51D3)
  | _ => emptyPacking
def g51I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g51 : Forest := ⟨51,3,fun i => g51Y[i]?.getD (0,0),g51C,[[]],g51L,g51I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g51P3_0 : block g51 3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g51B3 : block g51 3 0 1 = true := g51P3_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g51T : checkedTables g51 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g51B3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 4 := lower_forest (g:=g51) (i:=0) (hints:=65605) (before_sound K41 V41) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K41 4 [(51,[]),(58,[32, 50]),(83,[101]),(101,[16, 33, 100, 101]),(108,[32, 49, 100, 101]),(139,[16, 67, 101, 118]),(141,[16, 33, 67, 101, 118]),(153,[80, 33, 50, 83, 101, 118]),(172,[32, 49, 67, 100, 101, 118]),(184,[32, 49, 98, 99, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V41 low51 (by decide +kernel)

def g43Y : Array (Bits × Bits) := #[ (0xffffffffffffffffffffffffffffffffffffffffffffffffb7b1f5fcdbf66ba9,0xffffffffffffffffffffffffffffffffffffffffffffffffc864420652022a81), (0x3ceba3171fe91d86,0x43814eaa7d4a0d84), (0x0,0x0), (0x5e37fbacb87fbb5c,0x218801c82471011c), (0x0,0x0), (0xffffffffffffffffffffffffffffffffffffffffffffffffefefdfd377ddf4f7,0x1010800000841062), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g43C : List ColumnInfo := [(2,0,41,0,4)]
set_option maxRecDepth 100000 in
def g43D4 (_ : Nat) : Nat := 0x2f
def g43L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g43D4)
  | _ => emptyPacking
def g43I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g43 : Forest := ⟨43,4,fun i => g43Y[i]?.getD (0,0),g43C,[[]],g43L,g43I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g43P4_0 : block g43 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g43B4 : block g43 4 0 1 = true := g43P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g43B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K51 V51) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K51 5 [(43,[]),(75,[101]),(77,[33, 101]),(147,[16, 67, 101, 118]),(150,[32, 33, 67, 101, 118]),(165,[33, 67, 100, 101, 118]),(166,[32, 33, 67, 100, 101, 118]),(170,[32, 33, 66, 67, 100, 118]),(177,[33, 66, 99, 101, 118]),(204,[32, 65, 67, 100, 117, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V51 low43 (by decide +kernel)

def g105Y : Array (Bits × Bits) := #[ (0xeeefde679fb5e8e,0x11040102082020a), (0x0,0x0), (0x0,0x0), (0xfffffffffffffffffffffffffffffffffffffffffffffffffbd7f3dda777e573,0xfffffffffffffffffffffffffffffffffffffffffffffffff40805000020c411), (0x0,0x0), (0xfffffffffffffffffffffffffffffffffffffffffffffffff7936fa746faba65,0x86600ca4e540864), (0xf2c7b98fb94f1dc,0xc7a0220d1431c4), (0x0,0x0), (0x0,0x0) ]
def g105C : List ColumnInfo := [(64,0,41,0,4)]
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
def K105 := extendKnown K43 5 [(105,[]),(163,[80, 97, 98, 99, 118]),(169,[83, 118]),(178,[16, 67, 84, 101, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V105 : Known true K105 := extend_ok (m:=105) V43 low105 (by decide +kernel)

def g103Y : Array (Bits × Bits) := #[ (0xfffff73f5dccb6e57394efdbb6a7eb37306dbed1c6a5397bbfe83a93176d819d,0xffff08d1a2ba09100c39600344a356080e46c8048486ab72116a16900064808d), (0xb3dca71ceb7bfaef5a7c73de55286df5f9eabbdaa04e877f946aee62fc26,0x4c2b30c304c00c3a6002642711fc020841c18682a816052705a24a60ac06), (0x795e12b3baaf4f5580bc486fe3dafa6e63be8c6e5ea664fe417d16d44ad6,0x86a5f91c4450a62bc11bb58d60b84b380c0404673b0205cfc34c0e544a96), (0x0,0x0), (0x0,0x0), (0xffff5ffb75f93b76eef66f399f5f77bf18d0fb7cd7ad00aa7f9eb6ecfd43ebf1,0xa0040900e0281104993013408800d0012202101904882a90c84035034370), (0xfeddfffff7c99f4bf1f76bbffacbf72fb5e739d6ffd7d2f5695753bf164e,0x1000000822600800c00004080022081322209100400ca102801308b1040), (0x0,0x0), (0x0,0x0) ]
def g103C : List ColumnInfo := [(2,0,101,0,4)]
set_option maxRecDepth 100000 in
def g103D4 (_ : Nat) : Nat := 0x5f
def g103L : Nat → Packing
  | 4 => (1,0,1,0,0,1,0,g103D4)
  | _ => emptyPacking
def g103I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g103 : Forest := ⟨103,4,fun i => g103Y[i]?.getD (0,0),g103C,[[]],g103L,g103I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g103P4_0 : block g103 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g103B4 : block g103 4 0 1 = true := g103P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g103B4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore K105) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low103 : Lower true (varsX 103) (graphGoal 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=1621) (before_sound K105 V105) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K103 := extendKnown K105 5 [(103,[]),(115,[80, 97, 50, 67]),(248,[48, 65, 114, 83, 116, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V103 : Known true K103 := extend_ok (m:=103) V105 low103 (by decide +kernel)

def g87Y : Array (Bits × Bits) := #[ (0xda5d6c2ebf61c5768d28073a7bdfbdf4b4256df1775fd3f2133485563de990a,0x25a2c3e940573285d51456ce0250872b12f75809df5961e014b415506de9802), (0x97fdb1a77fefbb8fd8ff3aa7afdd773fedbcd25ace6b4e4eef573fcee0cbef6,0x680447580400606006189cdc2900a26000104248c76240028440419ec009c66), (0xf3d53335f87d19bf16a36c4559a73fe269beba3e738d8e605d4ce4d7f5754c33,0xfc2a468e3702a64ac1d8ddd5360561b02c89648404cf1a788548e44de5550c33), (0x0,0x0), (0x6eddeddcbe93aaadd9ee8c8dcf6c4b35e6bf77790e6ff68dfa3d1e0be9de49e,0x912210a3134c861278206200c29601955f8809b10899b2ac6a14b82109d6098), (0x0,0x0), (0xfffeffffbd7fd77feaf33fffbf7fbbfeb5fc3efe7f3d4b9f35fffe9fd9f37b69,0x110000090088000062000000890010010820a2200400012301a8200206308), (0x0,0x0), (0x0,0x0) ]
def g87C : List ColumnInfo := [(4,0,83,0,4)]
set_option maxRecDepth 100000 in
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
theorem g87G : graphValid g87 (boundsBefore K103) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low87 : Lower true (varsX 87) (graphGoal 87) 5 := lower_forest (g:=g87) (i:=0) (hints:=67142) (before_sound K103 V103) g87G g87T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K87 := extendKnown K103 5 [(87,[]),(118,[48, 97, 66, 83, 84]),(143,[16, 67, 118]),(188,[48, 81, 50, 67, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V87 : Known true K87 := extend_ok (m:=87) V103 low87 (by decide +kernel)

def g236Y : Array (Bits × Bits) := #[ (0x0,0x0), (0x0,0x0), (0xfffffffffafb3cfafa53b7bee66d49fb66b859e7702659d3de1fcd2367c28eab,0x504860131a4484608405295440ae43082461b01421d110144428e0a), (0xd7b62a5fd7b79b97d69fe11f97f2d64cbd7d87cbf6513e09187d11e,0x284952a02a0a024a49054a026402304a342403a4a09226881869118), (0x0,0x0), (0x3f4577fd4f73b3c3abcffb79972d1ac8fbd2a0cbab5de0dd91b7a32,0xc0a28012848544a484a2906109f002300192b01b1245c1042194a22), (0x7ef9f3d7f2ff2fbd7c77cdee5c76eb5645adcfd7350e8d6ee3587e4,0x81040c088410410500c890010840808101020441160c0120a1100e4), (0xfffffffffdbdedeb7fed1f471c966d6757bcfbfefdbb271a0ccf65ff6cfc3849,0xfffffffff240001c4010a080218000282960008460a0003a0c00228c20a43001), (0x0,0x0) ]
def g236C : List ColumnInfo := [(32,0,204,0,5)]
set_option maxRecDepth 100000 in
def g236D5 (_ : Nat) : Nat := 0x5f
def g236L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,g236D5)
  | _ => emptyPacking
def g236I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g236 : Forest := ⟨236,5,fun i => g236Y[i]?.getD (0,0),g236C,[[]],g236L,g236I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g236P5_0 : block g236 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g236B5 : block g236 5 0 1 = true := g236P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g236T : checkedTables g236 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g236B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g236G : graphValid g236 (boundsBefore K87) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low236 : Lower true (varsX 236) (graphGoal 236) 6 := lower_forest (g:=g236) (i:=0) (hints:=573593088) (before_sound K87 V87) g236G g236T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K236 := extendKnown K87 6 [(236,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V236 : Known true K236 := extend_ok (m:=236) V87 low236 (by decide +kernel)

def g174Y : Array (Bits × Bits) := #[ (0x0,0x0), (0xffffdabdeefc1fb6a1f19412f38fffccb4636fefda344fd2fabf0e83b7979135,0xffff25469502204916160bca08aa828920a2281c51200e5598cb060223161115), (0xb69b3c5a63a2cf3fcad6fcd08e6259ce74f5578e967945fc7f6034504dfc,0x496c83658c4706c3ad50800612dc2aa5dad40ba70671147cd22a06104df4), (0xdd1995e8b4e47d6e479f2410b79b1ff4e3dbb4cca7b7e1e2d04b4f35788e,0x22e54b134e1a03151bae168a745870881285d40c3507ebe9122e4235508e), (0x0,0x0), (0xffff77ffe53dff7f7f3465ffe73ff27957b79dffeedb2c57b8acfdddcf38fa73,0x880000c0000480a8c410204000008a01002208810000040489418c08a860), (0x0,0x0), (0xedff9fcfc79fbefffa7b9de86fbeffcf7eae35b7ffeac7573336b8ef07cc,0x120060081200410000041001400055500400a41090824200200450e10208), (0x0,0x0) ]
def g174C : List ColumnInfo := [(8,0,166,0,5)]
set_option maxRecDepth 100000 in
def g174D5 (_ : Nat) : Nat := 0x5f
def g174L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,g174D5)
  | _ => emptyPacking
def g174I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g174 : Forest := ⟨174,5,fun i => g174Y[i]?.getD (0,0),g174C,[[]],g174L,g174I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g174P5_0 : block g174 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g174B5 : block g174 5 0 1 = true := g174P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g174T : checkedTables g174 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g174B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g174G : graphValid g174 (boundsBefore K236) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low174 : Lower true (varsX 174) (graphGoal 174) 6 := lower_forest (g:=g174) (i:=0) (hints:=269506384) (before_sound K236 V236) g174G g174T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K174 := extendKnown K236 6 [(174,[]),(220,[65, 66, 67, 101, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V174 : Known true K174 := extend_ok (m:=174) V236 low174 (by decide +kernel)

def g227Y : Array (Bits × Bits) := #[ (0xebbdd57f2e8eddf7a51b166e1ccdd39f3f9b3369246f3b00,0x14460888c0418020b80830308910061803836540200b3200), (0xedc6bf3727f53f0df9ed774fa2326ea86c96cd73d38a82fa,0x120300887809c811080948a08880040021036d61500a8218), (0x0,0x0), (0x0,0x0), (0x0,0x0), (0xffffffffffffffff77ce73feba58bfb73f3851f1f42e46b11a6f8bbc9f486975,0x88b0040201a4030c019281020248c9c1184402100b404964), (0xb79f9e58f75de16f86dffb4eb903b95e9c4aeac763b30c2e,0x482061030226020e4002004b600c59410c08821609200c26), (0xffffffffffffffffdff778cfffb73aeeeb1fcdbc7bf81064e3f417c67dd4d685,0xffffffffffffffff200892200000300000600004140100240010008004940081), (0x0,0x0) ]
def g227C : List ColumnInfo := [(64,0,163,0,5)]
set_option maxRecDepth 100000 in
def g227D5 (_ : Nat) : Nat := 0x5f
def g227L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,g227D5)
  | _ => emptyPacking
def g227I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g227 : Forest := ⟨227,5,fun i => g227Y[i]?.getD (0,0),g227C,[[]],g227L,g227I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g227P5_0 : block g227 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g227B5 : block g227 5 0 1 = true := g227P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g227T : checkedTables g227 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g227B5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g227G : graphValid g227 (boundsBefore K174) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low227 : Lower true (varsX 227) (graphGoal 227) 6 := lower_forest (g:=g227) (i:=0) (hints:=85) (before_sound K174 V174) g227G g227T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K227 := extendKnown K174 6 [(233,[112, 33, 50, 115])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V227 : Known true K227 := extend_ok (m:=227) V174 low227 (by decide +kernel)

def g79Y : Array (Bits × Bits) := #[ (0x3bb7efecd42df5dd9179caef5967d2ff5fd58bb7a9d7e5b5d623a1fef654bc,0x4449111520921a02304085200b02558c60a050f301c7201517702024265424), (0x728c766e8612fb38efa83b8a56da65b57c81e5a6fa27b09b50fc7dc85c1f06,0xd7329d199ce20c530dc59a8fb8403a9c60efa05f74aa04150fd2d9c541f06), (0xbcee913c5549d7b2342c093fafa27c98d7c3ded9511b9dcb5b5cb21b0ac6e,0x74334ccd2e33628444805b2f4d4c9d26c49e1d6d0793f9dc0b9d2108b08c6e), (0xffdcdd19afeefaf54fbbf5c69b7daffbf2c2c7c17de87e66dfaaab09bbf78d89,0x2322e2c011014068412a32423424a220061e240488384cc8a80d0c98518988), (0x0,0x0), (0x0,0x0), (0xffff7ffff7bffffefa7eafbd77fef8fdedff3ffefe57b9bf6f7ddcfec709fb77,0xff8080000040008000820000000001004008010000000000020000c043082011), (0x0,0x0), (0x0,0x0) ]
def g79C : List ColumnInfo := [(4,0,75,0,5)]
set_option maxRecDepth 100000 in
def g79D5 (_ : Nat) : Nat := 0x5f
def g79L : Nat → Packing
  | 5 => (1,0,1,0,0,1,0,g79D5)
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
theorem g79G : graphValid g79 (boundsBefore K227) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 6 := lower_forest (g:=g79) (i:=0) (hints:=1635) (before_sound K227 V227) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K227 6 [(244,[64, 81, 66, 115, 84, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V227 low79 (by decide +kernel)

def g167Y : Array (Bits × Bits) := #[ (0x5d62aef1cb9a7d3f6dc8dfd8377094ec3cf67d20dbbef2a1ebac4bb48c,0x229d4106332281c1851368800e52d213aa30242aa8baca91a0a809b484), (0xfffffff93c3f4fcf69b467f325007f983efab2de77c3d33c2fbf9bb8028ceae1,0xffffff86c70111109603b911034ed01e61634691054706a0ba2990b80288aac1), (0x70e9db2cc1c847ffce7634ad4c62370c9dad898de9e46616a5b7d526d2,0xf1704d3e607a84e9976c5cab282d886b110ab0cadce66567108d526d0), (0x0,0x0), (0x0,0x0), (0xfffffffed7ef6dbff68f6bb7d59fb99bd9fcb1fdcd94f00fa6fddc7fdcfd01ed,0x1201680400150022828010140040c8004009090054410404014540128), (0x0,0x0), (0x3ffd7fbbf73f7bff7dff79f764bf3f4fb37afb3ff35943efa473b2ff12,0x4000880008400000400010200100000040400001520000080400224002), (0x0,0x0) ]
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
theorem g167G : graphValid g167 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (graphGoal 167) 6 := lower_forest (g:=g167) (i:=0) (hints:=1877) (before_sound K79 V79) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K79 6 [(167,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V79 low167 (by decide +kernel)

def g109Y : Array (Bits × Bits) := #[ (0xfffffffffcfd7ba9d7baffd6c2fbf7c789977cfafe97ccebf50acf35aae8c2cd,0xfffffffff300815a2041000814101261220210004000c009c00600158228800d), (0x0,0x0), (0x6eb569fe0b14cfd36d6403cd1bf3335fa5dfb042c26e1fbf0be3486,0x91411401f5d370215227a788d3494808e109b0f3a16e022a6ae3086), (0xfcfef6babff65613bbcbdf1377efed9b9bef75c53f95064e58d693a,0x3010045600805182822008c41000c2002430001118606004844122), (0x0,0x0), (0xbf39d1f0767ddd7edfea67b1e9d9950d3693ec7a3635b07bd46add4,0x40d60a0893022222021458400e9881598090cf60a21098031422cd0), (0xfffffffffb7cf7dc7b3fd6eb3e495f1ff573d3f7e66a9db4ccdfa5fa5a731633,0x4834820008048004048010410880819214a04300440098049510610), (0x0,0x0), (0x0,0x0) ]
def g109C : List ColumnInfo := [(32,0,77,0,5), (4,0,105,0,5), (0,4,41,64,5), (68,0,41,0,4), (8,0,101,0,4), (1,0,108,0,4)]
set_option maxRecDepth 100000 in
def g109D4 (_ : Nat) : Nat := 0x578d502
set_option maxRecDepth 100000 in
def g109H4 (_ : Nat) : Nat := 0x28
set_option maxRecDepth 100000 in
def g109D5 (_ : Nat) : Nat := 0x210808fd02
set_option maxRecDepth 100000 in
def g109H5 (_ : Nat) : Nat := 0x20
set_option maxRecDepth 100000 in
def g109D6 (_ : Nat) : Nat := 0x2c68819f
def g109L : Nat → Packing
  | 4 => (1,2,3,0,0,1,0,g109D4)
  | 5 => (1,1,3,0,0,1,0,g109D5)
  | 6 => (1,0,3,0,0,1,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 2 2 1 5 1 0 g109H4 h
  | 6, h => lookupWord 2 2 1 5 1 0 g109H5 h
  | _, _ => none
def g109 : Forest := ⟨109,6,fun i => g109Y[i]?.getD (0,0),g109C,[[]],g109L,g109I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g109P4_0 : block g109 4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g109B4 : block g109 4 0 1 = true := g109P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g109P5_0 : block g109 5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g109B5 : block g109 5 0 1 = true := g109P5_0
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
  · exact g109B4
  · exact g109B5
  · exact g109B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=1539) (before_sound K167 V167) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K167 7 [(109,[]),(173,[83, 118]),(185,[66, 83, 118]),(186,[16, 66, 67, 84, 101, 118]),(217,[66, 83, 117, 118]),(218,[16, 66, 67, 84, 117])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V167 low109 (by decide +kernel)

def g59Y : Array (Bits × Bits) := #[ (0xffffffdfc7f39ff376ae8ea19ca3ee67f7d5ff68f2fbe33f8d51a369d82dc967,0xffffffa03008e00509d020609640030898349019131241a6a110804108284945), (0xfffffffea4f6350beff7f73ab1fdddbf0db9f05f994c9dbab2ed9d8b6f731f81,0x15911a08450080b8440200a03780c00590b02040a6a49800a4d231b00), (0x0,0x0), (0x767bfdf8b72cc7f7fdcf19f0c6fa37e7f83ceb734e4b8b5afc1a83fc3c,0x98502034ac408001600178c0560084a4420cc060848085aac04039438), (0xffffffa7dddcafa874f537172fac372d21bcfbdb443c7b97b62a8daf46ee8695,0xffffffd822c05153834244221b99249886f26c00202c3995013263b122cc8495), (0x6dfb9fe36fdffed95fdefacadadf5a7acfefb18c7d54def0f7abdc315a,0x1200600c100007100121006080078020200421801014a0201022d42002), (0x0,0x0), (0x0,0x0), (0x0,0x0) ]
def g59C : List ColumnInfo := [(16,0,43,0,5), (0,16,41,2,5), (18,0,41,0,4), (8,0,51,0,4), (1,0,58,0,4)]
set_option maxRecDepth 100000 in
def g59D4 (_ : Nat) : Nat := 0xc2f40a925b89504
set_option maxRecDepth 100000 in
def g59H4 (_ : Nat) : Nat := 0xef8
set_option maxRecDepth 100000 in
def g59D5 (_ : Nat) : Nat := 0x1009011008c1306c894280fe24fd24fe04fd04fd02
set_option maxRecDepth 100000 in
def g59H5 (_ : Nat) : Nat := 0xa04801389c6
set_option maxRecDepth 100000 in
def g59D6 (_ : Nat) : Nat := 0x468815f
def g59L : Nat → Packing
  | 4 => (2,2,3,0,0,3,0,g59D4)
  | 5 => (5,1,3,0,0,6,0,g59D5)
  | 6 => (1,0,3,0,0,1,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 2 3 1 5 1 0 g59H4 h
  | 6, h => lookupWord 2 6 1 7 3 0 g59H5 h
  | _, _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,[[]],g59L,g59I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59B4 : block g59 4 0 2 = true := g59P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59B5 : block g59 5 0 5 = true := g59P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59B6 : block g59 6 0 1 = true := g59P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=65603) (before_sound K109 V109) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K109 7 [(59,[]),(155,[16, 67, 101, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V109 low59 (by decide +kernel)

def g171Y : Array (Bits × Bits) := #[ (0x776efc6e87bf3fbfb3dcfdea86318cf0bec57f9ee5158aac5e4c,0x880023068408834800388804882c00086403414d20000a84640), (0x3b52dcfdb1f6c5c8e6692a9e73bed4efe38869e7965875eb2a32,0x44a9c1026a090814ba08d50641a226044148fb26560004aa2a22), (0x0,0x0), (0xffffffffffffadf7566c3ee1dc7ece5679efe44616d0f43cdf2428bcfba319e9,0xffffffffffffd208b185010f234828c0331835210514301aca092030e70318a9), (0x0,0x0), (0xfffffffffffffeeffbb7fde36ae5ffbbb2ed3fcab777097eacb6abeb435ec183,0x112000800101000040400400200084900040080008900448100), (0x0,0x0), (0xffffffffffffddd3efb6663fdf39cc38af57efb5ed2b778b60595da73791a63d,0xffffffffffffa20410419022274241502200004800322092000909049311001d), (0x0,0x0) ]
def g171C : List ColumnInfo := [(128,0,43,0,5), (1,0,170,0,5), (8,0,163,0,5), (2,0,169,0,5)]
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
theorem g171G : graphValid g171 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := lower_forest (g:=g171) (i:=0) (hints:=83) (before_sound K59 V59) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K59 7 [(171,[]),(179,[16, 67, 117]),(205,[33, 101]),(211,[16, 67, 101, 118]),(229,[33, 67, 100, 101, 118]),(230,[32, 33, 67, 100, 101, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V59 low171 (by decide +kernel)

def g119Y : Array (Bits × Bits) := #[ (0x7ddaa7bc88dfe32b29a872f879a7157bd6318dd53cd90d50cef62822b1df2a77,0x2ac3470409edc008018852806165156ad208cc0e14540070006e2820919f2224), (0x23e762a75d688cc0d5ef0c670f798faf8185672cfbe596ab3daffef919329308,0x1425021012d8890110200200a651928000046241001942800a84c6911021200), (0xfeae3a61aee79c5e1a55d388c5a2e72d684f5acbd3cbfdb41014af456787e4c0,0x56eaa660846f8cd89300038863a3ae27592f580bc1d934248055ae456387a0c0), (0x0,0x0), (0x5952401fd842cf6fdfded88e0d5289233e4a1d78e1b606619e25ac827a90f52f,0x84080b4efc521463c85c500e4400a0d37c4a895921b60246df05a0826a90e52f), (0xbeca47f2a6994dcf8a1f3f5f743e26b81577ca954c8853caaebe92fa64cb49c6,0x434001866100506aa052c4f841222900971209149a221828e109292644049c2), (0xc5b7bd4e7376b7363274e7ec92b1f244eeca3ce63653f8df67505105cf6467b3,0x8014000a601013066074804390100000041020d022024883650011000c604513), (0x0,0x0), (0x0,0x0) ]
def g119C : List ColumnInfo := [(16,0,103,0,5), (4,0,115,0,5), (32,0,87,0,5), (1,0,118,0,5), (0,4,51,64,5), (0,16,101,2,5), (68,0,51,0,4), (18,0,101,0,4)]
set_option maxRecDepth 100000 in
def g119D6 (_ : Nat) : Nat := 0x1f58d1043f
def g119L : Nat → Packing
  | 6 => (1,0,3,0,0,1,0,g119D6)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g119 : Forest := ⟨119,6,fun i => g119Y[i]?.getD (0,0),g119C,[[]],g119L,g119I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119B6 : block g119 6 0 1 = true := g119P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g119B6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 7 := lower_forest (g:=g119) (i:=0) (hints:=67141) (before_sound K171 V171) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K171 7 [(119,[]),(126,[48])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V171 low119 (by decide +kernel)

def g252Y : Array (Bits × Bits) := #[ (0x0,0x0), (0x0,0x0), (0x1b1aca7cbad97fb1750eb8fd46c4620d856de3964bf8ba2188acc18570ce7d4e,0x1328cb22adc16e01a01efc3424dc0089012ca0a64368a81108880105704e1d42), (0xda4d353be6a7a67ce2758f475ad568e258cc07eaf4675d55584dd373952999d8,0x10a60328180086a4280ca556529348aa080409aa40041454001d831391299808), (0x76ad756368111d52a0c433a263ae3de8c933deb787ee4bd1d24789cf2ffa8110,0xbf1c98369451b158145b224636eb5a9c3b156a20ec26b57904709cf2fea0110), (0xf5190792af3dc72989354b21f151a275123bf3c16377cf547f6a7ee4922e2750,0x825958136535090191734801ad60a6452323e24021720100de427ce402062550), (0x9ecffb6dae5a281e5343165f19846ddfa6b764deffd086eabcd531902f836cb3,0x84010000218001a516102018800345422924010bc820222900230800e8060b0), (0xa5b3e4be71a1d1c32e8cf9eaa72a97366b76f923348935ab37bbae0f4a55922d,0x4062400000000c00a0001ca000100000040090900010480203082000011820d), (0x0,0x0) ]
def g252C : List ColumnInfo := [(16,0,236,0,6), (32,0,220,0,6), (8,0,244,0,6), (48,0,204,0,5), (4,0,248,0,5), (64,0,188,0,5), (0,16,108,128,5), (144,0,108,0,4), (80,0,172,0,4), (68,0,184,0,4), (128,16,108,0,4)]
set_option maxRecDepth 100000 in
def g252D4 (_ : Nat) : Nat := 0x930c09d40ea344b6351e254d26a33a2a9a7154545534
set_option maxRecDepth 100000 in
def g252H4 (_ : Nat) : Nat := 0x151872000000
set_option maxRecDepth 100000 in
def g252D5 (_ : Nat) : Nat := 0xa043c820140400274884f181e3030300be81945bb51a25bb41a25f58d915dd51515f349934f585934e755134f389534f545534
set_option maxRecDepth 100000 in
def g252H5 (_ : Nat) : Nat := 0x3bb41b70000069126ab0f4e1803023
set_option maxRecDepth 100000 in
def g252D6 (_ : Nat) : Nat := 0xa310021cd2880551c5180aa3003496920c06520e62ca20214939aa494404ec5ccd42b099807f517dc4bf515fe82f74d3da49ed02
set_option maxRecDepth 100000 in
def g252H6 (_ : Nat) : Nat := 0x185dadec62200f430
set_option maxRecDepth 100000 in
def g252D7 (_ : Nat) : Nat := 0x12ea84203bf
def g252L : Nat → Packing
  | 4 => (4,3,4,0,0,5,0,g252D4)
  | 5 => (10,2,4,0,0,7,0,g252D5)
  | 6 => (7,1,4,0,0,8,0,g252D6)
  | 7 => (1,0,4,0,0,1,0,g252D7)
  | _ => emptyPacking
def g252I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 4 7 1 6 2 0 g252H4 h
  | 6, h => lookupWord 5 13 3 8 4 0 g252H5 h
  | 7, h => lookupWord 3 9 3 7 3 0 g252H6 h
  | _, _ => none
def g252 : Forest := ⟨252,7,fun i => g252Y[i]?.getD (0,0),g252C,[[]],g252L,g252I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g252P4_0 : block g252 4 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g252B4 : block g252 4 0 4 = true := g252P4_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g252P5_0 : block g252 5 0 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g252B5 : block g252 5 0 10 = true := g252P5_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g252P6_0 : block g252 6 0 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g252B6 : block g252 6 0 7 = true := g252P6_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g252P7_0 : block g252 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g252B7 : block g252 7 0 1 = true := g252P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g252T : checkedTables g252 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g252B4
  · exact g252B5
  · exact g252B6
  · exact g252B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g252G : graphValid g252 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low252 : Lower true (varsX 252) (graphGoal 252) 8 := lower_forest (g:=g252) (i:=0) (hints:=574051840) (before_sound K119 V119) g252G g252T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K252 := extendKnown K119 8 [(252,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V252 : Known true K252 := extend_ok (m:=252) V119 low252 (by decide +kernel)

def g238Y : Array (Bits × Bits) := #[ (0x0,0x0), (0xceccd6932edee26b2afa8d3d617c193196062d04683ae3fd51ae3c9667199642,0x108981854304075860838c00230c1931800e2505603ba20a0906089645111240), (0x247a211aa9347753b46f6d4477aef3f220754ed9208d8864ebf482dc0dc9091d,0x20408ba31006445164273d041302815100244da524b591606be682d40dc90908), (0x9283b276bb4d6c08d3d65c8294da17e0ceaa1177df91acfa6c34c3fa94a05720,0x9201011939d80ce573c4c80081d81328c49af1a7249308a2493c81da94801720), (0x0,0x0), (0x629dbef6b0cfee9aa9849376ecc2d91eb2201646ffe09fe72ec51633833c292b,0x1642200800360020800314e4402c000134002400b441545200146210228280b), (0xf73e5500ce2288dcfe2c0fea8f07cff0fdcfb0a918146414d053e9455662ca91,0xc001400000110008008006a0c0004803140000819404015000040010220c091), (0x3dd76c995b1ddfe716d36ad79879a60f1197cf1a02cb5a08372d8c89b88734cc,0x801200500c708080035002908060020a401180100000080014080008b0060404), (0x0,0x0) ]
def g238C : List ColumnInfo := [(8,0,230,0,7)]
set_option maxRecDepth 100000 in
def g238D7 (_ : Nat) : Nat := 0xbf
def g238L : Nat → Packing
  | 7 => (1,0,1,0,0,1,0,g238D7)
  | _ => emptyPacking
def g238I : Nat → Nat → Option (Nat × Nat)

  | _, _ => none
def g238 : Forest := ⟨238,7,fun i => g238Y[i]?.getD (0,0),g238C,[[]],g238L,g238I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g238P7_0 : block g238 7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g238B7 : block g238 7 0 1 = true := g238P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g238T : checkedTables g238 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g238B7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g238G : graphValid g238 (boundsBefore K252) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low238 : Lower true (varsX 238) (graphGoal 238) 8 := lower_forest (g:=g238) (i:=0) (hints:=286283344) (before_sound K252 V252) g238G g238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K238 := extendKnown K252 8 [(238,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V238 : Known true K238 := extend_ok (m:=238) V252 low238 (by decide +kernel)

def g237Y : Array (Bits × Bits) := #[ (0x71e55dfe34b5cfcdbe83ce7188afc501eac07d8ad3e2947993e99048c269658a,0x1880243085029010020001882a000420004c8842a200018020044842090082), (0x0,0x0), (0x6ed0f755eaccd264eb6f362f3541105433d55ce53caf313a387e5cdc598acb10,0x7a978020038982099a816225ab03101401804ec8351910221a786cdc5908c900), (0x19972fae162af7d87a7219cc639db82354b0d8faef9c3b941543a0a67014a30f,0x920323080008c12c601831002311c22b508010128d0029123002e0061014a30c), (0x0,0x0), (0x7ea2b9bbcc8c02d3481a62bd6ce1016a147f2f524439beeccb10a3bc057050b5,0x400893080228418f040a9c00c00910057d22400010506c439400b005605011), (0xa15be2c0fbdff16104353b11379aba978a7f81e510424b479cb70a13242f8c51,0x40081180003442040088900480090002568124004042044085000124220411), (0xcf28550fff99fb8efdf995568160c6caa58ee615ae45e1b56438df419f941268,0x100570044604004002800400010c26ac00000010004a1902400920080940268), (0x0,0x0) ]
def g237C : List ColumnInfo := [(128,0,109,0,7), (64,0,173,0,7), (32,0,205,0,7), (8,0,229,0,7), (1,0,236,0,6), (4,0,233,0,6), (0,4,41,192,6)]
set_option maxRecDepth 100000 in
def g237D7 (_ : Nat) : Nat := 0x54ba981952ea606f03ec03f501
set_option maxRecDepth 100000 in
def g237H7 (_ : Nat) : Nat := 0xc80
set_option maxRecDepth 100000 in
def g237D8 (_ : Nat) : Nat := 0x358d103bf
def g237L : Nat → Packing
  | 7 => (2,1,3,0,0,5,0,g237D7)
  | 8 => (1,0,3,0,0,1,0,g237D8)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 8, h => lookupWord 2 3 1 5 1 0 g237H7 h
  | _, _ => none
def g237 : Forest := ⟨237,8,fun i => g237Y[i]?.getD (0,0),g237C,[[]],g237L,g237I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237B7 : block g237 7 0 2 = true := g237P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237B8 : block g237 8 0 1 = true := g237P8_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g237B7
  · exact g237B8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K238) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 9 := lower_forest (g:=g237) (i:=0) (hints:=1539) (before_sound K238 V238) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K238 9 [(237,[])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V238 low237 (by decide +kernel)

def g175Y : Array (Bits × Bits) := #[ (0xffc56f523be1fdf71d9c5c0a703e0837726b9b250d9d2df9dca746745228d98e,0x41a10c40216b81251d0c140e2034180250230a242404005c0c4040745200108e), (0x8f94c64f387162ad4fe7c245431073a21896eca4176bff6c6073f0c50e63253f,0x50846ea12c08f0b4a9c9424c4034598a0896eaa40349be4c105a00c40a23053f), (0x1ad39ca1d7cecea56b25ab8eb8cf940c84bd0ad235ac9f89da1eb805e09f979a,0x1b0dc7f066cb492d6365589e185c118c44d122e2b59c1fd0530ea805e08b979a), (0xceeb7622b1e555f099a57ff9daa84518293735efd9b66423d00bcf282bb1a5a8,0x8a4070ab50107a9080a06aa1c4080509ac847580d9720221f00b0f082831a520), (0x0,0x0), (0x533b3c3fccc64d2ec2bb27f3044936d239493edec6c1dbd20dee999b89c81c56,0x201080100204040a020201100001001000480048008041000324900181c80840), (0x0,0x0), (0x2c97c5f26f3ef20737528887efd7cf6fcf96d1d9732e100ca7152546f4176261,0x844210060000020000108021068206218100101108200000a001050204146000), (0x0,0x0) ]
def g175C : List ColumnInfo := [(2,0,173,0,7), (4,0,171,0,7), (1,0,174,0,6), (8,0,167,0,6), (0,4,43,128,6), (132,0,43,0,5), (9,0,166,0,5), (5,0,170,0,5), (12,0,163,0,5), (6,0,169,0,5), (32,0,143,0,5), (2,4,41,128,5), (128,4,43,0,5), (134,0,41,0,4), (36,0,139,0,4), (34,0,141,0,4), (3,0,172,0,4)]
set_option maxRecDepth 100000 in
def g175D4 (_ : Nat) : Nat := (0x30446080000001cb666c16aa4e9109e2d3c6090c0c02c54606451535b1908191454d6394221751a258e61859e258d38351535819248e61859e258123986167895048cd788da25412e89212650101b524841535406741e1404d501b515850135407c4551404d5019e24841e25406399a147895019e17850225407685d14089501 + (0x2 <<< 1024))
set_option maxRecDepth 100000 in
def g175H4 (_ : Nat) : Nat := 0x9b05430803e80e9068035d28558004a0a001b000c7000000021421c00c80
set_option maxRecDepth 100000 in
def g175D5 (_ : Nat) : Nat := (0x413671b44a825f107d1901bac6ea32037991d2640773a324c80df24754101be4aea0203f48dd40407f093a8080fe12650101be20fa2a03ec413454067b33a8a80df10751501f6208a2a03dc41545407e903a6a80f51054d501eaa8a9aa03f450135406f2b3c4a80de10789501bca8f12a03f850225406f333a4880fe10449101 + ((0x54e349dacf12c693d85d564d27d03aac9a65f6554d34d5aa903249b34d6064927b0baad0265d654d604e3a8a9ac093b59e25812d6a3c4b024de37559049ec2eab2093755e364136693c6c826ce3649904e720aaa209b38d9244126fb3a6a824dc674d504cbaca9aa09d6415354138ea2a6a824ed6789504bd20f12a096b51e25 + ((0x1c66e1aa6718e621825f1765a1625313e4e12a47106380d2330c62c0a225086180521303e0c02a0700e0026f1ba0da2cf50785945bac2ea326b7681d464d6ea8b88c9add90711935eac2ea2a6b5781d454d78fb228a9af1c6451535dcc2ea344b3985d468967703a8d12cee4741a25eb40e9aa0b97919354167b0baad1a65d65 + ((0x4040850400190100000000000000003101000000000080710100003040c1c40710100000023040092108841008c123041e1821009a380108c10002300084012c048c12c2342e110b01002c12504063042c16306deb62d2b32c6b02b2ab29ea428a9f2769c262972569424a9123e8e2328b2268821283206801fa7d1ee781d273 + (0x2301019016 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g175H5 (_ : Nat) : Nat := (0xc00084e0f5bf987cee0c0a300047356a410000035af1011191452c200000035d00000000000000f0400347006733c5b927b425e000004ae0000014a5b182e4cd1310cc3e8de45b11161edad900090bc1f4949550289c5519df73c0e4003c33428b5f228d53c369ec2153730a47e840007680863301422040a08d2300c0110800 + (0x150355838c156262262 <<< 1024))
set_option maxRecDepth 100000 in
def g175D6 (_ : Nat) : Nat := (0x1505d74d505bf55a34f754e34fb89634bf95934bf55934f754d34fb89534bb81924fb4d124bf55a04ef55204f74d604fb89604bf95904bf55904f78d904b78d904fb49904fe54104ef95104ef55104fb49104f74d504fb89504fd55901fdd1901fd51901f949901fc54101fc50101fdd1501fd51501f54d501f989501f949101 + ((0xacc576a8d492814d996f23a3d46686d051fcbec7a2ebdd139c6cad7da2337638c3d7a2d257ca8d40a6d4c09311520f3f6764e29a32ae464748c713c1b81f000bf4db45bf41b45bf8d945fd85945bd85945bf81945bf91935df51535f7d1935f791935f751935f711935f781935f741935d751535bb51a25bb41a25bf91905df5 + ((0x3930588880e01c008040071010b12086101080c0861018100203c2142c38031c1e301102c40a203101043a1a10220589043090c21ab122111221087a44684420b04c64a931c24300a20b0325460b08020806460b080196240484420b1202422ac4a8e16180325498e1218032c8c9526384860119bf2a64ec67862fede2b9d6e + (0x80c08604cc20039917086100800c2840218c0612442105480d0889112140205480d121403240689088192224220c0a0f0e014284038040a11101c02840210c0410c0a0e161c03040604008162410c202101810c202020040a08 <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g175H6 (_ : Nat) : Nat := 0x3ca00065a1106a1648fa9a9974008ac57950000a25bb9fce627ae1d9422654b868524c6e1a37e6b595800011dbcdc2d534a8c00003ede3c00b40acf0400c0f1e2cecc580076c9008541f00000ac06200000c4c6400024010c300432005a011c612a622
set_option maxRecDepth 100000 in
def g175D7 (_ : Nat) : Nat := (0x388284180030c1438a180698512388180730a1851030a106000b2861440e20a106000b2861430a106000938c2a61448e206028a1851030a106000a2861440c284180028c1c61448c20602501a58c28401f18b5aa69622e7f9b65b9323c0ae1b030003fe8bfd45ef9aff4d7ba6bee25fe82ff8d3fa69ed24ff027f413da05f501 + (0x30a1440c284180028c2851030a106000a3061438a180730a18510 <<< 1024))
set_option maxRecDepth 100000 in
def g175H7 (_ : Nat) : Nat := 0x397b2cc5b0826dc68016c0105f522900000903f
set_option maxRecDepth 100000 in
def g175D8 (_ : Nat) : Nat := 0x18a3104033f
def g175L : Nat → Packing
  | 4 => (17,4,5,0,0,7,0,g175D4)
  | 5 => (70,3,5,0,0,10,0,g175D5)
  | 6 => (55,2,5,0,0,11,0,g175D6)
  | 7 => (14,1,5,0,0,10,0,g175D7)
  | 8 => (1,0,5,0,0,1,0,g175D8)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 5, h => lookupWord 9 24 3 9 5 0 g175H4 h
  | 6, h => lookupWord 28 87 5 11 7 0 g175H5 h
  | 7, h => lookupWord 22 68 5 10 6 0 g175H6 h
  | 8, h => lookupWord 6 18 3 8 4 0 g175H7 h
  | _, _ => none
def g175 : Forest := ⟨175,8,fun i => g175Y[i]?.getD (0,0),g175C,[[]],g175L,g175I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P4_0 : block g175 4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P4_16 : block g175 4 16 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175B4 : block g175 4 0 17 = true := (@block_merge g175 4 0 16 1 g175P4_0 g175P4_16)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P5_0 : block g175 5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P5_16 : block g175 5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P5_32 : block g175 5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P5_48 : block g175 5 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P5_64 : block g175 5 64 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175B5 : block g175 5 0 70 = true := (@block_merge g175 5 0 64 6 (@block_merge g175 5 0 32 32 (@block_merge g175 5 0 16 16 g175P5_0 g175P5_16) (@block_merge g175 5 32 16 16 g175P5_32 g175P5_48)) g175P5_64)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : block g175 6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P6_16 : block g175 6 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P6_32 : block g175 6 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P6_48 : block g175 6 48 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175B6 : block g175 6 0 55 = true := (@block_merge g175 6 0 32 23 (@block_merge g175 6 0 16 16 g175P6_0 g175P6_16) (@block_merge g175 6 32 16 7 g175P6_32 g175P6_48))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175B7 : block g175 7 0 14 = true := g175P7_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175P8_0 : block g175 8 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175B8 : block g175 8 0 1 = true := g175P8_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g175B4
  · exact g175B5
  · exact g175B6
  · exact g175B7
  · exact g175B8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 9 := lower_forest (g:=g175) (i:=0) (hints:=1875) (before_sound K237 V237) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K237 9 [(222,[64, 65, 66, 67, 101, 118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V237 low175 (by decide +kernel)

def g187Y : Array (Bits × Bits) := #[ (0x194fb6dd51625ade9c83bd950b7ac45935e04d7bc6177042a871b672023ce44e,0x1646223f003242232001849501120e5820700040060c700029410020023c4446), (0xf3e7cf271fadf56f4c6966fcf94d1bd0a685c3a23b2a6a35c75c214dca2208e7,0x500158ab208a1a430100608490080850a6640164030800254118a044c2220087), (0x0,0x0), (0x6a4fbcdfd375af0a63bcab42aab0f164eba21fae86d0329f6ee2a2e610453ba3,0x8830d4400b800dc0811c4300a820b12041822b2ea1900203540ee6c6104138a1), (0xdaf55700f79c975f799796b06cd4be1628142eb099f78c3d607759a5a0a93578,0x823682101710801c66e910310870162e08189e9010329858206651a120892568), (0x34b06a75971b61a1d63649df955715a15f0edd5516c089d9158319101fdb0309,0x200000009000001446a20868044400030008d41010400058008001100c800308), (0x0,0x0), (0xf51c2a6beeafdc12e349110cf48be55fd059221a70bdc7a8fa8a6e8865c0dc94,0x800010040450000801001006081c100100220022081008292000e0801409810), (0x0,0x0) ]
def g187C : List ColumnInfo := [(2,0,185,0,7), (1,0,186,0,7), (128,0,59,0,7), (32,0,155,0,7), (16,0,171,0,7), (8,0,179,0,7), (0,8,146,33,6), (0,16,41,130,6), (144,0,43,0,5), (40,0,147,0,5), (17,0,170,0,5), (10,0,177,0,5), (24,0,163,0,5), (18,0,169,0,5), (9,0,178,0,5), (1,8,146,32,5), (2,16,41,128,5), (32,8,146,1,5), (128,16,41,2,5), (146,0,41,0,4), (41,0,146,0,4), (26,0,161,0,4), (25,0,162,0,4), (136,0,51,0,4), (129,0,58,0,4), (48,0,139,0,4), (34,0,153,0,4), (3,0,184,0,4), (33,8,146,0,4), (130,16,41,0,4)]
set_option maxRecDepth 100000 in
def g187D5 (_ : Nat) : Nat := 0x60800000204360d7a32e2bf60a921e1e03c68214541534e351581954453c98614549514b3a1841554413338de2645504e3904595454078d4516551501e396441545407cc4510551501e356445545407cc4111551501
set_option maxRecDepth 100000 in
def g187H5 (_ : Nat) : Nat := 0x1a328035402dc02440388818d1ae7505043
set_option maxRecDepth 100000 in
def g187D6 (_ : Nat) : Nat := (0x4067eabc8c80cfe5751901bf48ea8203be919504077ca32a080efa5650101df2aca0203bd919514077aa32a280ff14054501becaea0a03bd959414077aab28280ff150505019fccea2a033f59d45406fc83a8a80df51751501d7ac8a2a03ee41145407da8a28a80e7d6551501ef20aa2a03dd45545407b482a4a80f95144d101 + ((0x95914bec2eab229bd85d564527f03aac8a4fd5781914dec0ca8a29ed85d544539a8aaa88a6be0655114f3c0e9a229e74193445396a2a4a8a73d4541514df40eab2093f85d5641276abc4c825fa1754104f740eaa209ce41554413771326a825de3745504e7a8a8aa09bb89915412f713a0889dde37455029fa8f2b2033f91d56 + ((0x51a16497b70ba8a92f6d1751525edc2ca2a4b3751e36457bb0ba8a8acfd1791905bf40ea320b3f51e16417bd03a8a82e7e1651505edc2e92a0bdb459254167eabc0c9a4fd1781934dbaa703269af552064d2eeabc0c9a5dd1781934dbaad03269e781d544d3ce83aa89a79e0655134e1a8a92a69c7515054d2ef1ba2a924fd07 + ((0x18bbcb80aa4a18a0c9e09b497896c96095493889c8808447f876c7607247186dc6d06a46085fc5e05d45b85ac5a057454851c4f04d44b848c47045443841c3f03d43b838c3603543082cc29026423821c1f01d41a80dc0013f41e165167e8bc0ca2cfd47859259fa0f0b24bbb50a164973ea2c2c92ded4785925bda0f0b24bbb + ((0x40e0810302843808e023804101820608102040b2d2043a08e823a0610e8e0400383028208384a0018e920086380410e0d843808e81843a08e8d8438302e261f8f4c4bc804838060e8e0d0c8a0853e3729201e0a01b03900d000fe4fd8facfa0f74f58f1cec0e84e48e1cdf0dc4db8d9cd80d44cf8ceccd0cc4c98c8cc70c54c + ((0x2189893230080008200e508403002c008e01b086382822cac228e0c91063a3823a15f8f4d4b888645c3c068e8c8963d30191509000302843a0010e89800600000182278f4ecc064404800048e0233808018a08b2b088382e238f4c8605804003828001800d86c4180380610a63d33301910120809206282052020000c0a10382 + (0x302840e08100000803b40100c240130823a04c018e898932300a3a2e46183b1e1063a04103820438001000408e822f828 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g187H6 (_ : Nat) : Nat := (0x8f2c006ba23b62400000c5b735c7bb8286708004109a0f1823ed43534579780076f0af88d13649484dde0c001e7800000000001a0000730606c5000d9e88ac468621aa51da8d6faa90753187001ac69c9aca173305a19750aacf119bee5da3a6771f1a6a5812c9c824b4840400f12c62c00401781c30840000673447580c00c0 + (0x4b0900a6581d271948fc005020008ca1511af902a29e24956d86c002c5c090f6e8aa088 <<< 1024))
set_option maxRecDepth 100000 in
def g187D7 (_ : Nat) : Nat := (0x1534ff4d524ff45524bf95914ff55914bf55914bf81914ff41914fd54514ef55114e74d114fbc9514fb49514ff41514bf55904bb89904fe54104ef55104ff4d504ff45504ff41113ff45502bf95901ff55901bf55901bf91901ff51901bf51901fe54101fe50101fd54501fd50501ff51501fbc9501fb49501f7cd101f74d101 + ((0x3979b54d4a6522ff9774b5a5922bb943c9b04772078f606ee30f15709343ca1ae0a6835c0fa000ff85945bf85945ff45945ff81945bf81945ff41945bf85925fb85925db51525b78d915df51515bf91905ff51905bf85905ff45905df51505db49505f3c9734f349734f741734bf81934f781934e755134f3c9534f349534f74 + ((0x4460e0810071d386c18202007284e8474a1724486881418069c2e4e80f8e98325c9121a205060204e7c6cb15204460e1418061d3864a109e9c3c6cb15223070a0c0465eb29492ec8d23a719c896c3320e50427f7be39eaeeef75c39cdc24ddb6c7b4d598cc65605aefd6bcaef56a2ac94a2a1a4e025612428ce444a0a0f9c75f + ((0x4096203c50821427152010030d0e9431c1920674d93a01c305080d141030001c6cc1320911021ce9b304e8070c14203450601a70d949e1c305088c141030001c6cd141e951831ce1b34527870c14223050601a74d98263e3a74b91102030001c70d941e9e325c88c1818000d3a6c9908e9b2a4440a0810069c3668a108c9b2a + ((0x689d00e1828486880c030e1a28bc3860a12182420600038d9a28452a10239d344c8474d0c1a20400b34463a706881400049d34c88904f95204078b0c034e94a11d285890d1028300c3a70b91a11d3064b121a2050601e74e1a300400c70c149e1c305090d14100606c90f141c031c30507c74d0c1a20404b38508cf8e981a205 + ((0x2696243458700e709af4c962434587014709af4c96204860d1214061c32517c70c162430609081c000f3864a2f8e992c486890e04069d2446847cb10203458701874a508e96243458701474e11a0be3a64b121a2c380d3a70c925f1c3a64b12183448501e203860c4860a9043a6a8070c1424344080c00069d344c824440873a + ((0x85090e102420401a70c1422950811ce9726c03c68a101c205840a00079d2e4d8278d1522385850a034e12233e3450b91182c380c0f971c2c30063a4c9504f19183050001670c4f0e1828447081410200d3860a0f4a8c18e74c13601c305080e141028001c6cc1324910001cc128c99183050409270c12623d3250b931828380d + (0x3a0c1200029d601c305c8121c2040500034e9a26492200039c060908114e2f0e1b2 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g187H7 (_ : Nat) : Nat := 0x68001aa001a5c07b45541a49cc37ece4ddaa9ae24d0b2001cd39608badafee55f2407a5e3c2a3e0a4083fb2195ddff02b0f467ed7b1bd27cfbcc663baaa85cc0014d8000064ee9000b0000000000000000280129dd1111a28a6000001b98593b8000180078252230d2448c41114001042d
set_option maxRecDepth 100000 in
def g187D8 (_ : Nat) : Nat := (0x48d1c69451230e20a10403d240f2871a51448c38820600104503cb1c61641230e20a10404165513871859048c38820600106d03c71a51641230e208100fcd9832eb570a5130a3142c78cdf98f2be4b07c8c912c18c180007f517fa6bef25fe92fb497fa2bfd05ef9a7f4d3ba69fd24fe8a7f413fa47fd13fe81ff44bfa05fd01 + ((0x28602174913c71859048c30a106001071244f1859230a180b7534901c69459048c30a104041848f1c69459048c30818003d34651038a18086524501c694510388284180041d4914079440e28602d53c91c61641038828418003da4501c69459040e20a10403dc5113c71a51641038820600104503cc1c61448c3882841800415 + (0x124471a51641030a106000e5902071a51448c30a106000f5121648c <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g187H8 (_ : Nat) : Nat := 0x1b100718000776481468b60a1510e9d83a8dc8217db624000000001840b2000311
set_option maxRecDepth 100000 in
def g187D9 (_ : Nat) : Nat := 0x1483104033f
def g187L : Nat → Packing
  | 5 => (11,4,5,0,0,7,0,g187D5)
  | 6 => (87,3,5,0,0,12,0,g187D6)
  | 7 => (62,2,5,0,0,13,0,g187D7)
  | 8 => (19,1,5,0,0,11,0,g187D8)
  | 9 => (1,0,5,0,0,1,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6, h => lookupWord 6 15 3 8 4 0 g187H5 h
  | 7, h => lookupWord 29 103 6 11 7 0 g187H6 h
  | 8, h => lookupWord 25 78 5 10 6 0 g187H7 h
  | 9, h => lookupWord 9 25 4 9 5 0 g187H8 h
  | _, _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,[[]],g187L,g187I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187B5 : block g187 5 0 11 = true := g187P5_0
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
theorem g187P6_80 : block g187 6 80 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187B6 : block g187 6 0 87 = true := (@block_merge g187 6 0 64 23 (@block_merge g187 6 0 32 32 (@block_merge g187 6 0 16 16 g187P6_0 g187P6_16) (@block_merge g187 6 32 16 16 g187P6_32 g187P6_48)) (@block_merge g187 6 64 16 7 g187P6_64 g187P6_80))
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
theorem g187P7_48 : block g187 7 48 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187B7 : block g187 7 0 62 = true := (@block_merge g187 7 0 32 30 (@block_merge g187 7 0 16 16 g187P7_0 g187P7_16) (@block_merge g187 7 32 16 14 g187P7_32 g187P7_48))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187P8_16 : block g187 8 16 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187B8 : block g187 8 0 19 = true := (@block_merge g187 8 0 16 3 g187P8_0 g187P8_16)
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
  · rfl
  · exact g187B5
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=65603) (before_sound K175 V175) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K175 10 [(187,[]),(219,[101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V175 low187 (by decide +kernel)

def g255Y : Array (Bits × Bits) := #[ (0x2bc1c00410829c4d70de58969001c89905018b02d0496d9cb708566450c007a0,0x301006010808804509a1006130040190000810280482d98b300566000c00480), (0x941028a4854fed9a023a51af315e0b24c3629ca4a6181a402a02786106629c39,0x100020a41006cd0a421a11a3350b020c03428804a61810400200706106628420), (0x51ed0361f91f57e9c801b2e508f81235dbc4710a9c400a5bc653b3b9c65982ac,0x406d0062d18f5f49d00086cd18586201c1c4710294400a5a8653b3b9465882ac), (0xa4b333994062c311a6060ad92c81370b86fe2a51015282061440001e4fefa4e1,0xa0943280410242138e0009580c81360286fe2a400012820604000016472f8021), (0xcd684885819d04d6b481cc4e2abc347670b1648499feab18718aa28c5908f80c,0xcd00cc01658800d130014c480ab430317cb1648019e6ab18710a828c5808780c), (0x1868e72336a162448168c5024c5c07b0700050415da1910b82798c48340e3a5a,0x868c503240120400060c400805401a05000500159a100010059880830003a5a), (0x6a179d99680210383713da41d1d6a2c2aa8f819028234461491c92828a106852,0x800c5112000202021414000800400002801009008214001480c000088006852), (0xcb0a24520a5ccb604fbd24704a26d8407150622a02a420b000a5413321254107,0x21000085000000c04000040008840000002280000002000a0000201050101), (0x0,0x0) ]
def g255C : List ColumnInfo := [(4,0,219,32,11), (32,0,219,4,11), (64,0,187,4,11), (1,0,222,32,10), (2,0,237,16,10), (16,0,237,2,10), (18,0,237,0,9), (0,4,59,192,9), (0,16,109,130,9), (8,0,230,17,9), (128,0,109,18,9), (3,0,252,0,8), (17,0,238,0,8), (0,8,150,97,8), (2,16,109,128,8), (5,0,218,32,8), (6,0,217,32,8), (9,0,230,16,8), (10,0,229,16,8), (12,0,211,32,8), (24,0,230,1,8), (128,4,59,64,8), (128,16,109,2,8), (144,0,109,2,8), (146,0,109,0,7), (25,0,230,0,7), (136,0,119,0,7), (129,0,126,0,7), (1,8,150,96,7), (130,16,109,0,7), (11,0,244,0,6), (5,8,146,96,6), (137,0,118,0,5), (154,0,101,0,4), (147,0,108,0,4)]
set_option maxRecDepth 100000 in
def g255D8 (_ : Nat) : Nat := (0x3f0bc1e018020568454d22c0b525c571203245d06c568448b52587719c571283f09c2f05c1e0180445aa3c8f22d4961dc6715c4a0fc270bc1704e4448fb1bc5b1183f0bc1e009c77860a72871bc4307a06800f76825184dd07f728293741d12f7a469074dd02f72469074dd02f72865074dd02e7241e184dd02adf969395e101 + (0x21622ec5b10c460c661f86e114 <<< 1024))
set_option maxRecDepth 100000 in
def g255H8 (_ : Nat) : Nat := 0x2900b1dc53003500fc00020
set_option maxRecDepth 100000 in
def g255D9 : Nat → Nat
  | 0 => (0xfed3941d12ef69ba0e897734dd0744afdaf281a25fcd7340d12ff2b8a06897fa4e57040bfd232b8205bea185c102de70c66e815fb8653740bbd20e9ba05fce194dd02ee483a6e816f38613740af5c928ba05fe97044d02dfe9caf080efb8e528407ff272b8203ff1704c501bfd04a6e80f7e41d37407fb4129ba03dd9074dd01 + ((0x4cc1e59d29591a07fe357184896039611a04b00027fa130c26f7dd0986137bef0ca109be77a25730de7fa331c20fbfd3846107aee9cc6e83f7f4613741fbb4129ba0fdde194dd07eee8c26e83cff8657840ef7c928ba07be6085c512de70466e895fb8253744b7dc109ba25fce094dd12fe684a6e896f38213744afdc7283a25 + ((0x60230d459270dc5c20110603e1707807870361a0a8469a8b059281449c3717088301f0b83c04cb51808c351649c3717088441f0b83c038381b0d054228b250289386e2e1107c2e0f010c9ae27f00178eb7c5a62c175aba93d2467d334a95ec9523b3131844bfcdebaeeb7263841af4cff634aee1620a564ce248514c7f53991a + ((0x7178883e1707007162228fa531b8ac4c1f0b8380401915c8e3e9448c3b168983e1707006071361b4ad48228f07d34954983d1a8b4441f0a85c1a0a015108803d1d48a381a09c3315825c55231087b29930703e198b844260d07c261705829080351508927088481901c4d86c3112090469a0b24c1a8b040220c07c2e0f0132d4 + ((0x1c0d95a2b118782d9287633158903e130b82c1c020140fc6cb11107d298dc56240f85c1c01a5888a3e9549637158983e1707008034b51588e3c1e4a2481d8c45621130603e110b8241c0261f0e06cb4560a8451e0fa692a9387e3717888301f0b838054b51588e3d1e4943b198ac4c1a0f84c2e0b0700887036560a8451f87e3 + ((0x2d454a24d24d0c62d9682a51c81289387c3717094321f0b8380402a51c81289387c37170943e17070069692a51081340f8622e100943e110b8241c0205a4a946204d251260f86a2e12094321f0a85c1a0e0134c0612b5148040954983a1a8a84a1f0a85c1a0a0121007c381b8a8461ecd64b210ec56240f84c2e0b07008050ba + ((0x145214aa4e1b8b8461f0b8380401a5a8a944204a2481f0c45c20118643e110b8241c0251828a40214aa4e1b8b45c24118643e150b834140245a8a945204943e198b844230f84c2e0b0700816a2a51481350f8662e1108c3e130b82c1c0211828a429586e2e1187c2e0e01006454a210269240f8622e10094321f0885c120e011 + (0x37178983e17078078602d1126a2c164962b12065070361a8b04591c6e2f1107c2e0f01807069170a849258cc56260d07c26170583c060201d0d8602d1145c2892c662b1307c26170583c0602458888461a0d630158804c180f8402e0807800044ad91856249008a241307c2c170703c0c01f18688429506e2c1187c2e0e00b8c <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 1 => 0x9b0d461221106d180b440230c07c20170403c000241a8c244234622d1088c321f0885c120f00808469311108c358c45621128643e110b8241e010110a048230de371789c3e170780c032220d058258c05620130603e100b8201e000101026a2c0d248268b4422010a0d0602c15268289209e
  | _ => 0
set_option maxRecDepth 100000 in
def g255H9 (_ : Nat) : Nat := 0x23516b052401a6ce9c2394d98a501a25fea585cea140095582b8800003e0770000000000303003c7ab79987b9d4a4d1c218c5a000003a6aac1fa114b0024086c49f3c0a64965042aee85ef00000009eb1004f
set_option maxRecDepth 100000 in
def g255D10 : Nat → Nat
  | 0 => (0x3fdd7384eff5e113fdd7344fff41d13bfd7880ff75ce03bfd7840ff75cd03ffe1740fff45d03bee0844bf95c512fcf3744bfb4dd12fcd3744bfb41d12fed0344afb86102fe97040bfb51d02fcf3740bfb4dd02fcd3740bfb45d02fed1340aff5e101bfd38406fb4a101ff970407fd5c501ff531407f7cdd01ffd37407f74dd01 + ((0x37bfd388def74e237bfd088deff86137bfe084dff79e137dde784dff786137fdd184dff782137fdd084def7ce037ddd730def7ce217bfd3885ef74e217bfd0885eef92117bdf3881eff4e207bdd3881f7f4de07ddd3781eff8e107ffd3841eff86107ffd1841ff7cdd07dfe3741fff4dd07dfd3741ff74dd07ddd3741eff5e21 + ((0x3588aca20c859a108828a04c7e99f407a89e4c77d9d407349c4c6f99b3869e99dc64b9890602971c5a395e855e94f451593a84bc920445b90c84068f643ab8de03608d0c3258be02de8ad428d89d025488a420d87601ba863c16384e011283e40d782d009281ac0298000bdf3891eff4e247bdd3891eff42247bed28cdff34a3 + ((0x44a442d28281b1514120c0f0b070111c12114d0b490906c545048303c2c1c0406054462d282924261b1616120f0a0b0607020131c5a1a181512114d0d8b0b4a0a490986c5854584048303c28242c18141c08040807068605444362d282a1b1616120f0a0b060702014ab9aa38a74a92ca2ba8309e0a70c997a5b093ca44c8f9a + ((0x118f4a87c6c5c483c2c18038716056463c3d29261c1d1b1515120c0f090b05060151c52118f0f4d4a49870746c545448303c242c141805488746c6244342d2824221b1416120f080b0407000151e12110d0b0a4986c5058483c202c101c000485644403c1e1b16120f0b0500c1b1815110b4a0a4986c5840403c2c1c04070605 + ((0x261c1e1b151610110f090b05060145190104d4a49870786c545840443c242c141804c7d62443d1b15120f0b060000c1b5615110f4a87c6c5c403c2c180003d5c56463c3d2925221c1d191711120c0f090b050601515118f4a4987c6c5c483c2c180347c71695854463c3d352925221c1f1b151711120c0f090b050601a1c5615 + ((0xa890946854544048303c28242c18141c08040596062444435282a24251a151510120c0f0a090b060507020101998511086c58443c2c180002c605448412a1c1b14130f0b060000e151251904a498786c584c3c2c1803968544a40413529261c1e1b151610130d0f090b05060161512904a8786c584c3c2c180316c5546404129 + (0x4c38343c282c181c08058716c6c624848463435282a24261a151610110c0f0a090b060507020101d14124a0908c6c505c4048303c202c101c00048685049282826231b161712120c0f0a0b060702014201a5856110d4a8908c6c505c40483c202c101c000546961584435282826231b161712120c0f0a0b060702016110d4a0 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | 1 => (0x507020101d1c1b1a16114d0a4909c6c5c48303c2c1c04468605854442826231b161712120f0a0b0607020141c1b16110a09c6c5c483c2c1c0344528261b141610130c0f080b04070001018114a0a0986c5858404c38343c282c181c0804c7470686048352a24221b1416130c0f080b0407000151c1a18120d4a0a0986c58584 + ((0x15201c1b1a96114d0d8a490948c545c44483c242c141c0405c6c62443628251b141510120c0f080b0407000131d1c1b1816910b8a4946c545440483c242c141c04054605854442926231b161712120f0a0b060702013181615114d0a4909c6c5c48303c2c1c0406c68605854443429242621231615171211120c0f0a090b06 + ((0xc1b15510d0a0986c50584044303c202c101c0004c5a4a282116130f0b0700a120a09c6c5c483c2c1c0286058544434292424231b141710120c0f080b0407000161816150d0a09c6c5c483c2c1c03460585445342924271b17120c0f0b07010181615110ac6c5c483c2c1c03262584436292424231b141710120c0f080b04070 + ((0x1a1816120d8a46c54544c343c242c141c04050706a6258462825231b151711110f090b050701014201a9896110d8a48c6c545c44443c242c141c04050484428271b17130f0b0700b1412110d09c6c5c4c3c2c1c0304428261b16130f0b0700a1a15120d0a490986c5058404c303c202c101c0005068543428261b16130f0b070 + ((0x1b17130f0b0700e1816150d0a890908c6c505c4044303c202c101c0005468604a46282a24251b141510130c0f080b0407000151c1a9896118a0a890908c6c505c4044303c202c101c0005c545048442825231b151711130d0f090b05070101414121109c6c5c4c3c2c1c0403068604a28251b1515130d0f090b0507010111d1c + (0x110a098685c4c3c2c1c02864545034292424221a141710130c0f080b0407000151a150d0a098685c4c3c2c1c030645544342824221a141710110c0f080b04070001415141312118a0907c6c5c4c3c2c1403c54504c484628251f1b17130f0b0500f1412110d0a0908c6c505c404c303c202c101c040005468605854342827 <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024)) <<< 1024))
  | _ => 0
set_option maxRecDepth 100000 in
def g255H10 (_ : Nat) : Nat := (0xc58d927dad4274d0f00013146064cc854400142060000a34003cf8005472b40000090b8451c0004660c80000fd2a00316000a5725900000b17c1c0053d691aefd21c3230ed3d0a2ad6d850dd6b947c41990717732c9d07489e4a24b1b80325d8ffd498ad3dc0b17a8d637516820000542c0882621ca00001038063000210002d + (0x1d06ce800c02000c6428e4400363c9 <<< 1024))
set_option maxRecDepth 100000 in
def g255D11 (_ : Nat) : Nat := (0x40a081800122a488070d14243850401664a911e1e345880e14100618244458a121a285080e1028206000468426163ea24a001db9c89a798a16c949d27107ce50c5caa08ac6b84a835c1f4003ff23ffd47ffe6ff7cdfff1bffd37fba6fff0dfff0bffd17ffc0fff41fff9a7fd34ffa09ff84ffe89ffe03ffa07fb44bf6817fd01 + ((0x814103000266cc1622284888d142c4080e10282060004cb1114244060b102430708141030002264b141a284880c16204860e10282060004cb1118284880c1620407081410300022445090d14284860e10282060003cc121a284868a14243070814103000225090a12223450b10203840a08180011324468a12223450b102038 + ((0xa2858812183840a081800133058a1222284c68b121c28300e3058a8d14244468a16204860e102820600050d182c34509111a2858812183840a0818001430585468b121c28300a2444509111a2858812183840a081800122a485090d14284860e102820600040c1214243450a12183840a081800103058a9114244468a1620407 + (0xc9528284880c16204860e102820600048c972c5050910182c4090c1c205040c0009942444509111 <<< 1024)) <<< 1024)) <<< 1024))
set_option maxRecDepth 100000 in
def g255H11 (_ : Nat) : Nat := 0x1a690302391f68a62284ed27adc649a100002068500025e9cdc5802c4a60f105b00
set_option maxRecDepth 100000 in
def g255D12 (_ : Nat) : Nat := 0x30a20610200eff
def g255L : Nat → Packing
  | 8 => (7,4,6,0,0,10,0,g255D8)
  | 9 => (46,3,6,0,0,13,0,g255D9)
  | 10 => (74,2,6,0,0,14,0,g255D10)
  | 11 => (22,1,6,0,0,12,0,g255D11)
  | 12 => (1,0,6,0,0,1,0,g255D12)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 9, h => lookupWord 7 13 1 7 3 0 g255H8 h
  | 10, h => lookupWord 18 57 5 10 6 0 g255H9 h
  | 11, h => lookupWord 28 91 5 11 7 0 g255H10 h
  | 12, h => lookupWord 8 26 4 9 5 0 g255H11 h
  | _, _ => none
def g255 : Forest := ⟨255,12,fun i => g255Y[i]?.getD (0,0),g255C,[[]],g255L,g255I⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B8 : block g255 8 0 7 = true := g255P8_0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_16 : block g255 9 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P9_32 : block g255 9 32 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B9 : block g255 9 0 46 = true := (@block_merge g255 9 0 32 14 (@block_merge g255 9 0 16 16 g255P9_0 g255P9_16) g255P9_32)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_16 : block g255 10 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_32 : block g255 10 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_48 : block g255 10 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P10_64 : block g255 10 64 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B10 : block g255 10 0 74 = true := (@block_merge g255 10 0 64 10 (@block_merge g255 10 0 32 32 (@block_merge g255 10 0 16 16 g255P10_0 g255P10_16) (@block_merge g255 10 32 16 16 g255P10_32 g255P10_48)) g255P10_64)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255P11_16 : block g255 11 16 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255B11 : block g255 11 0 22 = true := (@block_merge g255 11 0 16 6 g255P11_0 g255P11_16)
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
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (varsX 255) (graphGoal 255) 13 := lower_forest (g:=g255) (i:=0) (hints:=67139) (before_sound K187 V187) g255G g255T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def postedGraph : Sig := 0xfffffffffffffffffffffffffffffefefffefffefffefffeffeeffeeeeccaa00fffffffffffffffffffffffffffffefefffefffefffefffeffeeffeeeeccaa00
theorem postedGraphProper : proper postedGraph := by unfold proper; decide +kernel

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.or, [1, 7]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [0, 10]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.and, [14, 9]⟩,
    ⟨.and, [13, 12]⟩,
    ⟨.and, [11, 8]⟩,
    ⟨.and, [0, 10]⟩,
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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (([8, 16, 64, 1, 2, 1, 1, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((([8, 16, 64, 1, 2, 1, 1, 1] : List Nat).getD i.val 0) ||| (1 <<< i.val))

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

end PEqualNP.Outside.L_meta_31331

theorem PEqualNP.Outside.L_meta_31331 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_31331.replaceShort PEqualNP.Outside.L_meta_31331.excluded gates o fit correct
