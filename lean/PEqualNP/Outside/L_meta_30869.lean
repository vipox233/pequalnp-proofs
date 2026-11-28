import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30869_aux.Base
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

lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
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

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a

theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _

theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r

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

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none

def vars (m : Nat) := (selected m).map Prod.snd

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

abbrev Bits := BitVec 152

abbrev Signals := Bits × Bits

abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn

theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

def pairSig (r s : Fin 152 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)

def properPairs (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false

theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 152 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩

def faithful (r s : Fin 152 → Row) (x : Decor) := x.2 = pairSig r s x.1

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

def asRow (cols : Nat → Bits) (i : Fin 152) : Row :=
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

theorem asRow_bit (cols : Nat → Bits) (i : Fin 152) (j : Fin 9) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 152 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 152 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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

def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1

def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws

theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

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

def forestRecord (tab : Packing) (raw i : Nat) : Nat :=
  let (_,d,_,_,_,_,_,word) := tab
  let width := 10*d+raw+d
  packedAt word (i*width) width

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

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,_,_,ow,_,data) := tab
  let start := num*(10*d+raw+d)
  let pos := start+num*ow+packedAt data (start+i*ow) ow
  getPairs data cw d (packedAt data pos 6) (pos+6)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws

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

end PEqualNP.Outside.L_meta_30869_aux.Base

namespace PEqualNP.Outside.L_meta_30869_aux.Cert
open PEqualNP.Outside.L_meta_30869_aux.Base

def rulePool (raw : List Sig) (c : ColumnInfo) : BoundPool :=
  (subcube c.1 c.2.1, c.2.2.2.2, 0, raw)

def Matches (g : Forest) (T : Sig) : Prop :=
  properPairs T (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2)

def Rules (g : Forest) (T : Sig) : Prop :=
  ∀ c ∈ g.cols, Slice g.mode (vars g.mask) T (subcube c.1 c.2.1) c.2.2.2.2

def hintedRule (g : Forest) (k i : Nat) (h : Nat × Nat) : Option BoundPool :=
  match g.cols[h.1]? with
  | none => none
  | some c =>
    if h.2 = 0 then some (rulePool (vars g.mask) c) else
      let node := readNode g k i
      materialize g.mode (vars g.mask)
        (chosenSteps node.2.1 node.1 h.2 (g.levels k).2.1)
        (subcube c.1 c.2.1) c.2.2.2.2

theorem hintedRule_sound {g T k i h r} (cols : Rules g T)
    (he : hintedRule g k i h = some r) : ValidPool g.mode (vars g.mask) T r := by
  unfold hintedRule at he
  cases hc : g.cols[h.1]? with
  | none => simp [hc] at he
  | some c =>
    simp only [hc] at he
    split at he
    · cases he
      exact build_valid (cols c (List.mem_of_getElem? hc)) [] rfl
    · exact materialize_sound (cols c (List.mem_of_getElem? hc)) he

def nextState (g : Forest) (k tag : Nat) : Option (List Sig) := do
  let (j,_) ← g.index k tag
  if j < (g.levels (k-1)).1 then some (stateSet g (k-1) j) else none

def nodeCheck (g : Forest) (T : Sig) (k i : Nat) : Bool :=
  let ws := (readNode g k i).2.2
  let values := ws.map Prod.fst
  let raw := vars g.mask
  let rules := (forestHints (g.levels k) raw.length i).filterMap (hintedRule g k i)
  decide values.Nodup && !(values.contains T) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,fun tag => (nextState g k tag).toList) ws)

theorem nodeCheck_sound (g : Forest) (T : Sig) (k i : Nat)
    (pairs : Matches g T) (cols : Rules g T)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode T (k-1) (stateSet g (k-1) j).toFinset)
    (ok : nodeCheck g T k i = true) : Impossible g.mode T k (stateSet g k i).toFinset := by
  simp only [nodeCheck,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at ok
  have nd := ok.1.1
  have absent : T ∉ stateSet g k i := by simpa [stateSet] using ok.1.2
  by_cases hzero : k=0
  · subst k
    intro t lo h
    have eq : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hs,_⟩ := h
    exact absent (List.mem_toFinset.mp (by rw [he,hs]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) pairs _ nd absent _ _ (by simpa only [hzero,if_false] using ok.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro pool hp
    obtain ⟨_,_,he⟩ := List.mem_filterMap.mp hp
    exact hintedRule_sound cols he
  · intro tag xs hx
    have he : nextState g k tag = some xs := by simpa using hx
    unfold nextState at he
    cases idx : g.index k tag with
    | none => simp [idx] at he
    | some z =>
      rcases z with ⟨j,a⟩
      by_cases hj : j < (g.levels (k-1)).1
      · simp [idx,hj] at he
        subst xs
        exact prior (by omega) j hj
      · simp [idx,hj] at he

def checks (g : Forest) (T : Sig) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeCheck g T k (start+n) && checks g T k start n

theorem checks_at {g T k start n} (h : checks g T k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeCheck g T k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [checks,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem checks_merge {g T k start a b} (h : checks g T k start a=true)
    (h' : checks g T k (start+a) b=true) : checks g T k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [Nat.add_succ,checks,Bool.and_eq_true] at h' ⊢
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

theorem allRows {g T} (pairs : Matches g T) (cols : Rules g T)
    (checked : ∀ k ≤ g.cap, checks g T k 0 (g.levels k).1 = true) :
    ∀ k ≤ g.cap, ∀ i < (g.levels k).1, Impossible g.mode T k (stateSet g k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro hk i hi
    exact nodeCheck_sound g T 0 i pairs cols (by omega) (checks_at (checked 0 hk) i (by omega) (by omega))
  | succ k ih =>
    intro hk i hi
    exact nodeCheck_sound g T (k+1) i pairs cols (fun _ => by simpa using ih (by omega)) (checks_at (checked _ hk) i (by omega) (by omega))

theorem rootDone {g T}
    (pairs : Matches g T) (cols : Rules g T)
    (checked : ∀ k ≤ g.cap, checks g T k 0 (g.levels k).1 = true)
    (idx : indexedRoot g g.cap 0 (vars g.mask)=true) : Impossible g.mode T g.cap (vars g.mask).toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact allRows pairs cols checked _ (Nat.le_refl _) 0 idx.1

abbrev Claim := Sig × Forest × Nat

def essentialData (a : Claim) : List (Sig × Row × Row) :=
  (selected a.2.1.mask).map fun (i,w) =>
    let r := (a.2.2 >>> (7*i)) &&& 127
    (w,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def derivedZeros (a b : Claim) (c : ColumnInfo) :=
  c.1 ||| (a.2.1.mask ^^^ (a.2.1.mask &&& (b.2.1.mask ||| c.2.1)))

def ruleCheck (a b : Claim) (c : ColumnInfo) :=
  let ms := fixRows (derivedZeros a b c) c.2.1
  checkMap ms (vars a.2.1.mask) a.1 (vars b.2.1.mask) b.1 &&
    (movedWord ms (subcube c.1 c.2.1) == one) && properB b.1 &&
    (c.2.2.2.2 == b.2.1.cap+1)

def Solved (a : Claim) := Lower true (vars a.2.1.mask) a.1 (a.2.1.cap+1)

theorem ruleChecked {a b : Claim} {c : ColumnInfo} (prev : Solved b)
    (h : ruleCheck a b c = true) :
    Slice true (vars a.2.1.mask) a.1 (subcube c.1 c.2.1) c.2.2.2.2 := by
  simp only [ruleCheck,Bool.and_eq_true,beq_iff_eq] at h
  rw [h.2]
  exact slice_correct h.1.1.1 h.1.1.2 (proper_of _ h.1.2) prev

def localCheck (a : Claim) :=
  a.2.1.mode && properB a.1 && checkEssential a.1 (vars a.2.1.mask) (essentialData a) &&
  ((essentialData a).map Prod.fst == vars a.2.1.mask) &&
  indexedRoot a.2.1 a.2.1.cap 0 (vars a.2.1.mask)

def columnsCheck (book : Nat → Claim) (i : Nat) :=
  let a := book i
  a.2.1.cols.all fun c => decide (c.2.2.1 < i) && ruleCheck a (book c.2.2.1) c

def Resolved (a : Claim) :=
  Impossible true a.1 a.2.1.cap (vars a.2.1.mask).toFinset ∧ Solved a

set_option maxHeartbeats 2000000 in
theorem resolve {book : Nat → Claim} {i : Nat}
    (previous : ∀ j < i, Resolved (book j))
    (lc : localCheck (book i)=true) (pc : Matches (book i).2.1 (book i).1)
    (cc : columnsCheck book i=true)
    (rows : ∀ k ≤ (book i).2.1.cap, checks (book i).2.1 (book i).1 k 0 ((book i).2.1.levels k).1 = true) :
    Resolved (book i) := by
  let a := book i
  change localCheck a = true at lc
  simp only [localCheck,Bool.and_eq_true,beq_iff_eq] at lc
  have hm : a.2.1.mode = true := lc.1.1.1.1
  have cols : Rules a.2.1 a.1 := by
    intro c hc
    rw [hm]
    have h := List.all_eq_true.mp cc c hc
    simp only [Bool.and_eq_true,decide_eq_true_eq] at h
    exact ruleChecked (previous _ h.1).2 h.2
  have noRun := rootDone pc cols rows lc.2
  rw [hm] at noRun
  refine ⟨noRun,lower_impossible (proper_of _ lc.1.1.1.2) (essential_plain lc.1.1.2).1
    (essential_plain lc.1.1.2).2 ?_ noRun⟩
  intro v hv
  apply essential_ok lc.1.1.2 v
  rw [lc.1.2]
  exact List.mem_toFinset.mpr hv

theorem extendResults {book : Nat → Claim} {i : Nat}
    (prev : ∀ j < i, Resolved (book j)) (this : Resolved (book i)) :
    ∀ j < i+1, Resolved (book j) := by
  intro j hj
  by_cases h : j=i
  · exact h ▸ this
  · exact prev j (by omega)

def layers0 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x7 | _ => 0)⟩
  | _ => emptyPacking
def index0 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g0 : Forest := ⟨41,3,(fun | 0 => (0xffffffffffffffffffffffffffffffffffffcf,0xffffffffffffffffffffffffffffffffffffc5) | 3 => (0xfffffffffffffffffffffffffffffffffffff3,0x12) | 5 => (0x3c,0x28) | _ => (0,0)),[],[],layers0,index0⟩
def claim0 : Claim := (0xffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00ffaaffaaaa00aa00,g0,34361835528)

def layers1 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x7 | _ => 0)⟩
  | _ => emptyPacking
def index1 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g1 : Forest := ⟨42,3,(fun | 1 => (0xffffffffffffffffffffffffffffffffffffcf,0xffffffffffffffffffffffffffffffffffffc5) | 3 => (0xfffffffffffffffffffffffffffffffffffff3,0x12) | 5 => (0x3c,0x28) | _ => (0,0)),[],[],layers1,index1⟩
def claim1 : Claim := (0xffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00ffccffcccc00cc00,g1,68723672064)

def layers2 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x7 | _ => 0)⟩
  | _ => emptyPacking
def index2 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g2 : Forest := ⟨74,3,(fun | 1 => (0xffffffffffffffffffffffffffffffffffffcf,0xffffffffffffffffffffffffffffffffffffc5) | 3 => (0xfffffffffffffffffffffffffffffffffffff3,0x12) | 6 => (0x3c,0x28) | _ => (0,0)),[],[],layers2,index2⟩
def claim2 : Claim := (0xffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00ffccffccffccffcccc00cc00cc00cc00,g2,8796097217536)

def layers3 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x7 | _ => 0)⟩
  | _ => emptyPacking
def index3 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g3 : Forest := ⟨84,3,(fun | 2 => (0xffffffffffffffffffffffffffffffffffffcf,0xffffffffffffffffffffffffffffffffffffc5) | 4 => (0xfffffffffffffffffffffffffffffffffffff3,0x12) | 6 => (0x3c,0x28) | _ => (0,0)),[],[],layers3,index3⟩
def claim3 : Claim := (0xfffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000fffff0f0fffff0f0f0f00000f0f00000,g3,17593260048384)

def layers4 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xf | _ => 0)⟩
  | _ => emptyPacking
def index4 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g4 : Forest := ⟨51,3,(fun | 0 => (0xffffffffffffffffffffffffffffffffffff9f,0xffffffffffffffffffffffffffffffffffff8b) | 1 => (0x64,0x46) | 4 => (0xffffffffffffffffffffffffffffffffffffc7,0x44) | 5 => (0x78,0x30) | _ => (0,0)),[],[],layers4,index4⟩
def claim4 : Claim := (0xeeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000eeeeeeeeaaaa0000,g4,34628177936)

def layers5 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xf | _ => 0)⟩
  | _ => emptyPacking
def index5 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g5 : Forest := ⟨99,3,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffff9,0x30) | 1 => (0x1e,0xa) | 5 => (0xffffffffffffffffffffffffffffffffffffe7,0xffffffffffffffffffffffffffffffffffffc5) | 6 => (0x38,0xfffffffffffffffffffffffffffffffffffff1) | _ => (0,0)),[],[],layers5,index5⟩
def claim5 : Claim := (0xeeeeeeeecccccccceeeeeeee00000000eeeeeeeecccccccceeeeeeee00000000eeeeeeeecccccccceeeeeeee00000000eeeeeeeecccccccceeeeeeee00000000,g5,8830452764704)

def layers6 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xf | _ => 0)⟩
  | _ => emptyPacking
def index6 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g6 : Forest := ⟨29,3,(fun | 0 => (0xffffffffffffffffffffffffffffffffffff9f,0xffffffffffffffffffffffffffffffffffff8b) | 2 => (0x64,0x46) | 3 => (0xffffffffffffffffffffffffffffffffffffc7,0x44) | 4 => (0x78,0x30) | _ => (0,0)),[],[],layers6,index6⟩
def claim6 : Claim := (0xfafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00fafaaa00,g6,270794760)

def layers7 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xf | _ => 0)⟩
  | _ => emptyPacking
def index7 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g7 : Forest := ⟨53,3,(fun | 0 => (0xffffffffffffffffffffffffffffffffffffcb,0xffffffffffffffffffffffffffffffffffffc1) | 2 => (0x3c,0x18) | 4 => (0xfffffffffffffffffffffffffffffffffffff7,0x26) | 5 => (0x38,0x38) | _ => (0,0)),[],[],layers7,index7⟩
def claim7 : Claim := (0xfafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000fafaaaaafafa0000,g7,34628435984)

def layers8 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xf | _ => 0)⟩
  | _ => emptyPacking
def index8 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g8 : Forest := ⟨102,3,(fun | 1 => (0xffffffffffffffffffffffffffffffffffff9f,0xffffffffffffffffffffffffffffffffffff8b) | 2 => (0x64,0x46) | 5 => (0xffffffffffffffffffffffffffffffffffffc7,0x44) | 6 => (0x78,0x30) | _ => (0,0)),[],[],layers8,index8⟩
def claim8 : Claim := (0xfcfcfcfcfcfcfcfccccccccc00000000fcfcfcfcfcfcfcfccccccccc00000000fcfcfcfcfcfcfcfccccccccc00000000fcfcfcfcfcfcfcfccccccccc00000000,g8,8864813551616)

def layers9 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index9 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g9 : Forest := ⟨57,4,(fun | 0 => (0xffffffffffffffffffffffffffffffffffff3f,0xffffffffffffffffffffffffffffffffffff15) | 3 => (0xffffffffffffffffffffffffffffffffffffc3,0x42) | 4 => (0xcc,0xc8) | 5 => (0xf0,0xa0) | _ => (0,0)),[(16,0,0,0,4)],[],layers9,index9⟩
def claim9 : Claim := (0xffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00ffaaffaaaaaaaa00,g9,34630270984)

def layers10 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index10 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g10 : Forest := ⟨105,4,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffff1,0x30) | 3 => (0xffffffffffffffffffffffffffffffffffff9f,0xffffffffffffffffffffffffffffffffffff8b) | 5 => (0x66,0x44) | 6 => (0x78,0x70) | _ => (0,0)),[(64,0,0,0,4)],[],layers10,index10⟩
def claim10 : Claim := (0xffaaffaaff00ff00ffaaffaaaa00aa00ffaaffaaff00ff00ffaaffaaaa00aa00ffaaffaaff00ff00ffaaffaaaa00aa00ffaaffaaff00ff00ffaaffaaaa00aa00,g10,35218733924360)

def layers11 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index11 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g11 : Forest := ⟨75,4,(fun | 0 => (0xffffffffffffffffffffffffffffffffffffd9,0x58) | 1 => (0x1e,0xa) | 3 => (0xffffffffffffffffffffffffffffffffffffe7,0xffffffffffffffffffffffffffffffffffffa5) | 6 => (0x78,0x50) | _ => (0,0)),[(1,0,2,0,4)],[],layers11,index11⟩
def claim11 : Claim := (0xffccffccffccffccee00ee00ee00ee00ffccffccffccffccee00ee00ee00ee00ffccffccffccffccee00ee00ee00ee00ffccffccffccffccee00ee00ee00ee00,g11,8796095120392)

def layers12 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index12 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g12 : Forest := ⟨43,4,(fun | 0 => (0xffffffffffffffffffffffffffffffffffff2d,0x24) | 1 => (0x36,0x24) | 3 => (0xffffffffffffffffffffffffffffffffffffc7,0xffffffffffffffffffffffffffffffffffff43) | 5 => (0xf8,0x98) | _ => (0,0)),[(1,0,1,0,4)],[],layers12,index12⟩
def claim12 : Claim := (0xffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00ffeeffeeee00ee00,g12,34361836552)

def layers13 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index13 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g13 : Forest := ⟨43,4,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffe13,0x0) | 1 => (0xfffffffffffffffffffffffffffffffffffe6d,0xfffffffffffffffffffffffffffffffffffe25) | 3 => (0x18e,0x8a) | 5 => (0x1f0,0x150) | _ => (0,0)),[(1,0,1,0,4)],[],layers13,index13⟩
def claim13 : Claim := (0xffeeffeeeeaaeeaaffeeffeeeeaaeeaaffeeffeeeeaaeeaaffeeffeeeeaaeeaaffeeffeeeeaaeeaaffeeffeeeeaaeeaaffeeffeeeeaaeeaaffeeffeeeeaaeeaa,g13,68723672064)

def layers14 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xf | _ => 0)⟩
  | _ => emptyPacking
def index14 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g14 : Forest := ⟨77,3,(fun | 0 => (0xffffffffffffffffffffffffffffffffffffcf,0xa) | 2 => (0xe,0xe) | 3 => (0xfffffffffffffffffffffffffffffffffffff7,0xffffffffffffffffffffffffffffffffffffd5) | 6 => (0x38,0x20) | _ => (0,0)),[],[],layers14,index14⟩
def claim14 : Claim := (0xfff0fff0fff0fff0aa00aa00aa00aa00fff0fff0fff0fff0aa00aa00aa00aa00fff0fff0fff0fff0aa00aa00aa00aa00fff0fff0fff0fff0aa00aa00aa00aa00,g14,17592189190152)

def layers15 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xf | _ => 0)⟩
  | _ => emptyPacking
def index15 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨108,3,(fun | 2 => (0x26,0x26) | 3 => (0xffffffffffffffffffffffffffffffffffffdf,0xffffffffffffffffffffffffffffffffffffcb) | 5 => (0xffffffffffffffffffffffffffffffffffffe7,0x24) | 6 => (0x38,0x10) | _ => (0,0)),[],[],layers15,index15⟩
def claim15 : Claim := (0xfff0fff0fff0fff0ff00ff0000000000fff0fff0fff0fff0ff00ff0000000000fff0fff0fff0fff0ff00ff0000000000fff0fff0fff0fff0ff00ff0000000000,g15,17867132108800)

def layers16 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index16 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g16 : Forest := ⟨46,4,(fun | 1 => (0xfffffffffffffffffffffffffffffffffffe37,0xfffffffffffffffffffffffffffffffffffe13) | 2 => (0xfffffffffffffffffffffffffffffffffffe49,0x0) | 3 => (0x18e,0x8c) | 5 => (0x1f0,0x160) | _ => (0,0)),[(4,0,1,0,4)],[],layers16,index16⟩
def claim16 : Claim := (0xfffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0fffcfffcfcf0fcf0,g16,68723672064)

def layers17 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index17 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g17 : Forest := ⟨78,4,(fun | 1 => (0xffffffffffffffffffffffffffffffffffff0f,0xffffffffffffffffffffffffffffffffffff05) | 2 => (0xffffffffffffffffffffffffffffffffffff33,0xffffffffffffffffffffffffffffffffffff13) | 3 => (0xffffffffffffffffffffffffffffffffffffc3,0x42) | 6 => (0xfc,0xa8) | _ => (0,0)),[(4,0,2,0,4)],[],layers17,index17⟩
def claim17 : Claim := (0xfffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00fffcfffcfffcfffccc00cc00cc00cc00,g17,8796098266112)

def layers18 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xf | _ => 0)⟩
  | _ => emptyPacking
def index18 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g18 : Forest := ⟨113,3,(fun | 0 => (0xffffffffffffffffffffffffffffffffffff8f,0xffffffffffffffffffffffffffffffffffff81) | 4 => (0xfffffffffffffffffffffffffffffffffffff3,0x32) | 5 => (0x6c,0x6c) | 6 => (0x70,0x48) | _ => (0,0)),[],[],layers18,index18⟩
def claim18 : Claim := (0xffffaaaaffff0000aaaaaaaaaaaa0000ffffaaaaffff0000aaaaaaaaaaaa0000ffffaaaaffff0000aaaaaaaaaaaa0000ffffaaaaffff0000aaaaaaaaaaaa0000,g18,70403372351504)

def layers19 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xf | _ => 0)⟩
  | _ => emptyPacking
def index19 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g19 : Forest := ⟨83,3,(fun | 0 => (0xffffffffffffffffffffffffffffffffffffcf,0xa) | 1 => (0xe,0xe) | 4 => (0xfffffffffffffffffffffffffffffffffffff7,0xffffffffffffffffffffffffffffffffffffd5) | 6 => (0x38,0x20) | _ => (0,0)),[],[],layers19,index19⟩
def claim19 : Claim := (0xffffccccffffccccaaaa0000aaaa0000ffffccccffffccccaaaa0000aaaa0000ffffccccffffccccaaaa0000aaaa0000ffffccccffffccccaaaa0000aaaa0000,g19,8796361465872)

def layers20 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xf | _ => 0)⟩
  | _ => emptyPacking
def index20 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g20 : Forest := ⟨114,3,(fun | 1 => (0xffffffffffffffffffffffffffffffffffff9f,0xffffffffffffffffffffffffffffffffffff8b) | 4 => (0x64,0x46) | 5 => (0xffffffffffffffffffffffffffffffffffffc7,0x44) | 6 => (0x78,0x30) | _ => (0,0)),[],[],layers20,index20⟩
def claim20 : Claim := (0xffffccccffffcccccccccccc00000000ffffccccffffcccccccccccc00000000ffffccccffffcccccccccccc00000000ffffccccffffcccccccccccc00000000,g20,8881992372224)

def layers21 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index21 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g21 : Forest := ⟨85,4,(fun | 0 => (0xffffffffffffffffffffffffffffffffffffd9,0x58) | 2 => (0x1e,0xa) | 4 => (0xffffffffffffffffffffffffffffffffffffe7,0xffffffffffffffffffffffffffffffffffffa5) | 6 => (0x78,0x50) | _ => (0,0)),[(1,0,3,0,4)],[],layers21,index21⟩
def claim21 : Claim := (0xfffff0f0fffff0f0fafa0000fafa0000fffff0f0fffff0f0fafa0000fafa0000fffff0f0fffff0f0fafa0000fafa0000fffff0f0fffff0f0fafa0000fafa0000,g21,17592454742032)

def layers22 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index22 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g22 : Forest := ⟨85,4,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffe13,0x0) | 2 => (0xfffffffffffffffffffffffffffffffffffe6d,0xfffffffffffffffffffffffffffffffffffe25) | 4 => (0x18e,0x8a) | 6 => (0x1f0,0x150) | _ => (0,0)),[(1,0,3,0,4)],[],layers22,index22⟩
def claim22 : Claim := (0xfffffafafffffafafafaaaaafafaaaaafffffafafffffafafafaaaaafafaaaaafffffafafffffafafafaaaaafafaaaaafffffafafffffafafafaaaaafafaaaaa,g22,17593260048384)

def layers23 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index23 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g23 : Forest := ⟨86,4,(fun | 1 => (0xffffffffffffffffffffffffffffffffffffc7,0xffffffffffffffffffffffffffffffffffffc3) | 2 => (0xffffffffffffffffffffffffffffffffffff9b,0xffffffffffffffffffffffffffffffffffff89) | 4 => (0xffffffffffffffffffffffffffffffffffffe3,0x42) | 6 => (0x7c,0x34) | _ => (0,0)),[(2,0,3,0,4)],[],layers23,index23⟩
def claim23 : Claim := (0xfffffcfcfffffcfcf0f00000f0f00000fffffcfcfffffcfcf0f00000f0f00000fffffcfcfffffcfcf0f00000f0f00000fffffcfcfffffcfcf0f00000f0f00000,g23,8797167034368)

def layers24 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index24 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g24 : Forest := ⟨86,4,(fun | 1 => (0xfffffffffffffffffffffffffffffffffffe13,0x0) | 2 => (0xfffffffffffffffffffffffffffffffffffe6d,0xfffffffffffffffffffffffffffffffffffe25) | 4 => (0x18e,0x8a) | 6 => (0x1f0,0x150) | _ => (0,0)),[(2,0,3,0,4)],[],layers24,index24⟩
def claim24 : Claim := (0xfffffcfcfffffcfcfcfcccccfcfcccccfffffcfcfffffcfcfcfcccccfcfcccccfffffcfcfffffcfcfcfcccccfcfcccccfffffcfcfffffcfcfcfcccccfcfccccc,g24,17593260048384)

def layers25 : Nat → Packing
  | 3 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xf | _ => 0)⟩
  | _ => emptyPacking
def index25 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g25 : Forest := ⟨120,3,(fun | 3 => (0xffffffffffffffffffffffffffffffffffff9f,0xffffffffffffffffffffffffffffffffffff8b) | 4 => (0x64,0x46) | 5 => (0xffffffffffffffffffffffffffffffffffffc7,0x44) | 6 => (0x78,0x30) | _ => (0,0)),[],[],layers25,index25⟩
def claim25 : Claim := (0xffffff00ffffff00ff00ff0000000000ffffff00ffffff00ff00ff0000000000ffffff00ffffff00ff00ff0000000000ffffff00ffffff00ff00ff0000000000,g25,35476496973824)

def layers26 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index26 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g26 : Forest := ⟨57,4,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffe37,0xfffffffffffffffffffffffffffffffffffe15) | 3 => (0xfffffffffffffffffffffffffffffffffffecb,0x4a) | 4 => (0x10c,0x0) | 5 => (0x1f0,0x1a0) | _ => (0,0)),[(16,0,0,0,4)],[],layers26,index26⟩
def claim26 : Claim := (0xffffffaaffffaa00ffffffaaffffaa00ffffffaaffffaa00ffffffaaffffaa00ffffffaaffffaa00ffffffaaffffaa00ffffffaaffffaa00ffffffaaffffaa00,g26,34361835528)

def layers27 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index27 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g27 : Forest := ⟨58,4,(fun | 1 => (0xfffffffffffffffffffffffffffffffffffe37,0xfffffffffffffffffffffffffffffffffffe15) | 3 => (0xfffffffffffffffffffffffffffffffffffecb,0x4a) | 4 => (0x10c,0x0) | 5 => (0x1f0,0x1a0) | _ => (0,0)),[(16,0,1,0,4)],[],layers27,index27⟩
def claim27 : Claim := (0xffffffccffffcc00ffffffccffffcc00ffffffccffffcc00ffffffccffffcc00ffffffccffffcc00ffffffccffffcc00ffffffccffffcc00ffffffccffffcc00,g27,68723672064)

def layers28 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index28 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g28 : Forest := ⟨90,4,(fun | 1 => (0xffffffffffffffffffffffffffffffffffffc7,0xffffffffffffffffffffffffffffffffffffc1) | 3 => (0xffffffffffffffffffffffffffffffffffff9b,0xa) | 4 => (0xffffffffffffffffffffffffffffffffffffe3,0xffffffffffffffffffffffffffffffffffffc3) | 6 => (0x7c,0x34) | _ => (0,0)),[(16,0,2,0,4)],[],layers28,index28⟩
def claim28 : Claim := (0xffffffccffffffcccc00cc00cc00cc00ffffffccffffffcccc00cc00cc00cc00ffffffccffffffcccc00cc00cc00cc00ffffffccffffffcccc00cc00cc00cc00,g28,8813277086720)

def layers29 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index29 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g29 : Forest := ⟨92,4,(fun | 2 => (0xffffffffffffffffffffffffffffffffffff0f,0xffffffffffffffffffffffffffffffffffff05) | 3 => (0xffffffffffffffffffffffffffffffffffff33,0xffffffffffffffffffffffffffffffffffff13) | 4 => (0xffffffffffffffffffffffffffffffffffffc3,0x42) | 6 => (0xfc,0xa8) | _ => (0,0)),[(8,0,3,0,4)],[],layers29,index29⟩
def claim29 : Claim := (0xfffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000fffffff0fffffff0f0f00000f0f00000,g29,17593394266112)

def layers30 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index30 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g30 : Forest := ⟨92,4,(fun | 2 => (0xfffffffffffffffffffffffffffffffffffe37,0xfffffffffffffffffffffffffffffffffffe13) | 3 => (0xfffffffffffffffffffffffffffffffffffe49,0x0) | 4 => (0x18e,0x8c) | 6 => (0x1f0,0x160) | _ => (0,0)),[(8,0,3,0,4)],[],layers30,index30⟩
def claim30 : Claim := (0xfffffff0fffffff0fff0ff00fff0ff00fffffff0fffffff0fff0ff00fff0ff00fffffff0fffffff0fff0ff00fff0ff00fffffff0fffffff0fff0ff00fff0ff00,g30,17593260048384)

def layers31 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index31 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g31 : Forest := ⟨105,4,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffe4f,0xfffffffffffffffffffffffffffffffffffe45) | 3 => (0xfffffffffffffffffffffffffffffffffffeb3,0x92) | 5 => (0x13c,0x128) | 6 => (0x1c0,0x0) | _ => (0,0)),[(64,0,0,0,4)],[],layers31,index31⟩
def claim31 : Claim := (0xffffffffffffffffffaaffaaaa00aa00ffffffffffffffffffaaffaaaa00aa00ffffffffffffffffffaaffaaaa00aa00ffffffffffffffffffaaffaaaa00aa00,g31,34361835528)

def layers32 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x2f | _ => 0)⟩
  | _ => emptyPacking
def index32 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g32 : Forest := ⟨106,4,(fun | 1 => (0xfffffffffffffffffffffffffffffffffffe4f,0xfffffffffffffffffffffffffffffffffffe45) | 3 => (0xfffffffffffffffffffffffffffffffffffeb3,0x92) | 5 => (0x13c,0x128) | 6 => (0x1c0,0x0) | _ => (0,0)),[(64,0,1,0,4)],[],layers32,index32⟩
def claim32 : Claim := (0xffffffffffffffffffccffcccc00cc00ffffffffffffffffffccffcccc00cc00ffffffffffffffffffccffcccc00cc00ffffffffffffffffffccffcccc00cc00,g32,68723672064)

def layers33 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x1f | _ => 0)⟩
  | _ => emptyPacking
def index33 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g33 : Forest := ⟨55,4,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffe33,0xfffffffffffffffffffffffffffffffffffe11) | 1 => (0xfffffffffffffffffffffffffffffffffffecb,0xfffffffffffffffffffffffffffffffffffe43) | 2 => (0x1ec,0x1e0) | 4 => (0xffffffffffffffffffffffffffffffffffff0f,0xe) | 5 => (0x1f0,0x1a0) | _ => (0,0)),[],[],layers33,index33⟩
def claim33 : Claim := (0xfefeeeeefafa0000fefeeeeefafa0000fefeeeeefafa0000fefeeeeefafa0000fefeeeeefafa0000fefeeeeefafa0000fefeeeeefafa0000fefeeeeefafa0000,g33,34628440080)

def layers34 : Nat → Packing
  | 4 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x1f | _ => 0)⟩
  | _ => emptyPacking
def index34 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g34 : Forest := ⟨103,4,(fun | 0 => (0xffffffffffffffffffffffffffffffffffff6d,0x64) | 1 => (0x72,0x22) | 2 => (0x9c,0x9c) | 5 => (0xffffffffffffffffffffffffffffffffffff9f,0xffffffffffffffffffffffffffffffffffff99) | 6 => (0xe0,0x40) | _ => (0,0)),[],[],layers34,index34⟩
def claim34 : Claim := (0xfefefefefcfcfcfceeeeeeee00000000fefefefefcfcfcfceeeeeeee00000000fefefefefcfcfcfceeeeeeee00000000fefefefefcfcfcfceeeeeeee00000000,g34,8830453813280)

def layers35 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index35 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g35 : Forest := ⟨59,5,(fun | 0 => (0xffffffffffffffffffffffffffffffffffe19f,0xffffffffffffffffffffffffffffffffffe08d) | 1 => (0x1278,0x1038) | 3 => (0xffffffffffffffffffffffffffffffffffec63,0x442) | 4 => (0x107c,0x1070) | 5 => (0x1f80,0xb00) | _ => (0,0)),[(0,16,13,0,5)],[],layers35,index35⟩
def claim35 : Claim := (0xffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00ffeeffeeeeaaee00,g35,34630272008)

def layers36 : Nat → Packing
  | 6 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x209f | _ => 0)⟩
  | _ => emptyPacking
def index36 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g36 : Forest := ⟨107,6,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffd81,0xd80) | 1 => (0x19e,0x8a) | 3 => (0xffffffffffffffffffffffffffffffffffe667,0xffffffffffffffffffffffffffffffffffe225) | 5 => (0x1878,0x1050) | 6 => (0x1f80,0x1d00) | _ => (0,0)),[(33,0,2,0,4),(66,0,0,0,4)],[],layers36,index36⟩
def claim36 : Claim := (0xffeeffeeffccffccffeeffeeee00ee00ffeeffeeffccffccffeeffeeee00ee00ffeeffeeffccffccffeeffeeee00ee00ffeeffeeffccffccffeeffeeee00ee00,g36,8830454858760)

def layers37 : Nat → Packing
  | 4 => ⟨2,2,3,0,0,3,0,(fun | 0 => 0xc2dea4a04f91520 | _ => 0)⟩
  | 5 => ⟨5,1,3,0,0,6,0,(fun | 0 => 0x304c1404402100b099c380fd42fd40fd20fe20fe40 | _ => 0)⟩
  | 6 => ⟨1,0,3,0,0,1,0,(fun | 0 => 0x8d111f | _ => 0)⟩
  | _ => emptyPacking
def index37 : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 1 5 1 0 (fun | 0 => 0xd016 | _ => 0)
  | 6 => lookupWord 1 6 1 7 3 0 (fun | 0 => 0x42e003db988 | _ => 0)
  | _ => fun _ => none
def g37 : Forest := ⟨61,6,(fun | 0 => (0xfffffffffffffffffffffffffffffffff878ff,0x4014) | 2 => (0x1c70c,0xe20c) | 3 => (0xfffffffffffffffffffffffffffffffffe060f,0x2064a) | 4 => (0x787f0,0x705e0) | 5 => (0x7f800,0x5b080) | _ => (0,0)),[(0,4,26,0,5),(4,0,9,0,5),(16,4,0,0,4),(8,0,7,0,4),(32,0,6,0,4)],[],layers37,index37⟩
def claim37 : Claim := (0xfffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00fffaffaafafaaa00,g37,34630533128)

def layers38 : Nat → Packing
  | 4 => ⟨2,2,3,0,0,3,0,(fun | 0 => 0xc2f6a099578d520 | _ => 0)⟩
  | 5 => ⟨5,1,3,0,0,6,0,(fun | 0 => 0x304c1404402100b099c380fd32fd30fd20ff20fe32 | _ => 0)⟩
  | 6 => ⟨1,0,3,0,0,1,0,(fun | 0 => 0x8d111f | _ => 0)⟩
  | _ => emptyPacking
def index38 : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 2 4 1 5 1 0 (fun | 0 => 0x124000 | _ => 0)
  | 6 => lookupWord 1 7 1 7 3 0 (fun | 0 => 0x350cc60005990 | _ => 0)
  | _ => fun _ => none
def g38 : Forest := ⟨109,6,(fun | 0 => (0xfffffffffffffffffffffffffffffffff9860f,0xa606) | 2 => (0x607c8,0x202cc) | 3 => (0xfffffffffffffffffffffffffffffffff878ff,0x848) | 5 => (0x780f0,0x740a0) | 6 => (0x7ff00,0x5f500) | _ => (0,0)),[(0,4,31,0,5),(4,0,10,0,5),(64,4,0,0,4),(1,0,15,0,4),(32,0,14,0,4)],[],layers38,index38⟩
def claim38 : Claim := (0xfffafffafff0fff0ffaaffaaaa00aa00fffafffafff0fff0ffaaffaaaa00aa00fffafffafff0fff0ffaaffaaaa00aa00fffafffafff0fff0ffaaffaaaa00aa00,g38,17626548928520)

def layers39 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index39 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g39 : Forest := ⟨62,5,(fun | 1 => (0xffffffffffffffffffffffffffffffffffcc9f,0xffffffffffffffffffffffffffffffffffc49d) | 2 => (0xfffffffffffffffffffffffffffffffffff26f,0xffffffffffffffffffffffffffffffffffd227) | 3 => (0xffffffffffffffffffffffffffffffffffc373,0x262) | 4 => (0x3c7c,0x2c58) | 5 => (0x3f80,0x3900) | _ => (0,0)),[(0,4,27,0,5)],[],layers39,index39⟩
def claim39 : Claim := (0xfffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00fffcffccfcf0cc00,g39,69797676032)

def layers40 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index40 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g40 : Forest := ⟨79,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffff967,0xfffffffffffffffffffffffffffffffffff961) | 1 => (0x78,0x28) | 2 => (0x59c,0x41c) | 3 => (0xfffffffffffffffffffffffffffffffffffe1f,0x416) | 6 => (0x7e0,0x3c0) | _ => (0,0)),[(1,0,17,0,5)],[],layers40,index40⟩
def claim40 : Claim := (0xfffcfffcfffcfffcee00ee00ee00ee00fffcfffcfffcfffcee00ee00ee00ee00fffcfffcfffcfffcee00ee00ee00ee00fffcfffcfffcfffcee00ee00ee00ee00,g40,8796096168968)

def layers41 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index41 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g41 : Forest := ⟨110,5,(fun | 1 => (0xfffffffffffffffffffffffffffffffffff227,0xfffffffffffffffffffffffffffffffffff025) | 2 => (0xfffffffffffffffffffffffffffffffffffc53,0xfffffffffffffffffffffffffffffffffff413) | 3 => (0xfffffffffffffffffffffffffffffffffff19b,0x92) | 5 => (0xe1c,0xe08) | 6 => (0xfe0,0xb40) | _ => (0,0)),[(0,4,32,0,5)],[],layers41,index41⟩
def claim41 : Claim := (0xfffcfffcfffcfffcffccffcccc00cc00fffcfffcfffcfffcffccffcccc00cc00fffcfffcfffcfffcffccffcccc00cc00fffcfffcfffcfffcffccffcccc00cc00,g41,8864817742848)

def layers42 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index42 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g42 : Forest := ⟨47,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffff045,0x0) | 1 => (0xfffffffffffffffffffffffffffffffffff19b,0xfffffffffffffffffffffffffffffffffff08b) | 2 => (0x222,0x0) | 3 => (0xc3c,0x434) | 5 => (0xfc0,0xb40) | _ => (0,0)),[(1,0,16,0,5)],[],layers42,index42⟩
def claim42 : Claim := (0xfffefffefefafefafffefffefefafefafffefffefefafefafffefffefefafefafffefffefefafefafffefffefefafefafffefffefefafefafffefffefefafefa,g42,68723672064)

def layers43 : Nat → Packing
  | 4 => ⟨5,2,3,0,0,5,0,(fun | 0 => 0xc498605ed4132bba8a876f52502bc6a884f91521 | _ => 0)⟩
  | 5 => ⟨10,1,3,0,0,7,0,(fun | 0 => 0x4100020401000404030634074c13203440500fd43fd42fd41fd40fd32fd31fd30fd21fd20fd10 | _ => 0)⟩
  | 6 => ⟨1,0,3,0,0,1,0,(fun | 0 => 0x468815f | _ => 0)⟩
  | _ => emptyPacking
def index43 : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 6 1 7 3 0 (fun | 0 => 0x7ab1ac200a2 | _ => 0)
  | 6 => lookupWord 3 13 4 8 4 0 (fun | 0 => 0xf30080121179140765b6480000800 | _ => 0)
  | _ => fun _ => none
def g43 : Forest := ⟨115,6,(fun | 0 => (0xffffffffffffffffffffffffffffffccc03fff,0xffffffffffffffffffffffffffffffc4c01363) | 1 => (0xffc0c0,0x54c2ca) | 4 => (0xfffffffffffffffffffffffffffffff30c00ff,0x110c889c) | 5 => (0x3c0fff00,0x380b2c10) | 6 => (0x3ff00000,0x2ea23020) | _ => (0,0)),[(1,0,20,0,4),(2,0,18,0,4),(16,0,5,0,4),(32,0,19,0,4),(64,0,4,0,4)],[],layers43,index43⟩
def claim43 : Claim := (0xffffeeeeffffcccceeeeeeeeaaaa0000ffffeeeeffffcccceeeeeeeeaaaa0000ffffeeeeffffcccceeeeeeeeaaaa0000ffffeeeeffffcccceeeeeeeeaaaa0000,g43,8830721200144)

def layers44 : Nat → Packing
  | 4 => ⟨2,2,3,0,0,3,0,(fun | 0 => 0xc2eea2a14f91521 | _ => 0)⟩
  | 5 => ⟨5,1,3,0,0,6,0,(fun | 0 => 0x304c1404402100b099c380fd42fd41fd21ff21fe42 | _ => 0)⟩
  | 6 => ⟨1,0,3,0,0,1,0,(fun | 0 => 0x8d111f | _ => 0)⟩
  | _ => emptyPacking
def index44 : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 2 4 1 5 1 0 (fun | 0 => 0x4f80 | _ => 0)
  | 6 => lookupWord 1 6 1 7 3 0 (fun | 0 => 0x19d4d347b00 | _ => 0)
  | _ => fun _ => none
def g44 : Forest := ⟨117,6,(fun | 0 => (0xfffffffffffffffffffffffffffffffffb19cf,0xfffffffffffffffffffffffffffffffff918cb) | 2 => (0x1fb0,0xba2) | 4 => (0xfffffffffffffffffffffffffffffffffce63f,0x40404) | 5 => (0x707c0,0x68700) | 6 => (0x7f800,0x3d008) | _ => (0,0)),[(0,32,22,0,5),(32,0,21,0,5),(1,32,3,0,4),(4,0,18,0,4),(64,0,7,0,4)],[],layers44,index44⟩
def claim44 : Claim := (0xfffffafafffff0f0fafaaaaafafa0000fffffafafffff0f0fafaaaaafafa0000fffffafafffff0f0fafaaaaafafa0000fffffafafffff0f0fafaaaaafafa0000,g44,17626814480400)

def layers45 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index45 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g45 : Forest := ⟨87,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffb87,0xb82) | 1 => (0xf6,0x36) | 2 => (0x318,0x108) | 4 => (0xfffffffffffffffffffffffffffffffffffc1f,0xfffffffffffffffffffffffffffffffffff415) | 6 => (0xfe0,0xac0) | _ => (0,0)),[(1,0,23,0,5)],[],layers45,index45⟩
def claim45 : Claim := (0xfffffcfcfffffcfcfafa0000fafa0000fffffcfcfffffcfcfafa0000fafa0000fffffcfcfffffcfcfafa0000fafa0000fffffcfcfffffcfcfafa0000fafa0000,g45,8796361728016)

def layers46 : Nat → Packing
  | 4 => ⟨2,2,3,0,0,3,0,(fun | 0 => 0xc2eea2a15bd4941 | _ => 0)⟩
  | 5 => ⟨5,1,3,0,0,6,0,(fun | 0 => 0x30501304402100b099c380fd42fd41fd21ff41ff42 | _ => 0)⟩
  | 6 => ⟨1,0,3,0,0,1,0,(fun | 0 => 0x8d111f | _ => 0)⟩
  | _ => emptyPacking
def index46 : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 3 5 1 5 1 0 (fun | 0 => 0x36070 | _ => 0)
  | 6 => lookupWord 1 6 1 7 3 0 (fun | 0 => 0x70aba2176 | _ => 0)
  | _ => fun _ => none
def g46 : Forest := ⟨118,6,(fun | 1 => (0xfffffffffffffffffffffffffffffffff807ff,0xfffffffffffffffffffffffffffffffff803af) | 2 => (0xfffffffffffffffffffffffffffffffffb181b,0xfffffffffffffffffffffffffffffffff91119) | 4 => (0xfffffffffffffffffffffffffffffffffce063,0xc262) | 5 => (0x7007c,0x78050) | 6 => (0x7ff80,0x60400) | _ => (0,0)),[(0,32,24,0,5),(32,0,23,0,5),(2,32,3,0,4),(4,0,20,0,4),(16,0,8,0,4)],[],layers46,index46⟩
def claim46 : Claim := (0xfffffcfcfffffcfcfcfcccccf0f00000fffffcfcfffffcfcfcfcccccf0f00000fffffcfcfffffcfcfcfcccccf0f00000fffffcfcfffffcfcfcfcccccf0f00000,g46,8865886507008)

def layers47 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index47 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨87,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffff045,0x0) | 1 => (0x8a,0x0) | 2 => (0xfffffffffffffffffffffffffffffffffff333,0xfffffffffffffffffffffffffffffffffff113) | 4 => (0xc3c,0x42c) | 6 => (0xfc0,0xac0) | _ => (0,0)),[(1,0,24,0,5)],[],layers47,index47⟩
def claim47 : Claim := (0xfffffefefffffefefefeeeeefefeeeeefffffefefffffefefefeeeeefefeeeeefffffefefffffefefefeeeeefefeeeeefffffefefffffefefefeeeeefefeeeee,g47,17593260048384)

def layers48 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index48 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g48 : Forest := ⟨121,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffce3,0xfffffffffffffffffffffffffffffffffffc61) | 3 => (0x3e,0x16) | 4 => (0xffffffffffffffffffffffffffffffffffff0f,0x10e) | 5 => (0x3cc,0x388) | 6 => (0x3f0,0x2e0) | _ => (0,0)),[(16,0,10,0,5)],[],layers48,index48⟩
def claim48 : Claim := (0xffffffaaffffff00ffaaffaaaaaaaa00ffffffaaffffff00ffaaffaaaaaaaa00ffffffaaffffff00ffaaffaaaaaaaa00ffffffaaffffff00ffaaffaaaaaaaa00,g48,35219002359816)

def layers49 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index49 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g49 : Forest := ⟨91,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffce7,0xe2) | 1 => (0x7e,0x2e) | 3 => (0xfffffffffffffffffffffffffffffffffffe99,0xfffffffffffffffffffffffffffffffffffe11) | 4 => (0x31e,0x21c) | 6 => (0x3e0,0x1c0) | _ => (0,0)),[(1,0,28,0,5)],[],layers49,index49⟩
def claim49 : Claim := (0xffffffccffffffcceeaaee00eeaaee00ffffffccffffffcceeaaee00eeaaee00ffffffccffffffcceeaaee00eeaaee00ffffffccffffffcceeaaee00eeaaee00,g49,8796363555848)

def layers50 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index50 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g50 : Forest := ⟨122,5,(fun | 1 => (0xffffffffffffffffffffffffffffffffffe0df,0xffffffffffffffffffffffffffffffffffe04b) | 3 => (0xffffffffffffffffffffffffffffffffffe527,0x124) | 4 => (0x1a26,0x826) | 5 => (0x1c38,0x1c10) | 6 => (0x1fc0,0x1680) | _ => (0,0)),[(0,16,32,0,5)],[],layers50,index50⟩
def claim50 : Claim := (0xffffffccffffffccffccffcccc00cc00ffffffccffffffccffccffcccc00cc00ffffffccffffffccffccffcccc00cc00ffffffccffffffccffccffcccc00cc00,g50,8881996563456)

def layers51 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index51 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g51 : Forest := ⟨59,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffff8ad,0x8c) | 1 => (0xce,0x8c) | 3 => (0xfffffffffffffffffffffffffffffffffffb17,0xfffffffffffffffffffffffffffffffffff913) | 4 => (0x418,0x0) | 5 => (0x7e0,0x660) | _ => (0,0)),[(1,0,27,0,5)],[],layers51,index51⟩
def claim51 : Claim := (0xffffffeeffffee00ffffffeeffffee00ffffffeeffffee00ffffffeeffffee00ffffffeeffffee00ffffffeeffffee00ffffffeeffffee00ffffffeeffffee00,g51,34361836552)

def layers52 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index52 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g52 : Forest := ⟨93,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffffd67,0xfffffffffffffffffffffffffffffffffffd61) | 2 => (0xfffffffffffffffffffffffffffffffffffc7b,0xfffffffffffffffffffffffffffffffffffc2b) | 3 => (0xfffffffffffffffffffffffffffffffffffe9b,0x21a) | 4 => (0x31c,0x214) | 6 => (0x3e0,0x1c0) | _ => (0,0)),[(1,0,29,0,5)],[],layers52,index52⟩
def claim52 : Claim := (0xfffffff0fffffff0fafaaa00fafaaa00fffffff0fffffff0fafaaa00fafaaa00fffffff0fffffff0fafaaa00fafaaa00fffffff0fffffff0fafaaa00fafaaa00,g52,17592456839176)

def layers53 : Nat → Packing
  | 4 => ⟨2,2,3,0,0,3,0,(fun | 0 => 0xc2f6a0a15bd4940 | _ => 0)⟩
  | 5 => ⟨5,1,3,0,0,6,0,(fun | 0 => 0x30501304402100b099c380fd42fd40fd20ff40ff42 | _ => 0)⟩
  | 6 => ⟨1,0,3,0,0,1,0,(fun | 0 => 0x8d111f | _ => 0)⟩
  | _ => emptyPacking
def index53 : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 3 5 1 5 1 0 (fun | 0 => 0x2e050 | _ => 0)
  | 6 => lookupWord 1 6 1 7 3 0 (fun | 0 => 0x4218e6980b0 | _ => 0)
  | _ => fun _ => none
def g53 : Forest := ⟨124,6,(fun | 2 => (0xfffffffffffffffffffffffffffffffffb019b,0xfffffffffffffffffffffffffffffffff90519) | 3 => (0xfffffffffffffffffffffffffffffffff81e7f,0xfffffffffffffffffffffffffffffffff80e2f) | 4 => (0xfffffffffffffffffffffffffffffffffce063,0xc862) | 5 => (0x7007c,0x78050) | 6 => (0x7ff80,0x61000) | _ => (0,0)),[(0,32,30,0,5),(32,0,29,0,5),(8,32,3,0,4),(4,0,25,0,4),(16,0,15,0,4)],[],layers53,index53⟩
def claim53 : Claim := (0xfffffff0fffffff0fff0ff00f0f00000fffffff0fffffff0fff0ff00f0f00000fffffff0fffffff0fff0ff00f0f00000fffffff0fffffff0fff0ff00f0f00000,g53,17868205064192)

def layers54 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index54 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g54 : Forest := ⟨93,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffff045,0x0) | 2 => (0xfffffffffffffffffffffffffffffffffff19b,0xfffffffffffffffffffffffffffffffffff08b) | 3 => (0x222,0x0) | 4 => (0xc3c,0x434) | 6 => (0xfc0,0xb40) | _ => (0,0)),[(1,0,30,0,5)],[],layers54,index54⟩
def claim54 : Claim := (0xfffffffafffffffafffaffaafffaffaafffffffafffffffafffaffaafffaffaafffffffafffffffafffaffaafffaffaafffffffafffffffafffaffaafffaffaa,g54,17593260048384)

def layers55 : Nat → Packing
  | 4 => ⟨24,3,3,0,0,8,0,(fun | 0 => 0x8a847e78726c66605a544e48423c36302a241e18120c06009e580454ca7960115219d584454ca7561115309b588454c26d2611510974d8454865d36115109ed81454ca7b60515219ed8125d067b60497439dd85454ca7761515309dd8535d0277614d7429bd89454c26f62515109b89905d066e264174397d8d454865f6351510978d915d025e3645742 | _ => 0)⟩
  | 5 => ⟨52,2,3,0,0,10,0,(fun | 0 => 0x20c220422882280220c2204228822802080210421802188229022902082104a408008012902182304408810000800101082000014100000408040400060800141000000000862087e1e8761c86e1a8661885e168561484f53248917430fc3c4e636cd0328bf2e4b32a09d25c9122c801e8741b86317452130460ec350bc24078180480c01800fca0261f940443ea8290fd50510f6a1265ed42487ba86997750d30bea2a657d454c2fa8a90df51510be22a657c454c2fa6ba05f4d742be22a437d25d06fa4ba1df11510be8ae817d15d0afa0ba0df41743bfa8287fb5050af6a0a15fd4141fc82e81f75150eeea2a1dfd4542bfa8a81f515d06fc0ba0dfd4943bfa9283ef52502dea4a07b49742bf0ae857f5350bbea6a0d7d4d41bfa9a81dd35d0efc0ba1df89743bf22a657e454c2fc8a90df91510 | _ => 0)⟩
  | 6 => ⟨12,1,3,0,0,8,0,(fun | 0 => 0x5409502540950254095025409502540950254095029a8c7e70625446382a1c0e00fd43fd42fd41fd40fd32fd30fd21fd10ff40ff41ff42ff43 | _ => 0)⟩
  | 7 => ⟨1,0,3,0,0,1,0,(fun | 0 => 0x2c09f | _ => 0)⟩
  | _ => emptyPacking
def index55 : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 10 29 4 9 5 0 (fun | 0 => 0x10b34056a772389000189dbfb143e60000001e46712801a2a199e1ac5a7cd361f6002001bc02 | _ => 0)
  | 6 => lookupWord 18 60 6 10 6 0 (fun | 0 => 0x8378796c00000ef001c500172a70199016c8432d275c808e92a1ae4ead044a400bc3da14dcf00833146c1e82662318bd7d1612722da157061950018e001d47948a9b931a780060e2ac9ce13530c00800000091e80800c01e1 | _ => 0)
  | 7 => lookupWord 4 15 2 8 4 0 (fun | 0 => 0xf4007795ca20e1f3b6f900f2000b4802 | _ => 0)
  | _ => fun _ => none
def g55 : Forest := ⟨94,7,(fun | 1 => (0xffffffffffffffffffffffffffffff4010f3ff,0xffffffffffffffffffffffffffffff481261d5) | 2 => (0x21f0cf0,0xffffffffffffffffffffffffffffff02562473) | 3 => (0xffffffffffffffffffffffffffffff83e00f3f,0x92c40e2a) | 4 => (0xfc000fc0,0xd8804b8c) | 6 => (0xfffff000,0x21088000) | _ => (0,0)),[(2,0,29,0,5),(4,0,28,0,5),(8,0,23,0,5),(16,0,17,0,5),(10,0,3,0,4),(20,0,2,0,4)],[],layers55,index55⟩
def claim55 : Claim := (0xfffffffcfffffffcfcf0cc00fcf0cc00fffffffcfffffffcfcf0cc00fcf0cc00fffffffcfffffffcfcf0cc00fcf0cc00fffffffcfffffffcfcf0cc00fcf0cc00,g55,8797171221504)

def layers56 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index56 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g56 : Forest := ⟨94,5,(fun | 1 => (0xfffffffffffffffffffffffffffffffffff045,0x0) | 2 => (0xfffffffffffffffffffffffffffffffffff19b,0xfffffffffffffffffffffffffffffffffff08b) | 3 => (0x222,0x0) | 4 => (0xc3c,0x434) | 6 => (0xfc0,0xb40) | _ => (0,0)),[(2,0,30,0,5)],[],layers56,index56⟩
def claim56 : Claim := (0xfffffffcfffffffcfffcffccfffcffccfffffffcfffffffcfffcffccfffcffccfffffffcfffffffcfffcffccfffcffccfffffffcfffffffcfffcffccfffcffcc,g56,17593260048384)

def layers57 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index57 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g57 : Forest := ⟨107,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffff92d,0x124) | 1 => (0x136,0x124) | 3 => (0xfffffffffffffffffffffffffffffffffffac7,0xfffffffffffffffffffffffffffffffffffa43) | 5 => (0x4f8,0x498) | 6 => (0x700,0x0) | _ => (0,0)),[(1,0,32,0,5)],[],layers57,index57⟩
def claim57 : Claim := (0xffffffffffffffffffeeffeeee00ee00ffffffffffffffffffeeffeeee00ee00ffffffffffffffffffeeffeeee00ee00ffffffffffffffffffeeffeeee00ee00,g57,34361836552)

def layers58 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index58 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g58 : Forest := ⟨107,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffff013,0x0) | 1 => (0xfffffffffffffffffffffffffffffffffff26d,0xfffffffffffffffffffffffffffffffffff225) | 3 => (0x58e,0x48a) | 5 => (0x9f0,0x950) | 6 => (0xe00,0x0) | _ => (0,0)),[(1,0,32,0,5)],[],layers58,index58⟩
def claim58 : Claim := (0xffffffffffffffffffeeffeeeeaaeeaaffffffffffffffffffeeffeeeeaaeeaaffffffffffffffffffeeffeeeeaaeeaaffffffffffffffffffeeffeeeeaaeeaa,g58,68723672064)

def layers59 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index59 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g59 : Forest := ⟨110,5,(fun | 1 => (0xfffffffffffffffffffffffffffffffffff237,0xfffffffffffffffffffffffffffffffffff213) | 2 => (0xfffffffffffffffffffffffffffffffffff049,0x0) | 3 => (0x58e,0x48c) | 5 => (0x9f0,0x960) | 6 => (0xe00,0x0) | _ => (0,0)),[(4,0,32,0,5)],[],layers59,index59⟩
def claim59 : Claim := (0xfffffffffffffffffffcfffcfcf0fcf0fffffffffffffffffffcfffcfcf0fcf0fffffffffffffffffffcfffcfcf0fcf0fffffffffffffffffffcfffcfcf0fcf0,g59,68723672064)

def layers60 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index60 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g60 : Forest := ⟨121,5,(fun | 0 => (0xfffffffffffffffffffffffffffffffffff237,0xfffffffffffffffffffffffffffffffffff215) | 3 => (0xfffffffffffffffffffffffffffffffffff4cb,0x44a) | 4 => (0x10c,0x0) | 5 => (0x9f0,0x9a0) | 6 => (0xe00,0x0) | _ => (0,0)),[(16,0,31,0,5)],[],layers60,index60⟩
def claim60 : Claim := (0xffffffffffffffffffffffaaffffaa00ffffffffffffffffffffffaaffffaa00ffffffffffffffffffffffaaffffaa00ffffffffffffffffffffffaaffffaa00,g60,34361835528)

def layers61 : Nat → Packing
  | 5 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0x5f | _ => 0)⟩
  | _ => emptyPacking
def index61 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g61 : Forest := ⟨122,5,(fun | 1 => (0xfffffffffffffffffffffffffffffffffff237,0xfffffffffffffffffffffffffffffffffff215) | 3 => (0xfffffffffffffffffffffffffffffffffff4cb,0x44a) | 4 => (0x10c,0x0) | 5 => (0x9f0,0x9a0) | 6 => (0xe00,0x0) | _ => (0,0)),[(16,0,32,0,5)],[],layers61,index61⟩
def claim61 : Claim := (0xffffffffffffffffffffffccffffcc00ffffffffffffffffffffffccffffcc00ffffffffffffffffffffffccffffcc00ffffffffffffffffffffffccffffcc00,g61,68723672064)

def layers62 : Nat → Packing
  | 7 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xbf | _ => 0)⟩
  | _ => emptyPacking
def index62 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g62 : Forest := ⟨63,7,(fun | 0 => (0xfffffffffffffffffffffffffffffffffc0c35,0xfffffffffffffffffffffffffffffffffc0411) | 1 => (0x50fa,0x4078) | 2 => (0x1b34c,0xb10c) | 3 => (0xfffffffffffffffffffffffffffffffffe238f,0x2386) | 4 => (0x3c3f0,0x342e0) | 5 => (0x3fc00,0x39800) | _ => (0,0)),[(2,0,37,0,7)],[],layers62,index62⟩
def claim62 : Claim := (0xfffeffeefefaee00fffeffeefefaee00fffeffeefefaee00fffeffeefefaee00fffeffeefefaee00fffeffeefefaee00fffeffeefefaee00fffeffeefefaee00,g62,34630534152)

def layers63 : Nat → Packing
  | 7 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xbf | _ => 0)⟩
  | _ => emptyPacking
def index63 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨111,7,(fun | 0 => (0xffffffffffffffffffffffffffffffffff1b85,0xffffffffffffffffffffffffffffffffff0b81) | 1 => (0x1ba,0x98) | 2 => (0x626c,0x206c) | 3 => (0xffffffffffffffffffffffffffffffffff844f,0x446) | 5 => (0xf870,0xf020) | 6 => (0xff80,0xdb00) | _ => (0,0)),[(2,0,38,0,7)],[],layers63,index63⟩
def claim63 : Claim := (0xfffefffefffcfffcffeeffeeee00ee00fffefffefffcfffcffeeffeeee00ee00fffefffefffcfffcffeeffeeee00ee00fffefffefffcfffcffeeffeeee00ee00,g63,8830455907336)

def layers64 : Nat → Packing
  | 5 => ⟨5,3,4,0,0,5,0,(fun | 0 => 0xc4986074d32549539dee4b0aa73bdc96054e77b38c4a9f4f52cc953 | _ => 0)⟩
  | 6 => ⟨25,2,4,0,0,8,0,(fun | 0 => 0x904a04a242081041081001002042042040000000000081000081081000ded2c0b4a89c908a7e7266605a544e48423c302a24180c0600be58053bd58453bb58853f74c953f74c553df54953df54153bf58953bf58553bf58153bf55a53fb18953bf45a53bf41b53bfd8153dfd4153bfd8553f7cc553fbd8953bbd8953bfd8953dfd4953f7cc953df54353f74c653 | _ => 0)⟩
  | 7 => ⟨4,1,4,0,0,7,0,(fun | 0 => 0xa49c8215ac5a06219cd49482b16a3105c4f8f80fea9ff14ffea7fe53 | _ => 0)⟩
  | 8 => ⟨1,0,4,0,0,1,0,(fun | 0 => 0x864202bf | _ => 0)⟩
  | _ => emptyPacking
def index64 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 7 1 7 3 0 (fun | 0 => 0x94f24805720 | _ => 0)
  | 7 => lookupWord 8 29 5 9 5 0 (fun | 0 => 0xcc004d801f0c53b4ae853352746006093d963459a54c8007400330b18144b5d672080006447 | _ => 0)
  | 8 => lookupWord 3 7 1 6 2 0 (fun | 0 => 0x170188000158 | _ => 0)
  | _ => fun _ => none
def g64 : Forest := ⟨119,8,(fun | 0 => (0xfffffffffffffffffffffffffffffe35b0199f,0xfffffffffffffffffffffffffffffe15b0080f) | 1 => (0x83ce678,0xfffffffffffffffffffffffffffffe081c4279) | 2 => (0x41c33860,0x40053802) | 4 => (0xffffffffffffffffffffffffffffff8e03c07f,0x880ac050) | 5 => (0x1f003ff80,0x1e003b580) | 6 => (0x1fffc0000,0x135600104) | _ => (0,0)),[(1,0,46,0,7),(2,0,44,0,7),(4,0,43,0,7),(0,32,47,0,6),(32,0,45,0,6),(1,32,24,0,5),(2,32,22,0,5),(3,32,3,0,4),(35,0,3,0,4),(16,0,34,0,5),(64,0,33,0,5),(17,0,8,0,4),(20,0,5,0,4),(66,0,7,0,4),(68,0,4,0,4)],[],layers64,index64⟩
def claim64 : Claim := (0xfffffefefffffcfcfefeeeeefafa0000fffffefefffffcfcfefeeeeefafa0000fffffefefffffcfcfefeeeeefafa0000fffffefefffffcfcfefeeeeefafa0000,g64,8830721462288)

def layers65 : Nat → Packing
  | 7 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xbf | _ => 0)⟩
  | _ => emptyPacking
def index65 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g65 : Forest := ⟨123,7,(fun | 0 => (0xfffffffffffffffffffffffffffffffffe760d,0x3604) | 1 => (0x6be,0x28e) | 3 => (0xfffffffffffffffffffffffffffffffffe1953,0xfffffffffffffffffffffffffffffffffe0851) | 4 => (0x1819c,0x8198) | 5 => (0x1e1e0,0x1c120) | 6 => (0x1fe00,0x17400) | _ => (0,0)),[(8,0,43,0,7)],[],layers65,index65⟩
def claim65 : Claim := (0xffffffeeffffffccffeeffeeeeaaee00ffffffeeffffffccffeeffeeeeaaee00ffffffeeffffffccffeeffeeeeaaee00ffffffeeffffffccffeeffeeeeaaee00,g65,8830723294216)

def layers66 : Nat → Packing
  | 7 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xbf | _ => 0)⟩
  | _ => emptyPacking
def index66 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g66 : Forest := ⟨125,7,(fun | 0 => (0xfffffffffffffffffffffffffffffffffdbc27,0xfffffffffffffffffffffffffffffffffcbc21) | 2 => (0xfffffffffffffffffffffffffffffffffe0cfb,0xfffffffffffffffffffffffffffffffffe046b) | 3 => (0xfffffffffffffffffffffffffffffffffc531b,0x411a) | 4 => (0x63dc,0x4394) | 5 => (0x383e0,0x302c0) | 6 => (0x3fc00,0x1b800) | _ => (0,0)),[(1,0,53,0,7)],[],layers66,index66⟩
def claim66 : Claim := (0xfffffffafffffff0fffaffaafafaaa00fffffffafffffff0fffaffaafafaaa00fffffffafffffff0fffaffaafafaaa00fffffffafffffff0fffaffaafafaaa00,g66,17626816577544)

def layers67 : Nat → Packing
  | 8 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xbf | _ => 0)⟩
  | _ => emptyPacking
def index67 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g67 : Forest := ⟨95,8,(fun | 0 => (0xfffffffffffffffffffffffffffffffffef81b,0xfffffffffffffffffffffffffffffffffef809) | 1 => (0xcfc,0x478) | 2 => (0xfffffffffffffffffffffffffffffffffe3327,0xfffffffffffffffffffffffffffffffffe1107) | 3 => (0xffffffffffffffffffffffffffffffffff43c7,0x10386) | 4 => (0x183f8,0x102f0) | 6 => (0x1fc00,0xe800) | _ => (0,0)),[(1,0,55,0,8)],[],layers67,index67⟩
def claim67 : Claim := (0xfffffffcfffffffcfefaee00fefaee00fffffffcfffffffcfefaee00fefaee00fffffffcfffffffcfefaee00fefaee00fffffffcfffffffcfefaee00fefaee00,g67,8796363817992)

def layers68 : Nat → Packing
  | 8 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xbf | _ => 0)⟩
  | _ => emptyPacking
def index68 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g68 : Forest := ⟨126,8,(fun | 1 => (0xfffffffffffffffffffffffffffffffffc493f,0xfffffffffffffffffffffffffffffffffc091d) | 2 => (0xfffffffffffffffffffffffffffffffffca1cf,0xfffffffffffffffffffffffffffffffffc2147) | 3 => (0xfffffffffffffffffffffffffffffffffc36f3,0x24e2) | 4 => (0x304fc,0x104b8) | 5 => (0x3c700,0x3c200) | 6 => (0x3f800,0x2d000) | _ => (0,0)),[(32,0,55,0,8)],[],layers68,index68⟩
def claim68 : Claim := (0xfffffffcfffffffcfffcffccfcf0cc00fffffffcfffffffcfffcffccfcf0cc00fffffffcfffffffcfffcffccfcf0cc00fffffffcfffffffcfffcffccfcf0cc00,g68,8865890698240)

def layers69 : Nat → Packing
  | 6 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xbf | _ => 0)⟩
  | _ => emptyPacking
def index69 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g69 : Forest := ⟨95,6,(fun | 0 => (0xffffffffffffffffffffffffffffffffff8109,0x0) | 1 => (0x212,0x0) | 2 => (0xffffffffffffffffffffffffffffffffff8c67,0xffffffffffffffffffffffffffffffffff8427) | 3 => (0x1084,0x0) | 4 => (0x60f8,0x20d8) | 6 => (0x7f00,0x5b00) | _ => (0,0)),[(1,0,56,0,6)],[],layers69,index69⟩
def claim69 : Claim := (0xfffffffefffffffefffeffeefffeffeefffffffefffffffefffeffeefffeffeefffffffefffffffefffeffeefffeffeefffffffefffffffefffeffeefffeffee,g69,17593260048384)

def layers70 : Nat → Packing
  | 6 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xbf | _ => 0)⟩
  | _ => emptyPacking
def index70 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g70 : Forest := ⟨111,6,(fun | 0 => (0xffffffffffffffffffffffffffffffffff8045,0x0) | 1 => (0xffffffffffffffffffffffffffffffffff919b,0xffffffffffffffffffffffffffffffffff908b) | 2 => (0x222,0x0) | 3 => (0x2c3c,0x2434) | 5 => (0x4fc0,0x4b40) | 6 => (0x7000,0x0) | _ => (0,0)),[(1,0,59,0,6)],[],layers70,index70⟩
def claim70 : Claim := (0xfffffffffffffffffffefffefefafefafffffffffffffffffffefffefefafefafffffffffffffffffffefffefefafefafffffffffffffffffffefffefefafefa,g70,68723672064)

def layers71 : Nat → Packing
  | 6 => ⟨1,0,1,0,0,1,0,(fun | 0 => 0xbf | _ => 0)⟩
  | _ => emptyPacking
def index71 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g71 : Forest := ⟨123,6,(fun | 0 => (0xffffffffffffffffffffffffffffffffffc8ad,0x88c) | 1 => (0x8ce,0x88c) | 3 => (0xffffffffffffffffffffffffffffffffffd317,0xffffffffffffffffffffffffffffffffffd113) | 4 => (0x418,0x0) | 5 => (0x27e0,0x2660) | 6 => (0x3800,0x0) | _ => (0,0)),[(1,0,61,0,6)],[],layers71,index71⟩
def claim71 : Claim := (0xffffffffffffffffffffffeeffffee00ffffffffffffffffffffffeeffffee00ffffffffffffffffffffffeeffffee00ffffffffffffffffffffffeeffffee00,g71,34361836552)

def layers72 : Nat → Packing
  | 6 => ⟨5,5,7,0,0,5,0,(fun | 0 => 0x624c3029e7a15d7825d163f514c553547725925e7a15a553dc964a79e8553e0947d8696fa2592584dd10 | _ => 0)⟩
  | 7 => ⟨107,4,7,0,0,11,0,(fun | 0 => 0x20cc19039101c8204c040408c10720f020018020101903b0c458200330680e430840d81f0608c1c8408c070090c0000082001a0400220082012090e048702c2c1616080000438108408370400020000241046083a040002000101c080804004408410407020e8107208c2000014080a040682000040101e08042c102a0800541062088b040a8222c102a0831040a820000c4100002a0800000000e410460800e81000080004000222c1001c83d081e039080000000502000028b040000000084204002f65dbb7f6bac958caf7552a1d3da2d3be69cac94d28247c898f11ca2b44586908e094017f6fd5f7bde79aef1d5ba573ee39beb6c6b6d299cb28644c45802ef5bcb095e2b654aa5141a7d4ee9992aa4f47c8b513a1640a7d0f19d23826c0cf999326608be1762ca57cac95329a51c9b12523e4387e8ec1b6328620a81182184007a0e818c2e8570a21001d03405c07406006001ed11058d604c7fa22098ae0b1fbc4416458131ef8883009bec3de117481108cbdb2c0b1a8098f3e5c16458131ef083a4288465f553154d64547eaa62a9ac4a8f354c56758d10f6a98ac2ba2c7ed5315857058fdaa62b1ae2b07d54c55354542f6a98ac6b0a819f5184c774583d5a84b22c4a9fa750d651d163e5eba2ca3a2c71fd984c7745837aa1098ee2b1ef550f815d563dea99702baac79f574e057558f3eac9c0acea9e7d5cb815d563cfab1702b3aa79f542e056754f3e8e9c0aeab1ef54c7815d163d7ab0f02ba2c79f571e057458fbe221c0ace986fc443815cd60dea98f02b82c7af561e057058f3ea33c0ace9867d5c7815c163cfab8f02b9ac1ef1105837158fbe220b86e2b1f7c44108dc563f6ab0a87b8ac7ed5315837158edeb22b06e2b1d7d46508dc563f7888300b1ec35f79156137d8abef22ac26fb277948562dc553edaa0ac9b8aa75f59150b7154ebea93b0ee2a9d7d4a761dc553afbc8ac9b8aa75f79158b7154e3ff229c6e8b06bb597825d163cf6baf04ba2c79ed53e0967507bd260886e4b277954531dc964ef298a21b92c9dcd534c772593adacaa9ee4b275b54d51dc964e76b2ac7b92c95ed6954f72592bdab298ee4b267b5637294d64af69ca21b92c95ef9154f72592bef22baee4b1e7b54f8251f619fbc8ad0a9e85ead6454f62d0abdf24b26e6b2f764c38359d10dec98706b8ac1dd531e0d674439bac7c1ace886b758f835c560cee9cf06b3a215df93601674c73bae7c1ae2b067758f8359d10ecea1ac9b9aa35ef9259373547bc2209046e90f78441218dd208ff1ca31ba2c11fd98dd27558e37b31ba4e8b1d7de4575dd163afbc8aa723a431fd98dd67458ebdf24ba6eab1d7be4964dd563cbeb24b09ba2197d62961374432fa852c26e8857be496499d53a7fcb308b3a63cdd634c66750e7ef22b42a73257de45759d163 | 1 => 0x8 | _ => 0)⟩
  | 8 => ⟨362,3,7,0,0,14,0,(fun | 0 => 0xd741d163efd651d163dfd751d163dfd3759110dfd3758910dfd3750910efd6458131bfd68501319fd874c3619fd874c3419fd874c3629fd874c3649fd38dc5649fd38dc560dfd804df619fd38dc540dbd3759341dfd684df419fd38dc9659ff87596329fd38dc960dfd584df62dfd804df629fd38dd1659ff87597439fd38dd160cfd3758364dfd584df64dfd804df64dfd2754f61dfd2754f64ded651c964fed531c964ded511c9649fd8744232bec82591109fd18dc1639fd18dcd609fd18dcd409fd188dd20ded17482329fd18dd1659ff87597419fd18dd1639fd18dd1609ff8758f41bfd08dc5639fd08dc563cfd0758f619fd08dc543dbd0750f419fd088dd21ded07486329ff8059d31ef960dc163df908dc163ffb805cd60df960dc1639fb8055d43df910dc143ddf805cc649ff805cc649ff804df619ff804df419ff804df629ff804df64bf7815d5639f78159d53bff815d1639ff8159d43dbd43dc564dfd53dc564dff8159d30bff815c163bff815cd609ff8159d30fd531dc563ef561dc563df518dc563ff510dc563df510dc563fdd43dc563efd60dc563dfd74dc563dfd70dc563dfd40dc563dfd48dc563dfd08dc563dfd53dc562df930dc560cfd63dc560ff1104c361ef51058f61efd8058f61df541dc553df521dc553dfd64dc553dfd62dc553dfd42dc553df761dc5539ff8151d30ddd63dc543dbd64dc543dfd68dc543dbd43dc540f9d4358f41f9d434c341bbd8458f41fbd8458f41fbd6454f419fe08dc5639fe08dc5439ff87594429ef8259d54bef825d1639ef8259d439ef8259d419ef8259d40ded65dc964ded63dc9649ed87d8b42fed53dc964ded53dc964ded51dc964ded31dc964ded30dc964dfd53dc964ded10dc964efd65dc963dfd75dc9639ef8259f40be98010b62aed6810b62efd6454f629ef8251f619ef8251f63bed38d8b42fbd6454f42f7d6554f42efd6558f42bfd6854f42ead64d8b42fed53d8b42ddd63dcd65dfd64dcd65dfd62dcd65dfd42dcd65dff42dcd65dff8359d10bff835c5609ff8359d10df910dcd60ddd43dcd51dfd64dcd51dfd62dcd51dfd42dcd519ff8351d109fe3849d10df5108dd21ded208dd21df9108dd20ded218dd20fe92044232fe52144232bed2844232efd65dd163dfd75dd163dfd51dd1639bf8459d20dfd53dd162dfd31dd160ef9604c364efd6254f64dfd5391d21fdd43dd563dfd74dd563dfd64dd563dfd42dd563dff42dd563dde585cc64f9d4358e5497e584dd10dfd6499d53dfd6299d53dfd4299d53dff4299d53cfd6399d43dfd5199d43dbf4199d43dfd3199d40f7d6554e64efd6558e64bfd6854e64bff8359664bff8558e64bfe6854e649fe684df41dfd5399d219fe1899d43dfe8758d54dfe8758d52efd659d163dfd759d163dbf749d163dff759d163 | 1 => 0x43f90da42d909c420906840c10163f78fba3e80f723d38f2a3c18eec3b48eae3a50e7a3980e4638b0e1237e0dca3670d8235a0d4e34d0d1a33b0cc832b8c8a3170c423078bfa2fa8bb22e38b6a2d40b222bf8ad02ad8a882968a2c28209da26d8992259094a247090223a08c4228087c21b083e20688001fc07d61ec87981da87641cd87121be06de1ae869619f064e18d061017b05d216e059e1610560151852c14484f813504b0125847c118844810b84140f983e00ef03a20e203640d283300c582f20b102a00a1826c092022e08501f007301b2066017e059014a04c00f803780b0025807c01380200018000fe11048520ff11058131ff11050530ff1104c121ff1104c520ef96058d40df97054c64df9835c064df97058131ff96050131ef96059130bf98058530ff9305c560bf98019130ef96058d20df97059442fd93050d10ef96059110ef96058d10bf98058d10ff98058d10ff9105cd60ff93059110ff93058910ff93050910df9074c361df9074c362df90744232df9074c364df10748641cf90758f65de57148062f553154d51ed53158d61fd53158553fd53158d51ef56159541ef56158d41ff56154d41df57154c64bf58158131ff58158131ff55159131ff55158931ff55150931ff56150131bf58119130ef56159521ef56158d21ff56154d21ff54154d21df57159442fd53158d10ff53159110ff53158910ff53150910df53744361df51744232ead4259162fed6254d42ded7254c649ef8758a42bed8219130fed6254d21dcd3748062dad4748062d6d5748062ded3748362edd6359543edd6358543fdd435d563fdd435c563fdd6354543ddd585cc64ddd7354c64ddd805cc64f9d431d163edd6359532fdd325d563ddd3759442edd6358131fdd315d163fdd315c163fdd5359131fdd5358931fdd5350931fdd6350131bdd8319130ddd3758f41ddd374c341ddd3758e54dbd6750f41dbd6750e54fbd6454543fbd6454d42fbd6454d41f7d6559153f7d6558953f7d5359151f7d5358951c7d5758f60efd655d163efd6559163efd655c963efd6558d62cfd8559c42cfd6759442cfd6758d10efd615d163efd615c163efd605c563efd635c560afd689d163dfd755d163dfd6759153dfd755c9639fd8758d10dfd8459d31dfd745c563dfd8059d31dfd8159d30dfd715c1639fd8758f419fd8758e54dfd8758d10dfd8758f41dfd8758e54dfd6758953dfd8359d10dfd735c560dfd87581319fd68dc5439fd6895d43dfd5759131dfd5758931efd6458953dfd6754d42dfd6754d41dfd6754e64dfd6754d21dfd6754f41dfd6754f42dfd67545439ff8758e549fd87191309fc8759543dfd585cc64dfd4754d21f7d6554d42f7d5354542efd6558d42bfd6854d42dfd5750931efd6358540dfd6750131dfd4754f61dfd4754f62db | 2 => 0xf0e420e43f081003c0d0e449142e09c320cc4914490cc270c0908c209c031243c10170e420f039083b12421243b08410f0390c420f4390c160083c1244058020f049130b438390f0b238390c420f82047824283c100c0a03d0c1f0443e0c410e4208c3908410e422381003c0d0e4510428080e0a02202834142f0a0490c0e0e4204c0e0f83910220043e0c4101c390c360403e0c410e420701008360403e0c410e4209015083c0e420f039083c0e420f039083908c22388c0bc39108c238440e4411016081f058207c16088e0e420d43908420f0280f84828130f831082208010883b0c410a0330f840e43c08370583c0c42104370c16041003c0d0e44114390f0420d0b0d83b0c170e42e090b0d03c13010543c0f82c28150f04c0c3e088b608340f0422c310d03c120b0c4150f0402c3704036043c0a983108b60c3e0c3b6283e0c15625830f0405c0f088b60d880f0402c21081e0542c0c150f030a80b0f030a80b0f0302c1e0b0a0483e13010483e0c120f8202c102c35082102c350c17054282c310a83c1001042208439108b0dc100c0f02c203c0d080f05c0d0c23038390c0e0e420400f0343910390f0222c480e4322c3704030900f080f03420d43908370e42064390f430e43d08390f020d03b08390f020e4320ec3004210ec310422083e0802074110b030f8206c10081002824388920c3c10006c1905831041a084308020801010c303c0d081701820ec4908410a03c0f0ec328b0e4411010018303c05080f034203c1703431083c081d0442058420f830881c028310822082008820400c0822018208806081001820f41100c420f8507c1108110083c10840881a082106820882007c1a101f0442203040883e080c1b303ec09300abfc2fc2be7af70bce2f14bb9aeb8ba52e66b90ae1eb812dd6b6a2d7ab55ad32b412ce0b31acacb1fac5ab0b2c08af92bcaae4ab3cac8ab08abbaacaaa9aa82a952a30a85aa06a7da9e6a6e299ea5ea956a4ca90ea35a8a8a212860a11a8229fd27e49f0279c9dba7549cea7169bf26d89aaa686993a62a981a5e296fa590956252a93f24d892aa49091da45c913243c90b23fe8f1a3a28e223648d2a3268c5a2fc8b3a2aa8a42280897222487da1c88692180854a12483da0dc830a09e81c20388051fe67e91f807d71f387c51efa7b09ea87a39e747969e407871e0c77a1da67631d687539d3e7491d007371cc272a1c8e7159c3c7039bf46f69bc06e71b8c6dc9b586cf9b246c29ae66b31ab26a11a6a68f1a1867f99e466b1988659192c63d18c662b189261e184a60c18165ff17ce5ea97905dd975c5ce17005b716c25aa168e59a965058b160857915ac5649578557953a548150653614aa51c944e50593f24f393aa4e413764cf93064b892c84a69280499924c48c920e47a91bc463916a451912c | 3 => 0x390f420cc0e0f839103c0e420f439083e0e42024140f43c10414383b0e0c0c03c13048381300c210e450701303030f5034243c100e0cc320e44038230e430048c08c3b10140d03c0d0b0b43e0c3c0e42421030f83c10410c8330e44104330f439104108c390c4108c390c8b030130f4402c3c04830482b083c0e420690e20c3c10090d83b0c1a438830f04028150f030dc350e430b43e090e0bd0c22c3914221240e0d82f0283e0e480bc39082f0e420f83908160cc3e0c200bc160c414383b0c0e0cc340e4408c0e0e4382c20080b040b0409044c230230ec40e43e08160c83f0c0b0bc160c0b0bc160d0b0f83b0c410cc0e0f839148b404130f840d80b05430ac0b05430e43c080a0d83b0d0b0c43f0f0408011050e0ec30a80b0f031308c08c3b100e05820b43e080b0d03c0c140f82050150f0301e820a03c10280cc3e0e8241c1f0883e14220283e0c0c0bc1a0c418383b0c414383b0c4c830230ec41041a0f8220f4510d0b0a03d110707c430d0442c360ec3124330d039100b0f8208c39080c02c20381030102011308c08c3b10420803d0a03e14420f4390c270f820a0330f830a03c090b8041a0c0b040c058282c8740437108702c240c8b030202c10dc350e4382d010dc1f068582c2208037102407c1a82c40840b090382c2d0f830790b0d83d10340cc320e44108360883e10230e4203849080e08c390c410f41a0f8482c1f044100f8582c10030307c1102c1510490e81003c0d0e460d8100f830d8100f831242f0e431242e0e43124390842044030f43e14370e4207c3908420dc20dc1a080505421242c0e430e41124030e4382842044030cc3e18350e4282c3704030900f080b043803c202c3e040302c3704030d80f081f044207c11081d064150441014370e42230231303b10350e4210420082b054202c31084302c10c421080d054203c0d0822020207010080b0403e0c1b04020883e082007c07068481c0c088b0803704040782403c303c31083e04c20f4150400b02851043c0e431083d0e43104160090e0f05104160090e0f05044030f43e103c0e4210423083d0e420a0200f43e10420dc209c3e08280f02044020543c100e118410c4104820a03c08370e42008160f0322441a0c0e0f05038461043104130824054205c0f0a0b0d83b0c37040282c2d0f830643c0e4322c2d0f830400f034490e450e43c083d0e420f039080b0d03b0c280f020dc3908110083e0f040f8020683c101100c3d1043e144108c390c410400f0343914410f0390c420f0390c390cc3b0c3 | _ => 0)⟩
  | 9 => ⟨411,2,7,0,0,15,0,(fun | 0 => 0x710bfeb22a3ff58d51ffac4a8dfd57186feab8837f55c21bfaafb0dfd57d06feabe437f55f62bfaafa15fd57886feabec77f55f43bfaaf195fd578c6feabec97f55e42bfaaf20dfd57992feabcc57f55e61bfa8e995fd474c6fea3a61ff59543ffac2a1ffd5250ffea8a877f5cc64bfa8e90dfd47483feb2a85ff58d42ffaa6a17fd5150afea3a21ff59541ffac6a0ffd53507feb1a81ff58540bfae0325fd47d82fea3ec37f51f62bfa8fb1dfd47d97fe3a2cbff1d163ffaa6325fd37486fe9ba41ff59532ffaa8997fd514cafe9ba21ff59131ffac498ffd604c7fea1263ff50131ffac8987fd624c3feb0a61ff50930ffa82987fc644c2fe9bec17f4df40bfa6fb0dfd37d06fe9bec57f4df42bfa6fb25fd37d96fe9bca97f4de64bfa4e887fd65487feb1a437f49e21ffaa890ffd53487fea8a43ff50d21ffa6090dfd27187feb1a41ff4c520bfae0315fd7010afe93ec17f49f10bfa4fb0dfd27d8efe93c637f49f64bfa4f20dfd27d96fe93ca37f49e61ff8e4b2fec72592f6392c9fb48062bde4f20ffd6510bfeb2221ff58d10ffac4887fd43443fea1221ff4c910bfa2f905fd178cafe8bc857f45e52bfa2f315fd07d86fe83e837f41f21bfa0fb15fd07d0afe83ec77f41f43bfa0f195fd07d92fe83c857f41e64bfa0f315ff70593ffb82c77fdc163bfee0b16fd64d837eb1ec17fdc143f7a87a07fd63d02ffb8243fb48720fea43885ff71596ffb8ac9ffdc563bfee2b1dff7158affb8ac1fd44361dfacbb0efd63d87fea9ec3ff4c361bfee2aa5ff7154effb8aa57fdc543ffee2a1dff71502dfa38c3ef59341f7aa9a0fbd43d07feb2e83ff58f41ffaa7a0ffd30d06ffb8a417bc9c61fdac590fed52c87f690643ff59721ffaa390cff6710bffb92cb7fdc965fdee4b25ef72592ffb92c9ffdc963bfee4b1dff72583f6906c5bf59362ffaa7b17fd30d8bf6216c5fbc8362bfee4aa5ff7254effb92a37fdc943bfee4a05bf4718bf699685ef59342ffacba17fd63d0bfea9e85ff4c342fdec5a15f67110afb388c57fdcd65bfee6b25ff7358affb9ac1bf59763dfac1b1dff73552ffb9aa57fdcd51bfee6a07bd64d0fdeaa687ef50343ffacba1dfe37486ff1ba41fb58a32fdaa5197ed218cbf690465ff59632ffaa3197fd108cbfaa8c63ffdd165bfee8b2fff7458effba2c77fdd162bfee8b06fd62d937eb06c9ff54f64ffa61b25ff7454effba2a57fdd151bfc8e90dfe47482f7390c9fb58a42fda41217fd6590bfea8c85ff44242bece2327f521906ffbaac9ffdd563bfeeab1dff7558b7eb1ecb7f95d43ffcaea1fbd43953feb1ca97f95d21fda43295fe67552ff33aa77f99d52bfccea8dfe6750eff33a81ef50e64ffacb327fd63993fea9cc9ff4c264bfcce90dfe67483f690cc5ff59662ffaa3317fd1098bfa90cc3ff9d163 | 1 => 0xfd17e9afbb5f46bde57a7af375e3ebbb17462e3e5c28b7f16e92dba5b44b5bd6a2ad1b59f4b3896652ca05910b1c16232c2e581aaf8d5e5abb35724ada15a82b2f562eabfd56f2aab5502a9815242a0c53b2a6754b0a937523ea3f946a289850eea13541628024f9e9e713b4a7484e4e9bad35c268e4cda99312ff25c24b3095b92a6a5234a0492f523c244e48368fc51df2382469e8c9517da2da452a8965117a1ea435c85a509b20f1418e8299039a04940507ff8fee9fb33eee7d58f8d1ef93db07ab8f469e6c3c847884f001dd63b6a7650eb51d493a50741ce731cc5393671c4e1f1c14378c6e28da71b1235e26ad4d459a6a3480687cd0399e633786648cbd1950324c63f0c6918a830fc6174c1e182430065f1cbc5976a2e925c34b7196c22d3059dcb2b16352c165760ac9953c2a2453a0a5f149428b05094a0693f527844ea89b2933b26224bc095e92a524e4492090a91eb23a646c88c8917022b044dc88b10f5219642a8840104d20463fe47de8f8a1ec03cfc7860ec71d2839cc7248e281c2037e06eb8db61b1835886978d0519a4323462d0c30181e2fb85d90b7f16982c8857c0ace156c2a785358a41141c27d84e609ab1302255c496891511e8234c454888810e0213c417080d0fb41e9c3be87530e521c2035d06900cf0195c31f860c0bd617042d0057f0aaa14d028504e9097e129c23a043808400fd81ea83b407140d801a40330061e0b28159028804aa08ac10501e0036c05e80a80126020a039005d009900de01380007f960502fcb80c9fe58130ff2c0907f940482fcb80c57e5c042ff2c0887f930443fc902217e5c061bf2e010df907906fc83ecbfd58541beae2327f5614c7faa8a63fd58521fea8290df57118afab8885fd50510fea62887f521443f6b12857b5c864fdac4997ed524cbf6b1243fb54921fda6490ded27187f6a1241fb4c920fda42905ed27907eeb1a87775cc64fbac6997dd434caee9b8c5774dc42fbac698fdd534c6ee9b8c3f750d30f7ac8a1fbd5450fdeb22856f51c62f7ac8a0fbd54507dea1a836f51c61f7a86a077d65552beab8c9df59553efacaa977d5454abeab8c55f55c42efacaa8f7d53546beab8c35f55f60dfacab1efd6458a7eb3885bf59561dfac6b0efd645837eb1ac17f59d54bfacea9dfd6754afeb3aa37f59d43bfacea15fd67506feb3a81ff59564bfacf325fd674cafeb3a637f59d30ffaeab1ffd6558ffeba2c7ff59163ffae4b1ffd7158ffeb82c77f59d21bface907fd6558bfeb1ac57f59e62bface215fd67443feb9ac1ff58d60ffae2b05fd67d02feb3e417f59f41bfacf90dfd67d0afeb3e877f59e32bfacf215fd67952feb3ca57f55d43bfaaea15fd57507feb1aa9ff58554bfaae325fd574cafeaba63ff59153ffac4a9ffd6154efeaba43ff58d52bfaae315fd5 | 2 => 0xa440b8c0183210120e418f04060f4123b106c3c048ec40d20c1c2610162d1f060c110ec3168f82418f07c18b8723d1e0249231245c3d1c8f012320c243f0c27031f062e138dc6a09070c83048e478209c183c0c06271f0f041c8487e182c323d0c2c0a1e8617070f872206b048a060f451b0d704391f028823e088217050bc6c3e1c8389c110c2a3c1010021c8f0441820723c1042071a8e44208bc7c0e1e0e46020c60e161d0a3c1c84311c848e461103e3914623908184c150bc720a1e0e2f1402878202004391e8807050ec385058603d1f0a281d8420050f01a3914040e140ec4208bc500a1e8b07178c47220f47210b42a3c0c0e0a1d860b1e0f83188e42058547818d0503b0c0a3e1d062d03830162014503d0c2a02140f44c1017023e1e0b81c18f878222c62151e081ac102c68411e8c1101054163d1435030a8f0441854781c2c0a31150f051d0cc621105a0e1c382e1c83448cc5058cc5418506c0b19881a0a8f031b8e821b8e82058547818c02a3c0c5a070602c40d054163d121605100d078282c40341e081e058d06a3d160e340f85a180b180e0b860c04c3d14620b0a8f040702876181c143b0c2031109191639182c02408f87a2844040b1b0f0504808723c1042071a8e440720c123c1062390862390916482307472282404391e881a05c04183d14623908120c138f44010dc72182804391f8809010e47820686c0b1e08281d840a1c8fc3048e478180848281d881d1f8e431c8f02070f8721818503c0c04281e063e0d608923c1451821f40478290c622a1e09091f40c78210c622a1e0883070f031e0e85411408c5070e221c83448f041a8e820d0a87818d47411280831150f05168a87818b40e0c05882a058f43058a878187a16361e890b168f8314c2c5a3e100e0a1d8605050547820a07a10dc4482218e450803d0431218e46140f020f8dc6a391036351c86021a8e430f8346a39108201138f841f8e421f8e4214088761844200f06a1c883a1c683b081c171f0e84146087d011e0a4c1f088762204183c0c840e110ec4210807c3c10501f83a06183b18990c180f04c1128643f10002d1f060e058f430f42c6c3d12162d1f0632858b47c2058143d0c821f0d10840221e8f888a8b144a26fc4b5891711aa22043fb877f0e7a1ba434a86410bda161c29984a908620f2c1b28311057a09a40ef818b024a02fc0358028ff85fe03f9f7ed8fd2df90bf007d88fa69f3cbe467c4af7edee8bd837a8ef451e753cae791af169e183bfd77b8eeeddc43b67768cec71d6bbab6752ae9d1d20ba1773b6e6a1cbf39547242e3ddc66b88870aae065bfc37b36f36ddc5b9ab70b6db0da71b34b62d6bf4d6b1ab835226984d1f5a20b4056780ce119ad333065facb4d959327f6474c8418eeb1b36300c559891b10261b0c2958393051604eb | 3 => 0x4485814622a1e0a3c168301622081c3e1c88491b0385e391f0287848387b031e0a07818f4723c048c051a8e430f85c1e0c43c2c7238dc7210382e3e1c881102e087d011e0d0b188fc7826080b0a098f85848147c3d818f0640a081c221e8b8102880200c1e8c110102c2a3d141c490b8286c2f1f0e48470245c3d1e0e461a82a0e821bc2c3e392216410f8080222108e00e3928821a05e0a023e1e0e0b808801c221e8d821202c68431e8c36050d45e3e1c9247208b87a391e0246c14286c3d100d031e0f840382d04361e8a1e218d87a202c2a3c0c221e0602c7a28d0102c070f4723c1c13031c8f0420826060e1e0b03070e47820142703060f45090d8163c12141a100307a282c2a3c0e16201a0f041006a020c1e8a11010d8163c141633150602060a07a20086c16058f05000a07818c47210d472110440281e0822100f87220a07610dc72143a190b178e450883016871d0802f011ec0ca438c4223a1e0aa060b20628e178e441b8e42208784e3e10503b08503b0a02111d40c7c28647c2f1c880b818d87c20746a390c503b0862390804371a8e44188e42188e420106c6a3910503c083a371c86021b8d47220c47210c47210747c390c04171b8e44140f420e8d47218c472109c7c10747c390c220205854662808500a1e08301c8f03140f02030bc500a1f0f060f06c0c351c8a0c00c2c7c2f138c11409301a0e1d8d0a188ac7820d076102c683b0c3c0b198fc48387c2c0b1a0ec6058d076180818391e080c140f030e8a0663e120e3117c3072282406391a8f45018f472331f0b81070ec38184c7c1e080b0a080307a342c6210070f4502c047c3c10343e1e06221b8e431007c3407110f4823e201681088ea1c3b180428050f440109c123e1016281e8617058dc72202c7c390c6a1b0143a188b1c8e200e82c7213850f8716c286c3e10160e1e0f87228b6142b1f081c0585c7c3914180b84c0c7a3c181d09818487828f4788e1c880c848c8762030723c0c16034608c724c1d8e2e138dc6a09070c02138307821040e2f1c8dc143c1c0c4c140f4143b188211c1888520e058e110102c183c15021120e0c2e0e1e8e071b8d472201c1a390c40114083078282004391f0819140f430e8a0643f10320a1e86170c8dc7220120f0c058bc4a303c7e3a0c3a16060ac543c1832391e8615050f030189c683c1030391f060b070ec316830163c1206151e0619050f43c110c2a3c1016151e0619050f43218c42a3c102a0a1e061a0a8f030c8287a1864143d0c42351c868b188f87820d8763305882d0002c683c140a0e050ec42301c041e1cc2c6c3d22023e8184e103d188232070f878391a101205c0c2a3c1818391e062b0902e10341d8c15058e47a202c323d0c3c0a1c8fc4058647a18fc72102c323d0d06081c8f04008f4103b105a3e083483070 | 4 => 0x9030207a031e0c0dc081c183b151c3d018f012281406341e0805018a878202c1c3b0c782d0602c4048a81c3d018f0103854190e45c30723020063e0c3a25050f0402838143b103a25050f04038f87839130406050cc7c2e041a0e1d8836110bc1c391f028700c2c5e0e060e46c103814361e8a31028282e3d145a0b0703441e0b4180b12060c1c8f0409849160107030723c0c10391e88310302c7e3c141b81038307628682a0b1e88011b8e43c101016121f8a021b8e43140287a181c360a1a8205030d07618682a0b1e88081c8f830b83c180a07020603e08143c101a0e1d87822182c683d14162a1e062d058381a20b4160c1e082224838162f1c8f814400a1c2f8602c72301c540a1a820581824723c13041a05832023c1802351c870b028c47e3c145a0b070344c101214131f0a021a8e431402878181c540a1a8205048e4781818503c0c0e3e1e0e4411084040185a1c723814503d0c1a311c8607068e430f0f0280c058a22070f87220061c2f8622c72301c540a1a82051b8387839100f0b410e | _ => 0)⟩
  | 10 => ⟨50,1,7,0,0,12,0,(fun | 0 => 0x60b0e280314281e04360cf8f07060b830e0114301e0c2cf8f060d360a3e830e18f4342438f00c6070b0c283503181c307c04582c0c728070c0b033e18742c3830a00c6070b830c013c18380cecd02cc834707052a0a833c0c1c1c40342430f40c7018103300e0d181c30fa0cf42c6032f0e0c0b390a1c1c182c200c2460807360c05830a3d20981c302cf80c6012d030b0e0d181c04f00cb4302c7050e090c030818140464540c30281c209020e0a0d08140c382834205060b3735030e18cc1c24340c3060e360d030b141438300c28505210c0a833c0e1c380cc03428f4307020e2d0d083c0b1c188a0c2ca43860703320b300c0d1c083c14283830207370d83013c0e181c0cc03404f43073c0e03362d010d1c08542c30043820721810d83260e18380cd8b434cc2c715030d0c0a0e081c182cdcd40c3863707011a0d030c1c38d8340c2c5050e0c030a14cc0e041cc03430732032d0e0d0b1814086454382030288aeeab0a82a4ca169e09aa96c9369008ca88c84e8107da7a47667306ea6b467e64060a5bc58e56052a4f44c649845a41c3de3a836a32c2f62b827a23c2061c818a1541160e80ba07c046000ff597fd64ff58ffd62ff587fd60ff553fd53ff54bfd51ff50ffd42ff507fd40ff193fd32ff4c7fd30ff487fd20ff18bfc42ff443fc61ff107fc21ffd83ff40ffc83ff10ffd87ff41ffc87ff62ffd0bfe21ffd8fff43ff8cbfe31ffd93fe42ff907ff65ff953fe52ff947fe64ff98bfe61 | _ => 0)⟩
  | 11 => ⟨1,0,7,0,0,1,0,(fun | 0 => 0x20c27f | _ => 0)⟩
  | _ => emptyPacking
def index72 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 7 1 7 3 0 (fun | 0 => 0x1a96000302212 | _ => 0)
  | 8 => lookupWord 35 120 5 11 7 0 (fun | 0 => 0x13384dc1f0800015a001b102bb11f8c0e74ee7ef556b404e1a4f92843be6439f400ea9a6e0b9c9e071c3231c465b23aa8941d1d2483360b1bf352f000000e2c00093cbaa4aa2cdbc5fd8c310003b083c07f0080005870c000002965082d23de1525c832951b1a0fabd6100175229219ad20a5110001cc003e39c0c69cbe5ad36a30a9089b4ac6396c07fe4c8a1a024f4d49885310fa079f27411f2ea0a00044cd99bc570ee88a510ba05a681d2005f1d014812700020002e12ae01 | _ => 0)
  | 9 => lookupWord 120 406 7 13 9 0 (fun | 0 => 0x1dff116000256c1a631917f6b494ace6f60080000018a500000000000007b159a7a5226d0001c6a902b676042154c470d817e41cb969e706978001696f52eb4cd1aa85703cad2c155f56e57619b6b99ceab8a4c3df0b7ad97868498d70aba1561caa57cabdd2f90885bb65d55fa35dd19252a1de92520488a356acb5c8d1667b0c0f50842f675e720aa64836d2839eeca8d4a81a7b44c658c0189d2c4188277cacb27a982a0a4256acee7c2b2a9dfa98406c40b13f009a1c8956778c2acfe95eb47913204c06a920acd11daf4f89e493cd6cb1f586792e82feec50dd391656a92238881f53b673e781aa2deb0f252d0000144106b44a0100f32974a704600002098a658fa95c531000648c131c5799b425268a000745c57403800000052aba2b55558049340011110000000a9000010a0003210000212e57c001c3fb0fd02f92c000485c51162566c164000206e4dfb8ebc6ddadcc683f40bb02db0fb4c92175c185936e7842208b642b1cd0ddc2c00e751340638d2544dc3ec602424f927b286d0d2157c0d595344cb902fb9c82282c05b8bf6875c1a6712cdddd66066963535d53e8e3a3ec42ccd4b023b79d005647d40c084b842244a46ba18d38631214c335ea20f499008d406173d53040816a8a3c18b998d98a0d4441e9d519985840f0a4f27549124258ab2b1edb75df9b8aa7413b8f503d48f733071f0cf49c000c6f2c884f0000e0cdce400114169fdd5c001a43d1680bf54255cc070b0800129f5b28003d9fe380001ad666b27c0003223660000b33d2bc001ceec30b1971aa128ca0129000020d07ce874000d50948291554085c31ca193a29707e79db26491c5e00051460c4000c740000000ce91639cbb4d0000e0609aec50853353f28ecf400000064e2d00f09000558310e4f185c8b9842b5270425a828e05709020028e1c31f882e22f310e18000c6008808f299020e1e35406000100200201120831000241861ce8a806a0c118141c48000280000a000013214083781070c2a543010e36e4222580094c1c08834101250405100002c0000504000013840b06a9200 | _ => 0)
  | 10 => lookupWord 137 461 8 13 9 0 (fun | 0 => 0x14f135c21032a2ad74cb3d90332b87000659d142750f8d0bc99bdcb794c0000000000f76336aa1fcd6000057d9a387ce9cc9ed2fa9350003b9845c559a51d052a67b3db04d09a6605231ad393c0000007a5539eabc0006aec855a440006a2a1ea6db3420000003861af300028f0a3eb5455ddc20314b72436f87aa99021000382a4dc1552138ac50032e88a18002d57417d0c42300000000004413b1800000000024d137f39289de85a000b960194dd4f0a8480003d32c8284215b965f556d20f3d400000000002e4000c9c85a8001e534cbb24cb388b0000000284710c0594c74c1c5606efc603b2addda1f1590000001aac888000367ea8bc4af5bd289118e874e0400000079a1d480aded417854920c46fb7c8e38543578d661b45dcd7038a9b0e5f601280848cba458fe8fca9fc0f8384c6d0683ac00089632e2842717911814e04fcfbf096bd6c5b3290486158003009f4f78160d19c0000000639217ab385527abd474464000703e4d5c8d9b30c6dc49737789338c858a81d0005216b1032389c5e22f883d3b0693661876ba219ddd25520526ea51b217263869f9d66f690d00063e4e4e089456f324d29326f6db81db2b4b3ac8097bae0071f6cbcc4ac42fab1f8aa9ec77202b482a306d23b41cf397f102cc84ec12ef0027023b311da6468eb8f22bb111a5fa2d2d736fc9053680009a2bc7f000286e63ac97f7e18d61756d8662895fc8bf9a56a9473582c6f7bb53731a5a06845211b8c2ef745b51ceed9a2a56461a7d7c171f492981f0742221f71ca05fe3167f34bb98534bc533d02a5a242a7fe27feaf01239e29e0ad1161054bad00a6d49c7e8404df0e378bc93115db6a20252e1244b09e5c34130001a4e0000000934b826290000001c20b711dd5d4a000b01cafc00198f77a1a1e4cd01d5223058e4212bf8cb15027679209f31d3ae9565b5e0c1bca180e105bd6f0fdca7e6fc4e928280cda3ee6043208312afb3e0f3ea02c4fda9d3654ea2d95ce4d8785b66e174001067611d9476512938a6d0a0727433442f822dedf14010337212b1305b10202001a02050d0b071c171211510b06090500002214076b0c2b031200000000670007140f0508000108121321060900370015011945022924010301171704021000020336001413000102030000050f000e0c00011a170602041d0f040300020d01001f0321010749030213000117080401541006000c340c04000d0300000702 | _ => 0)
  | 11 => lookupWord 17 65 6 10 6 0 (fun | 0 => 0x397384c006c510024e7246000000bc4185c000000c596882b9ca800069bb68a9bb63a1da50038d033d00b2547701d811c8000030021f003d970446fac0018a6f001ea1929567ba60021613dd2b2c0034c51d41c000009d0008c204b004 | _ => 0)
  | _ => fun _ => none
def g72 : Forest := ⟨127,11,(fun | 0 => (0xf80218280c0783c001c208fc3e0320fff3f83f,0x2082809074351004008781601201c30d066) | 1 => (0x1026030000803ff86200f0fc13cc0f80c3fc0,0x20030800a01878200094c4110c450841944) | 2 => (0x2138040300ffc00183c0ff001c0ff000fc000,0x128000202b9802083c4de1054071002e8010) | 3 => (0xfc1c07803ff00000e03ff00001ff00000fffff,0x400028130700800202a100000e609810b2298) | 4 => (0x7e007ffc0000000ffc0000001fffffff00000,0x7400313c0400004f700800248ba8ee3c00300) | 5 => (0x7fff80000000000fffffffffe000000000000,0x3f9d002020010205d91e683a8001002000000) | 6 => (0x7ffffffffffffff0000000000000000000000,0x8d7c4c0f8462380001000030000004000420) | _ => (0,0)),[(1,0,68,0,9),(8,0,64,0,9),(32,0,67,0,9),(33,0,55,0,8),(2,0,66,0,8),(4,0,65,0,8),(16,0,63,0,8),(64,0,62,0,8),(3,0,53,0,7),(9,0,46,0,7),(10,0,44,0,7),(12,0,43,0,7),(18,0,38,0,7),(20,0,36,0,7),(66,0,37,0,7),(0,4,71,0,7),(0,16,70,0,7),(0,32,69,0,7),(1,4,61,0,6),(1,16,59,0,6),(1,32,56,0,6),(2,4,60,0,6),(2,32,54,0,6),(4,16,58,0,6),(5,0,50,0,6),(6,0,48,0,6),(8,32,47,0,6),(16,4,57,0,6),(17,0,41,0,6),(34,0,52,0,6),(36,0,49,0,6),(40,0,45,0,6),(48,0,40,0,6),(64,4,51,0,6),(64,16,42,0,6),(65,0,39,0,6),(68,0,35,0,6),(3,32,30,0,5),(5,16,32,0,5),(9,32,24,0,5),(10,32,22,0,5),(17,4,32,0,5),(18,4,31,0,5),(22,0,10,0,5),(35,0,29,0,5),(37,0,28,0,5),(41,0,23,0,5),(42,0,21,0,5),(49,0,17,0,5),(52,0,11,0,5),(65,4,27,0,5),(65,16,16,0,5),(66,4,26,0,5),(68,16,13,0,5),(70,0,9,0,5),(80,4,12,0,5),(84,0,12,0,5),(11,32,3,0,4),(43,0,3,0,4),(53,0,2,0,4),(69,16,1,0,4),(81,4,1,0,4),(82,4,0,0,4),(86,0,0,0,4),(80,0,12,0,5),(72,0,33,0,5),(24,0,34,0,5),(76,0,4,0,4),(44,0,19,0,4),(28,0,5,0,4),(98,0,6,0,4),(82,0,0,0,4),(50,0,14,0,4),(74,0,7,0,4),(14,0,18,0,4),(81,0,1,0,4),(25,0,8,0,4),(69,0,1,0,4),(85,0,1,0,4),(13,0,20,0,4),(19,0,15,0,4),(11,0,3,0,4),(7,0,25,0,4)],[],layers72,index72⟩
def claim72 : Claim := (0xfffffffefffffffcfffeffeefefaee00fffffffefffffffcfffeffeefefaee00fffffffefffffffcfffeffeefefaee00fffffffefffffffcfffeffeefefaee00,g72,8830723556360)

def catalogue : Nat → Claim
  | 0 => claim0
  | 1 => claim1
  | 2 => claim2
  | 3 => claim3
  | 4 => claim4
  | 5 => claim5
  | 6 => claim6
  | 7 => claim7
  | 8 => claim8
  | 9 => claim9
  | 10 => claim10
  | 11 => claim11
  | 12 => claim12
  | 13 => claim13
  | 14 => claim14
  | 15 => claim15
  | 16 => claim16
  | 17 => claim17
  | 18 => claim18
  | 19 => claim19
  | 20 => claim20
  | 21 => claim21
  | 22 => claim22
  | 23 => claim23
  | 24 => claim24
  | 25 => claim25
  | 26 => claim26
  | 27 => claim27
  | 28 => claim28
  | 29 => claim29
  | 30 => claim30
  | 31 => claim31
  | 32 => claim32
  | 33 => claim33
  | 34 => claim34
  | 35 => claim35
  | 36 => claim36
  | 37 => claim37
  | 38 => claim38
  | 39 => claim39
  | 40 => claim40
  | 41 => claim41
  | 42 => claim42
  | 43 => claim43
  | 44 => claim44
  | 45 => claim45
  | 46 => claim46
  | 47 => claim47
  | 48 => claim48
  | 49 => claim49
  | 50 => claim50
  | 51 => claim51
  | 52 => claim52
  | 53 => claim53
  | 54 => claim54
  | 55 => claim55
  | 56 => claim56
  | 57 => claim57
  | 58 => claim58
  | 59 => claim59
  | 60 => claim60
  | 61 => claim61
  | 62 => claim62
  | 63 => claim63
  | 64 => claim64
  | 65 => claim65
  | 66 => claim66
  | 67 => claim67
  | 68 => claim68
  | 69 => claim69
  | 70 => claim70
  | 71 => claim71
  | 72 => claim72
  | _ => claim0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK0 : localCheck claim0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK0 : columnsCheck catalogue 0 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK0 : Matches g0 claim0.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK1 : localCheck claim1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK1 : columnsCheck catalogue 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK1 : Matches g1 claim1.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK2 : localCheck claim2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK2 : columnsCheck catalogue 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK2 : Matches g2 claim2.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK3 : localCheck claim3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK3 : columnsCheck catalogue 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK3 : Matches g3 claim3.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK4 : localCheck claim4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK4 : columnsCheck catalogue 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK4 : Matches g4 claim4.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK5 : localCheck claim5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK5 : columnsCheck catalogue 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK5 : Matches g5 claim5.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK6 : localCheck claim6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK6 : columnsCheck catalogue 6 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK6 : Matches g6 claim6.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK7 : localCheck claim7 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK7 : columnsCheck catalogue 7 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK7 : Matches g7 claim7.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK8 : localCheck claim8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK8 : columnsCheck catalogue 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK8 : Matches g8 claim8.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK9 : localCheck claim9 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK9 : columnsCheck catalogue 9 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK9 : Matches g9 claim9.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK10 : localCheck claim10 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK10 : columnsCheck catalogue 10 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK10 : Matches g10 claim10.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK11 : localCheck claim11 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK11 : columnsCheck catalogue 11 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK11 : Matches g11 claim11.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK12 : localCheck claim12 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK12 : columnsCheck catalogue 12 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK12 : Matches g12 claim12.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK13 : localCheck claim13 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK13 : columnsCheck catalogue 13 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK13 : Matches g13 claim13.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK14 : localCheck claim14 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK14 : columnsCheck catalogue 14 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK14 : Matches g14 claim14.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK15 : localCheck claim15 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK15 : columnsCheck catalogue 15 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK15 : Matches g15 claim15.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK16 : localCheck claim16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK16 : columnsCheck catalogue 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK16 : Matches g16 claim16.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK17 : localCheck claim17 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK17 : columnsCheck catalogue 17 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK17 : Matches g17 claim17.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK18 : localCheck claim18 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK18 : columnsCheck catalogue 18 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK18 : Matches g18 claim18.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK19 : localCheck claim19 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK19 : columnsCheck catalogue 19 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK19 : Matches g19 claim19.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK20 : localCheck claim20 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK20 : columnsCheck catalogue 20 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK20 : Matches g20 claim20.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK21 : localCheck claim21 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK21 : columnsCheck catalogue 21 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK21 : Matches g21 claim21.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK22 : localCheck claim22 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK22 : columnsCheck catalogue 22 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK22 : Matches g22 claim22.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK23 : localCheck claim23 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK23 : columnsCheck catalogue 23 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK23 : Matches g23 claim23.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK24 : localCheck claim24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK24 : columnsCheck catalogue 24 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK24 : Matches g24 claim24.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK25 : localCheck claim25 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK25 : columnsCheck catalogue 25 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK25 : Matches g25 claim25.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK26 : localCheck claim26 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK26 : columnsCheck catalogue 26 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK26 : Matches g26 claim26.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK27 : localCheck claim27 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK27 : columnsCheck catalogue 27 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK27 : Matches g27 claim27.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK28 : localCheck claim28 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK28 : columnsCheck catalogue 28 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK28 : Matches g28 claim28.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK29 : localCheck claim29 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK29 : columnsCheck catalogue 29 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK29 : Matches g29 claim29.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK30 : localCheck claim30 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK30 : columnsCheck catalogue 30 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK30 : Matches g30 claim30.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK31 : localCheck claim31 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK31 : columnsCheck catalogue 31 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK31 : Matches g31 claim31.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK32 : localCheck claim32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK32 : columnsCheck catalogue 32 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK32 : Matches g32 claim32.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK33 : localCheck claim33 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK33 : columnsCheck catalogue 33 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK33 : Matches g33 claim33.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK34 : localCheck claim34 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK34 : columnsCheck catalogue 34 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK34 : Matches g34 claim34.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK35 : localCheck claim35 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK35 : columnsCheck catalogue 35 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK35 : Matches g35 claim35.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK36 : localCheck claim36 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK36 : columnsCheck catalogue 36 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK36 : Matches g36 claim36.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK37 : localCheck claim37 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK37 : columnsCheck catalogue 37 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK37 : Matches g37 claim37.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK38 : localCheck claim38 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK38 : columnsCheck catalogue 38 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK38 : Matches g38 claim38.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK39 : localCheck claim39 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK39 : columnsCheck catalogue 39 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK39 : Matches g39 claim39.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK40 : localCheck claim40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK40 : columnsCheck catalogue 40 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK40 : Matches g40 claim40.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK41 : localCheck claim41 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK41 : columnsCheck catalogue 41 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK41 : Matches g41 claim41.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK42 : localCheck claim42 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK42 : columnsCheck catalogue 42 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK42 : Matches g42 claim42.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK43 : localCheck claim43 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK43 : columnsCheck catalogue 43 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK43 : Matches g43 claim43.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK44 : localCheck claim44 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK44 : columnsCheck catalogue 44 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK44 : Matches g44 claim44.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK45 : localCheck claim45 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK45 : columnsCheck catalogue 45 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK45 : Matches g45 claim45.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK46 : localCheck claim46 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK46 : columnsCheck catalogue 46 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK46 : Matches g46 claim46.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK47 : localCheck claim47 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK47 : columnsCheck catalogue 47 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK47 : Matches g47 claim47.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK48 : localCheck claim48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK48 : columnsCheck catalogue 48 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK48 : Matches g48 claim48.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK49 : localCheck claim49 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK49 : columnsCheck catalogue 49 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK49 : Matches g49 claim49.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK50 : localCheck claim50 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK50 : columnsCheck catalogue 50 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK50 : Matches g50 claim50.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK51 : localCheck claim51 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK51 : columnsCheck catalogue 51 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK51 : Matches g51 claim51.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK52 : localCheck claim52 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK52 : columnsCheck catalogue 52 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK52 : Matches g52 claim52.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK53 : localCheck claim53 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK53 : columnsCheck catalogue 53 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK53 : Matches g53 claim53.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK54 : localCheck claim54 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK54 : columnsCheck catalogue 54 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK54 : Matches g54 claim54.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK55 : localCheck claim55 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK55 : columnsCheck catalogue 55 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK55 : Matches g55 claim55.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK56 : localCheck claim56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK56 : columnsCheck catalogue 56 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK56 : Matches g56 claim56.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK57 : localCheck claim57 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK57 : columnsCheck catalogue 57 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK57 : Matches g57 claim57.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK58 : localCheck claim58 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK58 : columnsCheck catalogue 58 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK58 : Matches g58 claim58.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK59 : localCheck claim59 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK59 : columnsCheck catalogue 59 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK59 : Matches g59 claim59.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK60 : localCheck claim60 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK60 : columnsCheck catalogue 60 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK60 : Matches g60 claim60.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK61 : localCheck claim61 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK61 : columnsCheck catalogue 61 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK61 : Matches g61 claim61.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK62 : localCheck claim62 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK62 : columnsCheck catalogue 62 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK62 : Matches g62 claim62.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK63 : localCheck claim63 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK63 : columnsCheck catalogue 63 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK63 : Matches g63 claim63.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK64 : localCheck claim64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK64 : columnsCheck catalogue 64 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK64 : Matches g64 claim64.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK65 : localCheck claim65 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK65 : columnsCheck catalogue 65 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK65 : Matches g65 claim65.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK66 : localCheck claim66 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK66 : columnsCheck catalogue 66 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK66 : Matches g66 claim66.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK67 : localCheck claim67 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK67 : columnsCheck catalogue 67 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK67 : Matches g67 claim67.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK68 : localCheck claim68 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK68 : columnsCheck catalogue 68 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK68 : Matches g68 claim68.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK69 : localCheck claim69 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK69 : columnsCheck catalogue 69 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK69 : Matches g69 claim69.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK70 : localCheck claim70 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK70 : columnsCheck catalogue 70 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK70 : Matches g70 claim70.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK71 : localCheck claim71 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK71 : columnsCheck catalogue 71 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK71 : Matches g71 claim71.1 := by unfold Matches properPairs; decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem localOK72 : localCheck claim72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem colsOK72 : columnsCheck catalogue 72 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem pairsOK72 : Matches g72 claim72.1 := by unfold Matches properPairs; decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c0_3_0 : checks g0 claim0.1 3 0 1 = true := by decide +kernel
theorem rows0 : ∀ k ≤ g0.cap, checks g0 claim0.1 k 0 (g0.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c0_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c1_3_0 : checks g1 claim1.1 3 0 1 = true := by decide +kernel
theorem rows1 : ∀ k ≤ g1.cap, checks g1 claim1.1 k 0 (g1.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c1_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c2_3_0 : checks g2 claim2.1 3 0 1 = true := by decide +kernel
theorem rows2 : ∀ k ≤ g2.cap, checks g2 claim2.1 k 0 (g2.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c2_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c3_3_0 : checks g3 claim3.1 3 0 1 = true := by decide +kernel
theorem rows3 : ∀ k ≤ g3.cap, checks g3 claim3.1 k 0 (g3.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c3_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c4_3_0 : checks g4 claim4.1 3 0 1 = true := by decide +kernel
theorem rows4 : ∀ k ≤ g4.cap, checks g4 claim4.1 k 0 (g4.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c4_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c5_3_0 : checks g5 claim5.1 3 0 1 = true := by decide +kernel
theorem rows5 : ∀ k ≤ g5.cap, checks g5 claim5.1 k 0 (g5.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c5_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c6_3_0 : checks g6 claim6.1 3 0 1 = true := by decide +kernel
theorem rows6 : ∀ k ≤ g6.cap, checks g6 claim6.1 k 0 (g6.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c6_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c7_3_0 : checks g7 claim7.1 3 0 1 = true := by decide +kernel
theorem rows7 : ∀ k ≤ g7.cap, checks g7 claim7.1 k 0 (g7.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c7_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c8_3_0 : checks g8 claim8.1 3 0 1 = true := by decide +kernel
theorem rows8 : ∀ k ≤ g8.cap, checks g8 claim8.1 k 0 (g8.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c8_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c9_4_0 : checks g9 claim9.1 4 0 1 = true := by decide +kernel
theorem rows9 : ∀ k ≤ g9.cap, checks g9 claim9.1 k 0 (g9.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c9_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c10_4_0 : checks g10 claim10.1 4 0 1 = true := by decide +kernel
theorem rows10 : ∀ k ≤ g10.cap, checks g10 claim10.1 k 0 (g10.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c10_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c11_4_0 : checks g11 claim11.1 4 0 1 = true := by decide +kernel
theorem rows11 : ∀ k ≤ g11.cap, checks g11 claim11.1 k 0 (g11.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c11_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c12_4_0 : checks g12 claim12.1 4 0 1 = true := by decide +kernel
theorem rows12 : ∀ k ≤ g12.cap, checks g12 claim12.1 k 0 (g12.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c12_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c13_4_0 : checks g13 claim13.1 4 0 1 = true := by decide +kernel
theorem rows13 : ∀ k ≤ g13.cap, checks g13 claim13.1 k 0 (g13.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c13_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c14_3_0 : checks g14 claim14.1 3 0 1 = true := by decide +kernel
theorem rows14 : ∀ k ≤ g14.cap, checks g14 claim14.1 k 0 (g14.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c14_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c15_3_0 : checks g15 claim15.1 3 0 1 = true := by decide +kernel
theorem rows15 : ∀ k ≤ g15.cap, checks g15 claim15.1 k 0 (g15.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c15_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c16_4_0 : checks g16 claim16.1 4 0 1 = true := by decide +kernel
theorem rows16 : ∀ k ≤ g16.cap, checks g16 claim16.1 k 0 (g16.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c16_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c17_4_0 : checks g17 claim17.1 4 0 1 = true := by decide +kernel
theorem rows17 : ∀ k ≤ g17.cap, checks g17 claim17.1 k 0 (g17.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c17_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c18_3_0 : checks g18 claim18.1 3 0 1 = true := by decide +kernel
theorem rows18 : ∀ k ≤ g18.cap, checks g18 claim18.1 k 0 (g18.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c18_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c19_3_0 : checks g19 claim19.1 3 0 1 = true := by decide +kernel
theorem rows19 : ∀ k ≤ g19.cap, checks g19 claim19.1 k 0 (g19.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c19_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c20_3_0 : checks g20 claim20.1 3 0 1 = true := by decide +kernel
theorem rows20 : ∀ k ≤ g20.cap, checks g20 claim20.1 k 0 (g20.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c20_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c21_4_0 : checks g21 claim21.1 4 0 1 = true := by decide +kernel
theorem rows21 : ∀ k ≤ g21.cap, checks g21 claim21.1 k 0 (g21.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c21_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c22_4_0 : checks g22 claim22.1 4 0 1 = true := by decide +kernel
theorem rows22 : ∀ k ≤ g22.cap, checks g22 claim22.1 k 0 (g22.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c22_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c23_4_0 : checks g23 claim23.1 4 0 1 = true := by decide +kernel
theorem rows23 : ∀ k ≤ g23.cap, checks g23 claim23.1 k 0 (g23.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c23_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c24_4_0 : checks g24 claim24.1 4 0 1 = true := by decide +kernel
theorem rows24 : ∀ k ≤ g24.cap, checks g24 claim24.1 k 0 (g24.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c24_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c25_3_0 : checks g25 claim25.1 3 0 1 = true := by decide +kernel
theorem rows25 : ∀ k ≤ g25.cap, checks g25 claim25.1 k 0 (g25.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => c25_3_0
  | _+4,h => by change _ ≤ 3 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c26_4_0 : checks g26 claim26.1 4 0 1 = true := by decide +kernel
theorem rows26 : ∀ k ≤ g26.cap, checks g26 claim26.1 k 0 (g26.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c26_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c27_4_0 : checks g27 claim27.1 4 0 1 = true := by decide +kernel
theorem rows27 : ∀ k ≤ g27.cap, checks g27 claim27.1 k 0 (g27.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c27_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c28_4_0 : checks g28 claim28.1 4 0 1 = true := by decide +kernel
theorem rows28 : ∀ k ≤ g28.cap, checks g28 claim28.1 k 0 (g28.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c28_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c29_4_0 : checks g29 claim29.1 4 0 1 = true := by decide +kernel
theorem rows29 : ∀ k ≤ g29.cap, checks g29 claim29.1 k 0 (g29.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c29_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c30_4_0 : checks g30 claim30.1 4 0 1 = true := by decide +kernel
theorem rows30 : ∀ k ≤ g30.cap, checks g30 claim30.1 k 0 (g30.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c30_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c31_4_0 : checks g31 claim31.1 4 0 1 = true := by decide +kernel
theorem rows31 : ∀ k ≤ g31.cap, checks g31 claim31.1 k 0 (g31.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c31_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c32_4_0 : checks g32 claim32.1 4 0 1 = true := by decide +kernel
theorem rows32 : ∀ k ≤ g32.cap, checks g32 claim32.1 k 0 (g32.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c32_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c33_4_0 : checks g33 claim33.1 4 0 1 = true := by decide +kernel
theorem rows33 : ∀ k ≤ g33.cap, checks g33 claim33.1 k 0 (g33.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c33_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c34_4_0 : checks g34 claim34.1 4 0 1 = true := by decide +kernel
theorem rows34 : ∀ k ≤ g34.cap, checks g34 claim34.1 k 0 (g34.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c34_4_0
  | _+5,h => by change _ ≤ 4 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c35_5_0 : checks g35 claim35.1 5 0 1 = true := by decide +kernel
theorem rows35 : ∀ k ≤ g35.cap, checks g35 claim35.1 k 0 (g35.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c35_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c36_6_0 : checks g36 claim36.1 6 0 1 = true := by decide +kernel
theorem rows36 : ∀ k ≤ g36.cap, checks g36 claim36.1 k 0 (g36.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => c36_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c37_4_0 : checks g37 claim37.1 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c37_5_0 : checks g37 claim37.1 5 0 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c37_6_0 : checks g37 claim37.1 6 0 1 = true := by decide +kernel
theorem rows37 : ∀ k ≤ g37.cap, checks g37 claim37.1 k 0 (g37.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c37_4_0
  | 5,_ => c37_5_0
  | 6,_ => c37_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c38_4_0 : checks g38 claim38.1 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c38_5_0 : checks g38 claim38.1 5 0 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c38_6_0 : checks g38 claim38.1 6 0 1 = true := by decide +kernel
theorem rows38 : ∀ k ≤ g38.cap, checks g38 claim38.1 k 0 (g38.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c38_4_0
  | 5,_ => c38_5_0
  | 6,_ => c38_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c39_5_0 : checks g39 claim39.1 5 0 1 = true := by decide +kernel
theorem rows39 : ∀ k ≤ g39.cap, checks g39 claim39.1 k 0 (g39.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c39_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c40_5_0 : checks g40 claim40.1 5 0 1 = true := by decide +kernel
theorem rows40 : ∀ k ≤ g40.cap, checks g40 claim40.1 k 0 (g40.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c40_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c41_5_0 : checks g41 claim41.1 5 0 1 = true := by decide +kernel
theorem rows41 : ∀ k ≤ g41.cap, checks g41 claim41.1 k 0 (g41.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c41_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c42_5_0 : checks g42 claim42.1 5 0 1 = true := by decide +kernel
theorem rows42 : ∀ k ≤ g42.cap, checks g42 claim42.1 k 0 (g42.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c42_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c43_4_0 : checks g43 claim43.1 4 0 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c43_5_0 : checks g43 claim43.1 5 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c43_5_8 : checks g43 claim43.1 5 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c43_6_0 : checks g43 claim43.1 6 0 1 = true := by decide +kernel
theorem rows43 : ∀ k ≤ g43.cap, checks g43 claim43.1 k 0 (g43.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c43_4_0
  | 5,_ => (@checks_merge g43 claim43.1 5 0 8 2 c43_5_0 c43_5_8)
  | 6,_ => c43_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c44_4_0 : checks g44 claim44.1 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c44_5_0 : checks g44 claim44.1 5 0 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c44_6_0 : checks g44 claim44.1 6 0 1 = true := by decide +kernel
theorem rows44 : ∀ k ≤ g44.cap, checks g44 claim44.1 k 0 (g44.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c44_4_0
  | 5,_ => c44_5_0
  | 6,_ => c44_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c45_5_0 : checks g45 claim45.1 5 0 1 = true := by decide +kernel
theorem rows45 : ∀ k ≤ g45.cap, checks g45 claim45.1 k 0 (g45.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c45_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c46_4_0 : checks g46 claim46.1 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c46_5_0 : checks g46 claim46.1 5 0 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c46_6_0 : checks g46 claim46.1 6 0 1 = true := by decide +kernel
theorem rows46 : ∀ k ≤ g46.cap, checks g46 claim46.1 k 0 (g46.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c46_4_0
  | 5,_ => c46_5_0
  | 6,_ => c46_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c47_5_0 : checks g47 claim47.1 5 0 1 = true := by decide +kernel
theorem rows47 : ∀ k ≤ g47.cap, checks g47 claim47.1 k 0 (g47.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c47_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c48_5_0 : checks g48 claim48.1 5 0 1 = true := by decide +kernel
theorem rows48 : ∀ k ≤ g48.cap, checks g48 claim48.1 k 0 (g48.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c48_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c49_5_0 : checks g49 claim49.1 5 0 1 = true := by decide +kernel
theorem rows49 : ∀ k ≤ g49.cap, checks g49 claim49.1 k 0 (g49.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c49_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c50_5_0 : checks g50 claim50.1 5 0 1 = true := by decide +kernel
theorem rows50 : ∀ k ≤ g50.cap, checks g50 claim50.1 k 0 (g50.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c50_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c51_5_0 : checks g51 claim51.1 5 0 1 = true := by decide +kernel
theorem rows51 : ∀ k ≤ g51.cap, checks g51 claim51.1 k 0 (g51.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c51_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c52_5_0 : checks g52 claim52.1 5 0 1 = true := by decide +kernel
theorem rows52 : ∀ k ≤ g52.cap, checks g52 claim52.1 k 0 (g52.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c52_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c53_4_0 : checks g53 claim53.1 4 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c53_5_0 : checks g53 claim53.1 5 0 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c53_6_0 : checks g53 claim53.1 6 0 1 = true := by decide +kernel
theorem rows53 : ∀ k ≤ g53.cap, checks g53 claim53.1 k 0 (g53.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => c53_4_0
  | 5,_ => c53_5_0
  | 6,_ => c53_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c54_5_0 : checks g54 claim54.1 5 0 1 = true := by decide +kernel
theorem rows54 : ∀ k ≤ g54.cap, checks g54 claim54.1 k 0 (g54.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c54_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_4_0 : checks g55 claim55.1 4 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_4_8 : checks g55 claim55.1 4 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_4_16 : checks g55 claim55.1 4 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_5_0 : checks g55 claim55.1 5 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_5_8 : checks g55 claim55.1 5 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_5_16 : checks g55 claim55.1 5 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_5_24 : checks g55 claim55.1 5 24 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_5_32 : checks g55 claim55.1 5 32 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_5_40 : checks g55 claim55.1 5 40 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_5_48 : checks g55 claim55.1 5 48 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_6_0 : checks g55 claim55.1 6 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_6_8 : checks g55 claim55.1 6 8 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c55_7_0 : checks g55 claim55.1 7 0 1 = true := by decide +kernel
theorem rows55 : ∀ k ≤ g55.cap, checks g55 claim55.1 k 0 (g55.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => (@checks_merge g55 claim55.1 4 0 8 16 c55_4_0 (@checks_merge g55 claim55.1 4 8 8 8 c55_4_8 c55_4_16))
  | 5,_ => (@checks_merge g55 claim55.1 5 0 24 28 (@checks_merge g55 claim55.1 5 0 8 16 c55_5_0 (@checks_merge g55 claim55.1 5 8 8 8 c55_5_8 c55_5_16)) (@checks_merge g55 claim55.1 5 24 16 12 (@checks_merge g55 claim55.1 5 24 8 8 c55_5_24 c55_5_32) (@checks_merge g55 claim55.1 5 40 8 4 c55_5_40 c55_5_48)))
  | 6,_ => (@checks_merge g55 claim55.1 6 0 8 4 c55_6_0 c55_6_8)
  | 7,_ => c55_7_0
  | _+8,h => by change _ ≤ 7 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c56_5_0 : checks g56 claim56.1 5 0 1 = true := by decide +kernel
theorem rows56 : ∀ k ≤ g56.cap, checks g56 claim56.1 k 0 (g56.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c56_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c57_5_0 : checks g57 claim57.1 5 0 1 = true := by decide +kernel
theorem rows57 : ∀ k ≤ g57.cap, checks g57 claim57.1 k 0 (g57.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c57_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c58_5_0 : checks g58 claim58.1 5 0 1 = true := by decide +kernel
theorem rows58 : ∀ k ≤ g58.cap, checks g58 claim58.1 k 0 (g58.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c58_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c59_5_0 : checks g59 claim59.1 5 0 1 = true := by decide +kernel
theorem rows59 : ∀ k ≤ g59.cap, checks g59 claim59.1 k 0 (g59.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c59_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c60_5_0 : checks g60 claim60.1 5 0 1 = true := by decide +kernel
theorem rows60 : ∀ k ≤ g60.cap, checks g60 claim60.1 k 0 (g60.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c60_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c61_5_0 : checks g61 claim61.1 5 0 1 = true := by decide +kernel
theorem rows61 : ∀ k ≤ g61.cap, checks g61 claim61.1 k 0 (g61.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c61_5_0
  | _+6,h => by change _ ≤ 5 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c62_7_0 : checks g62 claim62.1 7 0 1 = true := by decide +kernel
theorem rows62 : ∀ k ≤ g62.cap, checks g62 claim62.1 k 0 (g62.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => c62_7_0
  | _+8,h => by change _ ≤ 7 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c63_7_0 : checks g63 claim63.1 7 0 1 = true := by decide +kernel
theorem rows63 : ∀ k ≤ g63.cap, checks g63 claim63.1 k 0 (g63.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => c63_7_0
  | _+8,h => by change _ ≤ 7 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c64_5_0 : checks g64 claim64.1 5 0 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c64_6_0 : checks g64 claim64.1 6 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c64_6_8 : checks g64 claim64.1 6 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c64_6_16 : checks g64 claim64.1 6 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c64_6_24 : checks g64 claim64.1 6 24 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c64_7_0 : checks g64 claim64.1 7 0 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c64_8_0 : checks g64 claim64.1 8 0 1 = true := by decide +kernel
theorem rows64 : ∀ k ≤ g64.cap, checks g64 claim64.1 k 0 (g64.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => c64_5_0
  | 6,_ => (@checks_merge g64 claim64.1 6 0 16 9 (@checks_merge g64 claim64.1 6 0 8 8 c64_6_0 c64_6_8) (@checks_merge g64 claim64.1 6 16 8 1 c64_6_16 c64_6_24))
  | 7,_ => c64_7_0
  | 8,_ => c64_8_0
  | _+9,h => by change _ ≤ 8 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c65_7_0 : checks g65 claim65.1 7 0 1 = true := by decide +kernel
theorem rows65 : ∀ k ≤ g65.cap, checks g65 claim65.1 k 0 (g65.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => c65_7_0
  | _+8,h => by change _ ≤ 7 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c66_7_0 : checks g66 claim66.1 7 0 1 = true := by decide +kernel
theorem rows66 : ∀ k ≤ g66.cap, checks g66 claim66.1 k 0 (g66.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => c66_7_0
  | _+8,h => by change _ ≤ 7 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c67_8_0 : checks g67 claim67.1 8 0 1 = true := by decide +kernel
theorem rows67 : ∀ k ≤ g67.cap, checks g67 claim67.1 k 0 (g67.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => rfl
  | 8,_ => c67_8_0
  | _+9,h => by change _ ≤ 8 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c68_8_0 : checks g68 claim68.1 8 0 1 = true := by decide +kernel
theorem rows68 : ∀ k ≤ g68.cap, checks g68 claim68.1 k 0 (g68.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => rfl
  | 7,_ => rfl
  | 8,_ => c68_8_0
  | _+9,h => by change _ ≤ 8 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c69_6_0 : checks g69 claim69.1 6 0 1 = true := by decide +kernel
theorem rows69 : ∀ k ≤ g69.cap, checks g69 claim69.1 k 0 (g69.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => c69_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c70_6_0 : checks g70 claim70.1 6 0 1 = true := by decide +kernel
theorem rows70 : ∀ k ≤ g70.cap, checks g70 claim70.1 k 0 (g70.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => c70_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c71_6_0 : checks g71 claim71.1 6 0 1 = true := by decide +kernel
theorem rows71 : ∀ k ≤ g71.cap, checks g71 claim71.1 k 0 (g71.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => c71_6_0
  | _+7,h => by change _ ≤ 6 at h; omega
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_6_0 : checks g72 claim72.1 6 0 5 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_0 : checks g72 claim72.1 7 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_8 : checks g72 claim72.1 7 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_16 : checks g72 claim72.1 7 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_24 : checks g72 claim72.1 7 24 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_32 : checks g72 claim72.1 7 32 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_40 : checks g72 claim72.1 7 40 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_48 : checks g72 claim72.1 7 48 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_56 : checks g72 claim72.1 7 56 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_64 : checks g72 claim72.1 7 64 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_72 : checks g72 claim72.1 7 72 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_80 : checks g72 claim72.1 7 80 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_88 : checks g72 claim72.1 7 88 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_96 : checks g72 claim72.1 7 96 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_7_104 : checks g72 claim72.1 7 104 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_0 : checks g72 claim72.1 8 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_8 : checks g72 claim72.1 8 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_16 : checks g72 claim72.1 8 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_24 : checks g72 claim72.1 8 24 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_32 : checks g72 claim72.1 8 32 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_40 : checks g72 claim72.1 8 40 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_48 : checks g72 claim72.1 8 48 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_56 : checks g72 claim72.1 8 56 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_64 : checks g72 claim72.1 8 64 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_72 : checks g72 claim72.1 8 72 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_80 : checks g72 claim72.1 8 80 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_88 : checks g72 claim72.1 8 88 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_96 : checks g72 claim72.1 8 96 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_104 : checks g72 claim72.1 8 104 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_112 : checks g72 claim72.1 8 112 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_120 : checks g72 claim72.1 8 120 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_128 : checks g72 claim72.1 8 128 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_136 : checks g72 claim72.1 8 136 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_144 : checks g72 claim72.1 8 144 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_152 : checks g72 claim72.1 8 152 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_160 : checks g72 claim72.1 8 160 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_168 : checks g72 claim72.1 8 168 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_176 : checks g72 claim72.1 8 176 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_184 : checks g72 claim72.1 8 184 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_192 : checks g72 claim72.1 8 192 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_200 : checks g72 claim72.1 8 200 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_208 : checks g72 claim72.1 8 208 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_216 : checks g72 claim72.1 8 216 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_224 : checks g72 claim72.1 8 224 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_232 : checks g72 claim72.1 8 232 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_240 : checks g72 claim72.1 8 240 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_248 : checks g72 claim72.1 8 248 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_256 : checks g72 claim72.1 8 256 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_264 : checks g72 claim72.1 8 264 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_272 : checks g72 claim72.1 8 272 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_280 : checks g72 claim72.1 8 280 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_288 : checks g72 claim72.1 8 288 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_296 : checks g72 claim72.1 8 296 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_304 : checks g72 claim72.1 8 304 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_312 : checks g72 claim72.1 8 312 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_320 : checks g72 claim72.1 8 320 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_328 : checks g72 claim72.1 8 328 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_336 : checks g72 claim72.1 8 336 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_344 : checks g72 claim72.1 8 344 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_352 : checks g72 claim72.1 8 352 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_8_360 : checks g72 claim72.1 8 360 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_0 : checks g72 claim72.1 9 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_8 : checks g72 claim72.1 9 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_16 : checks g72 claim72.1 9 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_24 : checks g72 claim72.1 9 24 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_32 : checks g72 claim72.1 9 32 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_40 : checks g72 claim72.1 9 40 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_48 : checks g72 claim72.1 9 48 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_56 : checks g72 claim72.1 9 56 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_64 : checks g72 claim72.1 9 64 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_72 : checks g72 claim72.1 9 72 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_80 : checks g72 claim72.1 9 80 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_88 : checks g72 claim72.1 9 88 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_96 : checks g72 claim72.1 9 96 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_104 : checks g72 claim72.1 9 104 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_112 : checks g72 claim72.1 9 112 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_120 : checks g72 claim72.1 9 120 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_128 : checks g72 claim72.1 9 128 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_136 : checks g72 claim72.1 9 136 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_144 : checks g72 claim72.1 9 144 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_152 : checks g72 claim72.1 9 152 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_160 : checks g72 claim72.1 9 160 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_168 : checks g72 claim72.1 9 168 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_176 : checks g72 claim72.1 9 176 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_184 : checks g72 claim72.1 9 184 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_192 : checks g72 claim72.1 9 192 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_200 : checks g72 claim72.1 9 200 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_208 : checks g72 claim72.1 9 208 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_216 : checks g72 claim72.1 9 216 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_224 : checks g72 claim72.1 9 224 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_232 : checks g72 claim72.1 9 232 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_240 : checks g72 claim72.1 9 240 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_248 : checks g72 claim72.1 9 248 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_256 : checks g72 claim72.1 9 256 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_264 : checks g72 claim72.1 9 264 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_272 : checks g72 claim72.1 9 272 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_280 : checks g72 claim72.1 9 280 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_288 : checks g72 claim72.1 9 288 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_296 : checks g72 claim72.1 9 296 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_304 : checks g72 claim72.1 9 304 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_312 : checks g72 claim72.1 9 312 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_320 : checks g72 claim72.1 9 320 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_328 : checks g72 claim72.1 9 328 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_336 : checks g72 claim72.1 9 336 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_344 : checks g72 claim72.1 9 344 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_352 : checks g72 claim72.1 9 352 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_360 : checks g72 claim72.1 9 360 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_368 : checks g72 claim72.1 9 368 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_376 : checks g72 claim72.1 9 376 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_384 : checks g72 claim72.1 9 384 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_392 : checks g72 claim72.1 9 392 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_400 : checks g72 claim72.1 9 400 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_9_408 : checks g72 claim72.1 9 408 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_10_0 : checks g72 claim72.1 10 0 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_10_8 : checks g72 claim72.1 10 8 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_10_16 : checks g72 claim72.1 10 16 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_10_24 : checks g72 claim72.1 10 24 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_10_32 : checks g72 claim72.1 10 32 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_10_40 : checks g72 claim72.1 10 40 8 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_10_48 : checks g72 claim72.1 10 48 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem c72_11_0 : checks g72 claim72.1 11 0 1 = true := by decide +kernel
theorem rows72 : ∀ k ≤ g72.cap, checks g72 claim72.1 k 0 (g72.levels k).1 = true := fun k hk => match k, hk with
  | 0,_ => rfl
  | 1,_ => rfl
  | 2,_ => rfl
  | 3,_ => rfl
  | 4,_ => rfl
  | 5,_ => rfl
  | 6,_ => c72_6_0
  | 7,_ => (@checks_merge g72 claim72.1 7 0 56 51 (@checks_merge g72 claim72.1 7 0 24 32 (@checks_merge g72 claim72.1 7 0 8 16 c72_7_0 (@checks_merge g72 claim72.1 7 8 8 8 c72_7_8 c72_7_16)) (@checks_merge g72 claim72.1 7 24 16 16 (@checks_merge g72 claim72.1 7 24 8 8 c72_7_24 c72_7_32) (@checks_merge g72 claim72.1 7 40 8 8 c72_7_40 c72_7_48))) (@checks_merge g72 claim72.1 7 56 24 27 (@checks_merge g72 claim72.1 7 56 8 16 c72_7_56 (@checks_merge g72 claim72.1 7 64 8 8 c72_7_64 c72_7_72)) (@checks_merge g72 claim72.1 7 80 16 11 (@checks_merge g72 claim72.1 7 80 8 8 c72_7_80 c72_7_88) (@checks_merge g72 claim72.1 7 96 8 3 c72_7_96 c72_7_104))))
  | 8,_ => (@checks_merge g72 claim72.1 8 0 184 178 (@checks_merge g72 claim72.1 8 0 88 96 (@checks_merge g72 claim72.1 8 0 40 48 (@checks_merge g72 claim72.1 8 0 16 24 (@checks_merge g72 claim72.1 8 0 8 8 c72_8_0 c72_8_8) (@checks_merge g72 claim72.1 8 16 8 16 c72_8_16 (@checks_merge g72 claim72.1 8 24 8 8 c72_8_24 c72_8_32))) (@checks_merge g72 claim72.1 8 40 24 24 (@checks_merge g72 claim72.1 8 40 8 16 c72_8_40 (@checks_merge g72 claim72.1 8 48 8 8 c72_8_48 c72_8_56)) (@checks_merge g72 claim72.1 8 64 8 16 c72_8_64 (@checks_merge g72 claim72.1 8 72 8 8 c72_8_72 c72_8_80)))) (@checks_merge g72 claim72.1 8 88 48 48 (@checks_merge g72 claim72.1 8 88 24 24 (@checks_merge g72 claim72.1 8 88 8 16 c72_8_88 (@checks_merge g72 claim72.1 8 96 8 8 c72_8_96 c72_8_104)) (@checks_merge g72 claim72.1 8 112 8 16 c72_8_112 (@checks_merge g72 claim72.1 8 120 8 8 c72_8_120 c72_8_128))) (@checks_merge g72 claim72.1 8 136 24 24 (@checks_merge g72 claim72.1 8 136 8 16 c72_8_136 (@checks_merge g72 claim72.1 8 144 8 8 c72_8_144 c72_8_152)) (@checks_merge g72 claim72.1 8 160 8 16 c72_8_160 (@checks_merge g72 claim72.1 8 168 8 8 c72_8_168 c72_8_176))))) (@checks_merge g72 claim72.1 8 184 88 90 (@checks_merge g72 claim72.1 8 184 40 48 (@checks_merge g72 claim72.1 8 184 16 24 (@checks_merge g72 claim72.1 8 184 8 8 c72_8_184 c72_8_192) (@checks_merge g72 claim72.1 8 200 8 16 c72_8_200 (@checks_merge g72 claim72.1 8 208 8 8 c72_8_208 c72_8_216))) (@checks_merge g72 claim72.1 8 224 24 24 (@checks_merge g72 claim72.1 8 224 8 16 c72_8_224 (@checks_merge g72 claim72.1 8 232 8 8 c72_8_232 c72_8_240)) (@checks_merge g72 claim72.1 8 248 8 16 c72_8_248 (@checks_merge g72 claim72.1 8 256 8 8 c72_8_256 c72_8_264)))) (@checks_merge g72 claim72.1 8 272 48 42 (@checks_merge g72 claim72.1 8 272 24 24 (@checks_merge g72 claim72.1 8 272 8 16 c72_8_272 (@checks_merge g72 claim72.1 8 280 8 8 c72_8_280 c72_8_288)) (@checks_merge g72 claim72.1 8 296 8 16 c72_8_296 (@checks_merge g72 claim72.1 8 304 8 8 c72_8_304 c72_8_312))) (@checks_merge g72 claim72.1 8 320 24 18 (@checks_merge g72 claim72.1 8 320 8 16 c72_8_320 (@checks_merge g72 claim72.1 8 328 8 8 c72_8_328 c72_8_336)) (@checks_merge g72 claim72.1 8 344 8 10 c72_8_344 (@checks_merge g72 claim72.1 8 352 8 2 c72_8_352 c72_8_360))))))
  | 9,_ => (@checks_merge g72 claim72.1 9 0 208 203 (@checks_merge g72 claim72.1 9 0 104 104 (@checks_merge g72 claim72.1 9 0 48 56 (@checks_merge g72 claim72.1 9 0 24 24 (@checks_merge g72 claim72.1 9 0 8 16 c72_9_0 (@checks_merge g72 claim72.1 9 8 8 8 c72_9_8 c72_9_16)) (@checks_merge g72 claim72.1 9 24 8 16 c72_9_24 (@checks_merge g72 claim72.1 9 32 8 8 c72_9_32 c72_9_40))) (@checks_merge g72 claim72.1 9 48 24 32 (@checks_merge g72 claim72.1 9 48 8 16 c72_9_48 (@checks_merge g72 claim72.1 9 56 8 8 c72_9_56 c72_9_64)) (@checks_merge g72 claim72.1 9 72 16 16 (@checks_merge g72 claim72.1 9 72 8 8 c72_9_72 c72_9_80) (@checks_merge g72 claim72.1 9 88 8 8 c72_9_88 c72_9_96)))) (@checks_merge g72 claim72.1 9 104 48 56 (@checks_merge g72 claim72.1 9 104 24 24 (@checks_merge g72 claim72.1 9 104 8 16 c72_9_104 (@checks_merge g72 claim72.1 9 112 8 8 c72_9_112 c72_9_120)) (@checks_merge g72 claim72.1 9 128 8 16 c72_9_128 (@checks_merge g72 claim72.1 9 136 8 8 c72_9_136 c72_9_144))) (@checks_merge g72 claim72.1 9 152 24 32 (@checks_merge g72 claim72.1 9 152 8 16 c72_9_152 (@checks_merge g72 claim72.1 9 160 8 8 c72_9_160 c72_9_168)) (@checks_merge g72 claim72.1 9 176 16 16 (@checks_merge g72 claim72.1 9 176 8 8 c72_9_176 c72_9_184) (@checks_merge g72 claim72.1 9 192 8 8 c72_9_192 c72_9_200))))) (@checks_merge g72 claim72.1 9 208 104 99 (@checks_merge g72 claim72.1 9 208 48 56 (@checks_merge g72 claim72.1 9 208 24 24 (@checks_merge g72 claim72.1 9 208 8 16 c72_9_208 (@checks_merge g72 claim72.1 9 216 8 8 c72_9_216 c72_9_224)) (@checks_merge g72 claim72.1 9 232 8 16 c72_9_232 (@checks_merge g72 claim72.1 9 240 8 8 c72_9_240 c72_9_248))) (@checks_merge g72 claim72.1 9 256 24 32 (@checks_merge g72 claim72.1 9 256 8 16 c72_9_256 (@checks_merge g72 claim72.1 9 264 8 8 c72_9_264 c72_9_272)) (@checks_merge g72 claim72.1 9 280 16 16 (@checks_merge g72 claim72.1 9 280 8 8 c72_9_280 c72_9_288) (@checks_merge g72 claim72.1 9 296 8 8 c72_9_296 c72_9_304)))) (@checks_merge g72 claim72.1 9 312 48 51 (@checks_merge g72 claim72.1 9 312 24 24 (@checks_merge g72 claim72.1 9 312 8 16 c72_9_312 (@checks_merge g72 claim72.1 9 320 8 8 c72_9_320 c72_9_328)) (@checks_merge g72 claim72.1 9 336 8 16 c72_9_336 (@checks_merge g72 claim72.1 9 344 8 8 c72_9_344 c72_9_352))) (@checks_merge g72 claim72.1 9 360 24 27 (@checks_merge g72 claim72.1 9 360 8 16 c72_9_360 (@checks_merge g72 claim72.1 9 368 8 8 c72_9_368 c72_9_376)) (@checks_merge g72 claim72.1 9 384 16 11 (@checks_merge g72 claim72.1 9 384 8 8 c72_9_384 c72_9_392) (@checks_merge g72 claim72.1 9 400 8 3 c72_9_400 c72_9_408))))))
  | 10,_ => (@checks_merge g72 claim72.1 10 0 24 26 (@checks_merge g72 claim72.1 10 0 8 16 c72_10_0 (@checks_merge g72 claim72.1 10 8 8 8 c72_10_8 c72_10_16)) (@checks_merge g72 claim72.1 10 24 16 10 (@checks_merge g72 claim72.1 10 24 8 8 c72_10_24 c72_10_32) (@checks_merge g72 claim72.1 10 40 8 2 c72_10_40 c72_10_48)))
  | 11,_ => c72_11_0
  | _+12,h => by change _ ≤ 11 at h; omega

theorem ready0 : ∀ j < 0, Resolved (catalogue j) := fun j h => (Nat.not_lt_zero j h).elim
theorem resolved0 : Resolved (catalogue 0) := resolve (i:=0) ready0 localOK0 pairsOK0 colsOK0 rows0
theorem ready1 : ∀ j < 1, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=0) ready0 resolved0
theorem resolved1 : Resolved (catalogue 1) := resolve (i:=1) ready1 localOK1 pairsOK1 colsOK1 rows1
theorem ready2 : ∀ j < 2, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=1) ready1 resolved1
theorem resolved2 : Resolved (catalogue 2) := resolve (i:=2) ready2 localOK2 pairsOK2 colsOK2 rows2
theorem ready3 : ∀ j < 3, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=2) ready2 resolved2
theorem resolved3 : Resolved (catalogue 3) := resolve (i:=3) ready3 localOK3 pairsOK3 colsOK3 rows3
theorem ready4 : ∀ j < 4, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=3) ready3 resolved3
theorem resolved4 : Resolved (catalogue 4) := resolve (i:=4) ready4 localOK4 pairsOK4 colsOK4 rows4
theorem ready5 : ∀ j < 5, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=4) ready4 resolved4
theorem resolved5 : Resolved (catalogue 5) := resolve (i:=5) ready5 localOK5 pairsOK5 colsOK5 rows5
theorem ready6 : ∀ j < 6, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=5) ready5 resolved5
theorem resolved6 : Resolved (catalogue 6) := resolve (i:=6) ready6 localOK6 pairsOK6 colsOK6 rows6
theorem ready7 : ∀ j < 7, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=6) ready6 resolved6
theorem resolved7 : Resolved (catalogue 7) := resolve (i:=7) ready7 localOK7 pairsOK7 colsOK7 rows7
theorem ready8 : ∀ j < 8, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=7) ready7 resolved7
theorem resolved8 : Resolved (catalogue 8) := resolve (i:=8) ready8 localOK8 pairsOK8 colsOK8 rows8
theorem ready9 : ∀ j < 9, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=8) ready8 resolved8
theorem resolved9 : Resolved (catalogue 9) := resolve (i:=9) ready9 localOK9 pairsOK9 colsOK9 rows9
theorem ready10 : ∀ j < 10, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=9) ready9 resolved9
theorem resolved10 : Resolved (catalogue 10) := resolve (i:=10) ready10 localOK10 pairsOK10 colsOK10 rows10
theorem ready11 : ∀ j < 11, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=10) ready10 resolved10
theorem resolved11 : Resolved (catalogue 11) := resolve (i:=11) ready11 localOK11 pairsOK11 colsOK11 rows11
theorem ready12 : ∀ j < 12, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=11) ready11 resolved11
theorem resolved12 : Resolved (catalogue 12) := resolve (i:=12) ready12 localOK12 pairsOK12 colsOK12 rows12
theorem ready13 : ∀ j < 13, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=12) ready12 resolved12
theorem resolved13 : Resolved (catalogue 13) := resolve (i:=13) ready13 localOK13 pairsOK13 colsOK13 rows13
theorem ready14 : ∀ j < 14, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=13) ready13 resolved13
theorem resolved14 : Resolved (catalogue 14) := resolve (i:=14) ready14 localOK14 pairsOK14 colsOK14 rows14
theorem ready15 : ∀ j < 15, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=14) ready14 resolved14
theorem resolved15 : Resolved (catalogue 15) := resolve (i:=15) ready15 localOK15 pairsOK15 colsOK15 rows15
theorem ready16 : ∀ j < 16, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=15) ready15 resolved15
theorem resolved16 : Resolved (catalogue 16) := resolve (i:=16) ready16 localOK16 pairsOK16 colsOK16 rows16
theorem ready17 : ∀ j < 17, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=16) ready16 resolved16
theorem resolved17 : Resolved (catalogue 17) := resolve (i:=17) ready17 localOK17 pairsOK17 colsOK17 rows17
theorem ready18 : ∀ j < 18, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=17) ready17 resolved17
theorem resolved18 : Resolved (catalogue 18) := resolve (i:=18) ready18 localOK18 pairsOK18 colsOK18 rows18
theorem ready19 : ∀ j < 19, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=18) ready18 resolved18
theorem resolved19 : Resolved (catalogue 19) := resolve (i:=19) ready19 localOK19 pairsOK19 colsOK19 rows19
theorem ready20 : ∀ j < 20, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=19) ready19 resolved19
theorem resolved20 : Resolved (catalogue 20) := resolve (i:=20) ready20 localOK20 pairsOK20 colsOK20 rows20
theorem ready21 : ∀ j < 21, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=20) ready20 resolved20
theorem resolved21 : Resolved (catalogue 21) := resolve (i:=21) ready21 localOK21 pairsOK21 colsOK21 rows21
theorem ready22 : ∀ j < 22, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=21) ready21 resolved21
theorem resolved22 : Resolved (catalogue 22) := resolve (i:=22) ready22 localOK22 pairsOK22 colsOK22 rows22
theorem ready23 : ∀ j < 23, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=22) ready22 resolved22
theorem resolved23 : Resolved (catalogue 23) := resolve (i:=23) ready23 localOK23 pairsOK23 colsOK23 rows23
theorem ready24 : ∀ j < 24, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=23) ready23 resolved23
theorem resolved24 : Resolved (catalogue 24) := resolve (i:=24) ready24 localOK24 pairsOK24 colsOK24 rows24
theorem ready25 : ∀ j < 25, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=24) ready24 resolved24
theorem resolved25 : Resolved (catalogue 25) := resolve (i:=25) ready25 localOK25 pairsOK25 colsOK25 rows25
theorem ready26 : ∀ j < 26, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=25) ready25 resolved25
theorem resolved26 : Resolved (catalogue 26) := resolve (i:=26) ready26 localOK26 pairsOK26 colsOK26 rows26
theorem ready27 : ∀ j < 27, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=26) ready26 resolved26
theorem resolved27 : Resolved (catalogue 27) := resolve (i:=27) ready27 localOK27 pairsOK27 colsOK27 rows27
theorem ready28 : ∀ j < 28, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=27) ready27 resolved27
theorem resolved28 : Resolved (catalogue 28) := resolve (i:=28) ready28 localOK28 pairsOK28 colsOK28 rows28
theorem ready29 : ∀ j < 29, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=28) ready28 resolved28
theorem resolved29 : Resolved (catalogue 29) := resolve (i:=29) ready29 localOK29 pairsOK29 colsOK29 rows29
theorem ready30 : ∀ j < 30, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=29) ready29 resolved29
theorem resolved30 : Resolved (catalogue 30) := resolve (i:=30) ready30 localOK30 pairsOK30 colsOK30 rows30
theorem ready31 : ∀ j < 31, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=30) ready30 resolved30
theorem resolved31 : Resolved (catalogue 31) := resolve (i:=31) ready31 localOK31 pairsOK31 colsOK31 rows31
theorem ready32 : ∀ j < 32, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=31) ready31 resolved31
theorem resolved32 : Resolved (catalogue 32) := resolve (i:=32) ready32 localOK32 pairsOK32 colsOK32 rows32
theorem ready33 : ∀ j < 33, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=32) ready32 resolved32
theorem resolved33 : Resolved (catalogue 33) := resolve (i:=33) ready33 localOK33 pairsOK33 colsOK33 rows33
theorem ready34 : ∀ j < 34, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=33) ready33 resolved33
theorem resolved34 : Resolved (catalogue 34) := resolve (i:=34) ready34 localOK34 pairsOK34 colsOK34 rows34
theorem ready35 : ∀ j < 35, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=34) ready34 resolved34
theorem resolved35 : Resolved (catalogue 35) := resolve (i:=35) ready35 localOK35 pairsOK35 colsOK35 rows35
theorem ready36 : ∀ j < 36, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=35) ready35 resolved35
theorem resolved36 : Resolved (catalogue 36) := resolve (i:=36) ready36 localOK36 pairsOK36 colsOK36 rows36
theorem ready37 : ∀ j < 37, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=36) ready36 resolved36
theorem resolved37 : Resolved (catalogue 37) := resolve (i:=37) ready37 localOK37 pairsOK37 colsOK37 rows37
theorem ready38 : ∀ j < 38, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=37) ready37 resolved37
theorem resolved38 : Resolved (catalogue 38) := resolve (i:=38) ready38 localOK38 pairsOK38 colsOK38 rows38
theorem ready39 : ∀ j < 39, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=38) ready38 resolved38
theorem resolved39 : Resolved (catalogue 39) := resolve (i:=39) ready39 localOK39 pairsOK39 colsOK39 rows39
theorem ready40 : ∀ j < 40, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=39) ready39 resolved39
theorem resolved40 : Resolved (catalogue 40) := resolve (i:=40) ready40 localOK40 pairsOK40 colsOK40 rows40
theorem ready41 : ∀ j < 41, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=40) ready40 resolved40
theorem resolved41 : Resolved (catalogue 41) := resolve (i:=41) ready41 localOK41 pairsOK41 colsOK41 rows41
theorem ready42 : ∀ j < 42, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=41) ready41 resolved41
theorem resolved42 : Resolved (catalogue 42) := resolve (i:=42) ready42 localOK42 pairsOK42 colsOK42 rows42
theorem ready43 : ∀ j < 43, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=42) ready42 resolved42
theorem resolved43 : Resolved (catalogue 43) := resolve (i:=43) ready43 localOK43 pairsOK43 colsOK43 rows43
theorem ready44 : ∀ j < 44, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=43) ready43 resolved43
theorem resolved44 : Resolved (catalogue 44) := resolve (i:=44) ready44 localOK44 pairsOK44 colsOK44 rows44
theorem ready45 : ∀ j < 45, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=44) ready44 resolved44
theorem resolved45 : Resolved (catalogue 45) := resolve (i:=45) ready45 localOK45 pairsOK45 colsOK45 rows45
theorem ready46 : ∀ j < 46, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=45) ready45 resolved45
theorem resolved46 : Resolved (catalogue 46) := resolve (i:=46) ready46 localOK46 pairsOK46 colsOK46 rows46
theorem ready47 : ∀ j < 47, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=46) ready46 resolved46
theorem resolved47 : Resolved (catalogue 47) := resolve (i:=47) ready47 localOK47 pairsOK47 colsOK47 rows47
theorem ready48 : ∀ j < 48, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=47) ready47 resolved47
theorem resolved48 : Resolved (catalogue 48) := resolve (i:=48) ready48 localOK48 pairsOK48 colsOK48 rows48
theorem ready49 : ∀ j < 49, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=48) ready48 resolved48
theorem resolved49 : Resolved (catalogue 49) := resolve (i:=49) ready49 localOK49 pairsOK49 colsOK49 rows49
theorem ready50 : ∀ j < 50, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=49) ready49 resolved49
theorem resolved50 : Resolved (catalogue 50) := resolve (i:=50) ready50 localOK50 pairsOK50 colsOK50 rows50
theorem ready51 : ∀ j < 51, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=50) ready50 resolved50
theorem resolved51 : Resolved (catalogue 51) := resolve (i:=51) ready51 localOK51 pairsOK51 colsOK51 rows51
theorem ready52 : ∀ j < 52, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=51) ready51 resolved51
theorem resolved52 : Resolved (catalogue 52) := resolve (i:=52) ready52 localOK52 pairsOK52 colsOK52 rows52
theorem ready53 : ∀ j < 53, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=52) ready52 resolved52
theorem resolved53 : Resolved (catalogue 53) := resolve (i:=53) ready53 localOK53 pairsOK53 colsOK53 rows53
theorem ready54 : ∀ j < 54, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=53) ready53 resolved53
theorem resolved54 : Resolved (catalogue 54) := resolve (i:=54) ready54 localOK54 pairsOK54 colsOK54 rows54
theorem ready55 : ∀ j < 55, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=54) ready54 resolved54
theorem resolved55 : Resolved (catalogue 55) := resolve (i:=55) ready55 localOK55 pairsOK55 colsOK55 rows55
theorem ready56 : ∀ j < 56, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=55) ready55 resolved55
theorem resolved56 : Resolved (catalogue 56) := resolve (i:=56) ready56 localOK56 pairsOK56 colsOK56 rows56
theorem ready57 : ∀ j < 57, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=56) ready56 resolved56
theorem resolved57 : Resolved (catalogue 57) := resolve (i:=57) ready57 localOK57 pairsOK57 colsOK57 rows57
theorem ready58 : ∀ j < 58, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=57) ready57 resolved57
theorem resolved58 : Resolved (catalogue 58) := resolve (i:=58) ready58 localOK58 pairsOK58 colsOK58 rows58
theorem ready59 : ∀ j < 59, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=58) ready58 resolved58
theorem resolved59 : Resolved (catalogue 59) := resolve (i:=59) ready59 localOK59 pairsOK59 colsOK59 rows59
theorem ready60 : ∀ j < 60, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=59) ready59 resolved59
theorem resolved60 : Resolved (catalogue 60) := resolve (i:=60) ready60 localOK60 pairsOK60 colsOK60 rows60
theorem ready61 : ∀ j < 61, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=60) ready60 resolved60
theorem resolved61 : Resolved (catalogue 61) := resolve (i:=61) ready61 localOK61 pairsOK61 colsOK61 rows61
theorem ready62 : ∀ j < 62, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=61) ready61 resolved61
theorem resolved62 : Resolved (catalogue 62) := resolve (i:=62) ready62 localOK62 pairsOK62 colsOK62 rows62
theorem ready63 : ∀ j < 63, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=62) ready62 resolved62
theorem resolved63 : Resolved (catalogue 63) := resolve (i:=63) ready63 localOK63 pairsOK63 colsOK63 rows63
theorem ready64 : ∀ j < 64, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=63) ready63 resolved63
theorem resolved64 : Resolved (catalogue 64) := resolve (i:=64) ready64 localOK64 pairsOK64 colsOK64 rows64
theorem ready65 : ∀ j < 65, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=64) ready64 resolved64
theorem resolved65 : Resolved (catalogue 65) := resolve (i:=65) ready65 localOK65 pairsOK65 colsOK65 rows65
theorem ready66 : ∀ j < 66, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=65) ready65 resolved65
theorem resolved66 : Resolved (catalogue 66) := resolve (i:=66) ready66 localOK66 pairsOK66 colsOK66 rows66
theorem ready67 : ∀ j < 67, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=66) ready66 resolved66
theorem resolved67 : Resolved (catalogue 67) := resolve (i:=67) ready67 localOK67 pairsOK67 colsOK67 rows67
theorem ready68 : ∀ j < 68, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=67) ready67 resolved67
theorem resolved68 : Resolved (catalogue 68) := resolve (i:=68) ready68 localOK68 pairsOK68 colsOK68 rows68
theorem ready69 : ∀ j < 69, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=68) ready68 resolved68
theorem resolved69 : Resolved (catalogue 69) := resolve (i:=69) ready69 localOK69 pairsOK69 colsOK69 rows69
theorem ready70 : ∀ j < 70, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=69) ready69 resolved69
theorem resolved70 : Resolved (catalogue 70) := resolve (i:=70) ready70 localOK70 pairsOK70 colsOK70 rows70
theorem ready71 : ∀ j < 71, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=70) ready70 resolved70
theorem resolved71 : Resolved (catalogue 71) := resolve (i:=71) ready71 localOK71 pairsOK71 colsOK71 rows71
theorem ready72 : ∀ j < 72, Resolved (catalogue j) := extendResults (book:=catalogue) (i:=71) ready71 resolved71
theorem resolved72 : Resolved (catalogue 72) := resolve (i:=72) ready72 localOK72 pairsOK72 colsOK72 rows72

end PEqualNP.Outside.L_meta_30869_aux.Cert

namespace PEqualNP.Outside.L_meta_30869_aux
open PEqualNP.Outside.L_meta_30869_aux.Base
def target10900 (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 3, 0, 4, 2, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def graph10900 : Sig := 0xfffffffefffffffcfffeffeefefaee00fffffffefffffffcfffeffeefefaee00fffffffefffffffcfffeffeefefaee00fffffffefffffffcfffeffeefefaee00
theorem currentProper : proper graph10900 := by unfold proper; decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem currentTable : ∀ r : Row, bit r graph10900 = target10900 (sampleSeven r) := by decide +kernel
def lowCurrent (i : Fin 7) : Row := Fin.ofNat 512 (1 <<< ([3, 3, 4, 0, 0, 0, 1] : List Nat).getD i.val 0)
def highCurrent (i : Fin 7) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (lowCurrent i).val)
set_option maxHeartbeats 1000000 in
theorem currentRequired :
    (∀ i : Fin 7, bit (lowCurrent i) graph10900 ≠ bit (highCurrent i) graph10900) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (lowCurrent i) (sevenInputs.getD j.val zero) =
      bit (highCurrent i) (sevenInputs.getD j.val zero)) := by decide +kernel
theorem checkedLower : Impossible true graph10900 11 sevenInputs.toFinset := PEqualNP.Outside.L_meta_30869_aux.Cert.resolved72.1
end PEqualNP.Outside.L_meta_30869_aux

namespace PEqualNP.Outside.L_meta_30869_aux.Base
open PEqualNP.CircuitLowerBounds

def paidAtZero (g : Gate) : Bool := !isNot g && !g.inputs.contains 2

private theorem zeroLeft (d : Bool) (x : Sig) :
    prime d zero x = if d then x else zero := by
  apply bit_ext
  intro i
  cases d <;> simp [bit_prime, bit_zero]

private theorem zeroRight (d : Bool) (x : Sig) :
    prime d x zero = if d then x else zero := by
  apply bit_ext
  intro i
  cases d <;> simp [bit_prime, bit_zero]

private theorem gateReadingZero (w : List Sig) (g : Gate)
    (hzero : w.getD 2 zero = zero) (hreader : 2 ∈ g.inputs)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
    Repr true (w.map (nrm true)) (gv w g) := by
  obtain ⟨o, ids⟩ := g
  have prim (d : Bool) :
      Repr true (w.map (nrm true))
        ((ids.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime, bit_zero, bit_one]
    change 2 ∈ ids at hreader
    change ids.length ≤ 2 at hlen
    cases ids with
    | nil => simp at hreader
    | cons i tail =>
      cases tail with
      | nil => simpa only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, unit] using
          (get_rep (u := true) w i)
      | cons j tail =>
        cases tail with
        | cons k rest => simp at hlen
        | nil =>
          simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, unit]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hreader
          rcases hreader with h | h
          · rw [← h, hzero, zeroLeft]
            cases d
            · exact repr_const (Or.inl rfl)
            · exact get_rep w j
          · rw [← h, hzero, zeroRight]
            cases d
            · exact repr_const (Or.inl rfl)
            · exact get_rep w i
  change o = .and ∨ o = .or at hop
  rcases hop with rfl | rfl
  · exact prim false
  · exact prim true

private theorem paidRepresentation (g : Gate) (w : List Sig) (hzero : w.getD 2 zero = zero)
    (legal : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    represented (w.map (nrm true)) (nrm true (gv w g)) ∨
      ((if paidAtZero g then 1 else 0) = 1 ∧ witness true (w.map (nrm true)) (nrm true (gv w g))) := by
  obtain h | ⟨hn, hw⟩ := gate_rep true w g legal (by simp)
  · exact Or.inl h
  by_cases read : 2 ∈ g.inputs
  · have hob : g.op = .and ∨ g.op = .or := by
      have ops := legal.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops
      exact ops.imp_right (fun p => p.resolve_right (fun e => by
        obtain ⟨o, ids⟩ := g
        change o = .not at e
        subst o
        simp [isNot] at hn))
    exact Or.inl (gateReadingZero w g hzero read hob legal.2)
  · exact Or.inr ⟨by simp [paidAtZero, hn, read], hw⟩

theorem extractAtZero {target : Sig} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hsize : 2 < w.length) (hzero : w.getD 2 zero = zero)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm true)) :
    ∃ k S, k ≤ gs.countP paidAtZero ∧ Live true target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm true) := by
  induction gs generalizing w with
  | nil => exact ⟨0, {target}, by simp, Live.stop hp, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have preserve : (w ++ [gv w g]).getD 2 zero = zero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hsize, ← List.getD_eq_getElem?_getD]
      exact hzero
    obtain ⟨k, S, hk, hrun, hsub⟩ := ih (w ++ [gv w g]) (fun a ha => legal a (by simp [ha]))
      (by simp; omega) preserve hout
    rw [List.map_append] at hsub
    obtain ⟨l, T, hl, htail, hT⟩ := pull_gate hrun (paidRepresentation g w hzero (legal g (by simp))) hsub
    exact ⟨l, T, by rw [List.countP_cons]; omega, htail, hT⟩

end PEqualNP.Outside.L_meta_30869_aux.Base

namespace PEqualNP.Outside.L_meta_30869_aux
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_30869_aux.Base

def liftSeven (x : Fin 7 → Bool) : Fin 8 → Bool :=
  ![x 6, x 5, false, x 2, x 0, x 1, x 4, x 3]

def cutInputs : List Sig :=
  [sevenInputs.getD 6 zero, sevenInputs.getD 5 zero, zero, sevenInputs.getD 2 zero,
    sevenInputs.getD 0 zero, sevenInputs.getD 1 zero, sevenInputs.getD 4 zero, sevenInputs.getD 3 zero]

theorem cutSize : cutInputs.length = 8 := rfl

theorem cutZero : cutInputs.getD 2 zero = zero := rfl

set_option maxRecDepth 8192 in
theorem cutMap (r : Row) : cutInputs.map (bit r) = List.ofFn (liftSeven (sampleSeven r)) := by
  have h : List.ofFn (fun i : Fin 8 => cutInputs.getD i.val zero) = cutInputs := rfl
  conv_lhs => rw [← h, List.map_ofFn]
  congr 1
  funext i
  fin_cases i <;> first | rfl | simp [cutInputs, liftSeven, sampleSeven, bit, zero]

theorem cutEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates cutInputs).getD i zero) =
      (C.wires (List.ofFn (liftSeven (sampleSeven r)))).getD i false := by
  rw [← b_read, execute_bits _ _ _ (fun g hg => (h g hg).1), cutMap]
  rfl

set_option maxRecDepth 8192 in
theorem cutPlain : cutInputs.all plainWord = true := by decide +kernel

set_option maxRecDepth 8192 in
theorem cutCover : cutInputs.all (fun w => sevenInputs.contains w || w == zero) = true := by
  decide +kernel

theorem checkedCofactor
    (lower : Impossible true graph10900 11 sevenInputs.toFinset)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn (liftSeven x)) = target10900 x) :
    12 ≤ C.gates.countP paidAtZero := by
  have goalEq : (execute C.gates cutInputs).getD C.output zero = graph10900 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    exact (cutEval C legal C.output r).trans ((computes (sampleSeven r)).trans (currentTable r).symm)
  have out := get_rep (u := true) (execute C.gates cutInputs) C.output
  rw [goalEq] at out
  unfold Base.Repr at out
  have pg : bit 0 graph10900 = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k, S, hk, run, sub⟩ := extractAtZero C.gates cutInputs legal (by rw [cutSize]; omega) cutZero
    currentProper (out.resolve_right (fun h => h currentProper))
  rw [nrm_map cutPlain] at sub
  have subSeven (a : Sig) (ha : a ∈ S) : a ∈ sevenInputs := by
    have h := (List.all_eq_true.mp cutCover) a (sub a ha)
    have h' : a ∈ sevenInputs ∨ a = zero := by simpa using h
    exact h'.resolve_right (Base.live_proper run a ha).1
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 7, sevenInputs.getD i.val zero = a := by
    rw [← sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (subSeven a h)
    · intro ha
      obtain ⟨i, rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) subSeven (lowCurrent i) (highCurrent i)
        (currentRequired.1 i)
      intro v hv hn
      obtain ⟨j, rfl⟩ := idx v hv
      apply currentRequired.2 i j
      rintro rfl
      exact hn rfl
  by_contra! h
  exact lower k (by omega) (eq ▸ run)

private theorem filterTwo {α : Type} {p : α → Bool} {xs : List α} {a b : α}
    (ha : a ∈ xs) (hb : b ∈ xs) (pa : p a = false) (pb : p b = false) (hne : a ≠ b) :
    xs.countP p + 2 ≤ xs.length := by
  have ma : a ∈ xs.filter (fun g => !p g) := List.mem_filter.mpr ⟨ha, by simp [pa]⟩
  have mb : b ∈ xs.filter (fun g => !p g) := List.mem_filter.mpr ⟨hb, by simp [pb]⟩
  have sized : 2 ≤ (xs.filter (fun g => !p g)).length := by
    generalize h : xs.filter (fun g => !p g) = ys at ma mb ⊢
    cases ys with
    | nil => simp at ma
    | cons c ys =>
      cases ys with
      | nil => simp at ma mb; exact (hne (ma.trans mb.symm)).elim
      | cons d ys => simp
  have counts := List.length_eq_countP_add_countP p (l := xs)
  have negation : (fun a => decide (¬ (p a = true))) = (fun a => !p a) := by
    funext a
    cases p a <;> rfl
  rw [negation, List.countP_eq_length_filter (p := fun g => !p g)] at counts
  omega

theorem cofactorGateCount (gates : List Gate) {u b : Gate}
    (hu : u ∈ gates) (hnot : u.op = .not)
    (hb : b ∈ gates) (hbop : b.op = .and ∨ b.op = .or) (read : 2 ∈ b.inputs) :
    gates.countP paidAtZero + 2 ≤ gates.length := by
  refine filterTwo hu hb ?_ ?_ ?_
  · obtain ⟨o, ids⟩ := u
    change o = .not at hnot
    subst o
    simp [paidAtZero, isNot]
  · simp [paidAtZero, read]
  · intro e
    subst b
    rcases hbop with h | h <;> exact GateOp.noConfusion (hnot.symm.trans h)

end PEqualNP.Outside.L_meta_30869_aux

namespace PEqualNP.Outside.L_meta_30869_aux.Witness

open PEqualNP.CircuitLowerBounds

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

def witness : Circuit := ⟨[⟨.or, [5, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [4, 15]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [7, 15]⟩, ⟨.and, [5, 18]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [13, 20]⟩], 21⟩

theorem witnessFit : ∀ g ∈ witness.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

theorem witnessSize : witness.gates.length = 14 := rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

def row (mask : ℕ) (i : Fin 8) : Bool := mask.testBit i.val

theorem row32 : target (row 32) = false := by decide +kernel
theorem row36 : target (row 36) = true := by decide +kernel
theorem row4 : target (row 4) = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem liftCorrect : ∀ x : Fin 7 → Bool, target (liftSeven x) = target10900 x := by
  decide +kernel

end PEqualNP.Outside.L_meta_30869_aux.Witness

namespace PEqualNP.Outside.L_meta_30869_aux.Polarity

open PEqualNP.CircuitLowerBounds

private def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [gateBit w g]

private def Drops (a b : Bool) : Prop := b = true → a = true

private theorem getD_snoc (w : List Bool) (v : Bool) (i : Nat) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  by_cases hi : i < w.length
  · rw [ite_eq_right (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hi]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    by_cases he : i = w.length
    · subst i
      simp
    · rw [ite_eq_right he, List.getD_eq_getElem?_getD]
      have hn : ([v] : List Bool)[i - w.length]? = none := by
        apply List.getElem?_eq_none
        simp only [List.length_cons, List.length_nil]
        omega
      rw [hn, List.getElem?_eq_none (by omega)]

private theorem step_preserves {R : Bool → Bool → Prop} {a b : List Bool} {g : Gate}
    (hlen : a.length = b.length)
    (hw : ∀ i : Nat, i ≠ 2 → R (a.getD i false) (b.getD i false))
    (hg : R (gateBit a g) (gateBit b g)) :
    ∀ i : Nat, i ≠ 2 → R ((step a g).getD i false) ((step b g).getD i false) := by
  intro i hi
  unfold step
  rw [getD_snoc, getD_snoc, ← hlen]
  by_cases he : i = a.length
  · simpa only [ite_eq_left he] using hg
  · simpa only [ite_eq_right he] using hw i hi

private theorem and_or_drops {a b : List Bool} {g : Gate}
    (hg : g.op = .and ∨ g.op = .or)
    (hw : ∀ i ∈ g.inputs, Drops (a.getD i false) (b.getD i false)) :
    Drops (gateBit a g) (gateBit b g) := by
  cases hg with
  | inl ha =>
    unfold gateBit Drops
    simp only [ha, GateOp.eval, List.all_eq_true]
    intro hb v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    exact hw i hi (hb _ (List.mem_map.2 ⟨i, hi, rfl⟩))
  | inr ho =>
    unfold gateBit Drops
    simp only [ho, GateOp.eval, List.any_eq_true]
    rintro ⟨v, hv, hb⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    exact ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, hw i hi hb⟩

private theorem not_drops {a b : List Bool} {g : Gate} (hg : g.op = .not)
    (hw : ∀ i : Nat, i ≠ 2 → a.getD i false = b.getD i false)
    (h2 : a.getD 2 false = false ∧ b.getD 2 false = true) :
    Drops (gateBit a g) (gateBit b g) := by
  cases h : g.inputs with
  | nil => simp [gateBit, hg, h, GateOp.eval, Drops]
  | cons i rest =>
    by_cases he : i = 2
    · subst i
      unfold gateBit
      rw [hg, h]
      change Drops (!(a.getD 2 false)) (!(b.getD 2 false))
      rw [h2.2]
      simp [Drops]
    · unfold gateBit
      rw [hg, h]
      change Drops (!(a.getD i false)) (!(b.getD i false))
      rw [hw i he]
      exact fun hv => hv

private theorem fold_and_or_drops (gates : List Gate)
    (ops : ∀ g ∈ gates, g.op = .and ∨ g.op = .or)
    (avoid : ∀ g ∈ gates, 2 ∉ g.inputs)
    {a b : List Bool} (hlen : a.length = b.length)
    (hw : ∀ i : Nat, i ≠ 2 → Drops (a.getD i false) (b.getD i false)) :
    ∀ i : Nat, i ≠ 2 →
      Drops ((gates.foldl step a).getD i false) ((gates.foldl step b).getD i false) := by
  induction gates generalizing a b with
  | nil => exact hw
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hgate := and_or_drops (g := g) (ops g List.mem_cons_self)
      (fun i hi => hw i (fun he => avoid g List.mem_cons_self (he ▸ hi)))
    exact ih (fun k hk => ops k (List.mem_cons_of_mem g hk))
      (fun k hk => avoid k (List.mem_cons_of_mem g hk))
      (by simp [step, hlen]) (step_preserves hlen hw hgate)

private theorem fold_drops (gates : List Gate)
    (ops : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∨ g.op = .not)
    (uniqueNot : ∀ i j : Fin gates.length,
      (gates.get i).op = .not → (gates.get j).op = .not → i = j)
    (avoid : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) → 2 ∉ g.inputs)
    {a b : List Bool} (hlen : a.length = b.length) (hsize : 2 < a.length)
    (hw : ∀ i : Nat, i ≠ 2 → a.getD i false = b.getD i false)
    (h2 : a.getD 2 false = false ∧ b.getD 2 false = true) :
    ∀ i : Nat, i ≠ 2 →
      Drops ((gates.foldl step a).getD i false) ((gates.foldl step b).getD i false) := by
  induction gates generalizing a b with
  | nil =>
    intro i hi
    change Drops (a.getD i false) (b.getD i false)
    exact fun hb => (hw i hi).trans hb
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hlen' : (step a g).length = (step b g).length := by simp [step, hlen]
    have hrest : ∀ k ∈ rest, (k.op = .and ∨ k.op = .or) ∨ k.op = .not :=
      fun k hk => ops k (List.mem_cons_of_mem g hk)
    have hav : ∀ k ∈ rest, (k.op = .and ∨ k.op = .or) → 2 ∉ k.inputs :=
      fun k hk => avoid k (List.mem_cons_of_mem g hk)
    rcases ops g List.mem_cons_self with hg | hg
    · have hs : gateBit a g = gateBit b g := by
        apply congrArg (g.op.eval)
        apply List.map_congr_left
        exact fun i hi => hw i (fun he => avoid g List.mem_cons_self hg (he ▸ hi))
      have hnot' : ∀ i j : Fin rest.length,
          (rest.get i).op = .not → (rest.get j).op = .not → i = j := by
        intro i j hi hj
        have he := uniqueNot i.succ j.succ hi hj
        exact Fin.ext (by have := congrArg Fin.val he; simp only [Fin.val_succ] at this; omega)
      have h2' : (step a g).getD 2 false = false ∧ (step b g).getD 2 false = true := by
        unfold step
        rw [getD_snoc, getD_snoc, ite_eq_right (by omega), ite_eq_right (by omega)]
        exact h2
      exact ih hrest hnot' hav hlen' (by simp [step]; omega) (step_preserves hlen hw hs) h2'
    · have hn : ∀ k ∈ rest, k.op = .and ∨ k.op = .or := by
        intro k hk
        rcases hrest k hk with h | h
        · exact h
        · obtain ⟨i, rfl⟩ := List.get_of_mem hk
          have he := uniqueNot 0 i.succ hg h
          have hval : 0 = i.val + 1 := congrArg Fin.val he
          omega
      exact fold_and_or_drops rest hn (fun k hk => hav k hk (hn k hk)) hlen'
        (step_preserves hlen (fun i hi hb => (hw i hi).trans hb) (not_drops hg hw h2))

private theorem input_getD {f : Fin 8 → Bool} {i : Nat} :
    (List.ofFn f).getD i false = if h : i < 8 then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> rfl

theorem binary_reader (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (one : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i = j)
    (oNe : o ≠ 2)
    (rise : (Circuit.mk gates o).eval (List.ofFn (fun i : Fin 8 => decide (i.val = 5))) = false ∧
      (Circuit.mk gates o).eval (List.ofFn (fun i : Fin 8 => decide (i.val = 2 ∨ i.val = 5))) = true) :
    ∃ g ∈ gates, (g.op = .and ∨ g.op = .or) ∧ 2 ∈ g.inputs := by
  false_or_by_contra
  rename_i h
  have avoid : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) → 2 ∉ g.inputs :=
    fun g hg hop hi => h ⟨g, hg, hop, hi⟩
  have ops : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∨ g.op = .not := by
    intro g hg
    simpa only [or_assoc] using (fit g hg).1
  let a := List.ofFn (fun i : Fin 8 => decide (i.val = 5))
  let b := List.ofFn (fun i : Fin 8 => decide (i.val = 2 ∨ i.val = 5))
  have hlenA : a.length = 8 := List.length_ofFn
  have hlenB : b.length = 8 := List.length_ofFn
  have hw : ∀ i : Nat, i ≠ 2 → a.getD i false = b.getD i false := by
    intro i hi
    dsimp only [a, b]
    rw [input_getD, input_getD]
    by_cases h8 : i < 8 <;> simp [h8, hi]
  have h2 : a.getD 2 false = false ∧ b.getD 2 false = true := by
    simp [a, b]
  have hd := fold_drops gates ops one avoid (hlenA.trans hlenB.symm) (by omega) hw h2 o oNe
  have ha : (gates.foldl step a).getD o false = false := rise.1
  have hb : (gates.foldl step b).getD o false = true := rise.2
  have hc := hd hb
  rw [ha] at hc
  contradiction

end PEqualNP.Outside.L_meta_30869_aux.Polarity

namespace PEqualNP.Outside.L_meta_30869_aux
open PEqualNP.CircuitLowerBounds

private theorem foldKeepsInput (gs : List Gate) (w : List Bool) (h : 2 < w.length) :
    (gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) w).getD 2 false =
      w.getD 2 false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem outputNotInputTwo (gs : List Gate) (o : Nat)
    (computes : ∀ x : Fin 8 → Bool, (Circuit.mk gs o).eval (List.ofFn x) = Witness.target x) : o ≠ 2 := by
  rintro rfl
  have wrong := computes (Witness.row 4)
  rw [Witness.row4] at wrong
  unfold Circuit.eval Circuit.wires at wrong
  rw [foldKeepsInput gs (List.ofFn (Witness.row 4)) (by simp)] at wrong
  have atInput : (List.ofFn (Witness.row 4)).getD 2 false = true := by decide +kernel
  rw [atInput] at wrong
  exact Bool.noConfusion wrong

private theorem risingRows (gs : List Gate) (o : Nat)
    (computes : ∀ x : Fin 8 → Bool, (Circuit.mk gs o).eval (List.ofFn x) = Witness.target x) :
    (Circuit.mk gs o).eval (List.ofFn (fun i : Fin 8 => decide (i.val = 5))) = false ∧
      (Circuit.mk gs o).eval (List.ofFn (fun i : Fin 8 => decide (i.val = 2 ∨ i.val = 5))) = true := by
  have e32 : (fun i : Fin 8 => decide (i.val = 5)) = Witness.row 32 := by
    funext i
    fin_cases i <;> decide +kernel
  have e36 : (fun i : Fin 8 => decide (i.val = 2 ∨ i.val = 5)) = Witness.row 36 := by
    funext i
    fin_cases i <;> decide +kernel
  rw [e32, e36]
  exact ⟨(computes _).trans Witness.row32, (computes _).trans Witness.row36⟩

end PEqualNP.Outside.L_meta_30869_aux

open PEqualNP.Outside.L_meta_30869_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_30869 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o fit one computes
  change ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x) = Witness.target x at computes
  by_cases hasNot : ∃ g ∈ gates, g.op = .not
  · obtain ⟨inverter, hiMem, hiOp⟩ := hasNot
    obtain ⟨reader, hrMem, hrOp, hrRead⟩ :=
      Polarity.binary_reader gates o fit one (outputNotInputTwo gates o computes) (risingRows gates o computes)
    have legal : PEqualNP.MetaComplexity.FanInTwo ⟨gates, o⟩ := by
      intro g hg
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using fit g hg
    have bound := checkedCofactor checkedLower ⟨gates, o⟩ legal
      (fun x => (computes (liftSeven x)).trans (Witness.liftCorrect x))
    change 12 ≤ gates.countP Base.paidAtZero at bound
    have free := cofactorGateCount gates hiMem hiOp hrMem hrOp hrRead
    have size : Witness.witness.gates.length ≤ gates.length := by
      rw [Witness.witnessSize]
      omega
    exact ⟨Witness.witness.gates, Witness.witness.output, Witness.witnessFit, size, Witness.witnessCorrect⟩
  · exact ⟨gates, o, Base.noNotReuse fit (fun g hg hop => hasNot ⟨g, hg, hop⟩), le_rfl, computes⟩
