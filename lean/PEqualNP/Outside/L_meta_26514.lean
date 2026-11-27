import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_26514_aux

namespace Lower26514
abbrev Fn (n : Nat) := (Fin n → Bool) → Bool
def start {n : Nat} : List (Fn n) := [fun _ => false,fun _ => true] ++ (List.ofFn (fun i : Fin n => [fun x => x i,fun x => !(x i)] )).flatten
inductive Run {n : Nat} : List (Fn n) → Nat → Fn n → Prop
  | stop {v k t} : t ∈ v → Run v k t
  | step {v k t a b} : a ∈ v → b ∈ v → Run (v ++ [fun x => a x && b x,fun x => !(a x && b x)]) k t → Run v (k+1) t
def six : Fn 6 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3)
def five : Fn 5 := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0)
end Lower26514


namespace Pin26514
open Lower26514
abbrev inv {n} (f : Fn n) : Fn n := fun x => !(f x)
abbrev meet {n} (a b : Fn n) : Fn n := fun x => a x && b x
abbrev Has {n} (S : List (Fn n)) (f : Fn n) := f∈S ∧ inv f∈S
abbrev Both {n} (S : List (Fn n)) := Has S (fun _ => false)
abbrev Const {n} (f : Fn n) := ∃ c, ∀ x, f x = c
def append {n} (S : List (Fn n)) (a b : Fn n) := S ++ [meet a b,inv (meet a b)]
private theorem neg2 {n} (f : Fn n) : inv (inv f)=f := by funext x; simp
private theorem swap {n S} {f : Fn n} (h : Has S f) : Has S (inv f) := ⟨h.2,by rw [neg2]; exact h.1⟩
private theorem old {n S} {f a b : Fn n} (h : Has S f) : Has (append S a b) f := ⟨List.mem_append_left _ h.1,List.mem_append_left _ h.2⟩
private theorem fresh {n} (S : List (Fn n)) (a b : Fn n) : Has (append S a b) (meet a b) := by constructor <;> apply List.mem_append_right <;> simp
private theorem extend {n m} {S : List (Fn n)} {D : List (Fn m)} {a b : Fn n} (p : (Fin m → Bool) → (Fin n → Bool)) (base : ∀ f∈S,Has D (f ∘ p)) (h : Has D ((meet a b) ∘ p)) : ∀ f∈append S a b, Has D (f ∘ p) := by
  intro f hf; rcases List.mem_append.mp hf with hf|hf; exact base _ hf
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf; rcases hf with rfl|rfl; exact h; exact swap h
private theorem absorb {n} {S : List (Fn n)} {a b : Fn n} (z : Both S) (ha : Has S a) (hb : Has S b) (h : Const a ∨ Const b) : Has S (meet a b) := by
  rcases h with ⟨c,h⟩|⟨c,h⟩ <;> cases c
  · simpa only [show meet a b = fun _ => false by funext x; simp [meet,h]] using z
  · simpa only [show meet a b = b by funext x; simp [meet,h]] using hb
  · simpa only [show meet a b = fun _ => false by funext x; simp [meet,h]] using z
  · simpa only [show meet a b = a by funext x; simp [meet,h]] using ha

theorem weaken {n S k} {f : Fn n} (h : Run S k f) : ∀ {l},k≤l → Run S l f := by
  induction h with
  | stop ht => intro l hl; exact .stop ht
  | @step v k t a b ha hb h ih => intro l hl; obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l≠0); exact .step ha hb (ih (by omega))

theorem project {n m S k} {t : Fn n} (h : Run S k t) (p : (Fin m → Bool) → (Fin n → Bool)) (D : List (Fn m)) (base : ∀ f∈S, Has D (f ∘ p)) : Run D k (t ∘ p) := by
  induction h generalizing D with
  | stop ht => exact .stop (base _ ht).1
  | @step v k t a b ha hb h ih =>
    apply Run.step (base _ ha).1 (base _ hb).1; apply ih; exact extend p (fun f hf => old (base f hf)) (fresh _ _ _)


theorem save {n m S k} {t : Fn n} (h : Run S k t) (p : (Fin m → Bool) → (Fin n → Bool)) (Stable : Fn n → Prop)
    (nand : ∀ a b, Stable a → Stable b → Stable (meet a b)) (neg : ∀ f, Stable f → Stable (inv f))
    (nt : ¬Stable t) (nc : ¬Const (t ∘ p)) (bank : ∀ f∈S, Stable f ∨ Const (f ∘ p))
    (D : List (Fn m)) (constants : Both D) (base : ∀ f∈S, Has D (f ∘ p)) : ∃ l, l+1≤k ∧ Run D l (t ∘ p) := by
  classical
  induction h generalizing D with
  | stop ht => exact False.elim ((bank _ ht).elim nt nc)
  | @step v k t a b ha hb h ih =>
    by_cases sab : Stable a ∧ Stable b
    · have st := nand a b sab.1 sab.2
      have next : ∀ f∈append v a b,Stable f ∨ Const (f ∘ p) := by
        intro f hf; rcases List.mem_append.mp hf with hf|hf; exact bank _ hf
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hf; rcases hf with rfl|rfl; exact Or.inl st; exact Or.inl (neg _ st)
      obtain ⟨l,hl,hr⟩ := ih nt nc next _ (old constants) (extend p (fun f hf => old (base f hf)) (fresh _ _ _))
      exact ⟨l+1,by omega,.step (base _ ha).1 (base _ hb).1 hr⟩
    · have ca : Const (a ∘ p) ∨ Const (b ∘ p) := by rcases bank a ha with h|h <;> rcases bank b hb with j|j <;> tauto
      have hit := absorb constants (base _ ha) (base _ hb) ca
      exact ⟨k,by omega,project h p D (extend p base hit)⟩

theorem saveTwo {n m S k} {t : Fn n} (h : Run S k t) (p : Bool → (Fin m → Bool) → (Fin n → Bool)) (Stable : Fn n → Prop)
    (nand : ∀ a b, Stable a → Stable b → Stable (meet a b)) (neg : ∀ f, Stable f → Stable (inv f))
    (nt : ¬Stable t) (nc : ∀ c, ¬Const (t ∘ p c))
    (bank : ∀ f∈S, Stable f ∨ ((∀ c, Const (f ∘ p c)) ∧ ∃ c, ∀ x, f (p c x)=false))
    (D : Bool → List (Fn m)) (constants : ∀ c, Both (D c)) (base : ∀ c f, f∈S → Has (D c) (f ∘ p c)) :
    ∃ c l, l+2≤k ∧ Run (D c) l (t ∘ p c) := by
  classical
  induction h generalizing D with
  | stop ht => rcases bank _ ht with ht|ht; exact (nt ht).elim; exact (nc false (ht.1 false)).elim
  | @step v k t a b ha hb h ih =>
    by_cases sab : Stable a ∧ Stable b
    · have st := nand a b sab.1 sab.2
      have next : ∀ f∈append v a b,Stable f ∨ ((∀ c, Const (f ∘ p c)) ∧ ∃ c, ∀ x, f (p c x)=false) := by
        intro f hf; rcases List.mem_append.mp hf with hf|hf; exact bank _ hf
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hf; rcases hf with rfl|rfl; exact Or.inl st; exact Or.inl (neg _ st)
      obtain ⟨c,l,hl,hr⟩ := ih nt nc next (fun c => append (D c) (a ∘ p c) (b ∘ p c)) (fun c => old (constants c)) (fun c => extend (p c) (fun f hf => old (base c f hf)) (fresh _ _ _))
      exact ⟨c,l+1,by omega,.step (base c _ ha).1 (base c _ hb).1 hr⟩
    · have force : ∃ c, ∀ x, meet a b (p c x)=false := by
        by_cases sa : Stable a
        · obtain ⟨c,hc⟩ := ((bank _ hb).resolve_left (fun h => sab ⟨sa,h⟩)).2
          exact ⟨c,fun x => by simp [meet,hc]⟩
        · obtain ⟨c,hc⟩ := ((bank _ ha).resolve_left sa).2
          exact ⟨c,fun x => by simp [meet,hc]⟩
      obtain ⟨c,hc⟩ := force
      have hit : (meet a b ∘ p c) = fun _ => false := funext hc
      have next : ∀ f∈append v a b,Stable f ∨ Const (f ∘ p c) := by
        intro f hf; rcases List.mem_append.mp hf with hf|hf
        · exact (bank _ hf).imp_right (fun h => h.1 c)
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at hf; rcases hf with rfl|rfl
          · exact Or.inr ⟨false,hc⟩
          · exact Or.inr ⟨true,fun x => by simp [Function.comp_apply,inv,hc]⟩
      obtain ⟨l,hl,hr⟩ := save h (p c) Stable nand neg nt (nc c) next (D c) (constants c) (extend (p c) (base c) (hit ▸ constants c))
      exact ⟨c,l,by omega,hr⟩
end Pin26514


namespace Coord26514
open Lower26514 Pin26514
abbrev Code (m : Nat) := Option (Fin m)
def pin {n m} (c : Fin n → Code m) (v : Bool) (x : Fin m → Bool) (i : Fin n) := (c i).elim v x
def stable {n m} (c : Fin n → Code m) (f : Fn n) := ∀ x, f (pin c false x)=f (pin c true x)
private theorem both {n} : Both (@start n) := ⟨by simp [start],by change (fun _ => true)∈_; simp [start]⟩
private theorem lit {n} (i : Fin n) : Has start (fun x => x i) := by
  constructor <;> apply List.mem_append_right <;> apply List.mem_flatten.mpr <;> exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,by simp⟩
private theorem casesStart {n} {f : Fn n} (h : f∈start) : (∃ b, f=fun _ => b) ∨ ∃ i : Fin n, f=(fun x => x i) ∨ f=(fun x => !(x i)) := by
  rcases List.mem_append.mp h with h|h
  · simp at h; rcases h with rfl|rfl; exact Or.inl ⟨false,rfl⟩; exact Or.inl ⟨true,rfl⟩
  · obtain ⟨l,hl,h⟩ := List.mem_flatten.mp h; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl; exact Or.inr ⟨i,by simpa using h⟩
private theorem negHas {n S} {f : Fn n} (h : Has S f) : Has S (inv f) := ⟨h.2,by rw [show inv (inv f) = f by funext x; simp [inv]]; exact h.1⟩
private theorem available {n m} (c : Fin n → Code m) (v : Bool) (f : Fn n) (hf : f∈start) : Has start (f ∘ pin c v) := by
  rcases casesStart hf with ⟨b,rfl⟩|⟨i,hi⟩
  · cases b; exact both; exact negHas both
  · cases h : c i with
    | none => rcases hi with rfl|rfl <;> cases v <;> simp only [Function.comp_def,pin,h,Option.elim,Bool.not_true,Bool.not_false] <;> first | exact both | exact negHas both
    | some j => rcases hi with rfl|rfl <;> simp only [Function.comp_def,pin,h,Option.elim] <;> first | exact lit j | exact negHas (lit j)
private theorem bank {n m} (c : Fin n → Code m) (f : Fn n) (hf : f∈start) : stable c f ∨ ((∀ b, Const (f ∘ pin c b)) ∧ ∃ b, ∀ x, f (pin c b x)=false) := by
  rcases casesStart hf with ⟨b,rfl⟩|⟨i,h⟩
  · exact Or.inl fun _ => rfl
  · cases he : c i with
    | some j => rcases h with rfl|rfl <;> exact Or.inl (by simp [stable,pin,he])
    | none => rcases h with rfl|rfl
              · exact Or.inr ⟨fun b => ⟨b,by simp [pin,he,Function.comp_def]⟩,false,by simp [pin,he]⟩
              · exact Or.inr ⟨fun b => ⟨!b,by simp [pin,he,Function.comp_def]⟩,true,by simp [pin,he]⟩
private theorem sand {n m} (c : Fin n → Code m) (a b : Fn n) (ha : stable c a) (hb : stable c b) : stable c (meet a b) := by intro x; simp only [meet,ha x,hb x]
private theorem sneg {n m} (c : Fin n → Code m) (a : Fn n) (h : stable c a) : stable c (inv a) := by intro x; simp only [inv,h x]
theorem one {n m k} (c : Fin n → Code m) (v : Bool) (f : Fn n) (h : Run start k f) (dep : ¬stable c f) (nc : ¬Const (f ∘ pin c v)) : ∃ l,l+1≤k ∧ Run start l (f ∘ pin c v) :=
  save h _ _ (sand c) (sneg c) dep nc (fun a ha => (bank c a ha).imp_right fun z => z.1 v) _ both (available c v)
theorem two {n m k} (c : Fin n → Code m) (f : Fn n) (h : Run start k f) (dep : ¬stable c f) (nc : ∀ b,¬Const (f ∘ pin c b)) : ∃ b l,l+2≤k ∧ Run start l (f ∘ pin c b) :=
  saveTwo h _ _ (sand c) (sneg c) dep nc (bank c) _ (fun _ => both) (available c)
end Coord26514


namespace SignedKernel26514


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


abbrev Wire := Bool × ℕ
def zero : Wire := (false,0)
def flip (a : Wire) : Wire := (!a.1,a.2)
def combine (d a b : ℕ) : ℕ :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def opIndex (a b : Bool) : ℕ :=
  if a then (if b then 1 else 3) else (if b then 2 else 0)
def meet (a b : Wire) : Wire := (a.1 && b.1,combine (opIndex a.1 b.1) a.2 b.2)
def join (a b : Wire) : Wire := flip (meet (flip a) (flip b))
def read (j : ℕ) (a : Wire) : Bool := a.1 != a.2.testBit j
lemma read_zero (j : ℕ) : read j zero=false := by simp [read,zero]
lemma read_flip (j : ℕ) (a : Wire) : read j (flip a)=!(read j a) := by
  cases a with | mk s a => cases s <;> cases h : a.testBit j <;> simp [read,flip,h]
lemma read_meet (j : ℕ) (a b : Wire) : read j (meet a b) = (read j a && read j b) := by
  obtain ⟨s,a⟩ := a;obtain ⟨t,b⟩ := b
  cases s <;> cases t <;> cases h : a.testBit j <;> cases g : b.testBit j <;>
    simp [read,meet,combine,opIndex,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,h,g]
lemma read_join (j : ℕ) (a b : Wire) : read j (join a b) = (read j a || read j b) := by
  simp only [join,read_flip,read_meet];cases read j a <;> cases read j b <;> rfl

def gate (w : List Wire) (g : Gate) : Wire :=
  let arg := fun i => w.getD i zero
  match g.op,g.inputs with
  | .not, xs => flip (arg (xs.headD w.length))
  | .and, [] => flip zero
  | .or, [] => zero
  | .and, [i] | .or, [i] => arg i
  | .and, i::j::_ => meet (arg i) (arg j)
  | .or, i::j::_ => join (arg i) (arg j)
  | _,_ => zero
def execute (gs : List Gate) (w : List Wire) : List Wire :=
  gs.foldl (fun w g => w++[gate w g]) w
def boolRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma read_get (j : ℕ) (w : List Wire) (i : ℕ) :
    (w.map (read j)).getD i false = read j (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases h : w[i]? with
  | none => exact (read_zero j).symm
  | some a => rfl
lemma gate_read (w : List Wire) (g : Gate) (legal : g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (j : ℕ) :
    read j (gate w g) = g.op.eval (g.inputs.map fun i => (w.map (read j)).getD i false) := by
  simp_rw [read_get]
  obtain ⟨op,xs⟩ := g
  obtain ⟨ops,len⟩ := legal
  change op ∈ ({.and,.or,.not} : Set GateOp) at ops
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ops
  rcases ops with rfl|rfl|rfl <;>
    rcases xs with _|⟨i,_|⟨k,_|⟨h,rest⟩⟩⟩ <;>
    simp_all [gate,GateOp.eval,read_flip,read_meet,read_join,read_get,read_zero,List.getD_eq_default]
lemma execute_read (j : ℕ) (gs : List Gate) (w : List Wire) (legal : ∀ g ∈ gs,
    g.op ∈ ({.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (execute gs w).map (read j) = boolRun gs (w.map (read j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gate w g])).map (read j) = boolRun gs (_++[_])
    rw [ih _ (fun v hv => legal v (.tail _ hv))]
    simp [gate_read w g (legal g List.mem_cons_self) j]

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List Wire) := w.map Prod.snd
def simple (w : List Wire) (z : ℕ) := z=0 ∨ z∈reps w
def priced (w : List Wire) (paid : Bool) (z : ℕ) := simple w z ∨
    (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a≠0 ∧ b≠0 ∧ a≠b ∧ z=combine d a b)
lemma get_simple (w : List Wire) (i : ℕ) : simple w (w.getD i zero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a,List.mem_of_getElem? eq,rfl⟩)
lemma combine_eq_cases (d a b : ℕ) (hd : d<4) (h : a=0 ∨ b=0 ∨ a=b) :
    combine d a b=0 ∨ combine d a b=a ∨ combine d a b=b := by
  rcases h with h|h|h <;> subst_vars <;> interval_cases d <;> simp [combine]
lemma made (w : List Wire) (d : ℕ) (a b : Wire) (hd : d<4) (pa : simple w a.2) (pb : simple w b.2) :
    priced w true (combine d a.2 b.2) := by
  by_cases h : a.2=0 ∨ b.2=0 ∨ a.2=b.2
  · rcases combine_eq_cases _ _ _ hd h with e|e|e
    · exact Or.inl (Or.inl e)
    · apply Or.inl; rw [e]; exact pa
    · apply Or.inl; rw [e]; exact pb
  · push Not at h
    exact Or.inr ⟨rfl,d,hd,a.2,pa.resolve_left h.1,b.2,pb.resolve_left h.2.1,h.1,h.2.1,h.2.2,rfl⟩
lemma op_lt (s t : Bool) : opIndex s t < 4 := by cases s <;> cases t <;> decide
lemma gate_priced (w : List Wire) (g : Gate) : priced w (counted g) (gate w g).2 := by
  obtain ⟨op,xs⟩ := g
  cases op with
  | and =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _|⟨i,_|⟨j,t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made w _ _ _ (op_lt _ _) (get_simple w i) (get_simple w j)
  | mod _ | maj => exact Or.inl (Or.inl rfl)
  | _ => exact Or.inl (get_simple w _)






open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def Good (m a : ℕ) := ∀ i<m, a.testBit i ≠ a.testBit (m+i)

def Live (m : ℕ) : ℕ → Finset ℕ → Prop
  | 0, S => ∃ a, S = {a} ∧ Good m a ∧ a ≠ 0
  | k+1, S => ∃ (U : Finset ℕ) (a b d : ℕ),
      S = insert a (insert b U) ∧
      d < 4 ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      combine d a b ∉ insert a (insert b U) ∧
      Live m k (insert (combine d a b) U)

namespace Live

lemma done {m a : ℕ} (hg : Good m a) (nonzero : a ≠ 0) : Live m 0 {a} := by
  rw [Live]
  exact ⟨a, rfl, hg, nonzero⟩

lemma step {m k : ℕ} {U : Finset ℕ} {a b d : ℕ}
    (hd : d < 4) (ha : a ≠ 0) (hb : b ≠ 0) (diff : a ≠ b)
    (fresh : combine d a b ∉ insert a (insert b U))
    (next : Live m k (insert (combine d a b) U)) :
    Live m (k+1) (insert a (insert b U)) := by
  rw [Live]
  exact ⟨U, a, b, d, rfl, hd, ha, hb, diff, fresh, next⟩

end Live

lemma liveNonzero {m k S} (h : Live m k S) : ∀ a∈S,a≠0 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, hn⟩ := h
    simpa using hn
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma liveSize {m k S} (h : Live m k S) : S.card≤k+1 := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, _, _⟩ := h
    simp
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, fresh, tail⟩ := h
    have bound := ih tail
    have z : combine d a b ∉ U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    rw [Finset.card_insert_of_notMem z] at bound
    have u := Finset.card_insert_le a (insert b U)
    have v := Finset.card_insert_le b U
    omega
lemma combine_congr_bits (d a b i j : ℕ) (p : a.testBit i=a.testBit j) (q : b.testBit i=b.testBit j) :
    (combine d a b).testBit i=(combine d a b).testBit j := by
  rcases d with _|(_|(_|d)) <;> simp [combine,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,p,q]
lemma liveSeparates {m k S} (h : Live m k S) (i : ℕ) (hi : i<m) :
    ∃ a∈S,a.testBit i≠a.testBit (m+i) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at h
    obtain ⟨a, rfl, hg, _⟩ := h
    exact ⟨a, Finset.mem_singleton_self a, hg i hi⟩
  | succ k ih =>
    rw [Live] at h
    obtain ⟨U, a, b, d, rfl, _, _, _, _, _, tail⟩ := h
    obtain ⟨x,hx,dist⟩ := ih tail
    rcases Finset.mem_insert.mp hx with rfl|hx
    · by_cases v : a.testBit i=a.testBit (m+i)
      · exact ⟨b,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),fun u => dist (combine_congr_bits _ _ _ _ _ v u)⟩
      · exact ⟨a,Finset.mem_insert_self _ _,v⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx),dist⟩

lemma pull {m k S w z p} (h : Live m k S) (op : priced w p z)
    (sub : ∀ a∈S, a∈reps w ++ [z]) :
    ∃ l T, l ≤ k + p.toNat ∧ Live m l T ∧ ∀ a∈T, a∈reps w := by
  by_cases needed : z∈S
  · by_cases available : z∈reps w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a∈reps w ∨ a=z) with old|rfl
      · exact old
      · exact available
    · rcases op with easy|⟨rfl,d,hd,a,xa,b,xb,na,nb,ab,rfl⟩
      · rcases easy with e|e
        · exact ((liveNonzero h z needed) e).elim
        · exact (available e).elim
      · let g := combine d a b
        let U := S.erase g
        have tail : Live m k (insert g U) := by change Live m k (insert g (S.erase g)); rw [Finset.insert_erase (show g∈S from needed)]; exact h
        have old (x : ℕ) (hx : x∈U) : x∈reps w := by
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
          have h' : x∈reps w ∨ x=g := by simpa using sub x mem
          exact h'.resolve_right ne
        have fresh : g ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e|h'
          · exact available (show g∈reps w by rw [e];exact xa)
          rcases Finset.mem_insert.mp h' with e|u
          · exact available (show g∈reps w by rw [e];exact xb)
          · exact available (old _ u)
        refine ⟨k+1,insert a (insert b U),by simp,Live.step hd na nb ab fresh tail,?_⟩
        simpa using And.intro xa (And.intro xb old)
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have ne : a≠z := fun e => needed (e ▸ ha)
    simpa [ne] using sub a ha

lemma extract {m out} (hg : Good m out) (hn : out≠0) (gs : List Gate) (w : List Wire)
    (found : out∈reps (execute gs w)) :
    ∃ k S, k≤gs.countP counted ∧ Live m k S ∧ ∀ a∈S, a∈reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0,{out},by simp,Live.done hg hn,by simpa [execute] using found⟩
  | cons g gs ih =>
    obtain ⟨k,S,lim,h,sub⟩ := ih (w++[gate w g]) found
    have sub' : ∀ a∈S,a∈reps w ++ [(gate w g).2] := by simpa [reps] using sub
    obtain ⟨l,T,cost,ht,raw⟩ := pull h (gate_priced w g) sub'
    refine ⟨l,T,?_,ht,raw⟩
    cases e : counted g <;> simp [e,Bool.toNat] at cost ⊢ <;> omega
def separation (m a : ℕ) := a ^^^ (a >>> m)
def cover (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => separation m a ||| cover m t
def full (m : ℕ) := (1 <<< m)-1
def enough (m c : ℕ) := (c &&& full m) == full m
lemma coverBit (m i : ℕ) (v : List ℕ) : (cover m v).testBit i=true ↔
    ∃ a∈v,a.testBit i≠a.testBit (m+i) := by
  induction v with
  | nil => simp [cover]
  | cons a t ih =>
    simp only [cover,Nat.testBit_or,Bool.or_eq_true,ih,List.mem_cons,separation,Nat.testBit_xor,Nat.testBit_shiftRight]
    cases v1 : a.testBit i <;> cases v2 : a.testBit (m+i) <;> simp [v1,v2] <;> aesop
lemma enoughLive {m k S} (h : Live m k S) (v : List ℕ) (rep : v.toFinset=S) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have bit : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases hi : i<m
  · have ⟨x,hx,good⟩ := liveSeparates h i hi
    have xc : x∈v := List.mem_toFinset.mp (rep ▸ hx)
    have mark := (coverBit m i v).2 ⟨x,xc,good⟩
    simp [mark,bit,hi]
  · simp [bit,hi]






def save (keep : Bool) (a : ℕ) (rest : List ℕ) := if keep then a::rest else rest
def without (v : List ℕ) (a b : ℕ) := v.filter (fun x => x != a && x != b)
def optionStep (m fuel : ℕ) (go : List ℕ → Bool) (rest : List ℕ) (n cv a b z : ℕ) (ka kb : Bool) : Bool :=
  let len := 1+n+ka.toNat+kb.toNat
  len ≤ fuel+1 && enough m (((separation m z ||| cv) ||| (if ka then separation m a else 0)) |||
    (if kb then separation m b else 0)) && go (z::save ka a (save kb b rest))
def gateStep (m fuel : ℕ) (go : List ℕ → Bool) (v rest : List ℕ) (n cv a b z : ℕ) : Bool :=
  z != 0 && !(v.contains z) &&
  (optionStep m fuel go rest n cv a b z false false || optionStep m fuel go rest n cv a b z true false ||
   optionStep m fuel go rest n cv a b z false true || optionStep m fuel go rest n cv a b z true true)
def pairStep (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) (a b : ℕ) : Bool :=
  if a<b then
    let rest := without v a b
    let check := gateStep m fuel go v rest rest.length (cover m rest) a b
    check (a &&& b) || check (a ||| b) || check (a ^^^ (a &&& b)) || check (b ^^^ (a &&& b))
  else false
def anyGate (m fuel : ℕ) (go : List ℕ → Bool) (v : List ℕ) : Bool :=
  v.any (fun a => v.any (fun b => pairStep m fuel go v a b))
def terminal (m : ℕ) (v : List ℕ) := v.any (fun a => enough m (separation m a))
def search (m : ℕ) : ℕ → List ℕ → Bool
  | 0, v => terminal m v
  | fuel+1, v => terminal m v || anyGate m fuel (search m fuel) v

lemma surface (m a i : ℕ) : (separation m a).testBit i=true ↔ a.testBit i≠a.testBit (m+i) := by
  simp only [separation,Nat.testBit_xor,Nat.testBit_shiftRight]
  cases a.testBit i <;> cases a.testBit (m+i) <;> decide
lemma ends {m a} (h : Good m a) (v : List ℕ) (mem : a∈v) : terminal m v=true := by
  apply List.any_eq_true.mpr;refine ⟨a,mem,?_⟩
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i;rw [Nat.testBit_and]
  have e : (full m).testBit i=decide (i<m) := by simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]
  by_cases l : i<m
  · simp [e,l,(surface _ _ _).2 (h i l)]
  · simp [e,l]
lemma option_ok {m fuel go rest a b z ka kb} (lim : (z::save ka a (save kb b rest)).length≤fuel+1)
    (cov : enough m (cover m (z::save ka a (save kb b rest)))=true)
    (next : go (z::save ka a (save kb b rest))=true) :
    optionStep m fuel go rest rest.length (cover m rest) a b z ka kb=true := by
  have size : 1+rest.length+ka.toNat+kb.toNat≤fuel+1 := by
    cases ka <;> cases kb <;> simp [save,Bool.toNat] at lim ⊢ <;> omega
  have eq : enough m (((separation m z ||| cover m rest) ||| (if ka then separation m a else 0)) ||| (if kb then separation m b else 0))=true := by
    cases ka <;> cases kb <;> simpa [save,cover,Nat.or_assoc,Nat.or_left_comm,Nat.or_comm] using cov
  simp [optionStep,size,eq,next]
lemma gate_ok {m fuel go v rest n cv a b z ka kb} (nz : z≠0) (fresh : z∉v)
    (which : optionStep m fuel go rest n cv a b z ka kb=true) :
    gateStep m fuel go v rest n cv a b z=true := by
  cases ka <;> cases kb <;> simp [gateStep,nz,fresh,which]
lemma pair_ok {m fuel go v a b d} (ordered : a<b) (hd : d<4)
    (step : let rest := without v a b;gateStep m fuel go v rest rest.length (cover m rest) a b (combine d a b)=true) :
    pairStep m fuel go v a b=true := by
  interval_cases d <;> simp only [combine] at step <;> simp [pairStep,ordered,step]
lemma swapOp (d a b : ℕ) (hd : d<4) : ∃ e<4,combine d a b=combine e b a := by
  interval_cases d
  · exact ⟨0,by decide,Nat.and_comm a b⟩
  · exact ⟨1,by decide,Nat.or_comm a b⟩
  · exact ⟨3,by decide,by simp [combine,Nat.and_comm]⟩
  · exact ⟨2,by decide,by simp [combine,Nat.and_comm]⟩
lemma listNext {v : List ℕ} {a b z : ℕ} {U : Finset ℕ} (rep : v.toFinset=insert a (insert b U))
    (ab : a≠b) (fz : z∉insert a (insert b U)) (nd : v.Nodup) :
    let rest := without v a b
    let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
    next.toFinset=insert z U ∧ next.Nodup := by
  dsimp only
  have mem (x : ℕ) : x∈without v a b ↔ x∈U ∧ x≠a ∧ x≠b := by
    simp only [without,List.mem_filter,Bool.and_eq_true,bne_iff_ne]
    have e : x∈v ↔ x=a ∨ x=b ∨ x∈U := by rw [← List.mem_toFinset,rep];simp
    tauto
  have nr := nd.filter (fun x => x != a && x != b)
  change (without v a b).Nodup at nr
  have md (x : ℕ) : (x∈save (decide (a∈U)) a (save (decide (b∈U)) b (without v a b))) ↔ x∈U := by
    by_cases xa : x=a
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,ab]
    by_cases xb : x=b
    · subst x; by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,Ne.symm ab]
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,mem,xa,xb]
  constructor
  · ext x;simp [md]
  · simp only [List.nodup_cons,md]
    refine ⟨fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m)),?_⟩
    have an : a∉without v a b := fun x => (mem _).1 x |>.2.1 rfl
    have bn : b∉without v a b := fun x => (mem _).1 x |>.2.2 rfl
    by_cases ka : a∈U <;> by_cases kb : b∈U <;> simp [save,ka,kb,nr,ab,an,bn]
lemma orderedStep {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (lt : a<b) (nz : combine d a b≠0) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    pairStep m fuel go v a b=true := by
  let z := combine d a b
  let rest := without v a b
  let next := z::save (decide (a∈U)) a (save (decide (b∈U)) b rest)
  obtain ⟨r,nu⟩ := listNext (z:=z) rep (Nat.ne_of_lt lt) fresh nd
  have small := liveSize tail
  change (insert z U).card≤n+1 at small
  have length : next.length=(insert z U).card := by rw [←r,List.toFinset_card_of_nodup nu]
  have bound : next.length≤fuel+1 := by omega
  have coverOK := enoughLive tail next r
  have ok := option_ok bound coverOK (nextOK next r nu)
  apply pair_ok lt hd
  exact gate_ok nz (fun h => fresh (rep ▸ List.mem_toFinset.mpr h)) ok
lemma transition {m fuel n U a b d v} {go : List ℕ→Bool} (hd : d<4)
    (ab : a≠b) (fresh : combine d a b∉insert a (insert b U))
    (rep : List.toFinset v=insert a (insert b U)) (nd : v.Nodup) (lim : n≤fuel)
    (tail : Live m n (insert (combine d a b) U))
    (nextOK : ∀ v : List ℕ, v.toFinset=insert (combine d a b) U → v.Nodup → go v=true) :
    anyGate m fuel go v=true := by
  have ma : a∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_self _ _)
  have mb : b∈v := List.mem_toFinset.mp (rep ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have nz := liveNonzero tail _ (Finset.mem_insert_self _ _)
  rcases lt_or_gt_of_ne ab with lt|gt
  · exact List.any_eq_true.mpr ⟨a,ma,List.any_eq_true.mpr ⟨b,mb,orderedStep hd lt nz fresh rep nd lim tail nextOK⟩⟩
  · obtain ⟨e,he,eq⟩ := swapOp d a b hd
    have rev : insert a (insert b U)=insert b (insert a U) := Finset.insert_comm a b U
    rw [rev] at fresh rep
    rw [eq] at fresh nz tail nextOK
    exact List.any_eq_true.mpr ⟨b,mb,List.any_eq_true.mpr ⟨a,ma,orderedStep he gt nz fresh rep nd lim tail nextOK⟩⟩

theorem complete (m fuel : ℕ) {n S} (h : Live m n S) (lim : n≤fuel)
    (v : List ℕ) (rep : v.toFinset=S) (nd : v.Nodup) : search m fuel v=true := by
  induction fuel generalizing n S v with
  | zero =>
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    | succ n => omega
  | succ k ih =>
    rw [search,Bool.or_eq_true]
    cases n with
    | zero =>
      rw [Live] at h
      obtain ⟨a, rfl, hg, _⟩ := h
      exact Or.inl (ends hg v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a)))
    | succ n =>
      rw [Live] at h
      obtain ⟨U, a, b, d, rfl, hd, _, _, ab, fresh, tail⟩ := h
      exact Or.inr (transition hd ab fresh rep nd (by omega) tail (fun v hv nv => ih tail (by omega) v hv nv))






abbrev Projection (m h : ℕ) := { f : ℕ → ℕ //
  f 0 = 0 ∧ (∀ d a b, d < 4 → f (combine d a b) = combine d (f a) (f b)) ∧
  (∀ a, Good m a → Good h (f a)) ∧ 0 < h }

namespace Projection
def toFun {m h : ℕ} (p : Projection m h) : ℕ → ℕ := p.val
theorem atZero {m h : ℕ} (p : Projection m h) : p.toFun 0 = 0 := p.property.1
theorem combineEq {m h : ℕ} (p : Projection m h) (d a b : ℕ) (hd : d < 4) :
    p.toFun (combine d a b) = combine d (p.toFun a) (p.toFun b) :=
  p.property.2.1 d a b hd
theorem good {m h : ℕ} (p : Projection m h) (a : ℕ) (ha : Good m a) :
    Good h (p.toFun a) := p.property.2.2.1 a ha
theorem someRow {m h : ℕ} (p : Projection m h) : 0 < h := p.property.2.2.2
end Projection

def Possible (m k : ℕ) (av : List ℕ) :=
  ∃ j S, j≤k ∧ Live m j S ∧ ∀ x∈S,x∈av
def charge (av : List ℕ) (z : ℕ) := z != 0 && !(av.contains z)
lemma pullPaid {m k d a b : ℕ} {av : List ℕ} (hd : d<4) (ha : a∈av) (hb : b∈av)
    (later : Possible m k (av++[combine d a b])) :
    Possible m (k+(charge av (combine d a b)).toNat) av := by
  let w := av.map (fun x => (false,x))
  have repr : reps w=av := by simp [w,reps,List.map_map,Function.comp_def]
  obtain ⟨j,S,lim,live,sub⟩ := later
  have needed : ∀ x∈S,x∈reps w++[combine d a b] := by simpa [repr] using sub
  have price : priced w (charge av (combine d a b)) (combine d a b) := by
    by_cases nz : combine d a b=0
    · exact Or.inl (Or.inl nz)
    by_cases old : combine d a b∈av
    · exact Or.inl (Or.inr (repr ▸ old))
    have paid : charge av (combine d a b)=true := by simp [charge,nz,old]
    have special : ¬(a=0 ∨ b=0 ∨ a=b) := by
      intro h
      rcases combine_eq_cases _ _ _ hd h with zero|rfl'|rfl'
      · exact nz zero
      · exact old (by rw [rfl'];exact ha)
      · exact old (by rw [rfl'];exact hb)
    exact Or.inr ⟨paid,d,hd,a,repr ▸ ha,b,repr ▸ hb,
      fun x => special (Or.inl x),fun x => special (Or.inr (Or.inl x)),fun x => special (Or.inr (Or.inr x)),rfl⟩
  obtain ⟨l,T,le,ok,sub'⟩ := pull live price needed
  exact ⟨l,T,by omega,ok,by simpa [repr] using sub'⟩

def dead (p : ℕ→ℕ) (S : Finset ℕ) := (S.filter (fun x => p x=0)).card
lemma deadStay {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (h : p a≠0) : dead p (insert a S)=dead p S := by
  simp [dead,Finset.filter_insert,h]
lemma deadLimit (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p (insert a S)≤dead p S+1 := by
  by_cases x : p a=0
  · simpa [dead,Finset.filter_insert,x] using Finset.card_insert_le a (S.filter (fun x => p x=0))
  · simp [deadStay x]
lemma deadMono (p : ℕ→ℕ) (a : ℕ) (S : Finset ℕ) : dead p S ≤ dead p (insert a S) := by
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
lemma deadGrow {p : ℕ→ℕ} {a : ℕ} {S : Finset ℕ} (z : p a=0) (fresh : a∉S) :
    dead p (insert a S)=dead p S+1 := by
  have nf : a∉S.filter (fun x => p x=0) := fun h => fresh (Finset.mem_filter.mp h).1
  simp [dead,Finset.filter_insert,z,Finset.card_insert_of_notMem nf]
lemma countCharge {m h d a b : ℕ} (p : Projection m h) (hd : d<4) (U : Finset ℕ)
    (fz : combine d a b∉insert a (insert b U)) (av : List ℕ) (ma : p.toFun a∈av) (mb : p.toFun b∈av) :
    (charge av (p.toFun (combine d a b))).toNat + dead p.toFun (insert a (insert b U)) ≤
      1+dead p.toFun (insert (combine d a b) U) := by
  have up := deadMono p.toFun (combine d a b) U
  have la := deadLimit p.toFun a (insert b U)
  have lb := deadLimit p.toFun b U
  have free (bad : p.toFun a=0 ∨ p.toFun b=0) : charge av (p.toFun (combine d a b))=false := by
    rw [p.combineEq _ _ _ hd]
    rcases combine_eq_cases _ _ _ hd (bad.imp_right Or.inl) with e|e|e <;> simp [charge,e,ma,mb]
  by_cases az : p.toFun a=0
  · rw [free (Or.inl az)];simp only [Bool.toNat_false,Nat.zero_add]
    by_cases bz : p.toFun b=0
    · have zz : p.toFun (combine d a b)=0 := by
        rw [p.combineEq _ _ _ hd,az,bz];interval_cases d <;> decide
      have fresh : combine d a b∉U := fun m => fz (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
      rw [deadGrow zz fresh];omega
    · rw [deadStay bz] at la;omega
  · rw [deadStay az]
    by_cases bz : p.toFun b=0
    · rw [free (Or.inr bz)];simp only [Bool.toNat_false,Nat.zero_add];omega
    · rw [deadStay bz];cases charge av (p.toFun (combine d a b)) <;> simp [Bool.toNat] <;> omega

theorem projectLive {m h k S} (p : Projection m h) (live : Live m k S) :
    ∃ j T,j+dead p.toFun S≤k ∧ Live h j T ∧ ∀ x∈T,x∈S.image p.toFun := by
  induction k generalizing S with
  | zero =>
    rw [Live] at live
    obtain ⟨a, rfl, hg, _⟩ := live
    have gp := p.good a hg
    have nz : p.toFun a≠0 := by intro e;have x := gp 0 p.someRow;simp [e] at x
    exact ⟨0,{p.toFun a},by simp [dead,nz],Live.done gp nz,by simp⟩
  | succ k ih =>
    rw [Live] at live
    obtain ⟨U, a, b, d, rfl, hd, ha, hb, ab, fz, tail⟩ := live
    obtain ⟨j,T,cost,ok,raw⟩ := ih tail
    let av := ((insert a (insert b U)).image p.toFun).toList
    have ma : p.toFun a∈av := by simp [av]
    have mb : p.toFun b∈av := by simp [av]
    have later : Possible h j (av++[combine d (p.toFun a) (p.toFun b)]) := by
      refine ⟨j,T,le_rfl,ok,?_⟩
      intro z hz
      have has := raw _ hz
      simp only [Finset.image_insert,Finset.mem_insert] at has
      rcases has with rfl|old
      · simp [p.combineEq d a b hd]
      · have inav : z∈av := by simpa [av] using (Or.inr (Or.inr old) : z=p.toFun a ∨ z=p.toFun b ∨ z∈U.image p.toFun)
        simp [inav]
    obtain ⟨l,V,lim,good,sub⟩ := pullPaid hd ma mb later
    rw [←p.combineEq d a b hd] at lim
    have bound := countCharge p hd U fz av ma mb
    exact ⟨l,V,by omega,good,by simpa [av] using sub⟩






lemma full_bit (m i : ℕ) : (full m).testBit i=decide (i<m) := by
  simp [full,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one]

lemma enoughSup {m k S} (h : Live m k S) (v : List ℕ) (sub : ∀ x∈S,x∈v) : enough m (cover m v)=true := by
  apply beq_iff_eq.mpr;apply Nat.eq_of_testBit_eq;intro i
  rw [Nat.testBit_and,full_bit]
  by_cases hi : i<m
  · obtain ⟨x,hx,g⟩ := liveSeparates h i hi
    have bit := (coverBit m i v).2 ⟨x,sub _ hx,g⟩
    simp [bit,hi]
  · simp [hi]
def start (m fuel : ℕ) (av : List ℕ) :=
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  extra.sublists.any (fun t =>
    let s := (must++t).dedup
    s.length≤fuel+1 && enough m (cover m s) && search m fuel s)

theorem start_complete {m k S} (h : Live m k S) (av : List ℕ) (sub : ∀ x∈S,x∈av)
    (fuel : ℕ) (lim : k≤fuel) : start m fuel av=true := by
  let v := av.eraseDups.filter (fun x => x != 0)
  let needed := fun a => !(enough m (cover m (v.filter (fun x => x != a))))
  let must := v.filter needed
  let extra := v.filter (fun x => !needed x)
  let t := extra.filter (fun x => decide (x∈S))
  let s := (must++t).dedup
  have inV (x : ℕ) (hx : x∈S) : x∈v := by simp [v,sub x hx,liveNonzero h x hx]
  have fixed (a : ℕ) (ha : a∈must) : a∈S := by
    by_contra absent
    have no := (List.mem_filter.mp ha).2
    have all (x : ℕ) (hx : x∈S) : x∈v.filter (fun y => y != a) := by
      have ne : x≠a := by rintro rfl;exact absent hx
      simp [inV x hx,ne]
    have yes := enoughSup h _ all
    simpa [needed,yes] using no
  have eq : s.toFinset=S := by
    ext x
    constructor
    · intro mem
      have e : x∈must ∨ x∈t := by simpa [s] using mem
      rcases e with l|r
      · exact fixed x l
      · simpa using (List.mem_filter.mp r).2
    · intro mem
      have raw := inV x mem
      cases H : needed x <;> simp [s,must,t,extra,H,raw,mem]
  have nd : s.Nodup := List.nodup_dedup _
  have size : s.length≤fuel+1 := by
    have vsize := liveSize h
    rw [←eq,List.toFinset_card_of_nodup nd] at vsize;omega
  have test := complete m fuel h lim s eq nd
  have cov := enoughLive h s eq
  apply List.any_eq_true.mpr
  refine ⟨t,List.mem_sublists.mpr (List.filter_sublist),?_⟩
  change (decide (s.length≤fuel+1) && enough m (cover m s) && search m fuel s)=true
  simp [size,cov,test]


def actL : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p :: ps, w => Nat.bit (w.testBit p) (actL ps w)

theorem actL_testBit : ∀ (pi : List ℕ) (w k : ℕ),
    (actL pi w).testBit k = (pi[k]?.map w.testBit).getD false
  | [], w, k => by simp [actL]
  | p :: ps, w, 0 => by simp [actL, Nat.testBit_bit_zero]
  | p :: ps, w, k + 1 => by simp [actL, Nat.testBit_bit_succ, actL_testBit ps w k]

theorem actL_and (pi : List ℕ) (a b : ℕ) : actL pi (a &&& b) = actL pi a &&& actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_and, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_and]

theorem actL_or (pi : List ℕ) (a b : ℕ) : actL pi (a ||| b) = actL pi a ||| actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_or, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_or]

theorem actL_xor (pi : List ℕ) (a b : ℕ) : actL pi (a ^^^ b) = actL pi a ^^^ actL pi b := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor, actL_testBit, actL_testBit, actL_testBit]
  cases pi[k]? <;> simp [Nat.testBit_xor]

def coord (m : ℕ) (r : List ℕ) := actL (r ++ r.map (m+·))

theorem coordC (m : ℕ) (r : List ℕ) (d a b : ℕ) (hd : d < 4) :
    coord m r (combine d a b) = combine d (coord m r a) (coord m r b) := by
  interval_cases d <;> simp [combine,coord,actL_and,actL_or,actL_xor]

def pick {m h : ℕ} (r : List ℕ) (len : r.length=h) (small : ∀ i∈r,i<m) (pos : 0<h) : Projection m h := by
  refine ⟨coord m r, ?_, coordC m r, ?_, pos⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    simp only [coord,actL_testBit,Nat.zero_testBit]
    cases (r ++ r.map (m+·))[i]? <;> simp
  · intro a ha i hi
    have ir : i<r.length := by omega
    have b := ha r[i] (small _ (List.getElem_mem ir))
    have H₁ : (r ++ r.map (m+·))[i]? = some r[i] := by simp [List.getElem?_append,ir]
    have H₂ : (r ++ r.map (m+·))[h+i]? = some (m+r[i]) := by
      have ne : ¬h+i<r.length := by omega
      have sub : h+i-r.length=i := by omega
      simp [List.getElem?_append,ne,sub,ir]
    simpa [coord,actL_testBit,H₁,H₂] using b

def Ban (m fuel : ℕ) (v : List ℕ) := ∀ n, n ≤ fuel → ¬Live m n v.toFinset
def Wide (m fuel : ℕ) (v : List ℕ) := ¬Possible m fuel v

theorem viaSearch {m fuel v} (test : start m fuel v=false) : Wide m fuel v := by
  rintro ⟨k,S,le,live,sub⟩
  have := start_complete live v sub fuel le
  simp_all


end SignedKernel26514



namespace Lower26514
open SignedKernel26514
private abbrev rows {n : Nat} (v : Fin n → Nat) (j : Nat) (i : Fin n) := (v i).testBit j
private def bank {n : Nat} (v : Fin n → Nat) := 0 :: List.ofFn v
private def Covered {n : Nat} (r : Nat → Fin n → Bool) (av : List Nat) (v : List (Fn n)) := ∀ f∈v, ∃ w : Wire, w.2 ∈ av ∧ ∀ j, read j w = f (r j)
private theorem covStart {n : Nat} (v : Fin n → Nat) : Covered (rows v) (bank v) start := by
  intro f hf
  simp [start] at hf
  rcases hf with rfl | rfl | ⟨i, rfl | rfl⟩
  · exact ⟨zero,by simp [zero,bank],fun j => read_zero j⟩
  · exact ⟨flip zero,by simp [zero,SignedKernel26514.flip,bank],fun j => by simp [read_flip,read_zero]⟩
  · exact ⟨(false,v i),by simp [bank],fun j => by simp [SignedKernel26514.read,rows]⟩
  · exact ⟨(true,v i),by simp [bank],fun j => by simp [SignedKernel26514.read,rows]⟩
private theorem possibleOfRun {n m : Nat} {v : List (Fn n)} {k : Nat} {t : Fn n} (run : Run v k t)
    (r : Nat → Fin n → Bool) (pos : 0<m) (diff : ∀ i<m, t (r i) ≠ t (r (m+i)))
    (av : List Nat) (cov : Covered r av v) : Possible m k av := by
  induction run generalizing av with
  | stop mem =>
    obtain ⟨w, wm, hw⟩ := cov _ mem
    have good : Good m w.2 := by
      intro i hi eq
      have same : read i w = read (m+i) w := by simp [SignedKernel26514.read,eq]
      exact diff i hi (by simpa only [hw] using same)
    have nz : w.2≠0 := by intro h; have hh:=good 0 pos; simp [h] at hh
    exact ⟨0,{w.2},Nat.zero_le _,Live.done good nz,by simpa using wm⟩
  | @step v k t a b ha hb rest ih =>
    obtain ⟨u,hu,ua⟩ := cov a ha
    obtain ⟨w,hw,wb⟩ := cov b hb
    let z := meet u w
    have ext : Covered r (av++[z.2]) (v++[fun x => a x && b x,fun x => !(a x && b x)]) := by
      intro f hf
      rcases List.mem_append.mp hf with old|new
      · obtain ⟨c,hc,ce⟩ := cov f old
        exact ⟨c,List.mem_append_left _ hc,ce⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at new
        rcases new with rfl|rfl
        · exact ⟨z,by simp,fun j => by simp [z,read_meet,ua,wb]⟩
        · exact ⟨flip z,by simp [SignedKernel26514.flip],fun j => by simp [read_flip,z,read_meet,ua,wb]⟩
    obtain ⟨l,S,le,live,sub⟩ := pullPaid (op_lt u.1 w.1) hu hw (ih diff _ ext)
    refine ⟨l,S,?_,live,sub⟩
    exact le.trans (Nat.add_le_add_left (Bool.toNat_le _) _)
private theorem certify {n m k : Nat} (v : Fin n → Nat) (t : Fn n) (pos : 0<m)
    (labels : ∀ i : Fin m, t (rows v i.val) ≠ t (rows v (m+i.val)))
    (closed : SignedKernel26514.start m k (bank v)=false) : ¬Run start k t := by
  intro run
  exact viaSearch closed (possibleOfRun run (rows v) pos (fun i hi => labels ⟨i,hi⟩) _ (covStart v))


private def colsFive : Fin 5 → Nat := ![0x412c6221f673,0x184908cc6487f,0x20b0531078f9c,0xd01ac1f80fe0,0x32ec001fff000]
private def colsSix : Fin 6 → Nat := ![0x1880c5170542e61734fc,0x10a0852314a8d3869c8cf,0x4c470238142b331c18e0f0f,0xb0b805c02a83c3e01f00ff0,0xff0007728003fc001fff000,0xffee50000003ffffe000000]




set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem noFive : ¬ Run start 6 five :=
  certify (m:=25) colsFive five (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem noSix : ¬ Run start 7 six :=
  certify (m:=46) colsSix six (by decide) (by decide +kernel) (by decide +kernel)
end Lower26514



namespace Physical26514
open PEqualNP.CircuitLowerBounds Lower26514

private def neg {n} (f : Fn n) : Fn n := fun x => !(f x)
private def Dual {n} (v : List (Fn n)) (f : Fn n) := f ∈ v ∧ neg f ∈ v
private abbrev zeroF {n} : Fn n := fun _ => false
private theorem dualNeg {n} {v : List (Fn n)} {f} (h : Dual v f) : Dual v (neg f) := by
  have e : neg (neg f) = f := by funext x; simp [neg]
  exact ⟨h.2, e.symm ▸ h.1⟩
private theorem dualIncl {n} {v w : List (Fn n)} {f} (sub : v ⊆ w) (h : Dual v f) : Dual w f := ⟨sub h.1,sub h.2⟩
private theorem raise {n} {v : List (Fn n)} {k t} (h : Run v k t) : Run v (k+1) t := by
  induction h with
  | stop hm => exact .stop hm
  | step ha hb _ ih => exact .step ha hb ih

private def value {n} (ws : List (Fn n)) (g : Gate) : Fn n := fun x =>
  g.op.eval (g.inputs.map fun i => (ws.getD i zeroF) x)
private def extend {n} (ws : List (Fn n)) (g : Gate) := ws ++ [value ws g]
private def scalar (ws : List Bool) (g : Gate) := ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
private abbrev Good (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
private def cost (g : Gate) := match g.op with | .not => 0 | _ => 1

private theorem takeGate {n k} {v ws : List (Fn n)} {t : Fn n} (g : Gate) (ok : Good g)
    (hz : Dual v zeroF) (hw : ∀ i, Dual v (ws.getD i zeroF))
    (cont : ∀ u : List (Fn n), v ⊆ u → Dual u (value ws g) → Run u k t) : Run v (k+cost g) t := by
  rcases g with ⟨op,ins⟩
  obtain ⟨hOp,hlen⟩ := ok
  cases ins with
  | nil => rcases hOp with rfl|rfl|rfl
           · exact raise (cont v (fun _ h => h) (dualNeg hz))
           · exact raise (cont v (fun _ h => h) hz)
           · exact cont v (fun _ h => h) (dualNeg hz)
  | cons a l => cases l with
    | nil => rcases hOp with rfl|rfl|rfl
             · apply raise; apply cont _ (fun _ h => h)
               convert hw a using 1; funext x; simp [value,GateOp.eval]
             · apply raise; apply cont _ (fun _ h => h)
               convert hw a using 1; funext x; simp [value,GateOp.eval]
             · exact cont v (fun _ h => h) (dualNeg (hw a))
    | cons b tail =>
      have hnil : tail = [] := by simpa using hlen
      subst tail
      rcases hOp with rfl|rfl|rfl
      · apply Run.step (hw a).1 (hw b).1
        apply cont _ (List.subset_append_left ..)
        constructor <;> apply List.mem_append_right <;> simp only [List.mem_cons,List.not_mem_nil,or_false]
        · left; funext x; simp [value,GateOp.eval]
        · right; funext x; simp [value,neg,GateOp.eval]
      · apply Run.step (hw a).2 (hw b).2
        apply cont _ (List.subset_append_left ..)
        constructor <;> apply List.mem_append_right <;> simp only [List.mem_cons,List.not_mem_nil,or_false]
        · right; funext x; simp [value,neg,GateOp.eval]
        · left; funext x; simp [value,neg,GateOp.eval]
      · exact cont v (fun _ h => h) (dualNeg (hw a))

private theorem avail {n} {v ws : List (Fn n)} (hz : Dual v zeroF) (hw : ∀ f ∈ ws, Dual v f)
    (i : Nat) : Dual v (ws.getD i zeroF) := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]; exact hw _ (List.getElem_mem _)
  · simpa [List.getD_eq_getElem?_getD,h] using hz

private theorem compile {n} (gs : List Gate) (o : Nat) (ws v : List (Fn n))
    (hgood : ∀ g ∈ gs, Good g) (hz : Dual v zeroF) (hw : ∀ f ∈ ws, Dual v f) :
    Run v (gs.map cost).sum ((gs.foldl extend ws).getD o zeroF) := by
  induction gs generalizing v ws with
  | nil => exact .stop (avail hz hw o).1
  | cons g gs ih =>
    rw [List.map_cons,List.sum_cons,Nat.add_comm,List.foldl_cons]
    apply takeGate g (hgood _ List.mem_cons_self) hz (avail hz hw)
    intro u sub hval
    apply ih _ _ (fun q hq => hgood q (List.mem_cons_of_mem _ hq)) (dualIncl sub hz)
    intro f hf
    rcases List.mem_append.mp hf with h | h
    · exact dualIncl sub (hw _ h)
    · obtain rfl := List.mem_singleton.mp h; exact hval

private theorem readMap {n} (x : Fin n → Bool) (ws : List (Fn n)) (i : Nat) :
    (ws.map (fun f => f x)).getD i false = ws.getD i zeroF x := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]; cases ws[i]? <;> rfl
private theorem foldMap {n} (x : Fin n → Bool) (gs : List Gate) (ws : List (Fn n)) :
    (gs.foldl extend ws).map (fun f => f x) = gs.foldl scalar (ws.map fun f => f x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih => simp only [List.foldl_cons,ih,extend,List.map_append,List.map_cons,List.map_nil,scalar,value,readMap]

private theorem cost_le (gs : List Gate) : (gs.map cost).sum ≤ gs.length := by
  induction gs with
  | nil => decide
  | cons g gs ih => cases g with | mk op ins => cases op <;> simp [cost] at * <;> omega
private theorem cost_lt {gs : List Gate} (h : ∃ g ∈ gs, g.op = .not) : (gs.map cost).sum < gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    by_cases hg : g.op = .not
    · have h0 : cost g = 0 := by simp [cost,hg]
      simpa [h0] using Nat.lt_succ_of_le (cost_le gs)
    · have htail : ∃ q ∈ gs, q.op = .not := by
        obtain ⟨q,hq,hop⟩ := h; rcases List.mem_cons.mp hq with rfl|hmem
        · contradiction
        · exact ⟨q,hmem,hop⟩
      have hcost : cost g ≤ 1 := by cases g with | mk op ins => cases op <;> simp [cost]
      simp; specialize ih htail; omega


theorem normalize {n} (gs : List Gate) (o : Nat) (hgood : ∀ g ∈ gs, Good g)
    (hnot : ∃ g ∈ gs, g.op = .not) (t : Fn n)
    (rep : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = t x) :
    ∃ k, k + 1 ≤ gs.length ∧ Run start k t := by
  let raw : List (Fn n) := List.ofFn fun i : Fin n => fun x => x i
  have hz : Dual (start (n:=n)) zeroF := ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
  have hin : ∀ f ∈ raw, Dual start f := by
    intro f hf; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    have hh : [fun x : Fin n → Bool => x i,fun x => !(x i)] ∈
        List.ofFn (fun j : Fin n => [fun x => x j,fun x => !(x j)]) := List.mem_ofFn.mpr ⟨i,rfl⟩
    constructor <;> apply List.mem_append_right <;> apply List.mem_flatten.mpr
    · exact ⟨_,hh,List.mem_cons_self⟩
    · exact ⟨_,hh,List.mem_cons_of_mem _ List.mem_cons_self⟩
  have h := compile gs o raw start hgood hz hin
  have heq : (gs.foldl extend raw).getD o zeroF = t := by
    funext x
    rw [←readMap,foldMap]
    simp only [raw,List.map_ofFn,Function.comp_def]; exact rep x
  exact ⟨_,cost_lt hnot,heq ▸ h⟩


theorem convertOfLower {n} {t : Fn n} {gs ms : List Gate} {o out : Nat}
    (hgood : ∀ g ∈ gs, Good g) (rep : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = t x)
    (hmono : ∀ g ∈ ms, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hrep : ∀ x, Circuit.eval ⟨ms,out⟩ (List.ofFn x) = t x)
    (lower : ∀ k, Run start k t → ms.length ≤ k+1) :
    ∃ (ls : List Gate) (z : Nat), (∀ g ∈ ls, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      ls.length ≤ gs.length ∧ ∀ x, Circuit.eval ⟨ls,z⟩ (List.ofFn x) = t x := by
  by_cases h : ∃ g ∈ gs, g.op = .not
  · obtain ⟨k,hk,hr⟩ := normalize gs o hgood h t rep
    exact ⟨ms,out,hmono,le_trans (lower k hr) hk,hrep⟩
  · refine ⟨gs,o,?_,le_rfl,rep⟩
    intro g hg
    obtain ⟨ho,hf⟩ := hgood g hg
    exact ⟨ho.imp_right (fun q => q.resolve_right (fun hn => h ⟨g,hg,hn⟩)),hf⟩

end Physical26514



namespace Witness26514
open PEqualNP.CircuitLowerBounds

def edges : List Nat := [0,4,1,4,0,5,1,5,2,5,0,6,2,6,4,6,0,7,1,7,2,7,3,7]

def graph (x : Fin 8 → Bool) : Bool := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)



def gates : List Gate := [
  ⟨.or,[0,1]⟩, ⟨.and,[8,4]⟩, ⟨.or,[8,2]⟩, ⟨.or,[5,7]⟩,
  ⟨.and,[10,11]⟩, ⟨.or,[0,2]⟩, ⟨.or,[13,4]⟩, ⟨.and,[6,14]⟩,
  ⟨.and,[3,7]⟩, ⟨.or,[9,12]⟩, ⟨.or,[15,16]⟩, ⟨.or,[17,18]⟩]

theorem size : gates.length = 12 := rfl
theorem mono : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [gates]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem computes : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,19⟩ (List.ofFn x) = graph x := by
  decide +kernel

end Witness26514





namespace Complete26514
open Coord26514 Pin26514 Lower26514 Witness26514

def c0 : Fin 8 → Code 7 := ![none,some 0,some 1,some 2,some 3,some 4,some 5,some 6]
def c3 : Fin 7 → Code 6 := ![some 0,some 1,none,some 3,some 4,some 2,some 5]
def c7 : Fin 6 → Code 5 := ![some 0,some 3,some 2,some 1,some 4,none]
def f7 : Fn 7 := graph ∘ pin c0 false
def f6 (b : Bool) : Fn 6 := f7 ∘ pin c3 b
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem lower (k) (h : Run start k graph) : 11 ≤ k := by
  have d0 : ¬stable c0 graph := by unfold stable; decide +kernel
  have n0 : ¬Const f7 := by unfold Const; decide +kernel
  obtain ⟨l,hl,hr⟩ := one c0 false graph h d0 n0
  have d3 : ¬stable c3 f7 := by unfold stable; decide +kernel
  have n3 : ∀ b,¬Const (f6 b) := by unfold Const; decide +kernel
  obtain ⟨b,j,hj,hjrun⟩ := two c3 f7 hr d3 n3
  change Run start j (f6 b) at hjrun
  cases b with
  | false =>
    have eq : f6 false = six := funext (by decide +kernel)
    rw [eq] at hjrun; by_contra! small; exact noSix (weaken hjrun (by omega))
  | true =>
    have d7 : ¬stable c7 (f6 true) := by unfold stable; decide +kernel
    have n7 : ¬Const (f6 true ∘ pin c7 false) := by unfold Const; decide +kernel
    obtain ⟨i,hi,hirun⟩ := one c7 false (f6 true) hjrun d7 n7
    have eq : f6 true ∘ pin c7 false = five := funext (by decide +kernel)
    rw [eq] at hirun; by_contra! small; exact noFive (weaken hirun (by omega))
end Complete26514

end PEqualNP.Outside.L_meta_26514_aux
open PEqualNP.Outside.L_meta_26514_aux
theorem PEqualNP.Outside.L_meta_26514 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fan _ rep
  apply Physical26514.convertOfLower fan rep Witness26514.mono Witness26514.computes
  intro k h; rw [Witness26514.size]; have := Complete26514.lower k h; omega
