import PEqualNP.Defs

-- The free-inversion circuit model, circuit conversion, and gate elimination
-- are adapted from L-meta-13643 by justusklocke-cloud.
-- The paired-assignment search is adapted from L-meta-37409.
namespace PEqualNP.Outside.L_meta_42970

namespace FreeAIG
abbrev Fn (α : Type*) := α → Bool
def neg {α} (f : Fn α) : Fn α := fun x => !(f x)
def meet {α} (a b : Fn α) : Fn α := fun x => a x && b x

inductive Avail {α : Type*} (S : Set (Fn α)) : Fn α → Prop where
  | src {f} : f∈S → Avail S f
  | const (b : Bool) : Avail S (fun _ => b)
  | neg {f} : Avail S f → Avail S (FreeAIG.neg f)

inductive Has {α : Type*} : Set (Fn α) → Nat → Fn α → Prop where
  | done {S k f} : Avail S f → Has S k f
  | step {S k a b f} : Avail S a → Avail S b → Has (insert (meet a b) S) k f → Has S (k+1) f

theorem Avail.lift {α : Type*} {S T : Set (Fn α)} (h : ∀g∈S,Avail T g) {f} (p : Avail S f) :
    Avail T f := by
  induction p with
  | src hs => exact h _ hs
  | const b => exact .const b
  | neg _ ih => exact .neg ih

theorem Avail.extend {α : Type*} {S : Set (Fn α)} {a f} (p : Avail S f) :
    Avail (insert a S) f := p.lift (fun _ hs=>.src (Set.mem_insert_of_mem _ hs))

theorem Avail.map {α β : Type*} {S : Set (Fn α)} {T : Set (Fn β)} (φ : β→α)
    (h : ∀g∈S,Avail T (g∘φ)) {f} (p : Avail S f) : Avail T (f∘φ) := by
  induction p with
  | src hs => exact h _ hs
  | const b => exact .const b
  | neg _ ih => exact .neg ih

theorem Has.map {α β : Type*} {S : Set (Fn α)} {T : Set (Fn β)} (φ : β→α)
    (h : ∀g∈S,Avail T (g∘φ)) {k f} (p : Has S k f) : Has T k (f∘φ) := by
  induction p generalizing T with
  | done hp => exact .done (hp.map φ h)
  | @step S k a b f ha hb _ ih =>
    apply Has.step (ha.map φ h) (hb.map φ h)
    apply ih
    rintro g (rfl|hg)
    · exact .src (Set.mem_insert _ _)
    · exact (h g hg).extend

def Inputs {n} : Set (Fn (Fin n→Bool)) := {g | ∃ i : Fin n,g=fun x=>x i}

theorem meetFalseR {α} (a : Fn α) : meet a (fun _=>false)=(fun _=>false) := by funext x;simp [meet]
theorem meetTrueR {α} (a : Fn α) : meet a (fun _=>true)=a := by funext x;simp [meet]
theorem meetFalseL {α} (b : Fn α) : meet (fun _=>false) b=(fun _=>false) := by funext x;simp [meet]
theorem meetTrueL {α} (b : Fn α) : meet (fun _=>true) b=b := by funext x;simp [meet]

def Restricted {α} (φ : α→α) (f : Fn α) := f∘φ=f ∨ ∃ b : Bool, f∘φ=fun _=>b

theorem Avail.restricted {α : Type*} {φ : α→α} {S : Set (Fn α)}
    (h : ∀g∈S,Restricted φ g) {f} (p : Avail S f) : Restricted φ f := by
  induction p with
  | src hs => exact h _ hs
  | const b => exact Or.inl rfl
  | @neg g _ ih =>
    rcases ih with eq|⟨b,eq⟩
    · exact Or.inl (congrArg FreeAIG.neg eq)
    · exact Or.inr ⟨!b,congrArg FreeAIG.neg eq⟩

theorem Has.save {α : Type*} {S T : Set (Fn α)} (φ : α→α) (mapS : ∀g∈S,Avail T (g∘φ))
    (good : ∀g∈S,Restricted φ g) {k f} (p : Has S k f) (hn : ¬Restricted φ f) :
    ∃ t, t+1≤k ∧ Has T t (f∘φ) := by
  induction p generalizing T with
  | done hp => exact (hn (hp.restricted good)).elim
  | @step S k a b f ha hb tail ih =>
    have ma := ha.map φ mapS
    have mb := hb.map φ mapS
    have finish (cheap : Avail T ((meet a b)∘φ)) : ∃ t, t+1≤k+1 ∧ Has T t (f∘φ) := by
      refine ⟨k,le_rfl,tail.map φ ?_⟩
      rintro g (rfl|hg)
      · exact cheap
      · exact mapS g hg
    rcases ha.restricted good with ea|⟨ba,ea⟩
    · rcases hb.restricted good with eb|⟨bb,eb⟩
      · have join : (meet a b)∘φ=meet a b := congrArg₂ meet ea eb
        obtain ⟨t,ht,sm⟩ := ih (T:=insert (meet (a∘φ) (b∘φ)) T) (by
          rintro g (rfl|hg)
          · exact .src (Set.mem_insert _ _)
          · exact (mapS g hg).extend) (by
          rintro g (rfl|hg)
          · exact Or.inl join
          · exact good g hg) hn
        exact ⟨t+1,by omega,.step ma mb sm⟩
      · apply finish
        change Avail T (meet (a∘φ) (b∘φ))
        rw [eb]
        cases bb
        · rw [meetFalseR];exact .const false
        · rw [meetTrueR];exact ma
    · apply finish
      change Avail T (meet (a∘φ) (b∘φ))
      rw [ea]
      cases ba
      · rw [meetFalseL];exact .const false
      · rw [meetTrueL];exact mb

theorem fixSave {n} (f : Fn (Fin n→Bool)) (i : Fin n) (b : Bool)
    (dep : ∃ x, f (Function.update x i b) ≠ f x)
    (nc : ∃ x x', f (Function.update x i b) ≠ f (Function.update x' i b))
    {k} (p : Has Inputs k f) :
    ∃ t, t+1≤k ∧ Has Inputs t (fun x=>f (Function.update x i b)) := by
  let φ : (Fin n→Bool)→(Fin n→Bool) := fun x=>Function.update x i b
  have other {j : Fin n} (ne : j≠i) : ((fun x : Fin n→Bool=>x j)∘φ)=(fun x=>x j) := by
    funext x;simp [φ,ne]
  have same : ((fun x : Fin n→Bool=>x i)∘φ)=(fun _=>b) := by funext x;simp [φ]
  apply p.save φ
  · rintro g ⟨j,rfl⟩
    by_cases e : j=i
    · subst j;rw [same];exact .const b
    · rw [other e];exact .src ⟨j,rfl⟩
  · rintro g ⟨j,rfl⟩
    by_cases e : j=i
    · subst j; exact Or.inr ⟨b,same⟩
    · exact Or.inl (other e)
  · rintro (eq|⟨v,eq⟩)
    · obtain ⟨x,h⟩ := dep
      exact h (congrFun eq x)
    · obtain ⟨x,x',h⟩ := nc
      exact h ((congrFun eq x).trans (congrFun eq x').symm)

def PinPattern {α : Type*} (φ : Bool→α→α) (g : Fn α) : Prop :=
  (∀ b,g∘φ b=g) ∨ ∃ q : Bool,∀ b,g∘φ b=(fun _=>decide (b≠q))

theorem PinPattern.restrict {α : Type*} {φ : Bool→α→α} {g : Fn α}
    (h : PinPattern φ g) (b : Bool) : Restricted (φ b) g := by
  rcases h with same|⟨q,eq⟩
  · exact .inl (same b)
  · exact .inr ⟨_,eq b⟩

theorem Avail.pattern {α : Type*} {φ : Bool→α→α} {S : Set (Fn α)} {g : Fn α}
    (h : ∀ f∈S,PinPattern φ f) (a : Avail S g) : PinPattern φ g := by
  induction a with
  | src hs=>exact h _ hs
  | const v=>exact .inl (fun _=>rfl)
  | @neg f orig ih=>
    rcases ih with same|⟨q,eq⟩
    · exact .inl (fun b=>congrArg FreeAIG.neg (same b))
    · refine .inr ⟨!q,?_⟩
      intro v
      have z:=congrArg FreeAIG.neg (eq v)
      cases q <;> cases v <;> exact z

theorem Has.saveTwo {α : Type*} {S : Set (Fn α)} {k : Nat} {f : Fn α}
    (p : Has S k f) (φ : Bool→α→α) {T : Bool→Set (Fn α)}
    (maps : ∀ v g,g∈S → Avail (T v) (g∘φ v))
    (shapes : ∀g∈S,PinPattern φ g) (nontrivial : ∀v,¬Restricted (φ v) f) :
    ∃ v t,t+2≤k ∧ Has (T v) t (f∘φ v) := by
  induction p generalizing T with
  | done last=>exact (nontrivial false ((last.pattern shapes).restrict false)).elim
  | @step S k a b f ha hb tail ih=>
    have finish (v : Bool) (dead : (meet a b)∘φ v=(fun _=>false)) :
        ∃ v t,t+2≤k+1 ∧ Has (T v) t (f∘φ v) := by
      obtain ⟨q,sz,net⟩:=tail.save (T:=T v) (φ v) (by
        rintro g (rfl|m)
        · rw [dead];exact .const false
        · exact maps _ _ m) (by
        rintro g (rfl|m)
        · exact .inr ⟨false,dead⟩
        · exact (shapes _ m).restrict v) (nontrivial v)
      exact ⟨v,q,by omega,net⟩
    rcases ha.pattern shapes with sa|⟨v,eq⟩
    · rcases hb.pattern shapes with sb|⟨v,eq⟩
      · obtain ⟨v,q,sz,net⟩:=ih (T:=fun v=>insert (meet (a∘φ v) (b∘φ v)) (T v))
          (by intro v g m;rcases m with rfl|m
              · exact .src (Set.mem_insert _ _)
              · exact (maps _ _ m).extend)
          (by rintro g (rfl|m)
              · exact .inl (fun v=>congrArg₂ meet (sa v) (sb v))
              · exact shapes _ m) nontrivial
        exact ⟨v,q+1,by omega,.step (ha.map _ (maps v)) (hb.map _ (maps v)) net⟩
      · apply finish v
        change meet (a∘φ v) (b∘φ v) = _
        rw [eq v];simp [meetFalseL,meetFalseR]
    · apply finish v
      change meet (a∘φ v) (b∘φ v) = _
      rw [eq v];simp [meetFalseL,meetFalseR]

theorem pinTwo {n} (f : Fn (Fin n→Bool)) (i : Fin n)
    (dep : ∀b,∃ x, f (Function.update x i b) ≠ f x)
    (nc : ∀b,∃ x y,f (Function.update x i b) ≠ f (Function.update y i b))
    {k} (p : Has Inputs k f) :
    ∃ b t,t+2≤k ∧ Has Inputs t (fun x=>f (Function.update x i b)) := by
  let φ := fun (b : Bool) (x : Fin n→Bool)=>Function.update x i b
  have own (b : Bool) : ((fun x : Fin n→Bool=>x i)∘φ b)=(fun _=>b) := by funext x;simp [φ]
  have other (j : Fin n) (h : j≠i) (b : Bool) : ((fun x : Fin n→Bool=>x j)∘φ b)=(fun x=>x j) := by
    funext x;simp [φ,h]
  apply p.saveTwo (T:=fun _=>Inputs) φ
  · rintro b _ ⟨j,rfl⟩
    by_cases e:j=i
    · subst j;rw [own];exact .const b
    · rw [other j e];exact .src ⟨j,rfl⟩
  · rintro g ⟨j,rfl⟩
    by_cases e:j=i
    · subst j
      exact .inr ⟨false,fun b=>by cases b <;> exact own _⟩
    · exact .inl (other j e)
  · intro b
    rintro (same|⟨v,eq⟩)
    · obtain ⟨x,h⟩:=dep b
      exact h (congrFun same x)
    · obtain ⟨x,y,h⟩:=nc b
      exact h ((congrFun eq x).trans (congrFun eq y).symm)


variable {n : Nat}

def cofactorAt (f : Fn (Fin (n + 1) → Bool)) (i : Fin (n + 1)) (b : Bool) :
    Fn (Fin n → Bool) :=
  fun x => f (i.insertNth (α := fun _ => Bool) b x)

variable {f : Fn (Fin (n + 1) → Bool)} {i : Fin (n + 1)} {b : Bool} {k m : Nat}

theorem Has.cofactorAt (h : Has Inputs k f) (i : Fin (n + 1)) (b : Bool) :
    Has Inputs k (cofactorAt f i b) := by
  apply h.map (i.insertNth (α := fun _ => Bool) b)
  rintro _ ⟨j, rfl⟩
  refine Fin.succAboveCases i ?_ (fun a => ?_) j
  · simpa [Function.comp_def] using (Avail.const (S := Inputs) b)
  · simpa [Function.comp_def] using
      (Avail.src (S := Inputs) (show (fun x : Fin n → Bool => x a) ∈ Inputs from ⟨a, rfl⟩))

private theorem canChange (dep : ∃ x, cofactorAt f i false x ≠ cofactorAt f i true x)
    (b : Bool) : ∃ x, f (Function.update x i b) ≠ f x := by
  obtain ⟨x, hx⟩ := dep
  refine ⟨i.insertNth (α := fun _ => Bool) (!b) x, ?_⟩
  cases b
  · simpa only [FreeAIG.cofactorAt, Bool.not_false, Fin.update_insertNth] using hx
  · simpa only [FreeAIG.cofactorAt, Bool.not_true, Fin.update_insertNth] using Ne.symm hx

private theorem canVary (nc : ∃ x y, cofactorAt f i b x ≠ cofactorAt f i b y) :
    ∃ x y, f (Function.update x i b) ≠ f (Function.update y i b) := by
  obtain ⟨x, y, h⟩ := nc
  exact ⟨i.insertNth (α := fun _ => Bool) b x, i.insertNth (α := fun _ => Bool) b y,
    by simpa only [FreeAIG.cofactorAt, Fin.update_insertNth] using h⟩

private theorem shrink {q : Nat} (h : Has Inputs q (fun x => f (Function.update x i b))) :
    Has Inputs q (cofactorAt f i b) := by
  have eq : cofactorAt (fun x => f (Function.update x i b)) i b = cofactorAt f i b := by
    funext x
    exact congrArg f (Fin.update_insertNth (α := fun _ => Bool) i b b x)
  exact eq ▸ h.cofactorAt i b

theorem saveOneCofactor (dep : ∃ x, cofactorAt f i false x ≠ cofactorAt f i true x)
    (nc : ∃ x y, cofactorAt f i b x ≠ cofactorAt f i b y) (h : Has Inputs k f) :
    ∃ q, q + 1 ≤ k ∧ Has Inputs q (cofactorAt f i b) := by
  obtain ⟨q, hq, net⟩ := fixSave f i b (canChange dep b) (canVary nc) h
  exact ⟨q, hq, shrink net⟩

theorem saveTwoCofactors (dep : ∃ x, cofactorAt f i false x ≠ cofactorAt f i true x)
    (nc : ∀ v, ∃ x y, cofactorAt f i v x ≠ cofactorAt f i v y) (h : Has Inputs k f) :
    ∃ v q, q + 2 ≤ k ∧ Has Inputs q (cofactorAt f i v) := by
  obtain ⟨v, q, hq, net⟩ := pinTwo f i (canChange dep) (fun v => canVary (nc v)) h
  exact ⟨v, q, hq, shrink net⟩

private theorem variesOfPositiveLower {g : Fn (Fin n → Bool)} (positive : 0 < m)
    (lower : ∀ {q}, Has Inputs q g → m ≤ q) : ∃ x y, g x ≠ g y := by
  classical
  by_contra! h
  let zero : Fin n → Bool := fun _ => false
  have eq : g = fun _ => g zero := funext (fun x => h x zero)
  have trivial : Has Inputs 0 g := by
    conv => arg 3; rw [eq]
    exact .done (.const _)
  exact (Nat.not_le_of_gt positive) (lower trivial)

theorem oneCofactorLower (positive : 0 < m)
    (dep : ∃ x, cofactorAt f i false x ≠ cofactorAt f i true x)
    (lower : ∀ {q}, Has Inputs q (cofactorAt f i b) → m ≤ q)
    (h : Has Inputs k f) : m + 1 ≤ k := by
  obtain ⟨q, hq, net⟩ := saveOneCofactor dep (variesOfPositiveLower positive lower) h
  exact le_trans (Nat.add_le_add_right (lower net) 1) hq

theorem twoCofactorsLower (positive : 0 < m)
    (dep : ∃ x, cofactorAt f i false x ≠ cofactorAt f i true x)
    (lower : ∀ v {q}, Has Inputs q (cofactorAt f i v) → m ≤ q)
    (h : Has Inputs k f) : m + 2 ≤ k := by
  obtain ⟨v, q, hq, net⟩ := saveTwoCofactors dep (fun v => variesOfPositiveLower positive (lower v)) h
  exact le_trans (Nat.add_le_add_right (lower v net) 2) hq

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def price : GateOp → Nat | .not => 0 | _ => 1
def binaryCount : List Gate → Nat
  | [] => 0
  | g::gs => price g.op + binaryCount gs

theorem leLength (gs : List Gate) : binaryCount gs ≤ gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h:g.op <;> simp [binaryCount,h,price] <;> omega

theorem notDiscount {gs : List Gate} (h : ∃ g∈gs,g.op=.not) : binaryCount gs+1≤gs.length := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨u,hu,op⟩ := h
    rcases List.mem_cons.mp hu with rfl|hg
    · simpa [binaryCount,op,price] using leLength gs
    · have hlt := ih ⟨u,hg,op⟩
      cases h:g.op <;> simp [binaryCount,h,price] <;> omega

theorem Has.bump {α : Type*} {S : Set (Fn α)} {k f} (p : Has S k f) : Has S (k+1) f := by
  induction p with
  | done h => exact .done h
  | step a b _ ih => exact .step a b ih

def applied {α} (g : Gate) (state : List (Fn α)) : Fn α := fun x =>
  g.op.eval (g.inputs.map (fun i => (state.getD i (fun _=>false)) x))
def run {α} (gs : List Gate) (state : List (Fn α)) : List (Fn α) :=
  gs.foldl (fun s g=>s++[applied g s]) state

theorem availGet {α : Type*} {S : Set (Fn α)} {st : List (Fn α)} (hs : ∀f∈st,Avail S f)
    (i : Nat) : Avail S (st.getD i (fun _=>false)) := by
  by_cases h : i<st.length
  · rw [List.getD_eq_getElem _ _ h]; exact hs _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]; exact .const false

theorem Has.same {α : Type*} {S T : Set (Fn α)} {k f} (p : Has S k f) (h : ∀g∈S,Avail T g) :
    Has T k f := p.map id h

theorem gateCost {α : Type*} {S : Set (Fn α)} (g : Gate) (st : List (Fn α))
    (old : ∀f∈st,Avail S f)
    (legal : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    {f k} (tail : ∀ T : Set (Fn α), (∀ a∈st,Avail T a) → Avail T (applied g st) → Has T k f) :
    Has S (price g.op + k) f := by
  have base (A : Avail S (applied g st)) : Has S k f := tail S old A
  have ext (a : Fn α) : ∀u∈st,Avail (insert a S) u := fun u hu=>(old u hu).extend
  obtain ⟨op,len⟩ := legal
  cases g with | mk opg ins =>
  change opg=.and ∨ opg=.or ∨ opg=.not at op
  change ins.length≤2 at len
  match ins,len with
  | [],_ =>
    have free := base (Avail.const (opg.eval []))
    rcases op with rfl|rfl|rfl <;> simp [price,Nat.add_comm] <;> first | exact free.bump | exact free
  | [i],_ =>
    let a := st.getD i (fun _=>false)
    have ha : Avail S a := availGet old i
    rcases op with rfl|rfl|rfl
    · have e : applied ⟨.and,[i]⟩ st=a := by funext x;simp [applied,a,GateOp.eval]
      simpa [price,Nat.add_comm] using (base (e ▸ ha)).bump
    · have e : applied ⟨.or,[i]⟩ st=a := by funext x;simp [applied,a,GateOp.eval]
      simpa [price,Nat.add_comm] using (base (e ▸ ha)).bump
    · simpa [price] using base ha.neg
  | [i,j],_ =>
    let a := st.getD i (fun _=>false)
    let b := st.getD j (fun _=>false)
    have ha : Avail S a := availGet old i
    have hb : Avail S b := availGet old j
    rcases op with rfl|rfl|rfl
    · have e : applied ⟨.and,[i,j]⟩ st=meet a b := by funext x;simp [applied,a,b,meet,GateOp.eval]
      have h := tail (insert (meet a b) S) (ext _) (e ▸ Avail.src (Set.mem_insert _ _))
      simpa [price,Nat.add_comm] using Has.step ha hb h
    · have e : applied ⟨.or,[i,j]⟩ st=neg (meet (neg a) (neg b)) := by
        funext x;simp [applied,a,b,meet,neg,GateOp.eval]
      have h := tail (insert (meet (neg a) (neg b)) S) (ext _)
        (e ▸ (Avail.src (Set.mem_insert _ _)).neg)
      simpa [price,Nat.add_comm] using Has.step ha.neg hb.neg h
    · simpa [price] using base ha.neg

theorem listAIG {α : Type*} (gs : List Gate) (legal : ∀g∈gs,
    (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
    (st : List (Fn α)) (S : Set (Fn α)) (old : ∀f∈st,Avail S f) (o) :
    Has S (binaryCount gs) ((run gs st).getD o (fun _=>false)) := by
  induction gs generalizing st S with
  | nil => exact .done (availGet old o)
  | cons g gs ih =>
    apply gateCost g st old (legal g (by simp))
    intro T prev h
    apply ih (fun u hu=>legal u (by simp [hu])) (st++[applied g st]) T
    intro u hu
    rcases List.mem_append.mp hu with u0|u1
    · exact prev u u0
    · have eq := List.mem_singleton.mp u1;exact eq ▸ h

theorem mapRun {α} (gs : List Gate) (st : List (Fn α)) (x : α) :
    (run gs st).map (fun a=>a x) =
    gs.foldl (fun s g=>s++[g.op.eval (g.inputs.map (fun j=>s.getD j false))]) (st.map (fun a=>a x)) := by
  induction gs generalizing st with
  | nil => rfl
  | cons g gs ih =>
    simp only [run,List.foldl_cons] at ih ⊢
    rw [ih]
    congr 1
    simp only [List.map_append,List.map_cons,List.map_nil,List.append_cancel_left_eq]
    congr 2
    unfold applied
    congr 1
    apply List.map_congr_left
    intro i _
    exact (List.getD_map st (fun _=>false) (n:=i) (fun a : Fn α=>a x)).symm

theorem circuitAIG {n} (C : Circuit) (legal : ∀g∈C.gates,
    (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2) :
    Has Inputs (binaryCount C.gates) (fun x : Fin n→Bool=>C.eval (List.ofFn x)) := by
  let st : List (Fn (Fin n→Bool)) := List.ofFn (fun i x=>x i)
  have h := listAIG C.gates legal st Inputs (by
    intro f hf
    obtain ⟨i,eq⟩ := List.mem_ofFn.mp hf
    exact .src ⟨i,eq.symm⟩) C.output
  convert h using 1
  funext x
  have hst : st.map (fun a=>a x)=List.ofFn x := by simp [st,List.map_ofFn,Function.comp_def]
  have eq := mapRun C.gates st x
  rw [hst] at eq
  change (C.wires (List.ofFn x)).getD C.output false=_
  rw [show C.wires (List.ofFn x)=(run C.gates st).map (fun a=>a x) from eq.symm]
  exact List.getD_map _ (fun _=>false) (n:=C.output) (fun a : Fn (Fin n→Bool)=>a x)


end FreeAIG

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 64 := ((x >>> 64) ^^^ x).setWidth 64
def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 64+i.val < 128 := by omega
  have hi' : i.val < 128 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 128 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 128)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)


set_option maxRecDepth 5000 in
def rowWord {α : Type*} (row : Fin 128 → α) (f : α → Bool) : W :=
  (BitVec.ofBoolListLE (List.ofFn fun k => f (row k))).cast (by simp)

set_option maxRecDepth 5000 in
theorem rowWord_bit {α : Type*} (row : Fin 128 → α) (f : α → Bool) (k : Fin 128) :
    (rowWord row f)[k.val] = f (row k) := by
  have h : (BitVec.ofBoolListLE (List.ofFn fun j => f (row j))).getLsbD k.val = f (row k) := by
    rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _
      (by simpa only [List.length_ofFn] using k.isLt), List.getElem_ofFn]
  simpa [rowWord] using h

theorem rowWord_const {α : Type*} (row : Fin 128 → α) (v : Bool) :
    rowWord row (fun _ => v) = if v then ~~~0 else 0 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [rowWord_bit row _ ⟨i, hi⟩]
  cases v
  · simp
  · change true = (BitVec.allOnes 128)[i]
    rw [BitVec.getElem_allOnes]

theorem rowWord_neg {α : Type*} (row : Fin 128 → α) (f : α → Bool) :
    rowWord row (FreeAIG.neg f) = ~~~(rowWord row f) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_not, rowWord_bit row _ ⟨i, hi⟩, FreeAIG.neg]

theorem rowWord_meet {α : Type*} (row : Fin 128 → α) (a b : α → Bool) :
    rowWord row (FreeAIG.meet a b) = rowWord row a &&& rowWord row b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, rowWord_bit row _ ⟨i, hi⟩, FreeAIG.meet]

theorem rowAvail {α : Type*} (row : Fin 128 → α) {S : Set (FreeAIG.Fn α)} {f}
    {av : Finset W} (held : ∀ g ∈ S, holds av (rowWord row g))
    (h : FreeAIG.Avail S f) : holds av (rowWord row f) := by
  induction h with
  | src hm => exact held _ hm
  | const b => rw [rowWord_const]; cases b
               · exact Or.inl rfl
               · exact Or.inr (Or.inl rfl)
  | neg _ ih => rw [rowWord_neg]; exact holds_not ih

theorem rowBuild {α : Type*} (row : Fin 128 → α) {S : Set (FreeAIG.Fn α)} {f : α → Bool}
    {q : ℕ} (h : FreeAIG.Has S q f) (eval : rowWord row f = ~~~goal)
    (av : Finset W) (held : ∀ g ∈ S, holds av (rowWord row g)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t q av := by
  induction h generalizing av with
  | done h =>
    have hh := rowAvail row held h
    rw [eval] at hh
    have memBuild (t : W) (ht : t ∈ av) (m : ℕ) : build basicOps t m av := by
      induction m with
      | zero => exact ht
      | succ _ ih => exact Or.inl ih
    rcases hh with hz | ho | ⟨t, ht, eq | eq⟩
    · exact ((by decide : ~~~goal ≠ 0) hz).elim
    · exact ((by decide : ~~~goal ≠ ~~~0) ho).elim
    · exact ⟨t, Or.inr eq.symm, memBuild t ht _⟩
    · refine ⟨t, Or.inl ?_, memBuild t ht _⟩
      simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm
  | @step S q a b f ha hb tail ih =>
    have reach := and_reach (rowAvail row held ha) (rowAvail row held hb)
    rw [← rowWord_meet] at reach
    rcases reach with existing | ⟨x, hx, y, hy, ne, z, hz, new⟩
    · obtain ⟨t, ht, run⟩ := ih eval av (by
        intro g hg
        rcases Set.mem_insert_iff.mp hg with rfl | old
        · exact existing
        · exact held g old)
      exact ⟨t, ht, Or.inl run⟩
    · obtain ⟨t, ht, run⟩ := ih eval (insert z av) (by
        intro g hg
        rcases Set.mem_insert_iff.mp hg with rfl | old
        · exact new
        · exact holds_insert (held g old))
      exact ⟨t, ht, Or.inr ⟨x, hx, y, hy, ne, z, hz, run⟩⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, w :: r)] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, w :: a :: r)] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, w :: b :: r)] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, w :: a :: b :: r)] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun (a,b,r) => (ops a b).flatMap fun w => kidsOf c.1 a b r w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (optimized k) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have hw := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := hw (extra, w :: r) (by simp [kidsOf, hv])
    simp_all
  · have := hw (extra - 1, w :: a :: r) (by simp [kidsOf, hv, hx])
    simp_all
  · have := hw (extra - 1, w :: b :: r) (by simp [kidsOf, hv, hx])
    simp_all
  · have := hw (extra - 2, w :: a :: b :: r) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem partition_empty {j : ℕ} {L : List (ℕ × List W)} (h : L.isEmpty = true) : FalseAt j L := by
  have he : L = [] := List.isEmpty_iff.mp h
  simp [FalseAt, he]

theorem partition_step {j size : ℕ} {L : List (ℕ × List W)}
    (a : chunkOK j (L.take size) = true) (b : FalseAt j (L.drop size)) : FalseAt j L := by
  intro c hc
  have split : L.take size ++ L.drop size = L := List.take_append_drop size L
  rw [← split] at hc
  obtain ht | hd := List.mem_append.mp hc
  · simpa using List.all_eq_true.mp a c ht
  · exact b c hd


theorem firstLayerReject {n : ℕ} {rows : List W}
    (g : (level0 (n+1) rows).all (fun c => goalFree c.2) = true)
    (h : FalseAt n ((level0 (n+1) rows).flatMap children)) : search (n+1) rows = false := by
  apply search_of_false
  intro c hc
  apply opt_false (List.all_eq_true.mp g c hc)
  intro kid hk
  exact h kid (List.mem_flatMap.mpr ⟨c,hc,hk⟩)
def testRow {n : ℕ} (inputs : List W) (k : Fin 128) (i : Fin n) : Bool :=
  (inputs.getD i.val 0)[k.val]

theorem ofSearchRejectAt {n q : ℕ} {f : (Fin n → Bool) → Bool} (d : ℕ) (inputs : List W)
    (len : inputs.length = n) (nd : inputs.Nodup) (reject : search d inputs = false)
    (sample : ∀ k : Fin 128, f (testRow inputs k) = (~~~goal)[k.val])
    (h : FreeAIG.Has FreeAIG.Inputs q f) : d + 1 ≤ q := by
  have hold : ∀ g ∈ (FreeAIG.Inputs : Set (FreeAIG.Fn (Fin n → Bool))),
      holds inputs.toFinset (rowWord (testRow inputs) g) := by
    rintro g ⟨i, rfl⟩
    have hi : i.val < inputs.length := len.symm ▸ i.isLt
    have hw : rowWord (testRow inputs) (fun x => x i) = inputs[i.val] := by
      apply BitVec.eq_of_getElem_eq
      intro j hj
      rw [rowWord_bit (testRow inputs) _ ⟨j, hj⟩]
      unfold testRow
      rw [List.getD_eq_getElem inputs 0 hi]
    rw [hw]
    exact Or.inr (Or.inr ⟨_, List.mem_toFinset.mpr (List.getElem_mem hi), Or.inl rfl⟩)
  have eval : rowWord (testRow inputs) f = ~~~goal := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    rw [rowWord_bit (testRow inputs) _ ⟨j, hj⟩]
    exact sample ⟨j, hj⟩
  obtain ⟨t, ht, run⟩ := rowBuild (testRow inputs) h eval inputs.toFinset hold
  by_contra! hb
  have lift {a b : ℕ} (h : a ≤ b) (p : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact p
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht d inputs nd (lift (by omega) run)))

theorem ofSearchReject {n q : ℕ} {f : (Fin n → Bool) → Bool} (inputs : List W)
    (len : inputs.length = n) (nd : inputs.Nodup) (reject : search 7 inputs = false)
    (sample : ∀ k : Fin 128, f (testRow inputs k) = (~~~goal)[k.val])
    (h : FreeAIG.Has FreeAIG.Inputs q f) : 8 ≤ q :=
  ofSearchRejectAt 7 inputs len nd reject sample h


def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276677320 * 2 ^ 32 + 4176011456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def pin : Fin 6 := 5

def cut (v : Bool) := FreeAIG.cofactorAt target pin v

set_option maxRecDepth 100000 in
theorem dependsOnPin : ∃ x : Fin 5 → Bool, cut false x ≠ cut true x :=
  ⟨fun i => (3 : ℕ).testBit i.val, by decide +kernel⟩

def zeroRows : List W :=
  [(0x404f33ddc09731bc#64 ++ 0x4a7a7bdfb99714fc#64 : W),
   (0x740941aa53829200#64 ++ 0xf7c9578edfdbea80#64 : W),
   (0x8b661e0024486c57#64 ++ 0xffffbd7d666cff7f#64 : W),
   (0x7729c1a7027e91e9#64 ++ 0x9b6ecd350072916f#64 : W),
   (0x34106c270d35c58a#64 ++ 0x213eeee6b9b7c59b#64 : W)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in

def zeroLayer := (level0 7 zeroRows).flatMap children

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerDone : FalseAt 6 (zeroLayer.drop 44) := partition_empty (by decide +kernel)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom42 : FalseAt 6 (zeroLayer.drop 42) := by
  apply partition_step (size := 2)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerDone

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom39 : FalseAt 6 (zeroLayer.drop 39) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom42

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom36 : FalseAt 6 (zeroLayer.drop 36) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom39

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom33 : FalseAt 6 (zeroLayer.drop 33) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom36

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom30 : FalseAt 6 (zeroLayer.drop 30) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom33

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom27 : FalseAt 6 (zeroLayer.drop 27) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom30

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom24 : FalseAt 6 (zeroLayer.drop 24) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom27

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom21 : FalseAt 6 (zeroLayer.drop 21) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom24

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom18 : FalseAt 6 (zeroLayer.drop 18) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom21

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom15 : FalseAt 6 (zeroLayer.drop 15) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom18

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom12 : FalseAt 6 (zeroLayer.drop 12) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom15

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom9 : FalseAt 6 (zeroLayer.drop 9) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom12

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom6 : FalseAt 6 (zeroLayer.drop 6) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom9

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom3 : FalseAt 6 (zeroLayer.drop 3) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom6

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroLayerFrom0 : FalseAt 6 (zeroLayer.drop 0) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using zeroLayerFrom3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zeroReject : search 7 zeroRows = false := by
  apply firstLayerReject (by decide +kernel)
  simpa only [List.drop_zero, zeroLayer] using zeroLayerFrom0


set_option maxRecDepth 100000 in
theorem zeroSample : ∀ k : Fin 128, cut false (testRow zeroRows k) = (~~~goal)[k.val] := by
  decide +kernel

def oneRows : List W :=
  [(0x4a05001990a12688#64 ++ 0x6bfd1acfb2ef36c8#64 : W),
   (0x104803e2005a4822#64 ++ 0x564e7f7a5d5bec26#64 : W),
   (0x8f343014dd80b149#64 ++ 0x9fbdb5304d90f9d9#64 : W),
   (0x145058e46206d017#64 ++ 0xfd57fa85a2a6d337#64 : W),
   (0x418bab0b2c2d09f4#64 ++ 0xdffbea00042d09ff#64 : W)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in

def oneLayer := (level0 7 oneRows).flatMap children

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerDone : FalseAt 6 (oneLayer.drop 40) := partition_empty (by decide +kernel)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom39 : FalseAt 6 (oneLayer.drop 39) := by
  apply partition_step (size := 1)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerDone

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom36 : FalseAt 6 (oneLayer.drop 36) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom39

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom33 : FalseAt 6 (oneLayer.drop 33) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom36

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom30 : FalseAt 6 (oneLayer.drop 30) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom33

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom27 : FalseAt 6 (oneLayer.drop 27) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom30

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom24 : FalseAt 6 (oneLayer.drop 24) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom27

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom21 : FalseAt 6 (oneLayer.drop 21) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom24

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom18 : FalseAt 6 (oneLayer.drop 18) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom21

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom15 : FalseAt 6 (oneLayer.drop 15) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom18

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom12 : FalseAt 6 (oneLayer.drop 12) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom15

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom9 : FalseAt 6 (oneLayer.drop 9) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom12

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom6 : FalseAt 6 (oneLayer.drop 6) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom9

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom3 : FalseAt 6 (oneLayer.drop 3) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom6

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneLayerFrom0 : FalseAt 6 (oneLayer.drop 0) := by
  apply partition_step (size := 3)
  · decide +kernel
  · simpa only [List.drop_drop] using oneLayerFrom3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem oneReject : search 7 oneRows = false := by
  apply firstLayerReject (by decide +kernel)
  simpa only [List.drop_zero, oneLayer] using oneLayerFrom0


set_option maxRecDepth 100000 in
theorem oneSample : ∀ k : Fin 128, cut true (testRow oneRows k) = (~~~goal)[k.val] := by
  decide +kernel
 
theorem cutLower (v : Bool) {q : ℕ} (h : FreeAIG.Has FreeAIG.Inputs q (cut v)) : 8 ≤ q := by
  cases v
  · exact ofSearchRejectAt 7 zeroRows rfl (by decide) zeroReject zeroSample h
  · exact ofSearchRejectAt 7 oneRows rfl (by decide) oneReject oneSample h

def witness : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [4, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [2, 13]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [8, 15]⟩], 16⟩

theorem witness_basis : Monotone2 witness := by simp [Monotone2, witness]

set_option maxRecDepth 100000 in
theorem witness_eval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem solve (s : ℕ) (h : HasCircuitSize 6 target s) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧ ∀ x : Fin 6 → Bool, D.eval (List.ofFn x) = target x := by
  classical
  obtain ⟨C,legal,sz,eval⟩ := h
  by_cases mono : Monotone2 C
  · exact ⟨C,mono,sz,eval⟩
  have hn : ∃ g ∈ C.gates, g.op = GateOp.not := by
    by_contra! h
    apply mono
    intro g hg
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa [h g hg] using (legal g hg).1
    exact ⟨hop, (legal g hg).2⟩
  have net := FreeAIG.circuitAIG (n := 6) C (by simpa [FanInTwo] using legal)
  rw [funext eval] at net
  have lb := FreeAIG.twoCofactorsLower (m := 8) (by decide) dependsOnPin (fun v => cutLower v) net
  have discount := FreeAIG.notDiscount hn
  have hs : C.gates.length ≤ s := sz
  refine ⟨witness,witness_basis,?_,witness_eval⟩
  change 11 ≤ s
  omega

end PEqualNP.Outside.L_meta_42970

theorem PEqualNP.Outside.L_meta_42970 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 4176011456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 4176011456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_42970.solve
