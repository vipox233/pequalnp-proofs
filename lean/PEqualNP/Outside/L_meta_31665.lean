import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31665.Frame
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List ℕ := [0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7]
def target (x : Fin 8 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def witness : List Gate := [
  ⟨.and, [0, 4]⟩,
  ⟨.or, [6, 8]⟩,
  ⟨.or, [1, 7]⟩,
  ⟨.or, [3, 5]⟩,
  ⟨.and, [10, 11]⟩,
  ⟨.or, [10, 11]⟩,
  ⟨.or, [0, 2]⟩,
  ⟨.or, [12, 14]⟩,
  ⟨.or, [5, 7]⟩,
  ⟨.and, [15, 16]⟩,
  ⟨.or, [9, 17]⟩,
  ⟨.or, [0, 13]⟩,
  ⟨.and, [18, 19]⟩]

theorem good : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

theorem correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness,20⟩ (List.ofFn x) = target x := by
  decide +kernel

theorem finish (lower : ∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,o⟩ →
    (∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) →
    (∃ g ∈ gs, g.op = .not) → 13 ≤ gs.length) : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o fan _ computes
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · exact ⟨witness, 20, good, lower gs o fan computes hn, correct⟩
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, len⟩ := fan g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩

end PEqualNP.Outside.L_meta_31665.Frame

namespace PEqualNP.Outside.L_meta_31665.Reduce
variable {m : Nat}
def canon (w : BitVec (m+1)) := if w.getLsbD 0 then ~~~w else w
def signed (d : Bool) (w : BitVec (m+1)) := if d then ~~~w else w
def gate (s t : Bool) (a b : BitVec (m+1)) := canon (signed s a &&& signed t b)
def Path (goal : BitVec (m+1)) (k : Nat) (S : Finset (BitVec (m+1))) : Prop :=
  ∀ P : Nat → Finset (BitVec (m+1)) → Prop, P 0 {goal} →
    (∀ {k a b U} (s t : Bool), a ≠ b → gate s t a b ∉ insert a (insert b U) →
      gate s t a b ≠ 0 → P k (insert (gate s t a b) U) → P (k+1) (insert a (insert b U))) →
    P k S
theorem Path.done {g : BitVec (m+1)} : Path g 0 {g} := fun _ d _ => d
theorem Path.binary {g : BitVec (m+1)} {k a b U} (s t : Bool) (ne : a ≠ b)
    (fresh : gate s t a b ∉ insert a (insert b U)) (proper : gate s t a b ≠ 0)
    (tail : Path g k (insert (gate s t a b) U)) : Path g (k+1) (insert a (insert b U)) :=
  fun P d f => f s t ne fresh proper (tail P d f)
theorem canon_not (x : BitVec (m+1)) : canon (~~~x) = canon x := by
  unfold canon
  simp only [BitVec.getLsbD_not, Nat.zero_lt_succ,decide_true, Bool.true_and]
  cases x.getLsbD 0 <;> simp

theorem canon_canon (x : BitVec (m+1)) : canon (canon x) = canon x := by
  by_cases h : x.getLsbD 0 = true
  · rw [show canon x = ~~~x from if_pos h,canon_not,show canon x = ~~~x from if_pos h]
  · rw [show canon x = x from if_neg h]
    exact if_neg h

theorem sign_back (x : BitVec (m+1)) : signed (x.getLsbD 0) (canon x) = x := by
  unfold signed canon
  cases x.getLsbD 0 <;> simp

theorem canon_zero : canon (0 : BitVec (m+1)) = 0 := by simp [canon]
theorem gate_left_zero (s t : Bool) (x : BitVec (m+1)) :
    gate s t 0 x = 0 ∨ gate s t 0 x = canon x := by
  cases s with
  | false => exact Or.inl ((congrArg canon (BitVec.zero_and (x := signed t x))).trans canon_zero)
  | true =>
    cases t with
    | false => right; simp [gate,signed]
    | true => right; simp [gate,signed,canon_not]

theorem gate_right_zero (s t : Bool) (x : BitVec (m+1)) :
    gate s t x 0 = 0 ∨ gate s t x 0 = canon x := by
  rw [show gate s t x 0 = gate t s 0 x from congrArg canon (BitVec.and_comm ..)]
  exact gate_left_zero _ _ _

theorem gate_same (s t : Bool) (x : BitVec (m+1)) : gate s t x x = 0 ∨ gate s t x x = canon x := by
  cases s <;> cases t
  · exact Or.inr (congrArg canon (BitVec.and_self (x := x)))
  · exact Or.inl ((congrArg canon (BitVec.and_not_self x)).trans canon_zero)
  · exact Or.inl ((congrArg canon (BitVec.not_and_self x)).trans canon_zero)
  · exact Or.inr ((congrArg canon (BitVec.and_self (x := ~~~x))).trans (canon_not x))

variable {A : Type} [DecidableEq A] (pin : A → BitVec (m+1))
def avail (S : Finset A) := (S.image pin).erase 0
def lost (S : Finset A) := (S.filter fun x => pin x = 0).card
theorem avail_mem {S : Finset A} {x : BitVec (m+1)} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono {S T : Finset A} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases {S : Finset A} {c : A} {x : BitVec (m+1)} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (c : A) (S : Finset A) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,if_neg (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [if_pos ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,if_pos h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [if_neg (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,if_neg h]

theorem cost_skip (a b c : A) (U : Finset A) (fresh : c ∉ U)
    (both : pin a = 0 → pin b = 0 → pin c = 0) :
    lost pin (insert a (insert b U)) ≤ lost pin (insert c U) + 1 := by
  simp only [lost_insert]
  split_ifs <;> grind

def Proj (goal : BitVec (m+1)) (limit extra : Nat) (S : Finset A) : Prop :=
  ∃ k, k + lost pin S + extra ≤ limit ∧ ∃ T ⊆ avail pin S, Path goal k T

theorem proj_done (x : A) (nz : pin x ≠ 0) : Proj pin (pin x) 0 0 {x} := by
  refine ⟨0,?_,{pin x},?_,Path.done⟩ <;> simp [lost,avail] <;> exact nz
theorem proj_inv {g : BitVec (m+1)} {limit extra : Nat} (a c : A) (U : Finset A)
    (newc : c ∉ U) (eq : pin c = pin a) (tail : Proj pin g limit extra (insert c U)) :
    Proj pin g limit extra (insert a U) := by
  obtain ⟨k,hle,T,sub,path⟩ := tail
  refine ⟨k,?_,T,?_,path⟩
  · simp only [lost_insert,eq] at hle ⊢
    split_ifs at * <;> grind
  · intro x hx
    rcases avail_cases pin (sub hx) with eq'|old
    · exact (avail_mem pin).mpr ⟨((avail_mem pin).mp (sub hx)).1,a,by simp,(eq'.trans eq).symm⟩
    · exact avail_mono pin (Finset.subset_insert _ _) old

theorem proj_strong {g : BitVec (m+1)} {limit : Nat} (a b c : A) (U : Finset A)
    (newc : c ∉ U) (hc : pin c = 0) (one : pin a ≠ 0 ∨ pin b ≠ 0)
    (tail : Proj pin g limit 0 (insert c U)) : Proj pin g (limit+1) 1 (insert a (insert b U)) := by
  obtain ⟨k,le,T,sub,path⟩ := tail
  refine ⟨k,?_,T,?_,path⟩
  · simp only [lost_insert,hc] at le ⊢
    split_ifs at * <;> grind
  · intro x hx
    rcases avail_cases pin (sub hx) with eq|old
    · exact (((avail_mem pin).mp (sub hx)).1 (eq.trans hc)).elim
    · exact avail_mono pin (by intro _ mem; simp [mem]) old

theorem proj_bin {g : BitVec (m+1)} {b extra : Nat} (a x c : A) (U : Finset A)
    (can : ∀ v, canon (pin v) = pin v) (cnew : c ∉ U) (s t : Bool)
    (repr : pin c = gate s t (pin a) (pin x))
    (tail : Proj pin g b extra (insert c U)) : Proj pin g (b+1) extra (insert a (insert x U)) := by
  let prev := insert a (insert x U)
  obtain ⟨k,hle,T,sub,path⟩ := tail
  change k + lost pin (insert c U) + extra ≤ b at hle
  change T ⊆ avail pin (insert c U) at sub
  have both (ha : pin a = 0) (hx : pin x = 0) : pin c = 0 := by
    rw [repr,ha,hx]
    exact (gate_same s t 0).elim id (fun q => q.trans canon_zero)
  have skipcost := cost_skip pin a x c U cnew both
  have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
  by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
  · have nz := ((avail_mem pin).mp (sub useful.1)).1
    have df (v : A) (hv : v ∈ prev) : pin c ≠ pin v := by
      intro e
      exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
    have da := df a (by simp [prev])
    have dx := df x (by simp [prev])
    have ha : pin a ≠ 0 := by
      intro h
      have drop := gate_left_zero s t (pin x)
      rw [h] at repr
      rw [←repr,can] at drop
      exact drop.elim nz dx
    have hx : pin x ≠ 0 := by
      intro h
      have drop := gate_right_zero s t (pin a)
      rw [h] at repr
      rw [←repr,can] at drop
      exact drop.elim nz da
    have distinct : pin a ≠ pin x := by
      intro e
      have drop := gate_same s t (pin x)
      rw [e] at repr
      rw [←repr,can] at drop
      exact drop.elim nz dx
    have vcost : lost pin prev ≤ lost pin (insert c U) := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    let V := T.erase (pin c)
    have old (v : BitVec (m+1)) (hv : v ∈ V) : v ∈ avail pin U :=
      (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
    refine ⟨k+1,by change k+1+lost pin prev + extra ≤ b+1; omega,insert (pin a) (insert (pin x) V),?_,?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (avail_mem pin).mpr ⟨ha,a,by simp [prev],rfl⟩
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (avail_mem pin).mpr ⟨hx,x,by simp [prev],rfl⟩
      exact liftU (old _ hv)
    · apply Path.binary s t distinct
      · rw [←repr]
        simp [V,da,dx]
      · rwa [←repr]
      · rwa [←repr,show insert (pin c) V = T from Finset.insert_erase useful.1]
  · refine ⟨k,by change k+lost pin (insert a (insert x U)) + extra ≤ b+1; omega,T,?_,path⟩
    intro v hv
    rcases avail_cases pin (sub hv) with rfl|old
    · by_contra miss
      exact useful ⟨hv,miss⟩
    · exact liftU old
end PEqualNP.Outside.L_meta_31665.Reduce

namespace PEqualNP.Outside.L_meta_31665
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word := BitVec 256
def ones : Word := BitVec.allOnes 256
def goal : Word := 0xfffffffffffffffffffffffcfffaee00ffffffffffffff00fffffffcfffaee00
def roots : List Word := [
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000]
def join (d : Bool) (a b : Word) : Word := if d then a ||| b else a &&& b

def Live (b n : Nat) (S : Finset Word) : Prop :=
  ∀ (P : Nat → Nat → Finset Word → Prop),
    P 0 0 {goal} →
    (∀ {i j : Nat} {a x : Word} {U : Finset Word} (d : Bool), a ≠ x →
      join d a x ∉ insert a (insert x U) → (join d a x ≠ 0 ∧ join d a x ≠ ones) →
      P i j (insert (join d a x) U) → P (i+1) j (insert a (insert x U))) →
    (∀ {i j : Nat} {a : Word} {U : Finset Word},
      ~~~a ∉ insert a U → (~~~a ≠ 0 ∧ ~~~a ≠ ones) →
      P i j (insert (~~~a) U) → P i (j+1) (insert a U)) →
    P b n S

theorem Live.done : Live 0 0 {goal} :=
  fun _ done _ _ => done

theorem Live.binary {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
    (fresh : join d a x ∉ insert a (insert x U))
    (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
    (tail : Live b n (insert (join d a x) U)) :
    Live (b+1) n (insert a (insert x U)) :=
  fun P done binary inversion => binary d ne fresh proper (tail P done binary inversion)

theorem Live.inversion {b n : Nat} {a : Word} {U : Finset Word}
    (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
    (tail : Live b n (insert (~~~a) U)) : Live b (n+1) (insert a U) :=
  fun P done binary inversion => inversion fresh proper (tail P done binary inversion)

theorem Live.recPlain {motive : ∀ {b n S}, Live b n S → Prop}
    (done : motive Live.done)
    (binary : ∀ {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
      (fresh : join d a x ∉ insert a (insert x U))
      (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
      (tail : Live b n (insert (join d a x) U)),
      motive tail → motive (Live.binary d ne fresh proper tail))
    (inversion : ∀ {b n : Nat} {a : Word} {U : Finset Word}
      (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
      (tail : Live b n (insert (~~~a) U)),
      motive tail → motive (Live.inversion fresh proper tail))
    {b n : Nat} {S : Finset Word} (h : Live b n S) : motive h := by
  let P (b n : Nat) (S : Finset Word) : Prop := ∃ p : Live b n S, motive p
  have result : P b n S := by
    apply h P
    · exact ⟨Live.done,done⟩
    · intro i j a x U d ne fresh proper tail
      obtain ⟨p,ih⟩ := tail
      exact ⟨Live.binary d ne fresh proper p,binary d ne fresh proper p ih⟩
    · intro i j a U fresh proper tail
      obtain ⟨p,ih⟩ := tail
      exact ⟨Live.inversion fresh proper p,inversion fresh proper p ih⟩
  obtain ⟨_,proof⟩ := result
  exact proof

theorem Live.casesPlain {motive : ∀ {b n S}, Live b n S → Prop}
    (done : motive Live.done)
    (binary : ∀ {b n : Nat} {a x : Word} {U : Finset Word} (d : Bool) (ne : a ≠ x)
      (fresh : join d a x ∉ insert a (insert x U))
      (proper : join d a x ≠ 0 ∧ join d a x ≠ ones)
      (tail : Live b n (insert (join d a x) U)), motive (Live.binary d ne fresh proper tail))
    (inversion : ∀ {b n : Nat} {a : Word} {U : Finset Word}
      (fresh : ~~~a ∉ insert a U) (proper : ~~~a ≠ 0 ∧ ~~~a ≠ ones)
      (tail : Live b n (insert (~~~a) U)), motive (Live.inversion fresh proper tail))
    {b n : Nat} {S : Finset Word} (h : Live b n S) : motive h := by
  apply Live.recPlain (motive := @motive) done _ _ h
  · intro i j a x U d ne fresh proper tail _
    exact binary d ne fresh proper tail
  · intro i j a U fresh proper tail _
    exact inversion fresh proper tail

theorem goal_proper : goal ≠ 0 ∧ goal ≠ ones := by decide +kernel

def assignment (r : Fin 256) : Fin 8 → Bool := fun i => r.val.testBit (([6,0,1,2,7,3,4,5] : List Nat).get i)
def readBit (r : Fin 256) (v : Word) := v.getLsbD r
@[local simp] theorem read_ones (r : Fin 256) : readBit r ones = true := by
  exact (BitVec.getLsbD_allOnes).trans (decide_eq_true r.isLt)
@[local simp] theorem read_zero (r : Fin 256) : readBit r 0 = false := by simp [readBit]
@[local simp] theorem ones_and (a : Word) : ones &&& a = a := BitVec.allOnes_and
@[local simp] theorem and_ones (a : Word) : a &&& ones = a := BitVec.and_allOnes
@[local simp] theorem ones_or (a : Word) : ones ||| a = ones := BitVec.allOnes_or
@[local simp] theorem or_ones (a : Word) : a ||| ones = ones := BitVec.or_allOnes

theorem roots_bits : ∀ r : Fin 256, roots.map (readBit r) = List.ofFn (assignment r) := by decide +kernel
abbrev graph := Frame.target
theorem row_flags : ∀ r : Fin 256, graph (assignment r) = readBit r goal := by decide +kernel

theorem getD_map {α β} (f : α → β) (s : List α) (i : Nat) (a : α) :
    (s.map f).getD i (f a) = f (s.getD i a) := by
  induction s generalizing i with
  | nil => simp
  | cons x s ih => cases i with
    | zero => rfl
    | succ i => exact ih i

theorem getD_mem_or (w : List Word) (i : Nat) : w.getD i 0 ∈ w ∨ w.getD i 0 = 0 := by
  by_cases h : i < w.length
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    exact List.getElem_mem h
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

def binaryWord (w : List Word) (g : Gate) : Word :=
  let d := match g.op with | .or => true | _ => false
  match g.inputs with
  | [] => if d then 0 else ones
  | [a] => w.getD a 0
  | a::b::_ => join d (w.getD a 0) (w.getD b 0)

def gateWord (w : List Word) (g : Gate) : Word :=
  match g.op with
  | .not => match g.inputs with | [] => ones | a::_ => ~~~(w.getD a 0)
  | _ => binaryWord w g

def binCost (g : Gate) : Nat :=
  match g.op, g.inputs with | .and, _::_::_ | .or, _::_::_ => 1 | _, _ => 0
def invCost (g : Gate) : Nat := match g.op with | .not => 1 | _ => 0

def binaryCount : List Gate → Nat
  | [] => 0 | g::gs => binaryCount gs + binCost g
def inversionCount : List Gate → Nat
  | [] => 0 | g::gs => inversionCount gs + invCost g

def stepWord (w : List Word) (g : Gate) := w ++ [gateWord w g]
def stepBit (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def allowed (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

theorem step_correct (r : Fin 256) (w : List Word) (g : Gate) (h : allowed g) :
    (stepWord w g).map (readBit r) = stepBit (w.map (readBit r)) g := by
  have get (j : Nat) : (w[j]?.map (readBit r)).getD false = readBit r (w[j]?.getD 0) := by
    cases w[j]? <;> simp [readBit]
  rcases g with ⟨op,ins⟩
  rcases h with ⟨hOp, hlen⟩
  change op = .and ∨ op = .or ∨ op = .not at hOp
  change ins.length ≤ 2 at hlen
  rcases hOp with rfl|rfl|rfl <;> cases ins with
  | nil => simp [stepWord,stepBit,gateWord,binaryWord,GateOp.eval] <;> exact read_zero r
  | cons a rest =>
    cases rest with
    | nil => simp [stepWord,stepBit,gateWord,binaryWord,get,GateOp.eval,readBit]
    | cons b tail =>
      cases tail with
      | nil => simp [stepWord,stepBit,gateWord,binaryWord,get,GateOp.eval,join,readBit]
      | cons c rest => simp at hlen

theorem fold_correct (r : Fin 256) (gs : List Gate) (w : List Word)
    (h : ∀ g ∈ gs, allowed g) :
    (gs.foldl stepWord w).map (readBit r) = gs.foldl stepBit (w.map (readBit r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by grind), step_correct r w g (h _ (by simp))]

theorem sampled_circuit (C : Circuit) (hp : ∀ g ∈ C.gates, allowed g)
    (accept : ∀ r : Fin 256, C.eval (List.ofFn (assignment r)) = readBit r goal) :
    (C.gates.foldl stepWord roots).getD C.output 0 = goal := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let r : Fin 256 := ⟨i,hi⟩
  change readBit r ((C.gates.foldl stepWord roots).getD C.output 0) = readBit r goal
  rw [← getD_map (readBit r) (C.gates.foldl stepWord roots) C.output 0]
  rw [fold_correct r C.gates roots hp, roots_bits]
  rw [read_zero]
  exact accept r

theorem nontrivial_join (d : Bool) (a b : Word)
    (haa : join d a b ≠ a) (hbb : join d a b ≠ b)
    (h0 : join d a b ≠ 0) (h1 : join d a b ≠ ones) :
    a ≠ 0 ∧ b ≠ 0 ∧ a ≠ ones ∧ b ≠ ones ∧ a ≠ b := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> rintro rfl <;> cases d <;> simp_all [join]

theorem not_ones : ~~~ones = (0 : Word) := by decide +kernel
theorem not_zero : ~~~(0 : Word) = ones := by decide +kernel

def Parents (w : List Word) (g : Gate) (c : Word) : Prop :=
  (∃ d a b, c = join d a b ∧ binCost g = 1 ∧ a ∈ w ∧ b ∈ w ∧
    a ≠ 0 ∧ b ≠ 0 ∧ a ≠ ones ∧ b ≠ ones ∧ a ≠ b) ∨
  (∃ a, c = ~~~a ∧ invCost g = 1 ∧ a ∈ w ∧ a ≠ 0 ∧ a ≠ ones)

theorem binary_parents (w : List Word) (op : GateOp) (opok : op = .and ∨ op = .or)
    (ins : List Nat) (missing : binaryWord w ⟨op,ins⟩ ∉ w)
    (p0 : binaryWord w ⟨op,ins⟩ ≠ 0) (p1 : binaryWord w ⟨op,ins⟩ ≠ ones) :
    Parents w ⟨op,ins⟩ (binaryWord w ⟨op,ins⟩) := by
  let d := match op with | .or => true | _ => false
  cases ins with
  | nil =>
    change (if d then 0 else ones) ≠ 0 at p0
    change (if d then 0 else ones) ≠ ones at p1
    cases d <;> simp_all
  | cons i rest =>
    cases rest with
    | nil =>
      change w.getD i 0 ∉ w at missing
      change w.getD i 0 ≠ 0 at p0
      exact (getD_mem_or w i).elim (fun h => (missing h).elim) (fun h => (p0 h).elim)
    | cons j tail =>
      let a := w.getD i 0
      let b := w.getD j 0
      change join d a b ∉ w at missing
      change join d a b ≠ 0 at p0
      change join d a b ≠ ones at p1
      have absent (u : Word) (mem : u ∈ w ∨ u = 0) : join d a b ≠ u := by
        intro e
        exact mem.elim (fun m => missing (e ▸ m)) (fun z => p0 (e.trans z))
      have parts := nontrivial_join d a b (absent _ (getD_mem_or w i))
        (absent _ (getD_mem_or w j)) p0 p1

      have cost : binCost ⟨op,i::j::tail⟩ = 1 := by rcases opok with rfl|rfl <;> rfl
      exact Or.inl ⟨d,a,b,rfl,cost,(getD_mem_or w i).resolve_right parts.1,
        (getD_mem_or w j).resolve_right parts.2.1,parts⟩

theorem gate_parents (w : List Word) (g : Gate) (okay : allowed g)
    (missing : gateWord w g ∉ w) (p0 : gateWord w g ≠ 0) (p1 : gateWord w g ≠ ones) :
    Parents w g (gateWord w g) := by
  rcases g with ⟨op,ins⟩
  have ops : op = .and ∨ op = .or ∨ op = .not := okay.1
  rcases ops with h|h|h
  · subst op
    exact binary_parents w _ (.inl rfl) ins missing p0 p1
  · subst op
    exact binary_parents w _ (.inr rfl) ins missing p0 p1
  · subst op
    cases ins with
    | nil => exact (p1 rfl).elim
    | cons i rest =>
      let a := w.getD i 0
      change ~~~a ≠ 0 at p0
      change ~~~a ≠ ones at p1
      have a0 : a ≠ 0 := fun e => p1 (e ▸ not_zero)
      have a1 : a ≠ ones := fun e => p0 (e ▸ not_ones)
      exact Or.inr ⟨a,rfl,rfl,(getD_mem_or w i).resolve_right a0,a0,a1⟩

def Trace (b n : Nat) (w : List Word) : Prop :=
  ∃ (k j : Nat) (S : Finset Word), k ≤ b ∧ j ≤ n ∧
    (∀ x ∈ S, x ∈ w ∧ x ≠ 0 ∧ x ≠ ones) ∧ Live k j S

theorem unwind (b n : Nat) (w : List Word) (g : Gate) (okay : allowed g)
    (t : Trace b n (stepWord w g)) : Trace (b + binCost g) (n + invCost g) w := by
  obtain ⟨k,j,S,hk,hj,valid,live⟩ := t
  let c := gateWord w g
  have prev (x : Word) (hx : x ∈ S) : (x ∈ w ∨ x = c) ∧ x ≠ 0 ∧ x ≠ ones := by
    simpa [c,stepWord] using valid x hx
  by_cases used : c ∈ S
  · by_cases old : c ∈ w
    · exact ⟨k,j,S,by omega,by omega,fun x hx => by have h := prev x hx; grind,live⟩
    · let U := S.erase c
      have uc : c ∉ U := Finset.notMem_erase _ _
      have sub (x : Word) (hx : x ∈ U) : x ∈ w ∧ x ≠ 0 ∧ x ≠ ones := by
        have hx' := Finset.mem_erase.mp hx
        have h := prev x hx'.2
        exact ⟨h.1.resolve_right hx'.1,h.2⟩
      have back : insert c U = S := Finset.insert_erase used
      rcases gate_parents w g okay old (valid c used).2.1 (valid c used).2.2 with binary|inv
      · obtain ⟨d,a,x,eqc,cost,ha,hx,a0,x0,a1,x1,ne⟩ := binary
        change c = join d a x at eqc
        have ca : c ≠ a := fun e => old (e ▸ ha)
        have cx : c ≠ x := fun e => old (e ▸ hx)
        refine ⟨k+1,j,insert a (insert x U),by omega,by omega,?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨ha,a0,a1⟩
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨hx,x0,x1⟩
          exact sub _ hy
        · apply Live.binary d ne
          · simpa [← eqc,ca,cx] using uc
          · exact eqc ▸ (valid c used).2
          · rwa [← eqc,back]
      · obtain ⟨a,eqc,cost,ha,a0,a1⟩ := inv
        change c = ~~~a at eqc
        have ca : c ≠ a := fun e => old (e ▸ ha)
        refine ⟨k,j+1,insert a U,by omega,by omega,?_,?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl|hy
          · exact ⟨ha,a0,a1⟩
          exact sub _ hy
        · apply Live.inversion
          · simpa [←eqc,ca] using uc
          · exact eqc ▸ (valid c used).2
          · rwa [←eqc,back]
  · exact ⟨k,j,S,by omega,by omega,fun x hx => by have h := prev x hx; grind,live⟩

theorem trace_aux (gs : List Gate) (w : List Word) (out : Nat) (hp : ∀ g ∈ gs, allowed g)
    (success : (gs.foldl stepWord w).getD out 0 = goal) :
    Trace (binaryCount gs) (inversionCount gs) w := by
  induction gs generalizing w with
  | nil =>
    change w.getD out 0 = goal at success
    have h := (getD_mem_or w out).resolve_right (success ▸ goal_proper.1)
    rw [success] at h
    refine ⟨0,0,{goal},by simp [binaryCount],by simp [inversionCount],?_,Live.done⟩
    simpa using And.intro h goal_proper
  | cons g gs ih => exact unwind _ _ w g (hp _ (by simp)) (ih _ (by grind) success)

theorem circuit_live (C : Circuit) (legal : ∀ g ∈ C.gates, allowed g)
    (correct : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    ∃ b ≤ binaryCount C.gates, ∃ n ≤ inversionCount C.gates, ∃ S ⊆ roots.toFinset, Live b n S := by
  have accept (r : Fin 256) : C.eval (List.ofFn (assignment r)) = readBit r goal :=
    (correct _).trans (row_flags r)
  obtain ⟨b,n,S,hb,hn,incl,live⟩ := trace_aux _ _ _ legal (sampled_circuit C legal accept)
  exact ⟨b,hb,n,hn,S,fun x hx => List.mem_toFinset.mpr (incl x hx).1,live⟩

theorem agree_join (p q : Fin 256) (d : Bool) (a x : Word)
    (ha : readBit p a = readBit q a) (hx : readBit p x = readBit q x) :
    readBit p (join d a x) = readBit q (join d a x) := by
  cases d <;> simp_all [join,readBit]

theorem agree_not (p q : Fin 256) (a : Word) (ha : readBit p a = readBit q a) :
    readBit p (~~~a) = readBit q (~~~a) := by simp_all [readBit]

theorem live_agrees {b n S} (live : Live b n S) (p q : Fin 256)
    (same : ∀ x ∈ S, readBit p x = readBit q x) : readBit p goal = readBit q goal := by
  induction live using Live.recPlain with
  | done => exact same goal (by simp)
  | @binary b n a x U d _ _ _ _ ih =>
    apply ih
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact agree_join p q d a x (same _ (by simp)) (same _ (by simp))
    · exact same _ (by simp [hy])
  | @inversion b n a U _ _ _ ih =>
    apply ih
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl|hy
    · exact agree_not p q a (same _ (by simp))
    · exact same _ (by simp [hy])

def witnesses (i : Fin 8) : Fin 256 × Fin 256 := ([(8,72),(8,9),(8,10),(16,20),(64,192),(1,9),(1,17),(2,34)] : List (Fin 256 × Fin 256)).get i
theorem witness_correct : ∀ i : Fin 8,
    readBit (witnesses i).1 goal ≠ readBit (witnesses i).2 goal ∧
    ∀ j : Fin 8, readBit (witnesses i).1 (roots.get j) =
      readBit (witnesses i).2 (roots.get j) ∨ j = i := by decide +kernel

theorem roots_full {b n S} (live : Live b n S) (sub : S ⊆ roots.toFinset) :
    S = roots.toFinset := by
  apply Finset.Subset.antisymm sub
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hx)
  obtain ⟨distinct,only⟩ := witness_correct i
  by_contra missing
  apply distinct (live_agrees live _ _ ?_)
  intro w hw
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp (sub hw))
  exact (only j).resolve_right (by rintro rfl; exact missing hw)

theorem cost_bound (gs : List Gate) : binaryCount gs + inversionCount gs ≤ gs.length := by
  induction gs with
  | nil => simp [binaryCount,inversionCount]
  | cons g gs ih =>
    have hg : binCost g + invCost g ≤ 1 := by
      rcases g with ⟨op,ins⟩
      cases op <;> cases ins with
      | nil => simp [binCost,invCost]
      | cons i tail => cases tail <;> simp [binCost,invCost]
    simp only [binaryCount,inversionCount,List.length_cons]
    omega

theorem zero_inversions (gs : List Gate) (none : ∀ g ∈ gs, g.op ≠ .not) :
    inversionCount gs = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have ng := none g (by simp)
    have cost : invCost g = 0 := by rcases g with ⟨op,ins⟩; cases op <;> simp_all [invCost]
    rw [inversionCount,cost,ih (by grind),Nat.add_zero]

theorem unique_inversion (gs : List Gate)
    (uniq : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i=j) :
    inversionCount gs ≤ 1 := by
  induction gs with
  | nil => decide
  | cons g gs ih =>
    by_cases head : g.op = .not
    · have none (x : Gate) (hx : x ∈ gs) : x.op ≠ .not := by
        obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hx
        intro nj
        have eq := uniq ⟨0,by simp⟩ j.succ head nj
        have e := congrArg Fin.val eq
        simp at e
      have one : invCost g = 1 := by simp [invCost,head]
      rw [inversionCount,zero_inversions gs none,one]
    · have zero : invCost g = 0 := by rcases g with ⟨op,ins⟩; cases op <;> simp_all [invCost]
      rw [inversionCount,zero,Nat.add_zero]
      apply ih
      intro i j ni nj
      exact Fin.succ_injective _ (uniq i.succ j.succ ni nj)

theorem full_chain (gates : List Gate) (out : Nat)
    (legal : ∀ g ∈ gates, allowed g)
    (uniq : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i=j)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,out⟩ (List.ofFn x) = graph x) :
    ∃ b n, b+n ≤ gates.length ∧ n ≤ 1 ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,hn,S,sub,live⟩ := circuit_live ⟨gates,out⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb hn).trans (cost_bound gates),hn.trans (unique_inversion gates uniq),live⟩

theorem has_inversion_cost (gates : List Gate) (hasNot : ∃ g ∈ gates, g.op = .not) :
    1 ≤ inversionCount gates := by
  induction gates with
  | nil => simp at hasNot
  | cons g gs ih =>
    by_cases top : g.op = .not
    · simp [inversionCount, invCost, top]
    · obtain ⟨f,hf,inv⟩ := hasNot
      have hin : f ∈ gs := (List.mem_cons.mp hf).resolve_left (fun eq => top (eq ▸ inv))
      have tail := ih ⟨f,hin,inv⟩
      rw [inversionCount]
      omega

theorem signed_chain {gates : List Gate} {out : Nat}
    (legal : ∀ g ∈ gates, allowed g)
    (uniq : ∀ i j : Fin gates.length, (gates.get i).op = .not → (gates.get j).op = .not → i=j)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,out⟩ (List.ofFn x) = graph x)
    (hasNot : ∃ g ∈ gates, g.op = .not) :
    ∃ b n, b+1 ≤ gates.length ∧ n ≤ 1 ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,hn,S,sub,live⟩ := circuit_live ⟨gates,out⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb (has_inversion_cost gates hasNot)).trans (cost_bound gates),
    hn.trans (unique_inversion gates uniq),live⟩

def counted (g : Gate) : Bool := match g.op with | .not => false | _ => true

theorem binaryCount_le_countP (gs : List Gate) :
    binaryCount gs ≤ gs.countP counted := by
  induction gs with
  | nil => simp [binaryCount]
  | cons g gs ih =>
    have cap : binCost g ≤ (counted g).toNat := by
      obtain ⟨op, inputs⟩ := g
      cases op <;> cases inputs with
      | nil => simp [binCost, counted]
      | cons a rest => cases rest <;> simp [binCost, counted]
    rw [binaryCount, List.countP_cons]
    cases h : counted g <;> simp [h] at cap ⊢ <;> omega

theorem circuit_chain (gs : List Gate) (o : Nat)
    (legal : FanInTwo ⟨gs,o⟩)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Frame.target x) :
    ∃ b n, b ≤ gs.countP counted ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,_,S,sub,live⟩ := circuit_live ⟨gs,o⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,hb.trans (binaryCount_le_countP gs),live⟩

theorem freely_chain (gs : List Gate) (o : Nat)
    (legal : FanInTwo ⟨gs,o⟩)
    (correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Frame.target x)
    (hasNot : ∃ g ∈ gs, g.op = .not) :
    ∃ b n, b+1 ≤ gs.length ∧ Live b n roots.toFinset := by
  obtain ⟨b,hb,n,_,S,sub,live⟩ := circuit_live ⟨gs,o⟩ legal correct
  rw [roots_full live sub] at live
  exact ⟨b,n,(Nat.add_le_add hb (has_inversion_cost gs hasNot)).trans (cost_bound gs),live⟩

end PEqualNP.Outside.L_meta_31665

namespace PEqualNP.Outside.L_meta_31665.Reduce
open PEqualNP.Outside.L_meta_31665

def half (b : Bool) (w : Word) : BitVec 128 :=
  if b then w.extractLsb' 128 128 else w.extractLsb' 0 128
def pin128 (b : Bool) (w : Word) := canon (half b w)
def lit : Word := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def literal (w : Word) := w = lit ∨ w = ~~~lit
def indep (w : Word) := half false w = half true w
def safe (w : Word) : Prop := literal w ∨ indep w ∧ pin128 false w ≠ 0

theorem half_not (b : Bool) (v : Word) : half b (~~~v) = ~~~half b v := by
  cases b <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj <;>
    simp [half,BitVec.getLsbD_not,hj,show 128+j < 256 by omega,show j < 256 by omega]
theorem half_and (b : Bool) (v w : Word) : half b (v &&& w) = half b v &&& half b w := by
  cases b <;> exact BitVec.extractLsb'_and
theorem half_or (b : Bool) (v w : Word) : half b (v ||| w) = half b v ||| half b w := by
  cases b <;> exact BitVec.extractLsb'_or
theorem indep_nz (w : Word) (h : indep w) (hp : w ≠ 0 ∧ w ≠ ones) : pin128 false w ≠ 0 := by
  change half false w = half true w at h
  have rebuild : half true w ++ half false w = w := BitVec.extractLsb'_append_extractLsb'
  rw [←h] at rebuild
  unfold pin128 canon
  intro bad
  split at bad
  · have both := congrArg (fun x : BitVec 128 => ~~~x) bad
    simp only [BitVec.not_not,BitVec.not_zero] at both
    rw [both] at rebuild
    exact hp.2 (rebuild.symm.trans (by decide))
  · rw [bad] at rebuild
    exact hp.1 (rebuild.symm.trans (by decide))

theorem safe_not (v : Word) (h : safe v) : safe (~~~v) := by
  rcases h with (rfl|rfl)|⟨e,q⟩
  · exact Or.inl (Or.inr rfl)
  · exact Or.inl (Or.inl BitVec.not_not)
  · right
    exact ⟨by simpa only [indep,half_not] using congrArg (fun t => ~~~t) e,
      by simpa only [pin128,half_not,canon_not] using q⟩
theorem indep_join (d : Bool) {a b : Word} (ha : indep a) (hb : indep b) :
    indep (join d a b) := by
  unfold indep at *
  cases d <;> simp [join,half_or,half_and,ha,hb]
theorem p128neg (b : Bool) (w : Word) : pin128 b (~~~w) = pin128 b w := by
  simp [pin128,half_not,canon_not]
theorem p128repr (e d : Bool) (a b : Word) :
    ∃ s t, pin128 e (join d a b) = gate s t (pin128 e a) (pin128 e b) := by
  cases d
  · exact ⟨(half e a).getLsbD 0,(half e b).getLsbD 0,by simp only [pin128,gate,sign_back]; exact congrArg canon (half_and _ _ _)⟩
  · refine ⟨(~~~(half e a)).getLsbD 0,(~~~(half e b)).getLsbD 0,?_⟩
    unfold gate pin128
    rw [←canon_not (half e a),←canon_not (half e b),sign_back,sign_back,←BitVec.not_or,canon_not]
    exact congrArg canon (half_or _ _ _)
theorem pin128goal (e : Bool) : pin128 e goal ≠ 0 := by cases e <;> decide +kernel
theorem ordinary {b n S} (h : Live b n S) (e : Bool) : Proj (pin128 e) (pin128 e goal) b 0 S := by
  induction h using Live.recPlain with
  | done => exact proj_done _ _ (pin128goal _)
  | @inversion b n a U fresh proper tail ih =>
    exact proj_inv _ _ _ _ (fun h => fresh (by simp [h])) (p128neg e a) ih
  | @binary b n a x U d ne fresh proper tail ih =>
    obtain ⟨s,t,rep⟩ := p128repr e d a x
    exact proj_bin _ _ _ _ _ (fun v => canon_canon _) (fun h => fresh (by simp [h])) s t rep ih

theorem choose_kill (d : Bool) (v w : Word) (h : literal v) :
    ∃ e, pin128 e (join d v w) = 0 := by
  rcases h with rfl|rfl <;> cases d
  · exact ⟨false,by rw [pin128,show join false lit w = lit &&& w from rfl,half_and,show half false lit = 0 by decide]; simp only [show ∀ v : BitVec 128, (0 : BitVec 128) &&& v = 0 from fun v => BitVec.zero_and]; decide⟩
  · exact ⟨true,by rw [pin128,show join true lit w = lit ||| w from rfl,half_or,show half true lit = BitVec.allOnes 128 by decide,BitVec.allOnes_or]; decide⟩
  · exact ⟨true,by rw [pin128,show join false (~~~lit) w = (~~~lit) &&& w from rfl,half_and,show half true (~~~lit) = 0 by decide]; simp only [show ∀ v : BitVec 128, (0 : BitVec 128) &&& v = 0 from fun v => BitVec.zero_and]; decide⟩
  · exact ⟨false,by rw [pin128,show join true (~~~lit) w = (~~~lit) ||| w from rfl,half_or,show half false (~~~lit) = BitVec.allOnes 128 by decide,BitVec.allOnes_or]; decide⟩
theorem nz_else {w : Word} (h : indep w) (nz : pin128 false w ≠ 0) (e : Bool) : pin128 e w ≠ 0 := by
  cases e
  · exact nz
  · change half false w = half true w at h
    simpa only [pin128,←h] using nz
theorem impossible_lits (d : Bool) (a x : Word) (ha : literal a) (hx : literal x)
    (ne : a ≠ x) (proper : join d a x ≠ 0 ∧ join d a x ≠ ones) : False := by
  rcases ha with rfl|rfl <;> rcases hx with rfl|rfl <;> cases d <;>
    first | exact ne rfl | exact proper.1 (by decide) | exact proper.2 (by decide)
theorem join_comm (d : Bool) (a b : Word) : join d a b = join d b a := by
  cases d <;> simp [join,BitVec.and_comm,BitVec.or_comm]

theorem chooseFirst {b n S} (h : Live b n S) :
    (∀ v ∈ S, safe v) → ∃ e, Proj (pin128 e) (pin128 e goal) b 1 S := by
  induction h using Live.recPlain with
  | done =>
    intro ok
    exact (show ¬ safe goal by unfold safe literal indep; decide +kernel) (ok _ (by simp)) |>.elim
  | @inversion b n a U fresh proper tail ih =>
    intro ok
    have ta : ∀ v ∈ insert (~~~a) U, safe v := by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|vU
      · exact safe_not a (ok a (by simp))
      · exact ok v (by simp [vU])
    obtain ⟨e,good⟩ := ih ta
    exact ⟨e,proj_inv _ _ _ _ (fun h => fresh (by simp [h])) (p128neg e a) good⟩
  | @binary b n a x U d ne fresh proper tail ih =>
    intro ok
    have freshU : join d a x ∉ U := fun h => fresh (by simp [h])
    rcases ok a (by simp) with ha|⟨ea,na⟩ <;> rcases ok x (by simp) with hx|⟨ex,nx⟩
    · exact (impossible_lits d a x ha hx ne proper).elim
    · obtain ⟨e,kill⟩ := choose_kill d a x ha
      exact ⟨e,proj_strong _ _ _ _ _ freshU kill (Or.inr (nz_else ex nx e)) (ordinary tail e)⟩
    · obtain ⟨e,kill⟩ := choose_kill d x a hx
      rw [join_comm d x a] at kill
      exact ⟨e,proj_strong _ _ _ _ _ freshU kill (Or.inl (nz_else ea na e)) (ordinary tail e)⟩
    · have ec := indep_join d ea ex
      have ta : ∀ v ∈ insert (join d a x) U, safe v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl|vU
        · exact Or.inr ⟨ec,indep_nz _ ec proper⟩
        · exact ok v (by simp [vU])
      obtain ⟨e,good⟩ := ih ta
      obtain ⟨s,t,rep⟩ := p128repr e d a x
      exact ⟨e,proj_bin _ _ _ _ _ (fun v => canon_canon _) freshU s t rep good⟩
end PEqualNP.Outside.L_meta_31665.Reduce

namespace PEqualNP.Outside.L_meta_31665.Reduce
open PEqualNP.Outside.L_meta_31665

def sixPin (w : BitVec 128) : BitVec 64 := canon (w.setWidth 64)
theorem sixPin_not (w : BitVec 128) : sixPin (~~~w) = sixPin w := by
  unfold sixPin; rw [BitVec.setWidth_not (by decide),canon_not]
theorem sixPin_canon (w : BitVec 128) : sixPin (canon w) = sixPin w := by
  by_cases h : w.getLsbD 0 = true
  · rw [show canon w = ~~~w from if_pos h,sixPin_not]
  · rw [show canon w = w from if_neg h]
theorem sixPin_signed (s : Bool) (w : BitVec 128) : sixPin (signed s w) = sixPin w := by
  cases s; rfl; exact sixPin_not _
theorem six_repr (s t : Bool) (a b : BitVec 128) :
    ∃ u v, sixPin (gate s t a b) = gate u v (sixPin a) (sixPin b) := by
  let x := signed s a; let y := signed t b
  change ∃ u v, sixPin (canon (x &&& y)) = gate u v (sixPin a) (sixPin b)
  rw [sixPin_canon,← sixPin_signed s a,← sixPin_signed t b]
  refine ⟨(x.setWidth 64).getLsbD 0,(y.setWidth 64).getLsbD 0,?_⟩
  change canon ((x &&& y).setWidth 64) = gate ((x.setWidth 64).getLsbD 0) ((y.setWidth 64).getLsbD 0) (canon (x.setWidth 64)) (canon (y.setWidth 64))
  simp only [gate,sign_back]; exact congrArg canon BitVec.setWidth_and
theorem second {g : BitVec 128} {k S} (h : Path g k S) (nz : sixPin g ≠ 0) :
    Proj sixPin (sixPin g) k 0 S := by
  apply h (fun k S => Proj sixPin (sixPin g) k 0 S) (proj_done _ _ nz)
  intro j a b U s t ne fresh proper tail
  obtain ⟨u,v,rep⟩ := six_repr s t a b
  exact proj_bin _ _ _ _ _ (fun w => canon_canon _) (fun q => fresh (by simp [q])) u v rep tail

def sevenRaw : List (BitVec 128) := [0xffffffffffffffff0000000000000000,0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000]
def cliqueRaw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def cliqueGoal : BitVec 64 := 0xfffffffcfffaee00
theorem path_equal {m : Nat} {g : BitVec (m+1)} {k S} (h : Path g k S) (p q : Fin (m+1))
    (same : ∀ x ∈ S, x.getLsbD p = x.getLsbD q) : g.getLsbD p = g.getLsbD q := by
  apply h (fun _ T => (∀ x ∈ T, x.getLsbD p = x.getLsbD q) → g.getLsbD p = g.getLsbD q) ?_ ?_ same
  · exact fun h => h _ (by simp)
  · intro i a b U s t ne fresh proper ih eq
    apply ih; intro w hw; rcases Finset.mem_insert.mp hw with rfl|old
    · have ea := eq a (by simp); have eb := eq b (by simp); unfold gate canon
      split <;> cases s <;> cases t <;> simp only [signed,Bool.false_eq_true,reduceIte,BitVec.getLsbD_not,BitVec.getLsbD_and,decide_eq_true p.isLt,decide_eq_true q.isLt,ea,eb]
    · exact eq _ (by simp [old])
def sevenPairs (e : Bool) (v : Fin 7) : Fin 128 × Fin 128 :=
  if e then ([(0,64),(8,9),(8,10),(16,20),(1,9),(1,17),(2,34)] : List _).get v
  else ([(8,72),(8,9),(8,10),(16,20),(1,9),(1,17),(2,34)] : List _).get v
theorem exclusive7 : ∀ e (i : Fin 7),
    (pin128 e goal).getLsbD (sevenPairs e i).1 ≠ (pin128 e goal).getLsbD (sevenPairs e i).2 ∧
    ∀ j : Fin 7, (sevenRaw.get j).getLsbD (sevenPairs e i).1 = (sevenRaw.get j).getLsbD (sevenPairs e i).2 ∨ j = i := by decide +kernel
theorem seven_full {e k T} (hp : Path (pin128 e goal) k T) (sub : T ⊆ sevenRaw.toFinset) :
    T = sevenRaw.toFinset := by
  apply Finset.Subset.antisymm sub; intro x hx
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hx)
  obtain ⟨distinct,only⟩ := exclusive7 e i; by_contra missing
  apply distinct (path_equal hp _ _ ?_); intro w hw
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp (sub hw))
  exact (only j).resolve_right (by rintro rfl; exact missing hw)
theorem to_six {b n} (h : Live b n roots.toFinset) :
    ∃ k, k+3 ≤ b ∧ ∃ T ⊆ cliqueRaw.toFinset, Path cliqueGoal k T := by
  have ok : ∀ v ∈ roots.toFinset, safe v := by
    simp only [List.mem_toFinset,roots,List.mem_cons,List.not_mem_nil,or_false]
    intro v hv; rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> unfold safe literal indep <;> decide +kernel
  obtain ⟨e,k,hk,T,sub,hp⟩ := chooseFirst h ok
  have av : avail (pin128 e) roots.toFinset = sevenRaw.toFinset := by cases e <;> decide +kernel
  have ls : lost (pin128 e) roots.toFinset = 1 := by cases e <;> decide +kernel
  rw [av] at sub; rw [seven_full hp sub] at hp
  have geq : sixPin (pin128 e goal) = cliqueGoal := by cases e <;> decide +kernel
  have nz : sixPin (pin128 e goal) ≠ 0 := by rw [geq]; decide
  obtain ⟨j,hj,U,sub6,hr⟩ := second hp nz
  have av6 : avail sixPin sevenRaw.toFinset = cliqueRaw.toFinset := by decide +kernel
  have ls6 : lost sixPin sevenRaw.toFinset = 1 := by decide +kernel
  rw [av6] at sub6; rw [geq] at hr; exact ⟨j,by omega,U,sub6,hr⟩
end PEqualNP.Outside.L_meta_31665.Reduce

namespace PEqualNP.Outside.L_meta_31665.ArchivedClique
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

theorem viaCut {m h f t : ℕ} {v w : List ℕ} (p : Projection m h)
    (bound : Wide h t w) (nd : v.Nodup)
    (mem : ∀ a∈v, p.toFun a=0 ∨ p.toFun a∈w)
    (cost : f≤t+(v.map p.toFun).count 0) : Ban m f v := by
  intro k lim run
  obtain ⟨j,T,c,ok,incl⟩ := projectLive p run
  have fixed : dead p.toFun v.toFinset=(v.map p.toFun).count 0 := by
    dsimp [dead]
    have E : v.toFinset.filter (fun x => p.toFun x=0) = (v.filter (fun x => decide (p.toFun x=0))).toFinset := by ext x;simp
    rw [E,List.toFinset_card_of_nodup (nd.filter _)]
    simp only [List.count_eq_countP,List.countP_map,Function.comp_apply]
    rw [List.countP_eq_length_filter]
    congr 2
  rw [fixed] at c
  apply bound
  refine ⟨j,T,by omega,ok,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp (incl _ hx)
  exact (mem y (List.mem_toFinset.mp hy)).resolve_left (liveNonzero ok _ hx)

theorem renameLive {m h k S} (p : Projection m h) (q : Projection h m)
    (run : Live m k S) (rec : ∀ x∈S, q.toFun (p.toFun x)=x) : Live h k (S.image p.toFun) := by
  induction k generalizing S with
  | zero =>
    rw [Live] at run
    obtain ⟨a,rfl,good,nz⟩ := run
    simp only [Finset.image_singleton]
    apply Live.done (p.good a good)
    intro e
    have := rec a (Finset.mem_singleton_self a)
    rw [e,q.atZero] at this
    exact nz this.symm
  | succ k ih =>
    rw [Live] at run
    obtain ⟨U,a,b,d,rfl,hd,ha,hb,ab,fr,tail⟩ := run
    let z := combine d a b
    have ra := rec a (Finset.mem_insert_self _ _)
    have rb := rec b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have rz : q.toFun (p.toFun z)=z := by simp only [z,p.combineEq _ _ _ hd,q.combineEq _ _ _ hd,ra,rb]
    have ru (x) (hx : x∈U) := rec x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx))
    have nr := ih tail (by intro x hx; rcases Finset.mem_insert.mp hx with rfl|h; exact rz; exact ru _ h)
    have eqz : p.toFun z=combine d (p.toFun a) (p.toFun b) := p.combineEq _ _ _ hd
    simp only [Finset.image_insert] at nr ⊢
    apply Live.step hd
    · intro e;rw [e,q.atZero] at ra;exact ha ra.symm
    · intro e;rw [e,q.atZero] at rb;exact hb rb.symm
    · intro e;rw [e,rb] at ra;exact ab ra.symm
    · rw [←eqz]
      intro bad
      rcases Finset.mem_insert.mp bad with e|bad
      · have hza := congrArg q.toFun e
        rw [rz,ra] at hza
        exact fr (Finset.mem_insert.mpr (Or.inl hza))
      rcases Finset.mem_insert.mp bad with e|bad
      · have hzb := congrArg q.toFun e
        rw [rz,rb] at hzb
        exact fr (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hzb)))
      obtain ⟨x,hx,e⟩ := Finset.mem_image.mp bad
      have eq := congrArg q.toFun e
      rw [ru x hx,rz] at eq
      exact fr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (eq ▸ hx : z ∈ U)))
    · simpa only [p.combineEq _ _ _ hd] using nr

theorem viaPerm {m h f v w} (p : Projection m h) (q : Projection h m)
    (ban : Ban h f w) (rec : ∀ a∈v, q.toFun (p.toFun a)=a)
    (eq : (v.map p.toFun).toFinset=w.toFinset) : Ban m f v := by
  intro n hn live
  have ok := renameLive p q live (by simpa using rec)
  apply ban n hn
  have E : (v.map p.toFun).toFinset=v.toFinset.image p.toFun := by ext x;simp
  rw [←eq,E];exact ok

def ordered (v : List ℕ) := v.insertionSort (· ≤ ·)
theorem ord_eq (v : List ℕ) : (ordered v).toFinset=v.toFinset := by
  ext x;simp [ordered,List.mem_insertionSort]
def banList (m f : ℕ) (vs : List (List ℕ)) := ∀ v∈vs, Ban m f v
theorem consBan {m f a l} (h : Ban m f a) (t : banList m f l) : banList m f (a::l) := by
  intro v hv;rcases List.mem_cons.mp hv with rfl|e;exact h;exact t _ e
theorem nilBan (m f) : banList m f [] := by simp [banList]

theorem viaBranch {m f : ℕ} {v : List ℕ} {ws : List (List ℕ)} (closed : banList m f ws)
    (nd : v.Nodup) (no : terminal m v=false)
    (test : anyGate m f (fun u => !ws.contains (ordered u)) v=false) : Ban m (f+1) v := by
  intro n lim live
  cases n with
  | zero =>
    rw [Live] at live
    obtain ⟨a,rep,g,_⟩ := live
    have ev := ends g v (List.mem_toFinset.mp (rep ▸ Finset.mem_singleton_self a))
    simp_all
  | succ n =>
    rw [Live] at live
    obtain ⟨U,a,b,d,rep,hd,_,_,ab,fr,tail⟩ := live
    have yes := @transition m f n U a b d v (fun u => !ws.contains (ordered u)) hd ab fr rep nd (by omega) tail (by
      intro u hu nu
      change (!ws.contains (ordered u))=true
      simp
      intro found
      have hv := closed _ found n (by omega)
      rw [ord_eq,hu] at hv
      exact hv tail)
    simp_all

theorem widen {m f v} (ess : ∀ a∈v, ∃ i : Fin m, ∀ b∈v, b.testBit i.val≠b.testBit (m+i.val) → b=a)
    (h : Ban m f v) : Wide m f v := by
  rintro ⟨n,S,le,live,sub⟩
  have eq : S=v.toFinset := by
    apply Finset.Subset.antisymm (fun x hx => List.mem_toFinset.mpr (sub _ hx))
    intro a ha
    obtain ⟨i,hi⟩ := ess a (List.mem_toFinset.mp ha)
    obtain ⟨b,hb,sep⟩ := liveSeparates live i.val i.isLt
    exact hi b (sub b hb) sep ▸ hb
  exact h n le (eq ▸ live)

theorem viaSmall {m f v} (ex : search m f v=false) (nd : v.Nodup) : Ban m f v := by
  intro n le live
  have := complete m f live le v rfl nd
  simp_all

theorem viaSub {m f v ws} (bs : banList m f ws) (nd : v.Nodup)
    (check : v.sublists.all (fun u => !(u.length≤f+1 && enough m (cover m u)) || ws.contains u)=true) :
    Wide m f v := by
  rintro ⟨n,S,lim,live,sub⟩
  let u := v.filter (fun x => decide (x∈S))
  have eq : u.toFinset=S := by ext x; simp [u]; exact fun hx => sub _ hx
  have nd' : u.Nodup := nd.filter _
  have len := liveSize live
  rw [←eq,List.toFinset_card_of_nodup nd'] at len
  have ok := List.all_eq_true.mp check u (List.mem_sublists.mpr List.filter_sublist)
  have cap : u.length≤f+1 := by omega
  have cov := enoughLive live u eq
  simp [cap,cov] at ok
  exact bs u ok n lim (eq ▸ live)

abbrev B := Ban
abbrev W := Wide
def pt0 : Projection 87 87 := pick [18,20,19,21,24,25,22,23,26,27,28,29,30,32,33,31,34,35,0,2,1,3,6,7,4,5,8,9,10,11,12,15,13,14,16,17,36,38,37,39,40,43,44,41,42,45,46,56,57,58,59,61,62,60,63,64,47,48,49,50,53,51,52,54,55,76,78,77,79,80,83,84,81,82,85,86,65,67,66,68,69,72,73,70,71,74,75] rfl (by decide +kernel) (by decide)
def pti0 : Projection 87 87 := pick [18,20,19,21,24,25,22,23,26,27,28,29,30,32,33,31,34,35,0,2,1,3,6,7,4,5,8,9,10,11,12,15,13,14,16,17,36,38,37,39,40,43,44,41,42,45,46,56,57,58,59,61,62,60,63,64,47,48,49,50,53,51,52,54,55,76,78,77,79,80,83,84,81,82,85,86,65,67,66,68,69,72,73,70,71,74,75] rfl (by decide +kernel) (by decide)
def pt1 : Projection 87 87 := pick [9,10,11,12,13,14,16,17,15,0,1,2,3,4,5,8,6,7,47,48,49,50,51,52,54,55,53,56,58,57,59,60,63,64,61,62,65,66,68,67,69,70,71,74,75,72,73,18,19,20,21,22,23,26,24,25,27,29,28,30,31,34,35,32,33,36,37,39,38,40,41,42,45,46,43,44,76,77,79,78,80,81,82,85,86,83,84] rfl (by decide +kernel) (by decide)
def pti1 : Projection 87 87 := pick [9,10,11,12,13,14,16,17,15,0,1,2,3,4,5,8,6,7,47,48,49,50,51,52,54,55,53,56,58,57,59,60,63,64,61,62,65,66,68,67,69,70,71,74,75,72,73,18,19,20,21,22,23,26,24,25,27,29,28,30,31,34,35,32,33,36,37,39,38,40,41,42,45,46,43,44,76,77,79,78,80,81,82,85,86,83,84] rfl (by decide +kernel) (by decide)
def pt2 : Projection 87 87 := pick [47,49,48,50,54,55,51,52,53,56,58,57,59,63,64,60,61,62,9,11,10,12,16,17,13,14,15,0,1,2,3,8,4,5,6,7,65,68,66,67,69,74,75,70,71,72,73,27,29,28,30,34,35,31,32,33,18,19,20,21,26,22,23,24,25,76,79,77,78,80,85,86,81,82,83,84,36,39,37,38,40,45,46,41,42,43,44] rfl (by decide +kernel) (by decide)
def pti2 : Projection 87 87 := pick [27,28,29,30,32,33,34,35,31,18,20,19,21,24,25,26,22,23,56,57,58,59,61,62,63,64,60,47,49,48,50,53,54,55,51,52,76,78,79,77,80,83,84,85,86,81,82,0,2,1,3,6,7,8,4,5,9,11,10,12,15,16,17,13,14,36,38,39,37,40,43,44,45,46,41,42,65,67,68,66,69,72,73,74,75,70,71] rfl (by decide +kernel) (by decide)
def pt3 : Projection 87 87 := pick [27,28,29,30,32,33,34,35,31,18,20,19,21,24,25,26,22,23,56,57,58,59,61,62,63,64,60,47,49,48,50,53,54,55,51,52,76,78,79,77,80,83,84,85,86,81,82,0,2,1,3,6,7,8,4,5,9,11,10,12,15,16,17,13,14,36,38,39,37,40,43,44,45,46,41,42,65,67,68,66,69,72,73,74,75,70,71] rfl (by decide +kernel) (by decide)
def pti3 : Projection 87 87 := pick [47,49,48,50,54,55,51,52,53,56,58,57,59,63,64,60,61,62,9,11,10,12,16,17,13,14,15,0,1,2,3,8,4,5,6,7,65,68,66,67,69,74,75,70,71,72,73,27,29,28,30,34,35,31,32,33,18,19,20,21,26,22,23,24,25,76,79,77,78,80,85,86,81,82,83,84,36,39,37,38,40,45,46,41,42,43,44] rfl (by decide +kernel) (by decide)
def pt4 : Projection 87 87 := pick [56,58,57,59,63,64,61,62,60,47,49,48,50,54,55,53,51,52,27,29,28,30,34,35,32,33,31,18,20,19,21,26,24,25,22,23,76,79,78,77,80,85,86,83,84,81,82,9,11,10,12,16,17,15,13,14,0,2,1,3,8,6,7,4,5,65,68,67,66,69,74,75,72,73,70,71,36,39,38,37,40,45,46,43,44,41,42] rfl (by decide +kernel) (by decide)
def pti4 : Projection 87 87 := pick [56,58,57,59,63,64,61,62,60,47,49,48,50,54,55,53,51,52,27,29,28,30,34,35,32,33,31,18,20,19,21,26,24,25,22,23,76,79,78,77,80,85,86,83,84,81,82,9,11,10,12,16,17,15,13,14,0,2,1,3,8,6,7,4,5,65,68,67,66,69,74,75,72,73,70,71,36,39,38,37,40,45,46,43,44,41,42] rfl (by decide +kernel) (by decide)
def pc0_0 : Projection 35 35 := pick [10,12,11,13,14,15,17,16,18,19,0,2,1,3,4,5,7,6,8,9,20,22,21,23,24,30,32,31,33,34,25,27,26,28,29] rfl (by decide +kernel) (by decide)
def pci0_0 : Projection 35 35 := pick [10,12,11,13,14,15,17,16,18,19,0,2,1,3,4,5,7,6,8,9,20,22,21,23,24,30,32,31,33,34,25,27,26,28,29] rfl (by decide +kernel) (by decide)
def pc1_0 : Projection 35 35 := pick [15,18,17,16,19,10,13,12,11,14,5,8,7,6,9,0,3,2,1,4,30,33,32,31,34,25,28,27,26,29,20,23,22,21,24] rfl (by decide +kernel) (by decide)
def pci1_0 : Projection 35 35 := pick [15,18,17,16,19,10,13,12,11,14,5,8,7,6,9,0,3,2,1,4,30,33,32,31,34,25,28,27,26,29,20,23,22,21,24] rfl (by decide +kernel) (by decide)
def pc6_0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def pci6_0 : Projection 20 20 := pick [4,6,5,7,0,2,1,3,12,14,13,15,8,10,9,11,16,18,17,19] rfl (by decide +kernel) (by decide)
def pc7_1 : Projection 20 20 := pick [8,9,10,11,16,17,18,19,0,1,2,3,12,13,14,15,4,5,6,7] rfl (by decide +kernel) (by decide)
def pci7_1 : Projection 20 20 := pick [8,9,10,11,16,17,18,19,0,1,2,3,12,13,14,15,4,5,6,7] rfl (by decide +kernel) (by decide)
def pc9_0 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def pci9_0 : Projection 16 16 := pick [1,0,2,3,13,12,14,15,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def pc11_0 : Projection 20 20 := pick [5,4,6,7,1,0,2,3,9,8,10,11,17,16,18,19,13,12,14,15] rfl (by decide +kernel) (by decide)
def pci11_0 : Projection 20 20 := pick [5,4,6,7,1,0,2,3,9,8,10,11,17,16,18,19,13,12,14,15] rfl (by decide +kernel) (by decide)
def pc18_0 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def pci18_0 : Projection 12 12 := pick [4,6,5,7,0,2,1,3,8,10,9,11] rfl (by decide +kernel) (by decide)
def pc18_1 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def pci18_1 : Projection 12 12 := pick [1,0,2,3,9,8,10,11,5,4,6,7] rfl (by decide +kernel) (by decide)
def pc18_2 : Projection 12 12 := pick [9,10,8,11,1,2,0,3,5,6,4,7] rfl (by decide +kernel) (by decide)
def pci18_2 : Projection 12 12 := pick [6,4,5,7,10,8,9,11,2,0,1,3] rfl (by decide +kernel) (by decide)
def pjt_0 : Projection 87 35 := pick [11,14,15,16,9,49,52,53,54,47,29,31,33,34,27,58,60,62,63,56,39,42,44,45,36,68,71,73,74,65,79,82,84,85,76] rfl (by decide +kernel) (by decide)
def pjt_1 : Projection 87 35 := pick [2,5,6,8,0,20,23,24,26,18,28,31,32,35,27,57,60,61,64,56,38,42,43,46,36,67,71,72,75,65,78,82,83,86,76] rfl (by decide +kernel) (by decide)
def pjt_2 : Projection 87 35 := pick [1,4,7,8,0,19,22,25,26,18,10,13,15,17,9,48,51,53,55,47,37,41,44,46,36,66,70,73,75,65,77,81,84,86,76] rfl (by decide +kernel) (by decide)
def pjt_6 : Projection 87 20 := pick [31,32,34,27,60,61,63,56,42,43,45,36,71,72,74,65,82,83,85,76] rfl (by decide +kernel) (by decide)
def pjt_7 : Projection 87 20 := pick [13,15,16,9,51,53,54,47,41,44,45,36,70,73,74,65,81,84,85,76] rfl (by decide +kernel) (by decide)
def pjt_8 : Projection 87 16 := pick [49,53,54,47,29,33,34,27,58,62,63,56,79,84,85,76] rfl (by decide +kernel) (by decide)
def pjt_9 : Projection 87 16 := pick [11,14,16,9,49,52,54,47,58,60,63,56,68,71,74,65] rfl (by decide +kernel) (by decide)
def pjt_10 : Projection 87 12 := pick [11,14,15,9,29,31,33,27,39,42,44,36] rfl (by decide +kernel) (by decide)
def pjt_11 : Projection 87 20 := pick [4,6,8,0,22,24,26,18,41,43,46,36,70,72,75,65,81,83,86,76] rfl (by decide +kernel) (by decide)
def pjt_12 : Projection 87 16 := pick [20,24,26,18,28,32,35,27,57,61,64,56,78,83,86,76] rfl (by decide +kernel) (by decide)
def pjt_14 : Projection 87 16 := pick [2,5,6,0,20,23,24,18,28,31,32,27,38,42,43,36] rfl (by decide +kernel) (by decide)
def pjt_16 : Projection 87 16 := pick [1,4,8,0,10,13,17,9,48,51,55,47,66,70,75,65] rfl (by decide +kernel) (by decide)
def pjt_17 : Projection 87 16 := pick [1,4,7,0,19,22,25,18,10,13,15,9,37,41,44,36] rfl (by decide +kernel) (by decide)
def pjt_18 : Projection 87 12 := pick [41,43,45,36,70,72,74,65,81,83,85,76] rfl (by decide +kernel) (by decide)
def pjt_20 : Projection 87 6 := pick [31,32,27,42,43,36] rfl (by decide +kernel) (by decide)
def pjt_23 : Projection 87 6 := pick [49,54,47,58,63,56] rfl (by decide +kernel) (by decide)
def pjt_29 : Projection 87 6 := pick [20,24,18,28,32,27] rfl (by decide +kernel) (by decide)
def pjt_33 : Projection 87 6 := pick [1,4,0,10,13,9] rfl (by decide +kernel) (by decide)
def f0 : ℕ := 0x1110f0
def f1 : ℕ := 0x1110ff
def f2 : ℕ := 0x222f0f
def f3 : ℕ := 0x444ff0
def f4 : ℕ := 0x111110ff00
def f5 : ℕ := 0x22222000ff
def f6 : ℕ := 0x22222f0f00
def f7 : ℕ := 0x44444ff0f0
def f8 : ℕ := 0x111110ff0f
def f9 : ℕ := 0xf
def f11 : ℕ := 0x22222f0f0f
def f13 : ℕ := 0x11111000ff
def f17 : ℕ := 0x44444ff000
def f18 : ℕ := 0x2004008080200404020100000000000000000000000
def f19 : ℕ := 0x2e05c0f0b02e078582c16000001ff00000ff8000000
def f20 : ℕ := 0x30060080c030040603018000ffe00007ff00003ffff
def f21 : ℕ := 0x8d11a261388d131144e4500000000ff80000003fe00
def f22 : ℕ := 0xc018030100c01818040607ff00000007ffffffc0000
def f23 : ℕ := 0x20b4168542a0b42a1d0a870000000000000007fc01ff
def f24 : ℕ := 0x300600c0603006020180807fffffffff800000000000
def f25 : ℕ := 0x111100f0
def f26 : ℕ := 0x111100ff
def f27 : ℕ := 0x3333ff0f
def f28 : ℕ := 0x4444fff0
def f29 : ℕ := 0xf00
def f30 : ℕ := 0x11110ff0
def f31 : ℕ := 0x4444ff00
def f32 : ℕ := 0x5555000f
def f34 : ℕ := 0x55500f
def f35 : ℕ := 0x4210842103ff0001f
def f36 : ℕ := 0x6318c63183ffffc1f
def f37 : ℕ := 0x842108427c1f07fe0
def f38 : ℕ := 0x1084210847fe0f8000
def f39 : ℕ := 0x1294a52948000003ff
def f40 : ℕ := 0x210842108000ffc00
def f41 : ℕ := 0xa5294a52fc1ffffe0
def f42 : ℕ := 0x210842108000f8000
def f43 : ℕ := 0x842108427c1f003e0
def f45 : ℕ := 0x21084210800007c00
def f46 : ℕ := 0x1084210847fe000000
def f47 : ℕ := 0x21084210800000000
def f50 : ℕ := 0x487
def f51 : ℕ := 0x4b8
def f52 : ℕ := 0x1f07c00
def f53 : ℕ := 0x6318c63183e0f801f
def f54 : ℕ := 0x842108427c00003e0
def f55 : ℕ := 0x16b5ad6b5ffffffc1f
def f56 : ℕ := 0x6318c631801f07c1f
def f57 : ℕ := 0x16b5ad6b583fffffff
def f58 : ℕ := 0x4210842103ffffc00
def f59 : ℕ := 0x18c6318c67ffffffe0
def f60 : ℕ := 0x84210842001f07fe0
def f61 : ℕ := 0x1ad6b5ad6fc1f07fff
def f62 : ℕ := 0x842108427c1f07c00
def f63 : ℕ := 0x1294a5294ffe0f83ff
def f64 : ℕ := 0x7fe0f8000
def f65 : ℕ := 0x210842108000003ff
def f67 : ℕ := 0x2222f00f
def f68 : ℕ := 0x11110f00
def f69 : ℕ := 0x7c00
def f71 : ℕ := 0x1f00000
def f72 : ℕ := 0x4210842103e00001f
def f74 : ℕ := 0x14a5294a57ffff801f
def f75 : ℕ := 0x42108421001f0001f
def f76 : ℕ := 0x16b5ad6b583ff003ff
def f77 : ℕ := 0x4210842103ff00000
def f78 : ℕ := 0x247
def f79 : ℕ := 0x278
def f80 : ℕ := 0x2222f0ff
def f83 : ℕ := 0xc6318c637fff07fff
def f84 : ℕ := 0x2222f0f0
def f85 : ℕ := 0x3333000f
def f86 : ℕ := 0xa5294a528000003ff
def f87 : ℕ := 0x1084210847fe0f83e0
def f89 : ℕ := 0x842108427c1f00000
def f91 : ℕ := 0x842108420000003ff
def f93 : ℕ := 0x1084210847fe0003e0
def f94 : ℕ := 0xe739ce73ffffffc1f
def f95 : ℕ := 0xe739ce7383fffffff
def f96 : ℕ := 0x3e0f8000
def f97 : ℕ := 0x1084210847c00003e0
def f98 : ℕ := 0xa5294a52fc1f07fff
def f99 : ℕ := 0x7c1f07c00
def f100 : ℕ := 0x10842108403e0f83e0
def f101 : ℕ := 0x1ad6b5ad6ffe0f83ff
def f102 : ℕ := 0xf8000
def f103 : ℕ := 0xc6318c637fff07c1f
def f104 : ℕ := 0xe739ce7383ff003ff
def f105 : ℕ := 0x3e000000
def f106 : ℕ := 0x1084210847c00f83e0
def f107 : ℕ := 0x4210842103ff07c1f
def f108 : ℕ := 0x84210842001f07c00
def f109 : ℕ := 0x8421084200000001f
def f110 : ℕ := 0x210842108000003e0
def f111 : ℕ := 0x7fe000000
def f112 : ℕ := 0x1ce739ce77ffffffff
def f113 : ℕ := 0xc6318c63001f07c1f
def f115 : ℕ := 0x333fff
def f116 : ℕ := 0x21084210801fffc00
def f117 : ℕ := 0x1f
def f118 : ℕ := 0xa5294a528000003e0
def f119 : ℕ := 0x14a5294a57fe0f83ff
def f120 : ℕ := 0x4210842100000001f
def f121 : ℕ := 0x842108427c0000000
def f122 : ℕ := 0x7c0000000
def f123 : ℕ := 0x4444ff0f
def f124 : ℕ := 0x842108427c0007c00
def f129 : ℕ := 0xe01c070300e038180c06000001ff00000ff8000000
def f130 : ℕ := 0x3e07c0f0f03e078783c1e000fffff007ffff803ffff
def f131 : ℕ := 0x3fe00
def f132 : ℕ := 0x1294a52948000003e0
def f133 : ℕ := 0xbd17a2e1f8bd171747e5d000ffe00fffff00003ffff
def f134 : ℕ := 0x30060080c030040603018000ffe00007ff0000001ff
def f135 : ℕ := 0x8d11a261388d131144e4500000000ff800000000000
def f136 : ℕ := 0x7ff000000000
def f137 : ℕ := 0xf01e0381c0f01c1e070787ffffe00007fffffffffff
def f138 : ℕ := 0x4444f0f0
def f139 : ℕ := 0x55550f00
def f140 : ℕ := 0x333330ffff
def f141 : ℕ := 0x33333fff0f
def f147 : ℕ := 0x14a5294a57ffff83ff
def f148 : ℕ := 0x30060080c030040603018000ffe000000000003ffff
def f149 : ℕ := 0xc018030100c01818040607ff0000000000ffffc0000
def f150 : ℕ := 0x1ff
def f151 : ℕ := 0x23b4768d4ea3b46a7d3a9f000ffe00007ff007ffffff
def f152 : ℕ := 0x30060080c030040603018000ffe00007ff00003fe00
def f153 : ℕ := 0x20b4168542a0b42a1d0a870000000000000007fc0000
def f154 : ℕ := 0xffe0000000000000000
def f155 : ℕ := 0x330660c86c33064261b0987ffffffffffff00003ffff
def f156 : ℕ := 0x30060080c03004060301800000000007ff00003ffff
def f157 : ℕ := 0x300600c0603006020180807ff001ffff800000000000
def f158 : ℕ := 0xc018060300c030100c04000000000000000003fe00
def f159 : ℕ := 0xbf17e2f1f8bf1797c7e5f000ffffffffffff803ffff
def f160 : ℕ := 0x32064090c03204868301a000fffff007ffff80001ff
def f161 : ℕ := 0x81102201088110104424100000000ff800000000000
def f162 : ℕ := 0x7ffff8000000
def f163 : ℕ := 0xa5294a52fc00ffc00
def f164 : ℕ := 0xe739ce73fffffffff
def f165 : ℕ := 0x421084217fffffc00
def f166 : ℕ := 0xe739ce73801f07c1f
def f167 : ℕ := 0x1084210840000003e0
def f168 : ℕ := 0xfe1fc3f1f0fe1f9f87c7e7fffffff007fffffffffff
def f169 : ℕ := 0x22200f
def f171 : ℕ := 0x2222ff0f
def f172 : ℕ := 0x33330fff
def f175 : ℕ := 0x22220f00
def f178 : ℕ := 0x111110f000
def f179 : ℕ := 0x6318c63183fff801f
def f180 : ℕ := 0xe739ce7383e0f83ff
def f181 : ℕ := 0x4210842103e0f8000
def f182 : ℕ := 0x6318c63180000001f
def f183 : ℕ := 0x3e07c0f0f03e078783c1e000fffff0000000003ffff
def f184 : ℕ := 0xc018030100c01818040607ff0000000000007fc0000
def f185 : ℕ := 0xa014050200a02818080600000000000000000001ff
def f186 : ℕ := 0x23f47e8f4fa3f47a7d3e9f000fffff007fffffffffff
def f187 : ℕ := 0x340680a0d034050603418000fffff007ffff803fe00
def f188 : ℕ := 0x2014028040a014020502810000000000000007fc0000
def f189 : ℕ := 0xfffff00000000000000
def f190 : ℕ := 0x33e67ccf6f33e67a79bc9e7ffffffffffffff803ffff
def f191 : ℕ := 0x3e07c0f0f03e078783c1e00000000007ffff803ffff
def f192 : ℕ := 0x300600c0603006020180807ff00000ff800000000000
def f193 : ℕ := 0x8010020100801010040400000000000000000000000
def f201 : ℕ := 0xcd19a36138cd1b1944e657ff00000fffffffffffe00
def f202 : ℕ := 0xd01a060380d030140e0500000000ff80000003fe00
def f203 : ℕ := 0x3c0780f0703c078381c0e07ffffffffffffffffc0000
def f204 : ℕ := 0xc018030100c018180406000000000007ffffffc0000
def f205 : ℕ := 0x2cf59eb753acf5bb9d4ee77ff00000ffffffffffffff
def f206 : ℕ := 0xc418832110c41918044607ff00000fffffff803fe00
def f207 : ℕ := 0x30b616c562b0b62a1d8a877fffffffff800007fc01ff
def f208 : ℕ := 0xb016050280b0281c0a070000000000000007fc01ff
def f209 : ℕ := 0x10020040201002000080007fffffffff800000000000
def f214 : ℕ := 0x4008010000400808000207ff00000007ffffffc0000
def f215 : ℕ := 0x90120402809020140a050000000000000000000000
def f217 : ℕ := 0x28f51ea753a8f53b1d4ec700000000ff800007ffffff
def f218 : ℕ := 0x84108221108411100444000000000ff80000003fe00
def f219 : ℕ := 0x202404814020240a0900820000000000000007fc01ff
def f220 : ℕ := 0xff800000000000
def f221 : ℕ := 0x5555ffff
def f222 : ℕ := 0x3333f0ff
def f223 : ℕ := 0xf00f
def f224 : ℕ := 0x22220000
def f225 : ℕ := 0x55550ff0
def f226 : ℕ := 0x1111ff0f
def f227 : ℕ := 0x444400f0
def f228 : ℕ := 0x38d71ae673b8d73315cec57fffffffff80000003fe00
def f229 : ℕ := 0x8d11a261388d131144e45000000000000000003fe00
def f230 : ℕ := 0x300600c0603006020180807fffffff00000000000000
def f231 : ℕ := 0x7fc0000
def f232 : ℕ := 0x2cb596b552acb5ab9d4ae77ff00000007ffffffc01ff
def f233 : ℕ := 0xc018030100c01818040607ff00000007ffff8000000
def f234 : ℕ := 0x20b4168542a0b42a1d0a8700000000000000000001ff
def f235 : ℕ := 0x7ff0000000000000000000
def f237 : ℕ := 0x3ff00000
def f243 : ℕ := 0x1084210847c00f8000
def f246 : ℕ := 0x3f07e0f87c3f07c3e1f0f87fffffffffffffffffffff
def f247 : ℕ := 0x30060080c030040603018000000000000000003ffff
def f248 : ℕ := 0xfffff007ffff8000000
def f249 : ℕ := 0x3c0780f0703c078381c0e07ff00000ff800007fc0000
def f250 : ℕ := 0x300600c060300602018080000fffffff800000000000
def f251 : ℕ := 0x20040080402004020100800000000000000000000000
def f252 : ℕ := 0x6318c6318000ffc00
def f253 : ℕ := 0x3ff0001f
def f256 : ℕ := 0x6318c6318000f8000
def f258 : ℕ := 0x3e00001f
def f261 : ℕ := 0x84210842000000000
def f264 : ℕ := 0x18c6318c67ffff83e0
def f270 : ℕ := 0x1ad6b5ad6fffffffe0
def f271 : ℕ := 0x1084210847fff003e0
def f273 : ℕ := 0x84210842001f003e0
def f274 : ℕ := 0x1ad6b5ad6fffff83ff
def f279 : ℕ := 0x3e0
def f281 : ℕ := 0x100200004010000201008000ffe00007ff00003ffff
def f282 : ℕ := 0xd01a030140d0181a050687ffffe00007fffffffffff
def f283 : ℕ := 0x100200004010000201008000ffe000000000003ffff
def f284 : ℕ := 0x310620c0643106022190887ffffffffffff00003ffff
def f285 : ℕ := 0x10020000401000020100800000000007ff00003ffff
def f286 : ℕ := 0xc018060300c030100c040000000000000000000000
def f287 : ℕ := 0xaf15e2f1b8af1795c6e57000001ffff800ff803fe00
def f288 : ℕ := 0x220440908022048482012000001ff00000ff8000000
def f289 : ℕ := 0x81102201088110104424100000000ff80000003fe00
def f290 : ℕ := 0xff8000000
def f291 : ℕ := 0xe739ce73fc1ffffe0
def f292 : ℕ := 0x6318c631801fffc00
def f293 : ℕ := 0x7c00f8000
def f294 : ℕ := 0x1ef7bdef7fffffffe0
def f295 : ℕ := 0xe739ce73801f07fe0
def f296 : ℕ := 0xc6318c637c1fffc00
def f297 : ℕ := 0x10842108400000001f
def f298 : ℕ := 0xee1dc3f1b0ee1f9d86c767ff001ff007ffffffc0000
def f299 : ℕ := 0x2e05c0f0b02e078582c16000001ff00000000000000
def f300 : ℕ := 0xc018030100c01818040607ff00000007ff007fc0000
def f301 : ℕ := 0xa014050200a0281808060000000000000000000000
def f302 : ℕ := 0x22f45e8f4ba2f47a5d2e97000001ff00000ffffc01ff
def f303 : ℕ := 0x240480a09024050402410000001ff00000ff8000000
def f304 : ℕ := 0x2014028040a014020502810000000000000007fc01ff
def f305 : ℕ := 0x1ff00000000000000
def f306 : ℕ := 0x32e65ccf6b32e67a59ac967fffffffff800ff8000000
def f307 : ℕ := 0x2e05c0f0b02e078582c160000000000000ff8000000
def f308 : ℕ := 0x300600c0603006020180807ffffe00ff800000000000
def f309 : ℕ := 0x22222f0ff0
def f310 : ℕ := 0x44444000ff
def f311 : ℕ := 0x222f00
def f312 : ℕ := 0x66666ffff0
def f313 : ℕ := 0x33330f00
def f317 : ℕ := 0x42108421000000000
def f318 : ℕ := 0xe739ce73fc1fffc00
def f319 : ℕ := 0xe739ce738000fffff
def f320 : ℕ := 0x421084210000ffc00
def f321 : ℕ := 0x42108421000007c00
def f322 : ℕ := 0x842108427fff0001f
def f323 : ℕ := 0xe739ce73ffff07fff
def f324 : ℕ := 0x421084217fff07c00
def f328 : ℕ := 0x6318c631800007c00
def f330 : ℕ := 0x421084210000f8000
def f336 : ℕ := 0xa5294a52fc00fffe0
def f337 : ℕ := 0x444f00
def f338 : ℕ := 0x666f0f
def f339 : ℕ := 0x777fff
def f340 : ℕ := 0x3330ff
def f341 : ℕ := 0x11100f
def f342 : ℕ := 0x222ff0
def f343 : ℕ := 0x555f0f
def f346 : ℕ := 0x555ff0
def f355 : ℕ := 0x8f11e271388f1391c4e47000001ffff800ff803fe00
def f356 : ℕ := 0x20040100002008080002000001ff00000ff8000000
def f357 : ℕ := 0xce19c37130ce1b9984c667ff001ff007ffffffc0000
def f358 : ℕ := 0xe01c070300e038180c06000001ff00000000000000
def f359 : ℕ := 0x20f41e8743a0f43a1d0e87000001ff00000ffffc01ff
def f360 : ℕ := 0x40080201004010000400000001ff00000ff8000000
def f361 : ℕ := 0x30e61cc76330e63a198c867fffffffff800ff8000000
def f362 : ℕ := 0xe01c070300e038180c060000000000000ff8000000
def f363 : ℕ := 0x16b5ad6b5ffe0fffe0
def f365 : ℕ := 0x9d13a261789d131345e4d000ffe00fffff00003ffff
def f366 : ℕ := 0x100200004010000201008000ffe00007ff0000001ff
def f367 : ℕ := 0x21b4368546a1b42a3d1a8f000ffe00007ff007ffffff
def f368 : ℕ := 0x100200004010000201008000ffe00007ff00003fe00
def f370 : ℕ := 0x84210842000007c00
def f371 : ℕ := 0xe739ce73fc1ffffff
def f372 : ℕ := 0x6318c6318000f83ff
def f373 : ℕ := 0xa5294a5280000001f
def f375 : ℕ := 0x1084210840000f83e0
def f376 : ℕ := 0xf83e0
def f377 : ℕ := 0xe739ce73800007c1f
def f382 : ℕ := 0xa5294a528000fffe0
def f385 : ℕ := 0x7c1f00000
def f394 : ℕ := 0x200400808020040402010000000000000000003fe00
def f395 : ℕ := 0x8f11e271388f1391c4e47000001ffff800ff8000000
def f396 : ℕ := 0x55555fff0f
def f421 : ℕ := 0x3ffff
def f422 : ℕ := 0x28f51ea753a8f53b1d4ec700000000ff800007fc0000
def f423 : ℕ := 0x4008010000400808000207ff00000007ffff8000000
def f424 : ℕ := 0x38f71ee773b8f73b1dcec77fffffffff800007ffffff
def f425 : ℕ := 0x8f11e271388f1391c4e470000000000000007ffffff
def f426 : ℕ := 0x2bf57eaf5fabf57b7d7edf000ffe00fffff007ffffff
def f427 : ℕ := 0x30060080c030040603018000ffe00007ff000000000
def f428 : ℕ := 0x8010020100801010040400000000000000ff8000000
def f429 : ℕ := 0xef1de3f1b8ef1f9dc6e777ff001fffffffffffffe00
def f430 : ℕ := 0x2f05e0f0b82f0785c2e17000001ffff80000003fe00
def f431 : ℕ := 0x4008010000400808000207ff00000007ff007fc0000
def f432 : ℕ := 0x8f11e271388f1391c4e4700000000ff80000003fe00
def f433 : ℕ := 0x2af55eaf5baaf57b5d6ed7000001ffff800fffffffff
def f434 : ℕ := 0x200400808020040402010000001ff00000ff8000000
def f435 : ℕ := 0x20040080402004020100800000000000000007fc01ff
def f436 : ℕ := 0x1ffff800000000000
def f437 : ℕ := 0x3af75eef7bbaf77b5deed77fffffffff800ff803fe00
def f438 : ℕ := 0xaf15e2f1b8af1795c6e570000000000000ff803fe00
def f439 : ℕ := 0x300600c0603006020180807ffffe0000000000000000
def f440 : ℕ := 0x8010020100801010040400000000000000007fc0000
def f441 : ℕ := 0x20f41e8743a0f43a1d0e8700000000ff80000003ffff
def f442 : ℕ := 0x200400804020040201008000000000ff800000000000
def f443 : ℕ := 0x10020040201002000080007fffffff00000000000000
def f444 : ℕ := 0x1ad6b5ad6fc00f83e0
def f445 : ℕ := 0x1294a529483e0f83ff
def f446 : ℕ := 0xa5294a528000f83ff
def f447 : ℕ := 0xb016050280b0281c0a070000000000000000000000
def f448 : ℕ := 0xa41482a190a4151406450000001ffff800ff803fe00
def f449 : ℕ := 0x4440f0
def f453 : ℕ := 0x32064090c03204868301a000fffff007ffff803ffff
def f454 : ℕ := 0xe21c439180e21c9c860727ff001ff007ffffffc0000
def f455 : ℕ := 0x220440908022048482012000001ff00000000000000
def f456 : ℕ := 0x200401000020080800020000000000000000000000
def f457 : ℕ := 0x22b4568d4aa2b46a5d2a97000001ff00000ffffc01ff
def f458 : ℕ := 0x2094128442a09422150a850000000000000007fc01ff
def f459 : ℕ := 0x322644c96832264a49a0927fffffffff800ff8000000
def f460 : ℕ := 0x2204409080220484820120000000000000ff8000000
def f462 : ℕ := 0x6ff
def f469 : ℕ := 0x20040080802004040201000000000007ff000000000
def f470 : ℕ := 0xce19c37130ce1b9984c667ff001ff00000ffffc0000
def f471 : ℕ := 0x200400808020040402010000ffe0000000000000000
def f472 : ℕ := 0x30e61cc76330e63a198c867ff001ffff800ff8000000
def f473 : ℕ := 0x8c118261308c131104c440000000000000000000000
def f474 : ℕ := 0x1002000080100004020100000000ff80000003fe00
def f475 : ℕ := 0x620c419080620c8c820327ff001ff007ffffffc0000
def f476 : ℕ := 0xc018060300c030100c0400000000ff800000000000
def f477 : ℕ := 0x811022010881101044241000000000000000003fe00
def f478 : ℕ := 0x322644c96832264a49a0927fffffff00000ff8000000
def f479 : ℕ := 0xa014050200a0281808060000000000000007fc0000
def f480 : ℕ := 0x2ef5debf5baef5fbdd6ef77ff001ff007ffffffc01ff
def f481 : ℕ := 0xe41c83a190e41d1c064707ff001ff007ffff8000000
def f482 : ℕ := 0x2014028040a0140205028100000000000000000001ff
def f483 : ℕ := 0x2e05c0f0b02e078582c167ff001ff00000ff8000000
def f484 : ℕ := 0x3ee7dcff7b3ee7fbd9ecf67ffffffffffffffffc0000
def f485 : ℕ := 0xc018030100c018180406000000000007ff007fc0000
def f486 : ℕ := 0x300600c060300602018080000ffe00ff800000000000
def f487 : ℕ := 0x20a414854220a42a1908860000000000000000000000
def f488 : ℕ := 0x32f65ecf6bb2f67a5dae977fffffffff800ffffc01ff
def f489 : ℕ := 0x100200008010000402010000000000000007fc01ff
def f490 : ℕ := 0x1242484a2912425040a4107fffffffff800ff8000000
def f492 : ℕ := 0x7ff001ff00000000000000
def f493 : ℕ := 0xee1dc3f1b0ee1f9d86c7600000000007ffffffc0000
def f494 : ℕ := 0xa5294a52fc00f83e0
def f495 : ℕ := 0x14a5294a57fffffc1f
def f496 : ℕ := 0x42108421001f07c1f
def f497 : ℕ := 0x16b5ad6b583ff07fff
def f498 : ℕ := 0x4210842103ff07c00
def f499 : ℕ := 0x1294a529480000001f
def f500 : ℕ := 0xa5294a52801f07fe0
def f501 : ℕ := 0x1ad6b5ad6fc1ffffff
def f502 : ℕ := 0x842108427c1fffc00
def f508 : ℕ := 0xf01e0381c0f01c1e070787ffffe00007ff007ffffff
def f509 : ℕ := 0xcd19a36138cd1b1944e657ff00000fffff007fffe00
def f510 : ℕ := 0x2cb596b552acb5ab9d4ae77ff00000007ff007fc01ff
def f511 : ℕ := 0xc018030100c01818040607ff00000007ff000000000
def f512 : ℕ := 0x3c0780f0703c078381c0e07ffffffffffff007fc0000
def f524 : ℕ := 0x1084210847ffff8000
def f534 : ℕ := 0xa5294a52800000000
def f535 : ℕ := 0x16b5ad6b5fffffffff
def f545 : ℕ := 0x1111100fff
def f546 : ℕ := 0x2e05c0f0b02e078582c16000001ff007ffff8000000
def f547 : ℕ := 0x8d11a261388d131144e4500000000fffff00003fe00
def f548 : ℕ := 0x20b4168542a0b42a1d0a8700000000007ff007fc01ff
def f549 : ℕ := 0x22f45e8f4ba2f47a5d2e97000001ff007ffffffc01ff
def f550 : ℕ := 0x2014028040a0140205028100000000007ff007fc01ff
def f551 : ℕ := 0x30060080c030040603018000ffe000000000003fe00
def f552 : ℕ := 0x28f51ea753a8f53b1d4ec700000000fffff007ffffff
def f553 : ℕ := 0x202404814020240a09008200000000007ff007fc01ff
def f554 : ℕ := 0xc018030100c01818040607ff0000000000ff8000000
def f555 : ℕ := 0x30b616c562b0b62a1d8a877ffffffffffff007fc01ff
def f556 : ℕ := 0xb016050280b0281c0a0700000000007ff007fc01ff
def f558 : ℕ := 0x1084210847ffff83e0
def f559 : ℕ := 0x16b5ad6b5fffffffe0
def f560 : ℕ := 0x300600c0603006020180807ffffffffffff000000000
def f561 : ℕ := 0x2004008080200404020100000000000000ff8000000
def f562 : ℕ := 0xd01a030140d0181a050687ffffe00007ff007ffffff
def f564 : ℕ := 0x1084210847fff003ff
def f565 : ℕ := 0x3ff
def f566 : ℕ := 0x1ef7bdef7fffff83ff
def f567 : ℕ := 0x14a5294a57ffff8000
def f568 : ℕ := 0x421084217fff0001f
def f569 : ℕ := 0x14a5294a503e0f83ff
def f570 : ℕ := 0x1111100f0f
def f571 : ℕ := 0x801002010080101004040000000000000000003fe00
def f572 : ℕ := 0xfd1fa3e1f8fd1f1f47e7d7ffffe00ffffffffffffff
def f573 : ℕ := 0xd01a060380d030140e0500000000ff800000000000
def f574 : ℕ := 0x700e0180c0700c0e030387ffffe00007ffffffc01ff
def f575 : ℕ := 0x7fc01ff
def f576 : ℕ := 0x2fb5f6bd5eafb5ebfd7aff7ffffe00007fffffffffff
def f580 : ℕ := 0xf01e0381c0f01c1e070787ffffe00007ffff803fe00
def f581 : ℕ := 0x33333fff00
def f582 : ℕ := 0x20b4168542a0b42a1d0a870000000000000000000000
def f583 : ℕ := 0x7ffffe0000000000000000
def f584 : ℕ := 0xf01e0381c0f01c1e0707800000000007fffffffffff
def f585 : ℕ := 0x33300f
def f586 : ℕ := 0x300600c060300602018080000001ffff800000000000
def f606 : ℕ := 0x111110f0ff
def f607 : ℕ := 0x3e07c0f0f03e078783c1e000fffff00000ff803ffff
def f608 : ℕ := 0xbd17a2e1f8bd171747e5d000ffe00ff80000003ffff
def f609 : ℕ := 0x30060080c030040603018000ffe00000000000001ff
def f610 : ℕ := 0x23b4768d4ea3b46a7d3a9f000ffe0000000007ffffff
def f611 : ℕ := 0x330660c86c33064261b0987fffffffff80000003ffff
def e0 : List ℕ := [f0,f1,f2,f3]
def e16 : List ℕ := [f1,f2,f3]
def e17 : List ℕ := [f18,f19,f20,f21,f22,f23,f24]
def e21 : List ℕ := [f35,f36,f37,f38,f39]
def e22 : List ℕ := [f40,f35,f37,f38,f39]
def e56 : List ℕ := [f40,f36,f37,f38,f39]
def e87 : List ℕ := [f40,f35,f37,f38,f63]
def e101 : List ℕ := [f71,f35,f36,f38,f39]
def e102 : List ℕ := [f78,f79]
def e103 : List ℕ := [f30,f31,f32]
def e104 : List ℕ := [f30,f80,f31,f32]
def e112 : List ℕ := [f35,f36,f62,f86,f87]
def e113 : List ℕ := [f40,f35,f62,f86,f87]
def e117 : List ℕ := [f42,f36,f62,f86,f87]
def e129 : List ℕ := [f40,f62,f86,f94,f87]
def e130 : List ℕ := [f40,f53,f62,f86,f87]
def e146 : List ℕ := [f40,f36,f62,f86,f87]
def e150 : List ℕ := [f42,f35,f62,f86,f87]
def e156 : List ℕ := [f102,f35,f62,f86,f87]
def e158 : List ℕ := [f35,f62,f86,f93,f87]
def e160 : List ℕ := [f40,f62,f86,f103,f87]
def e170 : List ℕ := [f40,f35,f62,f98,f87]
def e188 : List ℕ := [f26,f67,f27,f28]
def e190 : List ℕ := [f52,f36,f86,f103,f87]
def e191 : List ℕ := [f62,f86,f103,f94,f87]
def e192 : List ℕ := [f53,f86,f103,f87]
def e193 : List ℕ := [f53,f62,f86,f103,f87]
def e194 : List ℕ := [f53,f36,f86,f103,f87]
def e195 : List ℕ := [f62,f86,f103,f95,f87]
def e196 : List ℕ := [f58,f62,f86,f103,f87]
def e197 : List ℕ := [f107,f36,f62,f86,f87]
def e198 : List ℕ := [f42,f62,f86,f103,f87]
def e199 : List ℕ := [f96,f62,f86,f103,f87]
def e200 : List ℕ := [f96,f36,f62,f86,f103]
def e201 : List ℕ := [f56,f36,f62,f86,f103]
def e202 : List ℕ := [f62,f86,f103,f97,f87]
def e203 : List ℕ := [f36,f98,f103,f87]
def e204 : List ℕ := [f36,f86,f98,f103,f87]
def e205 : List ℕ := [f36,f62,f98,f103,f87]
def e206 : List ℕ := [f99,f36,f86,f103,f87]
def e207 : List ℕ := [f65,f36,f62,f103,f87]
def e208 : List ℕ := [f72,f36,f86,f103,f87]
def e209 : List ℕ := [f72,f36,f62,f86,f87]
def e210 : List ℕ := [f36,f86,f103,f59]
def e211 : List ℕ := [f36,f86,f103,f87,f59]
def e212 : List ℕ := [f36,f62,f86,f103,f59]
def e213 : List ℕ := [f36,f108,f86,f103,f87]
def e214 : List ℕ := [f36,f62,f86,f103,f100]
def e215 : List ℕ := [f36,f109,f62,f86,f87]
def e216 : List ℕ := [f110,f36,f62,f86,f87]
def e217 : List ℕ := [f36,f62,f86,f103,f101]
def e218 : List ℕ := [f36,f62,f86,f103,f38]
def e219 : List ℕ := [f111,f36,f62,f86,f103]
def e220 : List ℕ := [f36,f62,f86,f87,f112]
def e221 : List ℕ := [f36,f62,f86,f113]
def e222 : List ℕ := [f36,f62,f86,f113,f87]
def e223 : List ℕ := [f36,f62,f86,f113,f103]
def e224 : List ℕ := [f36,f62,f86,f103,f87]
def e225 : List ℕ := [f105,f36,f62,f86,f103]
def e226 : List ℕ := [f75,f36,f62,f86,f103]
def e227 : List ℕ := [f35,f53,f86,f103,f87]
def e228 : List ℕ := [f35,f62,f86,f94,f87]
def e229 : List ℕ := [f35,f36,f98,f103,f87]
def e230 : List ℕ := [f35,f36,f86,f103,f59]
def e231 : List ℕ := [f111,f35,f36,f62,f86]
def e232 : List ℕ := [f35,f36,f62,f86,f113]
def e233 : List ℕ := [f35,f36,f62,f86,f103,f87]
def e235 : List ℕ := [f116,f36,f62,f86,f87]
def e236 : List ℕ := [f116,f72,f62,f86,f87]
def e237 : List ℕ := [f117,f36,f62,f86,f87]
def e238 : List ℕ := [f36,f62,f118,f86,f87]
def e239 : List ℕ := [f105,f72,f36,f62,f86]
def e240 : List ℕ := [f36,f62,f86,f87,f119]
def e241 : List ℕ := [f120,f36,f62,f86]
def e242 : List ℕ := [f120,f36,f62,f86,f87]
def e243 : List ℕ := [f120,f72,f36,f62,f86]
def e244 : List ℕ := [f72,f86,f94,f87]
def e245 : List ℕ := [f72,f62,f86,f94,f87]
def e246 : List ℕ := [f72,f36,f86,f94,f87]
def e247 : List ℕ := [f72,f53,f62,f86,f87]
def e248 : List ℕ := [f72,f36,f121,f86,f87]
def e249 : List ℕ := [f72,f62,f86,f95,f87]
def e250 : List ℕ := [f72,f58,f62,f86,f87]
def e251 : List ℕ := [f96,f72,f62,f86,f87]
def e252 : List ℕ := [f96,f72,f36,f62,f86]
def e253 : List ℕ := [f72,f56,f36,f62,f86]
def e254 : List ℕ := [f72,f62,f86,f97,f87]
def e255 : List ℕ := [f72,f36,f86,f98,f87]
def e256 : List ℕ := [f72,f36,f62,f98,f87]
def e257 : List ℕ := [f99,f72,f36,f86,f87]
def e258 : List ℕ := [f65,f72,f36,f62,f87]
def e259 : List ℕ := [f122,f72,f36,f86,f87]
def e260 : List ℕ := [f72,f36,f62,f86,f59]
def e261 : List ℕ := [f72,f36,f86,f100,f87]
def e262 : List ℕ := [f72,f36,f62,f86,f100]
def e263 : List ℕ := [f72,f36,f62,f86,f101]
def e264 : List ℕ := [f72,f36,f62,f86,f38]
def e265 : List ℕ := [f30,f84,f85]
def e266 : List ℕ := [f30,f84,f85,f123]
def e279 : List ℕ := [f129,f130,f21,f22,f23,f24]
def e280 : List ℕ := [f129,f20,f21,f22,f23,f24]
def e281 : List ℕ := [f129,f20,f130,f21,f22,f23,f24]
def e282 : List ℕ := [f131,f20,f130,f21,f22,f23,f24]
def e283 : List ℕ := [f36,f37,f83,f38,f39]
def e284 : List ℕ := [f72,f36,f38,f39]
def e285 : List ℕ := [f72,f36,f37,f38,f39]
def e286 : List ℕ := [f72,f35,f36,f38,f39]
def e287 : List ℕ := [f36,f37,f38,f39,f74]
def e288 : List ℕ := [f75,f36,f37,f38,f39]
def e289 : List ℕ := [f117,f36,f37,f38,f39]
def e290 : List ℕ := [f36,f37,f38,f132,f39]
def e291 : List ℕ := [f52,f35,f37,f38,f39]
def e292 : List ℕ := [f52,f35,f36,f38,f39]
def e293 : List ℕ := [f35,f53,f36,f38,f39]
def e294 : List ℕ := [f35,f54,f37,f38,f39]
def e295 : List ℕ := [f35,f37,f38,f39,f55]
def e296 : List ℕ := [f35,f56,f37,f38,f39]
def e297 : List ℕ := [f35,f37,f38,f39,f57]
def e298 : List ℕ := [f35,f58,f37,f38,f39]
def e299 : List ℕ := [f35,f36,f38,f39,f59]
def e300 : List ℕ := [f35,f36,f60,f38,f39]
def e301 : List ℕ := [f35,f36,f38,f39,f61]
def e302 : List ℕ := [f35,f36,f62,f38,f39]
def e303 : List ℕ := [f35,f36,f37,f39,f63]
def e304 : List ℕ := [f35,f36,f37,f38,f63]
def e305 : List ℕ := [f64,f35,f36,f37,f39]
def e306 : List ℕ := [f65,f35,f36,f37,f38]
def e307 : List ℕ := [f20,f130,f21,f133,f22,f23,f24]
def e308 : List ℕ := [f134,f20,f130,f21,f22,f23,f24]
def e309 : List ℕ := [f20,f130,f135,f21,f22,f23,f24]
def e310 : List ℕ := [f136,f20,f130,f21,f22,f23,f24]
def e311 : List ℕ := [f130,f21,f22,f137,f23,f24]
def e314 : List ℕ := [f5,f6,f140,f7]
def e315 : List ℕ := [f8,f5,f6,f140,f7]
def e317 : List ℕ := [f5,f6,f141,f7]
def e318 : List ℕ := [f8,f5,f6,f141,f7]
def e323 : List ℕ := [f105,f35,f36,f62,f86]
def e324 : List ℕ := [f36,f62,f86,f87,f147]
def e325 : List ℕ := [f75,f36,f62,f86]
def e326 : List ℕ := [f75,f36,f62,f86,f87]
def e327 : List ℕ := [f75,f35,f36,f62,f86]
def e328 : List ℕ := [f35,f53,f62,f86,f87]
def e329 : List ℕ := [f35,f62,f86,f95,f87]
def e330 : List ℕ := [f35,f58,f62,f86,f87]
def e331 : List ℕ := [f96,f35,f62,f86,f87]
def e332 : List ℕ := [f96,f35,f36,f62,f86]
def e333 : List ℕ := [f35,f56,f36,f62,f86]
def e334 : List ℕ := [f35,f62,f86,f97,f87]
def e335 : List ℕ := [f35,f36,f86,f98,f87]
def e336 : List ℕ := [f35,f36,f62,f98,f87]
def e337 : List ℕ := [f99,f35,f36,f86,f87]
def e338 : List ℕ := [f65,f35,f36,f62,f87]
def e339 : List ℕ := [f35,f36,f62,f86,f59]
def e340 : List ℕ := [f35,f36,f62,f86,f100]
def e341 : List ℕ := [f35,f36,f62,f86,f101]
def e342 : List ℕ := [f35,f36,f62,f86,f38]
def e343 : List ℕ := [f20,f130,f21,f22,f137,f23,f24]
def e344 : List ℕ := [f148,f130,f21,f22,f23,f24]
def e345 : List ℕ := [f148,f20,f130,f21,f22,f23,f24]
def e346 : List ℕ := [f20,f130,f21,f149,f22,f23,f24]
def e347 : List ℕ := [f150,f20,f130,f21,f22,f23,f24]
def e348 : List ℕ := [f20,f130,f21,f22,f23,f151,f24]
def e349 : List ℕ := [f152,f20,f130,f21,f22,f23,f24]
def e350 : List ℕ := [f20,f130,f21,f22,f153,f23,f24]
def e351 : List ℕ := [f154,f20,f130,f21,f22,f23,f24]
def e352 : List ℕ := [f130,f21,f22,f23,f24,f155]
def e353 : List ℕ := [f20,f130,f21,f22,f23,f24,f155]
def e354 : List ℕ := [f156,f130,f21,f22,f23,f24]
def e355 : List ℕ := [f156,f20,f130,f21,f22,f23,f24]
def e356 : List ℕ := [f20,f130,f21,f22,f23,f157,f24]
def e357 : List ℕ := [f158,f20,f130,f21,f22,f23,f24]
def e358 : List ℕ := [f20,f21,f159,f22,f23,f24]
def e359 : List ℕ := [f20,f130,f21,f159,f22,f23,f24]
def e360 : List ℕ := [f20,f160,f21,f22,f23,f24]
def e361 : List ℕ := [f20,f160,f130,f21,f22,f23,f24]
def e362 : List ℕ := [f20,f130,f161,f21,f22,f23,f24]
def e363 : List ℕ := [f162,f20,f130,f21,f22,f23,f24]
def e364 : List ℕ := [f71,f35,f86,f94,f87]
def e365 : List ℕ := [f72,f35,f86,f94,f87]
def e366 : List ℕ := [f117,f62,f86,f94,f87]
def e367 : List ℕ := [f62,f118,f86,f94,f87]
def e368 : List ℕ := [f62,f86,f163,f94,f87]
def e369 : List ℕ := [f35,f62,f86,f163,f87]
def e370 : List ℕ := [f105,f35,f62,f86,f94]
def e371 : List ℕ := [f62,f86,f94,f87,f147]
def e372 : List ℕ := [f75,f62,f86,f94]
def e373 : List ℕ := [f75,f62,f86,f94,f87]
def e374 : List ℕ := [f75,f35,f62,f86,f94]
def e375 : List ℕ := [f35,f86,f98,f94,f87]
def e376 : List ℕ := [f99,f35,f86,f94,f87]
def e377 : List ℕ := [f35,f53,f86,f94,f87]
def e378 : List ℕ := [f35,f86,f94,f59]
def e379 : List ℕ := [f35,f86,f94,f87,f59]
def e380 : List ℕ := [f35,f62,f86,f94,f59]
def e381 : List ℕ := [f35,f108,f86,f94,f87]
def e382 : List ℕ := [f35,f62,f86,f94,f100]
def e383 : List ℕ := [f35,f62,f86,f164,f87]
def e384 : List ℕ := [f35,f165,f62,f86,f87]
def e385 : List ℕ := [f35,f62,f86,f94,f101]
def e386 : List ℕ := [f35,f62,f86,f94,f38]
def e387 : List ℕ := [f64,f35,f62,f86,f87]
def e388 : List ℕ := [f64,f35,f62,f86,f94]
def e389 : List ℕ := [f35,f62,f86,f166,f94]
def e390 : List ℕ := [f35,f62,f86,f167,f87]
def e391 : List ℕ := [f36,f62,f86,f163,f87]
def e392 : List ℕ := [f75,f36,f62,f86,f94]
def e393 : List ℕ := [f52,f35,f86,f94,f87]
def e394 : List ℕ := [f96,f35,f62,f86,f94]
def e395 : List ℕ := [f35,f56,f62,f86,f94]
def e396 : List ℕ := [f35,f36,f86,f94,f59]
def e397 : List ℕ := [f64,f35,f36,f62,f86]
def e398 : List ℕ := [f35,f36,f62,f86,f166]
def e399 : List ℕ := [f35,f36,f62,f86,f94,f87]
def e400 : List ℕ := [f20,f130,f21,f22,f168,f23,f24]
def e401 : List ℕ := [f169,f115,f34]
def e419 : List ℕ := [f35,f179,f62,f86,f87]
def e420 : List ℕ := [f42,f53,f62,f86,f87]
def e421 : List ℕ := [f35,f53,f124,f86,f87]
def e422 : List ℕ := [f117,f53,f62,f86,f87]
def e423 : List ℕ := [f53,f62,f118,f86,f87]
def e424 : List ℕ := [f105,f35,f53,f62,f86]
def e425 : List ℕ := [f53,f62,f86,f87,f147]
def e426 : List ℕ := [f75,f53,f62,f86]
def e427 : List ℕ := [f75,f53,f62,f86,f87]
def e428 : List ℕ := [f75,f35,f53,f62,f86]
def e429 : List ℕ := [f35,f62,f86,f180,f87]
def e430 : List ℕ := [f181,f35,f62,f86,f87]
def e431 : List ℕ := [f96,f35,f53,f62,f86]
def e432 : List ℕ := [f35,f182,f53,f62,f86]
def e433 : List ℕ := [f35,f53,f86,f98,f87]
def e434 : List ℕ := [f99,f35,f53,f86,f87]
def e435 : List ℕ := [f35,f53,f62,f86,f59]
def e436 : List ℕ := [f35,f53,f62,f86,f100]
def e437 : List ℕ := [f35,f53,f62,f86,f101]
def e438 : List ℕ := [f35,f53,f62,f86,f38]
def e439 : List ℕ := [f75,f53,f36,f62,f86]
def e440 : List ℕ := [f35,f182,f36,f62,f86]
def e441 : List ℕ := [f35,f56,f53,f62,f86]
def e442 : List ℕ := [f35,f53,f36,f98,f87]
def e443 : List ℕ := [f35,f53,f36,f62,f86,f87]
def e444 : List ℕ := [f20,f183,f130,f21,f22,f23,f24]
def e445 : List ℕ := [f20,f130,f21,f184,f22,f23,f24]
def e446 : List ℕ := [f185,f20,f130,f21,f22,f23,f24]
def e447 : List ℕ := [f20,f21,f22,f23,f186,f24]
def e448 : List ℕ := [f20,f130,f21,f22,f23,f186,f24]
def e449 : List ℕ := [f20,f187,f21,f22,f23,f24]
def e450 : List ℕ := [f20,f187,f130,f21,f22,f23,f24]
def e451 : List ℕ := [f20,f130,f21,f22,f188,f23,f24]
def e452 : List ℕ := [f189,f20,f130,f21,f22,f23,f24]
def e453 : List ℕ := [f20,f130,f21,f22,f23,f24,f190]
def e454 : List ℕ := [f20,f191,f130,f21,f22,f23,f24]
def e455 : List ℕ := [f20,f130,f21,f22,f23,f192,f24]
def e456 : List ℕ := [f20,f130,f193,f21,f22,f23,f24]
def e467 : List ℕ := [f129,f130,f22,f201,f23,f24]
def e468 : List ℕ := [f129,f20,f22,f201,f23,f24]
def e469 : List ℕ := [f130,f201,f137,f23,f24]
def e470 : List ℕ := [f130,f22,f201,f137,f23,f24]
def e471 : List ℕ := [f20,f130,f201,f137,f23,f24]
def e472 : List ℕ := [f148,f130,f22,f201,f23,f24]
def e473 : List ℕ := [f20,f130,f149,f201,f23,f24]
def e474 : List ℕ := [f130,f22,f201,f23,f24,f155]
def e475 : List ℕ := [f156,f130,f22,f201,f23,f24]
def e476 : List ℕ := [f20,f22,f201,f23,f186,f24]
def e477 : List ℕ := [f20,f187,f22,f201,f23,f24]
def e478 : List ℕ := [f202,f20,f130,f201,f23,f24]
def e479 : List ℕ := [f202,f20,f130,f22,f23,f24]
def e480 : List ℕ := [f20,f130,f201,f23,f24,f203]
def e481 : List ℕ := [f20,f130,f204,f201,f23,f24]
def e482 : List ℕ := [f20,f130,f22,f23,f205,f24]
def e483 : List ℕ := [f20,f130,f22,f206,f23,f24]
def e484 : List ℕ := [f20,f130,f22,f201,f24,f207]
def e485 : List ℕ := [f20,f130,f22,f201,f23,f207]
def e486 : List ℕ := [f208,f20,f130,f22,f201,f24]
def e487 : List ℕ := [f20,f130,f22,f201,f209,f23]
def e488 : List ℕ := [f20,f130,f22,f201,f23,f24]
def e490 : List ℕ := [f20,f130,f21,f201,f23,f24]
def e491 : List ℕ := [f20,f130,f21,f22,f201,f23,f24]
def e502 : List ℕ := [f202,f20,f130,f21,f22,f23,f24]
def e510 : List ℕ := [f20,f130,f214,f21,f23,f24]
def e511 : List ℕ := [f20,f130,f214,f21,f22,f23,f24]
def e512 : List ℕ := [f215,f20,f130,f21,f22,f23,f24]
def e517 : List ℕ := [f20,f130,f22,f23,f217,f24]
def e518 : List ℕ := [f20,f130,f21,f22,f217,f24]
def e519 : List ℕ := [f20,f130,f21,f22,f23,f217,f24]
def e522 : List ℕ := [f20,f130,f218,f22,f23,f24]
def e523 : List ℕ := [f20,f130,f218,f21,f22,f23,f24]
def e524 : List ℕ := [f20,f130,f21,f22,f219,f24]
def e525 : List ℕ := [f20,f130,f21,f22,f219,f23,f24]
def e526 : List ℕ := [f220,f20,f130,f21,f22,f23,f24]
def e527 : List ℕ := [f9,f26,f27,f221]
def e528 : List ℕ := [f67,f222,f27,f221]
def e529 : List ℕ := [f25,f27,f221]
def e530 : List ℕ := [f25,f67,f27,f221]
def e531 : List ℕ := [f25,f26,f27,f221]
def e532 : List ℕ := [f67,f27,f31,f221]
def e533 : List ℕ := [f26,f67,f27,f31]
def e534 : List ℕ := [f26,f68,f27,f221]
def e535 : List ℕ := [f26,f68,f67,f221]
def e536 : List ℕ := [f223,f26,f27,f221]
def e537 : List ℕ := [f223,f26,f67,f27]
def e538 : List ℕ := [f26,f224,f67,f27]
def e539 : List ℕ := [f26,f27,f225,f221]
def e540 : List ℕ := [f26,f226,f67]
def e541 : List ℕ := [f26,f226,f67,f221]
def e542 : List ℕ := [f26,f226,f67,f27]
def e543 : List ℕ := [f26,f67,f227,f221]
def e544 : List ℕ := [f26,f67,f27,f221]
def e545 : List ℕ := [f20,f130,f21,f22,f23,f228]
def e546 : List ℕ := [f20,f130,f21,f22,f23,f24,f228]
def e547 : List ℕ := [f20,f130,f229,f21,f22,f23,f24]
def e562 : List ℕ := [f20,f130,f21,f22,f23,f230]
def e563 : List ℕ := [f20,f130,f21,f22,f23,f230,f24]
def e564 : List ℕ := [f231,f20,f130,f21,f22,f23,f24]
def e565 : List ℕ := [f20,f130,f21,f23,f232,f24]
def e566 : List ℕ := [f20,f130,f21,f22,f23,f232,f24]
def e567 : List ℕ := [f20,f130,f21,f233,f23,f24]
def e568 : List ℕ := [f20,f130,f21,f233,f22,f23,f24]
def e569 : List ℕ := [f20,f130,f21,f22,f234,f23,f24]
def e570 : List ℕ := [f235,f20,f130,f21,f22,f23,f24]
def e618 : List ℕ := [f130,f21,f137,f23,f24,f203]
def e619 : List ℕ := [f130,f21,f22,f23,f155,f203]
def e620 : List ℕ := [f130,f21,f22,f23,f24,f246]
def e621 : List ℕ := [f247,f130,f21,f22,f23,f24]
def e622 : List ℕ := [f248,f20,f21,f22,f23,f24]
def e623 : List ℕ := [f20,f21,f22,f23,f24,f249]
def e624 : List ℕ := [f20,f130,f21,f22,f207,f203]
def e625 : List ℕ := [f20,f130,f21,f22,f23,f24,f203]
def e626 : List ℕ := [f20,f130,f21,f204,f22,f23,f24]
def e627 : List ℕ := [f20,f130,f21,f22,f23,f250,f24]
def e628 : List ℕ := [f20,f130,f21,f22,f251,f23,f24]
def e629 : List ℕ := [f20,f130,f21,f22,f24,f207]
def e630 : List ℕ := [f20,f130,f21,f22,f23,f207]
def e631 : List ℕ := [f20,f130,f21,f22,f23,f24,f207]
def e632 : List ℕ := [f208,f20,f130,f21,f22,f24]
def e633 : List ℕ := [f208,f20,f130,f21,f22,f23,f24]
def e634 : List ℕ := [f20,f130,f21,f22,f209,f23]
def e635 : List ℕ := [f20,f130,f21,f22,f209,f23,f24]
def e636 : List ℕ := [f20,f130,f21,f22,f23,f24]
def e641 : List ℕ := [f256,f36,f38,f39]
def e645 : List ℕ := [f252,f36,f62,f86,f87]
def e646 : List ℕ := [f253,f252,f62,f86,f87]
def e697 : List ℕ := [f19,f130,f21,f22,f23,f24]
def e698 : List ℕ := [f281,f19,f21,f22,f23,f24]
def e699 : List ℕ := [f130,f21,f22,f282,f23,f24]
def e700 : List ℕ := [f283,f130,f21,f22,f23,f24]
def e701 : List ℕ := [f130,f21,f22,f23,f24,f284]
def e702 : List ℕ := [f285,f130,f21,f22,f23,f24]
def e703 : List ℕ := [f281,f21,f159,f22,f23,f24]
def e704 : List ℕ := [f281,f160,f21,f22,f23,f24]
def e705 : List ℕ := [f281,f21,f22,f23,f186,f24]
def e706 : List ℕ := [f281,f187,f21,f22,f23,f24]
def e707 : List ℕ := [f281,f130,f22,f201,f23,f24]
def e708 : List ℕ := [f281,f130,f21,f201,f23,f24]
def e709 : List ℕ := [f202,f281,f130,f22,f23,f24]
def e710 : List ℕ := [f281,f130,f214,f21,f23,f24]
def e711 : List ℕ := [f281,f130,f22,f23,f217,f24]
def e712 : List ℕ := [f281,f130,f21,f22,f217,f24]
def e713 : List ℕ := [f281,f130,f218,f22,f23,f24]
def e714 : List ℕ := [f281,f130,f21,f22,f219,f24]
def e715 : List ℕ := [f281,f130,f21,f22,f23,f228]
def e716 : List ℕ := [f281,f130,f21,f22,f23,f230]
def e717 : List ℕ := [f281,f130,f21,f23,f232,f24]
def e718 : List ℕ := [f281,f130,f21,f233,f23,f24]
def e719 : List ℕ := [f281,f130,f21,f22,f24,f207]
def e720 : List ℕ := [f281,f130,f21,f22,f23,f207]
def e721 : List ℕ := [f208,f281,f130,f21,f22,f24]
def e722 : List ℕ := [f281,f130,f21,f22,f209,f23]
def e723 : List ℕ := [f281,f130,f21,f22,f23,f24]
def e724 : List ℕ := [f281,f19,f130,f21,f22,f23,f24]
def e725 : List ℕ := [f286,f19,f130,f21,f22,f23,f24]
def e726 : List ℕ := [f19,f130,f287,f22,f23,f24]
def e727 : List ℕ := [f19,f130,f21,f287,f22,f23,f24]
def e728 : List ℕ := [f288,f19,f130,f21,f22,f23,f24]
def e729 : List ℕ := [f19,f130,f289,f22,f23,f24]
def e730 : List ℕ := [f19,f130,f289,f21,f22,f23,f24]
def e731 : List ℕ := [f290,f19,f130,f21,f22,f23,f24]
def e732 : List ℕ := [f52,f37,f291,f38,f39]
def e733 : List ℕ := [f52,f36,f291,f38,f39]
def e734 : List ℕ := [f53,f36,f291,f38,f39]
def e735 : List ℕ := [f54,f37,f291,f38,f39]
def e736 : List ℕ := [f292,f37,f38,f39]
def e737 : List ℕ := [f292,f37,f291,f38,f39]
def e738 : List ℕ := [f292,f36,f37,f38,f39]
def e739 : List ℕ := [f258,f36,f37,f38,f39]
def e740 : List ℕ := [f37,f291,f38,f39,f55]
def e741 : List ℕ := [f56,f37,f291,f38,f39]
def e742 : List ℕ := [f37,f291,f38,f39,f57]
def e743 : List ℕ := [f36,f37,f291,f38,f57]
def e744 : List ℕ := [f58,f37,f291,f38,f39]
def e745 : List ℕ := [f36,f37,f291,f167,f38]
def e746 : List ℕ := [f256,f36,f291,f38,f39]
def e747 : List ℕ := [f256,f36,f37,f38,f39]
def e748 : List ℕ := [f36,f291,f38,f39,f59]
def e749 : List ℕ := [f36,f60,f291,f38,f39]
def e750 : List ℕ := [f279,f36,f37,f291,f38]
def e751 : List ℕ := [f36,f291,f38,f39,f61]
def e752 : List ℕ := [f36,f62,f291,f38]
def e753 : List ℕ := [f36,f62,f291,f38,f39]
def e754 : List ℕ := [f36,f62,f37,f291,f38]
def e755 : List ℕ := [f293,f36,f37,f291,f39]
def e756 : List ℕ := [f36,f37,f38,f39,f294]
def e757 : List ℕ := [f36,f37,f295,f39]
def e758 : List ℕ := [f36,f37,f295,f38,f39]
def e759 : List ℕ := [f36,f37,f295,f291,f39]
def e760 : List ℕ := [f110,f36,f37,f38,f39]
def e761 : List ℕ := [f110,f36,f37,f291,f38]
def e762 : List ℕ := [f36,f37,f296,f291,f38]
def e763 : List ℕ := [f36,f37,f297,f38,f39]
def e764 : List ℕ := [f36,f37,f291,f39,f63]
def e765 : List ℕ := [f36,f37,f291,f38,f63]
def e766 : List ℕ := [f64,f36,f37,f291,f39]
def e767 : List ℕ := [f65,f36,f37,f291,f38]
def e768 : List ℕ := [f36,f37,f291,f38,f39]
def e769 : List ℕ := [f130,f21,f22,f298,f23,f24]
def e770 : List ℕ := [f19,f130,f21,f22,f298,f23,f24]
def e771 : List ℕ := [f299,f130,f21,f22,f23,f24]
def e772 : List ℕ := [f299,f19,f130,f21,f22,f23,f24]
def e773 : List ℕ := [f19,f130,f21,f300,f22,f23,f24]
def e774 : List ℕ := [f301,f19,f130,f21,f22,f23,f24]
def e775 : List ℕ := [f19,f130,f21,f22,f302,f24]
def e776 : List ℕ := [f19,f130,f21,f22,f23,f302,f24]
def e777 : List ℕ := [f303,f19,f130,f21,f22,f23,f24]
def e778 : List ℕ := [f19,f130,f21,f22,f304,f24]
def e779 : List ℕ := [f19,f130,f21,f22,f304,f23,f24]
def e780 : List ℕ := [f305,f19,f130,f21,f22,f23,f24]
def e781 : List ℕ := [f130,f21,f22,f23,f24,f306]
def e782 : List ℕ := [f19,f130,f21,f22,f23,f24,f306]
def e783 : List ℕ := [f307,f130,f21,f22,f23,f24]
def e784 : List ℕ := [f307,f19,f130,f21,f22,f23,f24]
def e785 : List ℕ := [f19,f130,f21,f22,f23,f308,f24]
def e786 : List ℕ := [f158,f19,f130,f21,f22,f23,f24]
def e787 : List ℕ := [f19,f21,f159,f22,f23,f24]
def e788 : List ℕ := [f19,f130,f21,f159,f22,f23,f24]
def e789 : List ℕ := [f19,f160,f21,f22,f23,f24]
def e790 : List ℕ := [f19,f160,f130,f21,f22,f23,f24]
def e791 : List ℕ := [f19,f130,f161,f21,f22,f23,f24]
def e792 : List ℕ := [f162,f19,f130,f21,f22,f23,f24]
def e793 : List ℕ := [f8,f309,f310,f17]
def e794 : List ℕ := [f8,f5,f6,f7]
def e795 : List ℕ := [f19,f130,f21,f22,f168,f23,f24]
def e796 : List ℕ := [f19,f183,f130,f21,f22,f23,f24]
def e797 : List ℕ := [f1,f311,f2,f3]
def e798 : List ℕ := [f19,f130,f21,f184,f22,f23,f24]
def e799 : List ℕ := [f185,f19,f130,f21,f22,f23,f24]
def e800 : List ℕ := [f19,f21,f22,f23,f186,f24]
def e801 : List ℕ := [f19,f130,f21,f22,f23,f186,f24]
def e802 : List ℕ := [f19,f187,f21,f22,f23,f24]
def e803 : List ℕ := [f19,f187,f130,f21,f22,f23,f24]
def e804 : List ℕ := [f19,f130,f21,f22,f188,f23,f24]
def e805 : List ℕ := [f189,f19,f130,f21,f22,f23,f24]
def e806 : List ℕ := [f19,f130,f21,f22,f23,f24,f190]
def e807 : List ℕ := [f19,f191,f130,f21,f22,f23,f24]
def e808 : List ℕ := [f19,f130,f21,f22,f23,f192,f24]
def e809 : List ℕ := [f19,f130,f193,f21,f22,f23,f24]
def e810 : List ℕ := [f19,f130,f22,f201,f23,f24]
def e811 : List ℕ := [f19,f130,f21,f201,f23,f24]
def e812 : List ℕ := [f19,f130,f21,f22,f201,f23,f24]
def e813 : List ℕ := [f202,f19,f130,f22,f23,f24]
def e814 : List ℕ := [f202,f19,f130,f21,f22,f23,f24]
def e815 : List ℕ := [f19,f130,f214,f21,f23,f24]
def e816 : List ℕ := [f19,f130,f214,f21,f22,f23,f24]
def e817 : List ℕ := [f215,f19,f130,f21,f22,f23,f24]
def e818 : List ℕ := [f19,f130,f22,f23,f217,f24]
def e819 : List ℕ := [f19,f130,f21,f22,f217,f24]
def e820 : List ℕ := [f19,f130,f21,f22,f23,f217,f24]
def e821 : List ℕ := [f19,f130,f218,f22,f23,f24]
def e822 : List ℕ := [f19,f130,f218,f21,f22,f23,f24]
def e823 : List ℕ := [f19,f130,f21,f22,f219,f24]
def e824 : List ℕ := [f19,f130,f21,f22,f219,f23,f24]
def e825 : List ℕ := [f220,f19,f130,f21,f22,f23,f24]
def e826 : List ℕ := [f19,f130,f21,f22,f23,f228]
def e827 : List ℕ := [f19,f130,f21,f22,f23,f24,f228]
def e828 : List ℕ := [f19,f130,f229,f21,f22,f23,f24]
def e829 : List ℕ := [f19,f130,f21,f22,f23,f230]
def e830 : List ℕ := [f19,f130,f21,f22,f23,f230,f24]
def e831 : List ℕ := [f231,f19,f130,f21,f22,f23,f24]
def e832 : List ℕ := [f19,f130,f21,f23,f232,f24]
def e833 : List ℕ := [f19,f130,f21,f22,f23,f232,f24]
def e834 : List ℕ := [f19,f130,f21,f233,f23,f24]
def e835 : List ℕ := [f19,f130,f21,f233,f22,f23,f24]
def e836 : List ℕ := [f19,f130,f21,f22,f234,f23,f24]
def e837 : List ℕ := [f26,f138,f139]
def e838 : List ℕ := [f26,f171,f138,f139]
def e839 : List ℕ := [f235,f19,f130,f21,f22,f23,f24]
def e840 : List ℕ := [f8,f310,f17,f312]
def e841 : List ℕ := [f8,f309,f310,f17,f312]
def e842 : List ℕ := [f19,f130,f21,f22,f23,f24,f203]
def e843 : List ℕ := [f1,f169,f2,f3]
def e844 : List ℕ := [f19,f130,f21,f204,f22,f23,f24]
def e845 : List ℕ := [f19,f130,f21,f22,f23,f250,f24]
def e846 : List ℕ := [f19,f130,f21,f22,f251,f23,f24]
def e847 : List ℕ := [f19,f130,f21,f22,f24,f207]
def e848 : List ℕ := [f19,f130,f21,f22,f23,f207]
def e849 : List ℕ := [f19,f130,f21,f22,f23,f24,f207]
def e850 : List ℕ := [f208,f19,f130,f21,f22,f24]
def e851 : List ℕ := [f208,f19,f130,f21,f22,f23,f24]
def e852 : List ℕ := [f19,f130,f21,f22,f209,f23]
def e853 : List ℕ := [f19,f130,f21,f22,f209,f23,f24]
def e858 : List ℕ := [f317,f35,f252,f62,f86]
def e859 : List ℕ := [f35,f252,f36,f62,f86]
def e860 : List ℕ := [f253,f35,f252,f62,f86]
def e861 : List ℕ := [f40,f35,f252,f62,f86]
def e862 : List ℕ := [f71,f35,f252,f62,f86]
def e863 : List ℕ := [f69,f252,f62,f86,f103]
def e864 : List ℕ := [f62,f86,f103,f318]
def e865 : List ℕ := [f252,f62,f86,f103,f318]
def e866 : List ℕ := [f256,f62,f86,f103]
def e867 : List ℕ := [f256,f252,f62,f86,f103]
def e868 : List ℕ := [f252,f89,f62,f86,f103]
def e869 : List ℕ := [f47,f252,f62,f86,f103]
def e870 : List ℕ := [f252,f62,f86,f103,f319]
def e871 : List ℕ := [f320,f252,f62,f86,f103]
def e872 : List ℕ := [f252,f91,f62,f86,f103]
def e873 : List ℕ := [f321,f252,f62,f86,f103]
def e874 : List ℕ := [f252,f62,f86,f103,f94]
def e875 : List ℕ := [f42,f252,f62,f86,f103]
def e876 : List ℕ := [f252,f62,f322,f86,f103]
def e877 : List ℕ := [f252,f261,f62,f86,f103]
def e878 : List ℕ := [f252,f62,f86,f98,f103]
def e879 : List ℕ := [f99,f252,f62,f86,f103]
def e880 : List ℕ := [f65,f252,f62,f86,f103]
def e881 : List ℕ := [f72,f252,f86,f103]
def e882 : List ℕ := [f72,f252,f62,f86]
def e883 : List ℕ := [f72,f252,f62,f86,f103]
def e884 : List ℕ := [f252,f109,f62,f86,f103]
def e885 : List ℕ := [f252,f62,f86,f323]
def e886 : List ℕ := [f252,f62,f86,f103,f323]
def e887 : List ℕ := [f110,f252,f62,f86,f103]
def e888 : List ℕ := [f324,f252,f62,f86]
def e889 : List ℕ := [f324,f252,f62,f86,f103]
def e890 : List ℕ := [f252,f62,f86,f103]
def e891 : List ℕ := [f35,f252,f86,f103]
def e892 : List ℕ := [f35,f252,f62,f86,f103]
def e940 : List ℕ := [f18,f20,f130,f21,f22,f23,f24]
def e941 : List ℕ := [f18,f19,f130,f21,f22,f23,f24]
def e942 : List ℕ := [f129,f19,f130,f21,f22,f23,f24]
def e943 : List ℕ := [f281,f20,f130,f21,f22,f23,f24]
def e944 : List ℕ := [f281,f19,f20,f21,f22,f23,f24]
def e945 : List ℕ := [f286,f20,f130,f21,f22,f23,f24]
def e946 : List ℕ := [f20,f130,f21,f287,f22,f23,f24]
def e947 : List ℕ := [f19,f20,f130,f287,f22,f23,f24]
def e948 : List ℕ := [f288,f20,f130,f21,f22,f23,f24]
def e949 : List ℕ := [f20,f130,f289,f22,f23,f24]
def e950 : List ℕ := [f20,f130,f289,f21,f22,f23,f24]
def e951 : List ℕ := [f19,f20,f130,f289,f22,f23,f24]
def e952 : List ℕ := [f290,f20,f130,f21,f22,f23,f24]
def e957 : List ℕ := [f72,f36,f291,f38,f39]
def e958 : List ℕ := [f36,f37,f336,f38,f39]
def e959 : List ℕ := [f36,f37,f291,f243,f39]
def e960 : List ℕ := [f36,f37,f291,f38,f76]
def e961 : List ℕ := [f36,f37,f291,f38,f132]
def e962 : List ℕ := [f35,f292,f37,f38,f39]
def e963 : List ℕ := [f35,f37,f291,f39,f55]
def e964 : List ℕ := [f35,f37,f291,f38,f57]
def e965 : List ℕ := [f35,f256,f36,f38,f39]
def e966 : List ℕ := [f35,f36,f60,f291,f39]
def e967 : List ℕ := [f35,f36,f62,f291,f38]
def e968 : List ℕ := [f35,f36,f37,f295,f39]
def e969 : List ℕ := [f35,f36,f37,f296,f38]
def e970 : List ℕ := [f35,f36,f37,f291,f38,f39]
def e971 : List ℕ := [f20,f130,f21,f22,f298,f23,f24]
def e972 : List ℕ := [f19,f20,f130,f21,f298,f23,f24]
def e973 : List ℕ := [f299,f20,f130,f21,f22,f23,f24]
def e974 : List ℕ := [f0,f337,f34]
def e975 : List ℕ := [f0,f115,f337,f34]
def e976 : List ℕ := [f0,f2,f337,f34]
def e977 : List ℕ := [f29,f2,f115,f34]
def e978 : List ℕ := [f115,f337,f34,f338]
def e979 : List ℕ := [f169,f115,f337,f34]
def e980 : List ℕ := [f169,f2,f115,f34]
def e981 : List ℕ := [f2,f337,f34,f339]
def e982 : List ℕ := [f2,f340,f34]
def e983 : List ℕ := [f2,f340,f337,f34]
def e984 : List ℕ := [f2,f340,f115,f34]
def e985 : List ℕ := [f341,f2,f115,f337]
def e986 : List ℕ := [f2,f342,f337]
def e987 : List ℕ := [f2,f342,f337,f34]
def e988 : List ℕ := [f2,f342,f115,f337]
def e989 : List ℕ := [f2,f115,f343]
def e990 : List ℕ := [f2,f115,f34,f343]
def e991 : List ℕ := [f2,f115,f337,f343]
def e992 : List ℕ := [f2,f115,f337,f34]
def e993 : List ℕ := [f20,f130,f21,f300,f23,f24]
def e994 : List ℕ := [f20,f130,f21,f300,f22,f23,f24]
def e995 : List ℕ := [f19,f20,f130,f21,f300,f23,f24]
def e996 : List ℕ := [f301,f20,f130,f21,f22,f23,f24]
def e997 : List ℕ := [f20,f130,f21,f22,f23,f302,f24]
def e998 : List ℕ := [f19,f20,f130,f21,f22,f302,f24]
def e999 : List ℕ := [f303,f20,f130,f21,f22,f23,f24]
def e1000 : List ℕ := [f20,f130,f21,f22,f304,f24]
def e1001 : List ℕ := [f20,f130,f21,f22,f304,f23,f24]
def e1002 : List ℕ := [f19,f20,f130,f21,f22,f304,f24]
def e1003 : List ℕ := [f305,f20,f130,f21,f22,f23,f24]
def e1004 : List ℕ := [f20,f130,f21,f22,f23,f24,f306]
def e1005 : List ℕ := [f19,f20,f130,f21,f22,f23,f306]
def e1006 : List ℕ := [f307,f20,f130,f21,f22,f23,f24]
def e1007 : List ℕ := [f20,f130,f21,f22,f23,f308]
def e1008 : List ℕ := [f20,f130,f21,f22,f23,f308,f24]
def e1009 : List ℕ := [f19,f20,f130,f21,f22,f23,f308]
def e1010 : List ℕ := [f129,f19,f20,f21,f22,f23,f24]
def e1011 : List ℕ := [f131,f19,f130,f21,f22,f23,f24]
def e1012 : List ℕ := [f19,f130,f21,f133,f22,f23,f24]
def e1013 : List ℕ := [f19,f134,f130,f21,f22,f23,f24]
def e1014 : List ℕ := [f19,f130,f135,f21,f22,f23,f24]
def e1015 : List ℕ := [f136,f19,f130,f21,f22,f23,f24]
def e1016 : List ℕ := [f19,f130,f21,f22,f137,f23,f24]
def e1017 : List ℕ := [f19,f148,f130,f21,f22,f23,f24]
def e1018 : List ℕ := [f19,f130,f21,f149,f22,f23,f24]
def e1019 : List ℕ := [f150,f19,f130,f21,f22,f23,f24]
def e1020 : List ℕ := [f19,f130,f21,f22,f23,f151,f24]
def e1021 : List ℕ := [f19,f152,f130,f21,f22,f23,f24]
def e1022 : List ℕ := [f19,f130,f21,f22,f153,f23,f24]
def e1023 : List ℕ := [f154,f19,f130,f21,f22,f23,f24]
def e1024 : List ℕ := [f19,f130,f21,f22,f23,f24,f155]
def e1025 : List ℕ := [f19,f156,f130,f21,f22,f23,f24]
def e1026 : List ℕ := [f19,f130,f21,f22,f23,f157,f24]
def e1027 : List ℕ := [f158,f19,f20,f21,f22,f23,f24]
def e1028 : List ℕ := [f19,f20,f21,f159,f22,f23,f24]
def e1029 : List ℕ := [f19,f20,f160,f21,f22,f23,f24]
def e1030 : List ℕ := [f19,f20,f161,f21,f22,f23,f24]
def e1031 : List ℕ := [f26,f67,f313]
def e1032 : List ℕ := [f26,f67,f313,f28]
def e1033 : List ℕ := [f162,f19,f20,f21,f22,f23,f24]
def e1034 : List ℕ := [f19,f20,f21,f22,f168,f23,f24]
def e1035 : List ℕ := [f19,f20,f183,f21,f22,f23,f24]
def e1036 : List ℕ := [f19,f20,f21,f184,f22,f23,f24]
def e1037 : List ℕ := [f185,f19,f20,f21,f22,f23,f24]
def e1038 : List ℕ := [f19,f20,f21,f22,f23,f186,f24]
def e1039 : List ℕ := [f19,f20,f187,f21,f22,f23,f24]
def e1040 : List ℕ := [f19,f20,f21,f22,f188,f23,f24]
def e1041 : List ℕ := [f189,f19,f20,f21,f22,f23,f24]
def e1042 : List ℕ := [f19,f20,f21,f22,f23,f24,f190]
def e1043 : List ℕ := [f19,f20,f191,f21,f22,f23,f24]
def e1044 : List ℕ := [f19,f20,f21,f22,f23,f192,f24]
def e1045 : List ℕ := [f19,f20,f130,f22,f201,f23,f24]
def e1046 : List ℕ := [f19,f20,f130,f21,f201,f23,f24]
def e1047 : List ℕ := [f202,f19,f20,f130,f22,f23,f24]
def e1048 : List ℕ := [f19,f20,f130,f214,f21,f23,f24]
def e1049 : List ℕ := [f19,f20,f130,f22,f23,f217,f24]
def e1050 : List ℕ := [f19,f20,f130,f21,f22,f217,f24]
def e1051 : List ℕ := [f19,f20,f130,f218,f22,f23,f24]
def e1052 : List ℕ := [f19,f20,f130,f21,f22,f219,f24]
def e1053 : List ℕ := [f19,f20,f130,f21,f22,f23,f228]
def e1054 : List ℕ := [f19,f20,f130,f21,f22,f23,f230]
def e1055 : List ℕ := [f19,f20,f130,f21,f23,f232,f24]
def e1056 : List ℕ := [f19,f20,f130,f21,f233,f23,f24]
def e1057 : List ℕ := [f19,f20,f130,f21,f22,f24,f207]
def e1058 : List ℕ := [f19,f20,f130,f21,f22,f23,f207]
def e1059 : List ℕ := [f208,f19,f20,f130,f21,f22,f24]
def e1060 : List ℕ := [f19,f20,f130,f21,f22,f209,f23]
def e1061 : List ℕ := [f19,f20,f130,f21,f22,f23,f24]
def e1105 : List ℕ := [f26,f67,f138,f28]
def e1112 : List ℕ := [f26,f68,f67,f28]
def e1127 : List ℕ := [f286,f129,f20,f21,f22,f23,f24]
def e1128 : List ℕ := [f20,f21,f355,f22,f23,f24]
def e1129 : List ℕ := [f129,f20,f355,f22,f23,f24]
def e1130 : List ℕ := [f129,f20,f21,f355,f22,f23,f24]
def e1131 : List ℕ := [f356,f20,f21,f22,f23,f24]
def e1132 : List ℕ := [f356,f129,f20,f21,f22,f23,f24]
def e1133 : List ℕ := [f129,f20,f289,f22,f23,f24]
def e1134 : List ℕ := [f129,f20,f289,f21,f22,f23,f24]
def e1135 : List ℕ := [f290,f129,f20,f21,f22,f23,f24]
def e1136 : List ℕ := [f129,f20,f21,f357,f23,f24]
def e1137 : List ℕ := [f129,f20,f21,f22,f357,f23,f24]
def e1138 : List ℕ := [f358,f129,f20,f21,f22,f23,f24]
def e1139 : List ℕ := [f129,f20,f21,f300,f23,f24]
def e1140 : List ℕ := [f129,f20,f21,f300,f22,f23,f24]
def e1141 : List ℕ := [f301,f129,f20,f21,f22,f23,f24]
def e1142 : List ℕ := [f20,f21,f22,f23,f359,f24]
def e1143 : List ℕ := [f129,f20,f21,f22,f359,f24]
def e1144 : List ℕ := [f129,f20,f21,f22,f23,f359,f24]
def e1145 : List ℕ := [f360,f20,f21,f22,f23,f24]
def e1146 : List ℕ := [f360,f129,f20,f21,f22,f23,f24]
def e1147 : List ℕ := [f129,f20,f21,f22,f304,f24]
def e1148 : List ℕ := [f129,f20,f21,f22,f304,f23,f24]
def e1149 : List ℕ := [f305,f129,f20,f21,f22,f23,f24]
def e1150 : List ℕ := [f129,f20,f21,f22,f23,f361]
def e1151 : List ℕ := [f129,f20,f21,f22,f23,f24,f361]
def e1152 : List ℕ := [f362,f129,f20,f21,f22,f23,f24]
def e1153 : List ℕ := [f129,f20,f21,f22,f23,f308]
def e1154 : List ℕ := [f129,f20,f21,f22,f23,f308,f24]
def e1155 : List ℕ := [f131,f129,f20,f21,f22,f23,f24]
def e1156 : List ℕ := [f129,f21,f133,f22,f23,f24]
def e1157 : List ℕ := [f129,f20,f21,f133,f22,f23,f24]
def e1158 : List ℕ := [f129,f134,f21,f22,f23,f24]
def e1159 : List ℕ := [f129,f134,f20,f21,f22,f23,f24]
def e1160 : List ℕ := [f129,f20,f135,f21,f22,f23,f24]
def e1161 : List ℕ := [f136,f129,f20,f21,f22,f23,f24]
def e1162 : List ℕ := [f129,f20,f21,f22,f137,f23,f24]
def e1163 : List ℕ := [f129,f148,f20,f21,f22,f23,f24]
def e1164 : List ℕ := [f129,f20,f21,f149,f22,f23,f24]
def e1165 : List ℕ := [f150,f129,f20,f21,f22,f23,f24]
def e1166 : List ℕ := [f129,f21,f22,f23,f151,f24]
def e1167 : List ℕ := [f129,f20,f21,f22,f23,f151,f24]
def e1168 : List ℕ := [f129,f152,f21,f22,f23,f24]
def e1169 : List ℕ := [f129,f152,f20,f21,f22,f23,f24]
def e1170 : List ℕ := [f129,f20,f21,f22,f153,f23,f24]
def e1171 : List ℕ := [f154,f129,f20,f21,f22,f23,f24]
def e1172 : List ℕ := [f129,f20,f21,f22,f23,f24,f155]
def e1173 : List ℕ := [f129,f156,f20,f21,f22,f23,f24]
def e1174 : List ℕ := [f129,f20,f21,f22,f23,f157,f24]
def e1175 : List ℕ := [f129,f20,f193,f21,f22,f23,f24]
def e1176 : List ℕ := [f129,f20,f21,f201,f23,f24]
def e1177 : List ℕ := [f129,f20,f21,f22,f201,f23,f24]
def e1178 : List ℕ := [f202,f129,f20,f22,f23,f24]
def e1179 : List ℕ := [f202,f129,f20,f21,f22,f23,f24]
def e1180 : List ℕ := [f129,f20,f214,f21,f23,f24]
def e1181 : List ℕ := [f129,f20,f214,f21,f22,f23,f24]
def e1182 : List ℕ := [f215,f129,f20,f21,f22,f23,f24]
def e1183 : List ℕ := [f129,f20,f22,f23,f217,f24]
def e1184 : List ℕ := [f129,f20,f21,f22,f217,f24]
def e1185 : List ℕ := [f129,f20,f21,f22,f23,f217,f24]
def e1186 : List ℕ := [f129,f20,f218,f22,f23,f24]
def e1187 : List ℕ := [f129,f20,f218,f21,f22,f23,f24]
def e1188 : List ℕ := [f129,f20,f21,f22,f219,f24]
def e1189 : List ℕ := [f129,f20,f21,f22,f219,f23,f24]
def e1190 : List ℕ := [f220,f129,f20,f21,f22,f23,f24]
def e1191 : List ℕ := [f129,f20,f21,f22,f23,f228]
def e1192 : List ℕ := [f129,f20,f21,f22,f23,f24,f228]
def e1193 : List ℕ := [f129,f20,f229,f21,f22,f23,f24]
def e1194 : List ℕ := [f129,f20,f21,f22,f23,f230]
def e1195 : List ℕ := [f129,f20,f21,f22,f23,f230,f24]
def e1196 : List ℕ := [f231,f129,f20,f21,f22,f23,f24]
def e1197 : List ℕ := [f129,f20,f21,f23,f232,f24]
def e1198 : List ℕ := [f129,f20,f21,f22,f23,f232,f24]
def e1199 : List ℕ := [f129,f20,f21,f233,f23,f24]
def e1200 : List ℕ := [f129,f20,f21,f233,f22,f23,f24]
def e1201 : List ℕ := [f129,f20,f21,f22,f234,f23,f24]
def e1202 : List ℕ := [f235,f129,f20,f21,f22,f23,f24]
def e1203 : List ℕ := [f129,f20,f21,f22,f23,f24,f203]
def e1204 : List ℕ := [f129,f20,f21,f204,f22,f23,f24]
def e1205 : List ℕ := [f129,f20,f21,f22,f23,f250,f24]
def e1206 : List ℕ := [f129,f20,f21,f22,f251,f23,f24]
def e1207 : List ℕ := [f129,f20,f21,f22,f24,f207]
def e1208 : List ℕ := [f129,f20,f21,f22,f23,f207]
def e1209 : List ℕ := [f129,f20,f21,f22,f23,f24,f207]
def e1210 : List ℕ := [f208,f129,f20,f21,f22,f24]
def e1211 : List ℕ := [f208,f129,f20,f21,f22,f23,f24]
def e1212 : List ℕ := [f129,f20,f21,f22,f209,f23]
def e1213 : List ℕ := [f129,f20,f21,f22,f209,f23,f24]
def e1253 : List ℕ := [f252,f62,f86,f94,f87]
def e1274 : List ℕ := [f131,f281,f19,f21,f22,f23,f24]
def e1275 : List ℕ := [f19,f21,f365,f22,f23,f24]
def e1276 : List ℕ := [f281,f19,f21,f365,f22,f23,f24]
def e1277 : List ℕ := [f366,f19,f21,f22,f23,f24]
def e1278 : List ℕ := [f366,f281,f19,f21,f22,f23,f24]
def e1279 : List ℕ := [f281,f19,f135,f21,f22,f23,f24]
def e1280 : List ℕ := [f136,f281,f19,f21,f22,f23,f24]
def e1281 : List ℕ := [f281,f19,f21,f22,f282,f23,f24]
def e1282 : List ℕ := [f283,f281,f19,f21,f22,f23,f24]
def e1283 : List ℕ := [f281,f19,f21,f149,f22,f23,f24]
def e1284 : List ℕ := [f150,f281,f19,f21,f22,f23,f24]
def e1285 : List ℕ := [f19,f21,f22,f23,f367,f24]
def e1286 : List ℕ := [f281,f19,f21,f22,f23,f367,f24]
def e1287 : List ℕ := [f368,f19,f21,f22,f23,f24]
def e1288 : List ℕ := [f368,f281,f19,f21,f22,f23,f24]
def e1289 : List ℕ := [f281,f19,f21,f22,f153,f23,f24]
def e1290 : List ℕ := [f154,f281,f19,f21,f22,f23,f24]
def e1291 : List ℕ := [f281,f19,f21,f22,f23,f24,f284]
def e1292 : List ℕ := [f285,f281,f19,f21,f22,f23,f24]
def e1293 : List ℕ := [f281,f19,f21,f22,f23,f157,f24]
def e1294 : List ℕ := [f286,f281,f19,f21,f22,f23,f24]
def e1295 : List ℕ := [f281,f21,f287,f22,f23,f24]
def e1296 : List ℕ := [f281,f19,f287,f22,f23,f24]
def e1297 : List ℕ := [f281,f19,f21,f287,f22,f23,f24]
def e1298 : List ℕ := [f281,f288,f21,f22,f23,f24]
def e1299 : List ℕ := [f281,f288,f19,f21,f22,f23,f24]
def e1300 : List ℕ := [f281,f19,f289,f22,f23,f24]
def e1301 : List ℕ := [f281,f19,f289,f21,f22,f23,f24]
def e1302 : List ℕ := [f290,f281,f19,f21,f22,f23,f24]
def e1303 : List ℕ := [f281,f19,f21,f22,f298,f23,f24]
def e1304 : List ℕ := [f281,f299,f19,f21,f22,f23,f24]
def e1305 : List ℕ := [f281,f19,f21,f300,f22,f23,f24]
def e1306 : List ℕ := [f301,f281,f19,f21,f22,f23,f24]
def e1307 : List ℕ := [f281,f21,f22,f23,f302,f24]
def e1308 : List ℕ := [f281,f19,f21,f22,f302,f24]
def e1309 : List ℕ := [f281,f19,f21,f22,f23,f302,f24]
def e1310 : List ℕ := [f281,f303,f21,f22,f23,f24]
def e1311 : List ℕ := [f281,f303,f19,f21,f22,f23,f24]
def e1312 : List ℕ := [f281,f19,f21,f22,f304,f24]
def e1313 : List ℕ := [f281,f19,f21,f22,f304,f23,f24]
def e1314 : List ℕ := [f305,f281,f19,f21,f22,f23,f24]
def e1315 : List ℕ := [f281,f19,f21,f22,f23,f24,f306]
def e1316 : List ℕ := [f281,f307,f19,f21,f22,f23,f24]
def e1317 : List ℕ := [f281,f19,f21,f22,f23,f308,f24]
def e1318 : List ℕ := [f281,f19,f193,f21,f22,f23,f24]
def e1319 : List ℕ := [f281,f19,f22,f201,f23,f24]
def e1320 : List ℕ := [f281,f19,f21,f201,f23,f24]
def e1321 : List ℕ := [f281,f19,f21,f22,f201,f23,f24]
def e1322 : List ℕ := [f202,f281,f19,f22,f23,f24]
def e1323 : List ℕ := [f202,f281,f19,f21,f22,f23,f24]
def e1324 : List ℕ := [f281,f19,f214,f21,f23,f24]
def e1325 : List ℕ := [f281,f19,f214,f21,f22,f23,f24]
def e1326 : List ℕ := [f215,f281,f19,f21,f22,f23,f24]
def e1327 : List ℕ := [f281,f19,f22,f23,f217,f24]
def e1328 : List ℕ := [f281,f19,f21,f22,f217,f24]
def e1329 : List ℕ := [f281,f19,f21,f22,f23,f217,f24]
def e1330 : List ℕ := [f281,f19,f218,f22,f23,f24]
def e1331 : List ℕ := [f281,f19,f218,f21,f22,f23,f24]
def e1332 : List ℕ := [f281,f19,f21,f22,f219,f24]
def e1333 : List ℕ := [f281,f19,f21,f22,f219,f23,f24]
def e1334 : List ℕ := [f220,f281,f19,f21,f22,f23,f24]
def e1335 : List ℕ := [f281,f19,f21,f22,f23,f228]
def e1336 : List ℕ := [f281,f19,f21,f22,f23,f24,f228]
def e1337 : List ℕ := [f281,f19,f229,f21,f22,f23,f24]
def e1338 : List ℕ := [f281,f19,f21,f22,f23,f230]
def e1339 : List ℕ := [f281,f19,f21,f22,f23,f230,f24]
def e1340 : List ℕ := [f231,f281,f19,f21,f22,f23,f24]
def e1341 : List ℕ := [f281,f19,f21,f23,f232,f24]
def e1342 : List ℕ := [f281,f19,f21,f22,f23,f232,f24]
def e1343 : List ℕ := [f281,f19,f21,f233,f23,f24]
def e1344 : List ℕ := [f281,f19,f21,f233,f22,f23,f24]
def e1345 : List ℕ := [f281,f19,f21,f22,f234,f23,f24]
def e1346 : List ℕ := [f235,f281,f19,f21,f22,f23,f24]
def e1347 : List ℕ := [f281,f19,f21,f22,f23,f24,f203]
def e1348 : List ℕ := [f281,f19,f21,f204,f22,f23,f24]
def e1349 : List ℕ := [f281,f19,f21,f22,f23,f250,f24]
def e1350 : List ℕ := [f281,f19,f21,f22,f251,f23,f24]
def e1351 : List ℕ := [f281,f19,f21,f22,f24,f207]
def e1352 : List ℕ := [f281,f19,f21,f22,f23,f207]
def e1353 : List ℕ := [f281,f19,f21,f22,f23,f24,f207]
def e1354 : List ℕ := [f208,f281,f19,f21,f22,f24]
def e1355 : List ℕ := [f208,f281,f19,f21,f22,f23,f24]
def e1356 : List ℕ := [f281,f19,f21,f22,f209,f23]
def e1357 : List ℕ := [f281,f19,f21,f22,f209,f23,f24]
def e1358 : List ℕ := [f281,f18,f19,f21,f22,f23,f24]
def e1359 : List ℕ := [f131,f19,f20,f21,f22,f23,f24]
def e1360 : List ℕ := [f19,f20,f21,f365,f22,f23,f24]
def e1361 : List ℕ := [f366,f19,f20,f21,f22,f23,f24]
def e1362 : List ℕ := [f19,f20,f135,f21,f22,f23,f24]
def e1363 : List ℕ := [f136,f19,f20,f21,f22,f23,f24]
def e1364 : List ℕ := [f19,f20,f21,f22,f282,f23,f24]
def e1365 : List ℕ := [f283,f19,f20,f21,f22,f23,f24]
def e1366 : List ℕ := [f19,f20,f21,f149,f22,f23,f24]
def e1367 : List ℕ := [f150,f19,f20,f21,f22,f23,f24]
def e1368 : List ℕ := [f19,f20,f21,f22,f23,f367,f24]
def e1369 : List ℕ := [f368,f19,f20,f21,f22,f23,f24]
def e1370 : List ℕ := [f19,f20,f21,f22,f153,f23,f24]
def e1371 : List ℕ := [f154,f19,f20,f21,f22,f23,f24]
def e1372 : List ℕ := [f19,f20,f21,f22,f23,f24,f284]
def e1373 : List ℕ := [f285,f19,f20,f21,f22,f23,f24]
def e1374 : List ℕ := [f19,f20,f21,f22,f23,f157,f24]
def e1375 : List ℕ := [f129,f281,f21,f22,f23,f24]
def e1376 : List ℕ := [f129,f281,f20,f21,f22,f23,f24]
def e1377 : List ℕ := [f129,f281,f19,f21,f22,f23,f24]
def e1378 : List ℕ := [f281,f20,f21,f287,f22,f23,f24]
def e1379 : List ℕ := [f281,f19,f20,f287,f22,f23,f24]
def e1380 : List ℕ := [f281,f288,f20,f21,f22,f23,f24]
def e1381 : List ℕ := [f281,f19,f20,f289,f22,f23,f24]
def e1382 : List ℕ := [f281,f19,f20,f21,f298,f23,f24]
def e1383 : List ℕ := [f281,f19,f20,f21,f300,f23,f24]
def e1384 : List ℕ := [f281,f20,f21,f22,f23,f302,f24]
def e1385 : List ℕ := [f281,f19,f20,f21,f22,f302,f24]
def e1386 : List ℕ := [f281,f303,f20,f21,f22,f23,f24]
def e1387 : List ℕ := [f281,f19,f20,f21,f22,f304,f24]
def e1388 : List ℕ := [f281,f19,f20,f21,f22,f23,f306]
def e1389 : List ℕ := [f281,f19,f20,f21,f22,f23,f308]
def e1390 : List ℕ := [f281,f19,f21,f133,f22,f23,f24]
def e1391 : List ℕ := [f281,f19,f134,f21,f22,f23,f24]
def e1392 : List ℕ := [f281,f19,f21,f22,f137,f23,f24]
def e1393 : List ℕ := [f281,f19,f148,f21,f22,f23,f24]
def e1394 : List ℕ := [f281,f19,f21,f22,f23,f151,f24]
def e1395 : List ℕ := [f281,f19,f152,f21,f22,f23,f24]
def e1396 : List ℕ := [f281,f19,f21,f22,f23,f24,f155]
def e1397 : List ℕ := [f281,f19,f156,f21,f22,f23,f24]
def e1398 : List ℕ := [f281,f19,f20,f22,f201,f23,f24]
def e1399 : List ℕ := [f281,f19,f20,f21,f201,f23,f24]
def e1400 : List ℕ := [f202,f281,f19,f20,f22,f23,f24]
def e1401 : List ℕ := [f281,f19,f20,f214,f21,f23,f24]
def e1402 : List ℕ := [f281,f19,f20,f22,f23,f217,f24]
def e1403 : List ℕ := [f281,f19,f20,f21,f22,f217,f24]
def e1404 : List ℕ := [f281,f19,f20,f218,f22,f23,f24]
def e1405 : List ℕ := [f281,f19,f20,f21,f22,f219,f24]
def e1406 : List ℕ := [f281,f19,f20,f21,f22,f23,f228]
def e1407 : List ℕ := [f281,f19,f20,f21,f22,f23,f230]
def e1408 : List ℕ := [f281,f19,f20,f21,f23,f232,f24]
def e1409 : List ℕ := [f281,f19,f20,f21,f233,f23,f24]
def e1410 : List ℕ := [f281,f19,f20,f21,f22,f24,f207]
def e1411 : List ℕ := [f281,f19,f20,f21,f22,f23,f207]
def e1412 : List ℕ := [f208,f281,f19,f20,f21,f22,f24]
def e1413 : List ℕ := [f281,f19,f20,f21,f22,f209,f23]
def e1414 : List ℕ := [f286,f19,f20,f21,f22,f23,f24]
def e1416 : List ℕ := [f26,f67,f172,f28]
def e1425 : List ℕ := [f86,f103,f319,f59]
def e1426 : List ℕ := [f86,f103,f319,f87,f59]
def e1433 : List ℕ := [f320,f62,f86,f103,f87]
def e1435 : List ℕ := [f62,f103,f319,f87,f101]
def e1447 : List ℕ := [f62,f86,f103,f319,f87]
def e1460 : List ℕ := [f86,f103,f319,f147]
def e1461 : List ℕ := [f86,f103,f319,f87,f147]
def e1471 : List ℕ := [f320,f35,f86,f103,f87]
def e1473 : List ℕ := [f35,f103,f319,f87,f101]
def e1485 : List ℕ := [f35,f86,f103,f319,f87]
def e1487 : List ℕ := [f62,f86,f103,f319,f147]
def e1490 : List ℕ := [f35,f86,f103,f319,f59]
def e1492 : List ℕ := [f35,f109,f62,f319,f87]
def e1517 : List ℕ := [f72,f62,f319,f87,f101]
def e1548 : List ℕ := [f35,f124,f319,f87,f101]
def e1560 : List ℕ := [f131,f20,f21,f287,f22,f23,f24]
def e1561 : List ℕ := [f20,f21,f287,f133,f22,f23,f24]
def e1562 : List ℕ := [f134,f20,f21,f287,f22,f23,f24]
def e1563 : List ℕ := [f20,f135,f21,f287,f22,f23,f24]
def e1564 : List ℕ := [f394,f20,f21,f287,f22,f23,f24]
def e1565 : List ℕ := [f20,f21,f287,f159,f22,f23,f24]
def e1566 : List ℕ := [f366,f20,f21,f287,f22,f23,f24]
def e1567 : List ℕ := [f20,f21,f395,f22,f23,f24]
def e1568 : List ℕ := [f20,f21,f395,f287,f22,f23,f24]
def e1569 : List ℕ := [f136,f20,f21,f287,f22,f23,f24]
def e1570 : List ℕ := [f13,f4,f11,f7]
def e1571 : List ℕ := [f13,f4,f141,f7]
def e1572 : List ℕ := [f13,f4,f11,f141,f7]
def e1573 : List ℕ := [f20,f21,f287,f22,f137,f23,f24]
def e1574 : List ℕ := [f148,f20,f21,f287,f22,f23,f24]
def e1575 : List ℕ := [f20,f21,f287,f149,f22,f23,f24]
def e1576 : List ℕ := [f150,f20,f21,f287,f22,f23,f24]
def e1577 : List ℕ := [f21,f287,f22,f23,f151,f24]
def e1578 : List ℕ := [f20,f21,f287,f22,f23,f151,f24]
def e1579 : List ℕ := [f152,f21,f287,f22,f23,f24]
def e1580 : List ℕ := [f152,f20,f21,f287,f22,f23,f24]
def e1581 : List ℕ := [f20,f21,f287,f22,f153,f23,f24]
def e1582 : List ℕ := [f154,f20,f21,f287,f22,f23,f24]
def e1583 : List ℕ := [f309,f310,f17,f396]
def e1584 : List ℕ := [f8,f309,f310,f17,f396]
def e1585 : List ℕ := [f20,f21,f287,f22,f23,f24,f155]
def e1586 : List ℕ := [f341,f1,f2,f3]
def e1587 : List ℕ := [f156,f20,f21,f287,f22,f23,f24]
def e1588 : List ℕ := [f1,f2,f337,f3]
def e1589 : List ℕ := [f20,f21,f287,f22,f23,f157,f24]
def e1590 : List ℕ := [f288,f20,f287,f22,f23,f24]
def e1591 : List ℕ := [f288,f20,f21,f22,f23,f24]
def e1592 : List ℕ := [f288,f20,f21,f287,f22,f23,f24]
def e1593 : List ℕ := [f20,f193,f21,f287,f22,f23,f24]
def e1594 : List ℕ := [f20,f21,f287,f201,f23,f24]
def e1595 : List ℕ := [f20,f21,f287,f22,f201,f23,f24]
def e1596 : List ℕ := [f202,f20,f21,f287,f22,f23,f24]
def e1597 : List ℕ := [f20,f214,f21,f287,f23,f24]
def e1598 : List ℕ := [f20,f214,f21,f287,f22,f23,f24]
def e1599 : List ℕ := [f215,f20,f21,f287,f22,f23,f24]
def e1640 : List ℕ := [f394,f20,f287,f22,f217,f24]
def e1647 : List ℕ := [f395,f159,f22,f217,f24]
def e1648 : List ℕ := [f20,f395,f22,f217,f24]
def e1649 : List ℕ := [f159,f22,f137,f217,f24]
def e1650 : List ℕ := [f148,f159,f22,f217,f24]
def e1651 : List ℕ := [f421,f159,f22,f217,f24]
def e1652 : List ℕ := [f159,f22,f422,f217,f24]
def e1653 : List ℕ := [f159,f22,f217,f24,f155]
def e1654 : List ℕ := [f156,f159,f22,f217,f24]
def e1655 : List ℕ := [f20,f159,f217,f205,f24]
def e1656 : List ℕ := [f20,f423,f159,f217,f24]
def e1657 : List ℕ := [f20,f159,f22,f24,f424]
def e1658 : List ℕ := [f20,f425,f159,f22,f24]
def e1659 : List ℕ := [f20,f159,f22,f217,f24]
def e1660 : List ℕ := [f20,f287,f159,f22,f217,f24]
def e1661 : List ℕ := [f366,f20,f287,f22,f217,f24]
def e1662 : List ℕ := [f20,f395,f287,f22,f217,f24]
def e1663 : List ℕ := [f136,f20,f287,f22,f217,f24]
def e1664 : List ℕ := [f20,f287,f22,f137,f217,f24]
def e1665 : List ℕ := [f148,f20,f287,f22,f217,f24]
def e1666 : List ℕ := [f20,f287,f149,f22,f217,f24]
def e1667 : List ℕ := [f421,f20,f287,f22,f217,f24]
def e1668 : List ℕ := [f20,f287,f22,f217,f426,f24]
def e1669 : List ℕ := [f427,f20,f287,f22,f217,f24]
def e1670 : List ℕ := [f20,f287,f22,f422,f217,f24]
def e1671 : List ℕ := [f154,f20,f287,f22,f217,f24]
def e1672 : List ℕ := [f20,f287,f22,f217,f24,f155]
def e1673 : List ℕ := [f156,f20,f287,f22,f217,f24]
def e1674 : List ℕ := [f20,f287,f22,f217,f157,f24]
def e1675 : List ℕ := [f20,f428,f287,f22,f217,f24]
def e1676 : List ℕ := [f20,f287,f429,f217,f24]
def e1677 : List ℕ := [f20,f287,f22,f429,f217,f24]
def e1678 : List ℕ := [f430,f20,f287,f22,f217,f24]
def e1679 : List ℕ := [f20,f431,f287,f217,f24]
def e1680 : List ℕ := [f20,f431,f287,f22,f217,f24]
def e1681 : List ℕ := [f20,f432,f287,f22,f217,f24]
def e1682 : List ℕ := [f20,f287,f22,f217,f433,f24]
def e1683 : List ℕ := [f434,f20,f287,f22,f217,f24]
def e1684 : List ℕ := [f20,f287,f22,f435,f217,f24]
def e1685 : List ℕ := [f436,f20,f287,f22,f217,f24]
def e1686 : List ℕ := [f20,f287,f22,f217,f24,f437]
def e1687 : List ℕ := [f20,f438,f287,f22,f217,f24]
def e1688 : List ℕ := [f20,f287,f22,f217,f439,f24]
def e1689 : List ℕ := [f20,f440,f287,f22,f217,f24]
def e1690 : List ℕ := [f20,f287,f217,f205,f24]
def e1691 : List ℕ := [f20,f287,f22,f217,f205,f24]
def e1692 : List ℕ := [f20,f423,f287,f217,f24]
def e1693 : List ℕ := [f20,f423,f287,f22,f217,f24]
def e1694 : List ℕ := [f20,f287,f22,f441,f217,f24]
def e1695 : List ℕ := [f235,f20,f287,f22,f217,f24]
def e1696 : List ℕ := [f20,f287,f22,f217,f24,f203]
def e1697 : List ℕ := [f20,f287,f204,f22,f217,f24]
def e1698 : List ℕ := [f20,f287,f22,f217,f250,f24]
def e1699 : List ℕ := [f20,f287,f22,f442,f217,f24]
def e1700 : List ℕ := [f20,f287,f22,f24,f424]
def e1701 : List ℕ := [f20,f287,f22,f217,f24,f424]
def e1702 : List ℕ := [f20,f425,f287,f22,f24]
def e1703 : List ℕ := [f20,f425,f287,f22,f217,f24]
def e1704 : List ℕ := [f20,f287,f22,f443,f217,f24]
def e1705 : List ℕ := [f20,f287,f22,f217,f24]
def e1706 : List ℕ := [f20,f287,f22,f23,f217,f24]
def e1707 : List ℕ := [f20,f21,f287,f22,f217,f24]
def e1708 : List ℕ := [f20,f21,f287,f22,f23,f217,f24]
def e1709 : List ℕ := [f20,f218,f287,f22,f23,f24]
def e1710 : List ℕ := [f20,f218,f21,f287,f22,f23,f24]
def e1711 : List ℕ := [f20,f21,f287,f22,f219,f24]
def e1712 : List ℕ := [f20,f21,f287,f22,f219,f23,f24]
def e1713 : List ℕ := [f220,f20,f21,f287,f22,f23,f24]
def e1714 : List ℕ := [f35,f62,f95,f87,f101]
def e1715 : List ℕ := [f35,f62,f382,f87,f101]
def e1716 : List ℕ := [f35,f62,f319,f147,f101]
def e1717 : List ℕ := [f35,f62,f319,f106,f101]
def e1718 : List ℕ := [f258,f62,f319,f87,f101]
def e1719 : List ℕ := [f62,f319,f87,f444,f101]
def e1720 : List ℕ := [f35,f319,f371,f87,f101]
def e1721 : List ℕ := [f35,f62,f371,f87,f101]
def e1722 : List ℕ := [f385,f35,f319,f87,f101]
def e1723 : List ℕ := [f35,f372,f62,f87,f101]
def e1724 : List ℕ := [f122,f35,f319,f87,f101]
def e1725 : List ℕ := [f35,f62,f319,f59,f101]
def e1726 : List ℕ := [f35,f319,f100,f101]
def e1727 : List ℕ := [f35,f319,f100,f87,f101]
def e1728 : List ℕ := [f35,f62,f319,f100,f101]
def e1729 : List ℕ := [f35,f121,f319,f87,f101]
def e1730 : List ℕ := [f35,f319,f87,f445,f101]
def e1731 : List ℕ := [f376,f35,f62,f87,f101]
def e1732 : List ℕ := [f376,f35,f62,f319,f101]
def e1733 : List ℕ := [f35,f62,f377,f319,f101]
def e1734 : List ℕ := [f35,f62,f46,f87,f101]
def e1735 : List ℕ := [f35,f62,f446,f87]
def e1736 : List ℕ := [f35,f62,f446,f87,f101]
def e1737 : List ℕ := [f35,f62,f446,f319,f87]
def e1738 : List ℕ := [f321,f35,f62,f319,f87]
def e1739 : List ℕ := [f35,f62,f373,f319]
def e1740 : List ℕ := [f35,f62,f373,f319,f101]
def e1741 : List ℕ := [f35,f62,f373,f319,f87]
def e1742 : List ℕ := [f35,f62,f319,f87,f101]
def e1743 : List ℕ := [f20,f287,f22,f23,f24,f228]
def e1744 : List ℕ := [f20,f21,f287,f22,f23,f24,f228]
def e1745 : List ℕ := [f20,f229,f287,f22,f23,f24]
def e1746 : List ℕ := [f20,f229,f21,f287,f22,f23,f24]
def e1747 : List ℕ := [f20,f21,f287,f22,f23,f230,f24]
def e1748 : List ℕ := [f20,f428,f21,f287,f22,f23,f24]
def e1749 : List ℕ := [f20,f21,f287,f429,f23,f24]
def e1750 : List ℕ := [f20,f21,f287,f22,f429,f23,f24]
def e1751 : List ℕ := [f430,f20,f21,f287,f22,f23,f24]
def e1752 : List ℕ := [f20,f431,f21,f287,f23,f24]
def e1753 : List ℕ := [f20,f431,f21,f287,f22,f23,f24]
def e1754 : List ℕ := [f447,f20,f21,f287,f22,f23,f24]
def e1755 : List ℕ := [f20,f21,f22,f23,f433,f24]
def e1756 : List ℕ := [f20,f21,f287,f22,f433,f24]
def e1757 : List ℕ := [f20,f21,f287,f22,f23,f433,f24]
def e1758 : List ℕ := [f20,f21,f448,f22,f23,f24]
def e1759 : List ℕ := [f20,f21,f448,f287,f22,f23,f24]
def e1760 : List ℕ := [f20,f21,f287,f22,f435,f24]
def e1761 : List ℕ := [f20,f21,f287,f22,f435,f23,f24]
def e1762 : List ℕ := [f436,f20,f21,f287,f22,f23,f24]
def e1763 : List ℕ := [f20,f21,f287,f22,f23,f24,f437]
def e1764 : List ℕ := [f20,f21,f438,f287,f22,f23,f24]
def e1765 : List ℕ := [f20,f21,f287,f22,f23,f439,f24]
def e1766 : List ℕ := [f231,f20,f21,f287,f22,f23,f24]
def e1767 : List ℕ := [f20,f21,f287,f23,f232,f24]
def e1768 : List ℕ := [f20,f21,f287,f22,f23,f232,f24]
def e1769 : List ℕ := [f20,f21,f287,f233,f23,f24]
def e1770 : List ℕ := [f20,f21,f287,f233,f22,f23,f24]
def e1771 : List ℕ := [f20,f21,f287,f22,f234,f23,f24]
def e1772 : List ℕ := [f235,f20,f21,f287,f22,f23,f24]
def e1773 : List ℕ := [f20,f21,f287,f22,f23,f24,f203]
def e1774 : List ℕ := [f20,f21,f287,f204,f22,f23,f24]
def e1775 : List ℕ := [f1,f2,f449,f3]
def e1776 : List ℕ := [f20,f21,f287,f22,f23,f250,f24]
def e1777 : List ℕ := [f20,f21,f287,f22,f251,f23,f24]
def e1778 : List ℕ := [f20,f21,f287,f22,f24,f207]
def e1779 : List ℕ := [f20,f21,f287,f22,f23,f207]
def e1780 : List ℕ := [f20,f21,f287,f22,f23,f24,f207]
def e1781 : List ℕ := [f208,f20,f21,f287,f22,f24]
def e1782 : List ℕ := [f208,f20,f21,f287,f22,f23,f24]
def e1783 : List ℕ := [f20,f21,f287,f22,f209,f23]
def e1784 : List ℕ := [f20,f21,f287,f22,f209,f23,f24]
def e1785 : List ℕ := [f20,f21,f287,f22,f23,f24]
def e1786 : List ℕ := [f19,f20,f287,f22,f23,f24]
def e1787 : List ℕ := [f19,f20,f21,f287,f22,f23,f24]
def e1794 : List ℕ := [f18,f288,f20,f21,f22,f23,f24]
def e1795 : List ℕ := [f20,f453,f21,f22,f23,f24]
def e1796 : List ℕ := [f288,f453,f21,f22,f23,f24]
def e1797 : List ℕ := [f288,f20,f453,f21,f22,f23,f24]
def e1798 : List ℕ := [f356,f288,f20,f21,f22,f23,f24]
def e1799 : List ℕ := [f290,f288,f20,f21,f22,f23,f24]
def e1800 : List ℕ := [f288,f20,f21,f454,f23,f24]
def e1801 : List ℕ := [f288,f20,f21,f22,f454,f23,f24]
def e1802 : List ℕ := [f455,f288,f20,f21,f22,f23,f24]
def e1803 : List ℕ := [f288,f20,f21,f300,f23,f24]
def e1804 : List ℕ := [f288,f20,f21,f300,f22,f23,f24]
def e1805 : List ℕ := [f456,f288,f20,f21,f22,f23,f24]
def e1806 : List ℕ := [f20,f21,f22,f23,f457,f24]
def e1807 : List ℕ := [f288,f20,f21,f22,f457,f24]
def e1808 : List ℕ := [f288,f20,f21,f22,f23,f457,f24]
def e1809 : List ℕ := [f434,f20,f21,f22,f23,f24]
def e1810 : List ℕ := [f434,f288,f20,f21,f22,f23,f24]
def e1811 : List ℕ := [f288,f20,f21,f22,f458,f24]
def e1812 : List ℕ := [f288,f20,f21,f22,f458,f23,f24]
def e1813 : List ℕ := [f305,f288,f20,f21,f22,f23,f24]
def e1814 : List ℕ := [f288,f20,f21,f22,f23,f459]
def e1815 : List ℕ := [f288,f20,f21,f22,f23,f24,f459]
def e1816 : List ℕ := [f460,f288,f20,f21,f22,f23,f24]
def e1817 : List ℕ := [f288,f20,f21,f22,f23,f308]
def e1818 : List ℕ := [f288,f20,f21,f22,f23,f308,f24]
def e1819 : List ℕ := [f131,f288,f20,f21,f22,f23,f24]
def e1820 : List ℕ := [f288,f20,f21,f133,f22,f23,f24]
def e1821 : List ℕ := [f288,f134,f20,f21,f22,f23,f24]
def e1822 : List ℕ := [f288,f20,f135,f21,f22,f23,f24]
def e1823 : List ℕ := [f26,f175,f67,f28]
def e1824 : List ℕ := [f136,f288,f20,f21,f22,f23,f24]
def e1825 : List ℕ := [f288,f20,f21,f22,f137,f23,f24]
def e1826 : List ℕ := [f288,f148,f20,f21,f22,f23,f24]
def e1827 : List ℕ := [f288,f20,f21,f149,f22,f23,f24]
def e1828 : List ℕ := [f150,f288,f20,f21,f22,f23,f24]
def e1829 : List ℕ := [f288,f21,f22,f23,f151,f24]
def e1830 : List ℕ := [f288,f20,f21,f22,f23,f151,f24]
def e1831 : List ℕ := [f288,f152,f21,f22,f23,f24]
def e1832 : List ℕ := [f288,f152,f20,f21,f22,f23,f24]
def e1833 : List ℕ := [f288,f20,f21,f22,f153,f23,f24]
def e1834 : List ℕ := [f154,f288,f20,f21,f22,f23,f24]
def e1835 : List ℕ := [f288,f20,f21,f22,f23,f24,f155]
def e1836 : List ℕ := [f288,f156,f20,f21,f22,f23,f24]
def e1837 : List ℕ := [f288,f20,f21,f22,f23,f157,f24]
def e1838 : List ℕ := [f288,f20,f193,f21,f22,f23,f24]
def e1839 : List ℕ := [f288,f20,f22,f201,f23,f24]
def e1840 : List ℕ := [f288,f20,f21,f201,f23,f24]
def e1841 : List ℕ := [f288,f20,f21,f22,f201,f23,f24]
def e1842 : List ℕ := [f202,f288,f20,f22,f23,f24]
def e1843 : List ℕ := [f202,f288,f20,f21,f22,f23,f24]
def e1844 : List ℕ := [f288,f20,f214,f21,f23,f24]
def e1845 : List ℕ := [f288,f20,f214,f21,f22,f23,f24]
def e1846 : List ℕ := [f215,f288,f20,f21,f22,f23,f24]
def e1847 : List ℕ := [f288,f20,f22,f23,f217,f24]
def e1848 : List ℕ := [f288,f20,f21,f22,f217,f24]
def e1849 : List ℕ := [f288,f20,f21,f22,f23,f217,f24]
def e1850 : List ℕ := [f288,f20,f218,f22,f23,f24]
def e1851 : List ℕ := [f288,f20,f218,f21,f22,f23,f24]
def e1852 : List ℕ := [f288,f20,f21,f22,f219,f24]
def e1853 : List ℕ := [f288,f20,f21,f22,f219,f23,f24]
def e1854 : List ℕ := [f220,f288,f20,f21,f22,f23,f24]
def e1855 : List ℕ := [f288,f20,f21,f22,f23,f24,f228]
def e1856 : List ℕ := [f288,f20,f229,f21,f22,f23,f24]
def e1857 : List ℕ := [f288,f20,f21,f22,f23,f230,f24]
def e1858 : List ℕ := [f231,f288,f20,f21,f22,f23,f24]
def e1859 : List ℕ := [f288,f20,f21,f23,f232,f24]
def e1860 : List ℕ := [f288,f20,f21,f22,f23,f232,f24]
def e1861 : List ℕ := [f288,f20,f21,f233,f23,f24]
def e1862 : List ℕ := [f288,f20,f21,f233,f22,f23,f24]
def e1863 : List ℕ := [f288,f20,f21,f22,f234,f23,f24]
def e1864 : List ℕ := [f235,f288,f20,f21,f22,f23,f24]
def e1865 : List ℕ := [f288,f20,f21,f22,f23,f24,f203]
def e1866 : List ℕ := [f288,f20,f21,f204,f22,f23,f24]
def e1867 : List ℕ := [f288,f20,f21,f22,f23,f250,f24]
def e1868 : List ℕ := [f288,f20,f21,f22,f251,f23,f24]
def e1869 : List ℕ := [f288,f20,f21,f22,f24,f207]
def e1870 : List ℕ := [f288,f20,f21,f22,f23,f207]
def e1871 : List ℕ := [f288,f20,f21,f22,f23,f24,f207]
def e1872 : List ℕ := [f208,f288,f20,f21,f22,f24]
def e1873 : List ℕ := [f208,f288,f20,f21,f22,f23,f24]
def e1874 : List ℕ := [f288,f20,f21,f22,f209,f23]
def e1875 : List ℕ := [f288,f20,f21,f22,f209,f23,f24]
def e1876 : List ℕ := [f288,f19,f20,f21,f22,f23,f24]
def e1877 : List ℕ := [f19,f20,f289,f22,f23,f24]
def e1878 : List ℕ := [f19,f20,f289,f21,f22,f23,f24]
def e1879 : List ℕ := [f290,f19,f20,f21,f22,f23,f24]
def e1885 : List ℕ := [f18,f19,f20,f21,f298,f23,f24]
def e1886 : List ℕ := [f129,f19,f20,f21,f298,f23,f24]
def e1887 : List ℕ := [f286,f19,f20,f21,f298,f23,f24]
def e1888 : List ℕ := [f20,f21,f287,f298,f23,f24]
def e1889 : List ℕ := [f19,f20,f21,f287,f298,f23,f24]
def e1890 : List ℕ := [f288,f20,f21,f298,f23,f24]
def e1891 : List ℕ := [f288,f19,f20,f21,f298,f23,f24]
def e1892 : List ℕ := [f19,f20,f289,f21,f298,f23,f24]
def e1893 : List ℕ := [f79,f51,f462]
def e1894 : List ℕ := [f20,f21,f300,f298,f23,f24]
def e1895 : List ℕ := [f19,f20,f21,f300,f23,f24]
def e1896 : List ℕ := [f19,f20,f21,f300,f298,f23,f24]
def e1897 : List ℕ := [f301,f19,f20,f21,f298,f23,f24]
def e1898 : List ℕ := [f19,f20,f21,f298,f23,f302,f24]
def e1899 : List ℕ := [f303,f19,f20,f21,f298,f23,f24]
def e1900 : List ℕ := [f19,f20,f21,f298,f304,f23,f24]
def e1901 : List ℕ := [f305,f19,f20,f21,f298,f23,f24]
def e1922 : List ℕ := [f131,f20,f21,f298,f23,f306]
def e1923 : List ℕ := [f21,f133,f298,f23,f306]
def e1924 : List ℕ := [f20,f21,f133,f298,f23,f306]
def e1925 : List ℕ := [f134,f21,f298,f23,f306]
def e1926 : List ℕ := [f134,f20,f21,f298,f23,f306]
def e1927 : List ℕ := [f20,f135,f21,f298,f23,f306]
def e1928 : List ℕ := [f469,f20,f21,f298,f23,f306]
def e1929 : List ℕ := [f20,f21,f298,f168,f23,f306]
def e1930 : List ℕ := [f283,f20,f21,f298,f23,f306]
def e1931 : List ℕ := [f20,f21,f470,f298,f23,f306]
def e1932 : List ℕ := [f150,f20,f21,f298,f23,f306]
def e1933 : List ℕ := [f21,f298,f23,f151,f306]
def e1934 : List ℕ := [f20,f21,f298,f23,f151,f306]
def e1935 : List ℕ := [f152,f21,f298,f23,f306]
def e1936 : List ℕ := [f152,f20,f21,f298,f23,f306]
def e1937 : List ℕ := [f20,f21,f298,f153,f23,f306]
def e1938 : List ℕ := [f471,f20,f21,f298,f23,f306]
def e1939 : List ℕ := [f20,f21,f298,f23,f306,f190]
def e1940 : List ℕ := [f285,f20,f21,f298,f23,f306]
def e1941 : List ℕ := [f20,f21,f298,f23,f472,f306]
def e1942 : List ℕ := [f20,f473,f21,f298,f23,f306]
def e1943 : List ℕ := [f20,f21,f298,f429,f23,f306]
def e1944 : List ℕ := [f474,f20,f21,f298,f23,f306]
def e1945 : List ℕ := [f20,f475,f21,f298,f23,f306]
def e1946 : List ℕ := [f215,f20,f21,f298,f23,f306]
def e1947 : List ℕ := [f20,f298,f23,f217,f306]
def e1948 : List ℕ := [f20,f21,f298,f217,f306]
def e1949 : List ℕ := [f20,f21,f298,f23,f217,f306]
def e1950 : List ℕ := [f20,f218,f298,f23,f306]
def e1951 : List ℕ := [f20,f218,f21,f298,f23,f306]
def e1952 : List ℕ := [f20,f21,f298,f219,f306]
def e1953 : List ℕ := [f20,f21,f298,f219,f23,f306]
def e1954 : List ℕ := [f476,f20,f21,f298,f23,f306]
def e1955 : List ℕ := [f20,f21,f298,f23,f437]
def e1956 : List ℕ := [f20,f21,f298,f23,f306,f437]
def e1957 : List ℕ := [f20,f477,f21,f298,f23,f306]
def e1958 : List ℕ := [f20,f21,f298,f23,f478]
def e1959 : List ℕ := [f20,f21,f298,f23,f478,f306]
def e1960 : List ℕ := [f479,f20,f21,f298,f23,f306]
def e1961 : List ℕ := [f20,f21,f23,f480,f306]
def e1962 : List ℕ := [f20,f21,f298,f23,f480,f306]
def e1963 : List ℕ := [f20,f21,f481,f23,f306]
def e1964 : List ℕ := [f20,f21,f481,f298,f23,f306]
def e1965 : List ℕ := [f20,f21,f298,f482,f23,f306]
def e1966 : List ℕ := [f483,f20,f21,f298,f23,f306]
def e1967 : List ℕ := [f20,f21,f298,f23,f306,f484]
def e1968 : List ℕ := [f20,f21,f485,f298,f23,f306]
def e1969 : List ℕ := [f20,f21,f298,f23,f486,f306]
def e1970 : List ℕ := [f20,f21,f298,f487,f23,f306]
def e1971 : List ℕ := [f20,f21,f298,f23,f306,f488]
def e1972 : List ℕ := [f489,f20,f21,f298,f23,f306]
def e1973 : List ℕ := [f20,f21,f298,f490,f23,f306]
def e1974 : List ℕ := [f20,f21,f298,f23,f306]
def e1976 : List ℕ := [f21,f133,f298,f23,f24,f306]
def e1977 : List ℕ := [f134,f21,f298,f23,f24,f306]
def e1978 : List ℕ := [f21,f298,f23,f151,f24,f306]
def e1979 : List ℕ := [f152,f21,f298,f23,f24,f306]
def e1980 : List ℕ := [f154,f20,f21,f298,f23,f306]
def e1981 : List ℕ := [f20,f21,f298,f23,f306,f155]
def e1982 : List ℕ := [f156,f20,f21,f298,f23,f306]
def e1983 : List ℕ := [f20,f21,f298,f23,f157,f306]
def e1984 : List ℕ := [f20,f21,f429,f23,f24,f306]
def e1985 : List ℕ := [f20,f475,f21,f23,f24,f306]
def e1986 : List ℕ := [f20,f298,f23,f217,f24,f306]
def e1987 : List ℕ := [f20,f21,f298,f217,f24,f306]
def e1988 : List ℕ := [f20,f218,f298,f23,f24,f306]
def e1989 : List ℕ := [f20,f21,f298,f219,f24,f306]
def e1990 : List ℕ := [f220,f20,f21,f298,f23,f306]
def e1991 : List ℕ := [f20,f21,f298,f23,f306,f228]
def e1992 : List ℕ := [f20,f229,f21,f298,f23,f306]
def e1993 : List ℕ := [f20,f21,f298,f23,f230,f306]
def e1994 : List ℕ := [f20,f21,f298,f23,f24,f437]
def e1995 : List ℕ := [f20,f21,f298,f23,f24,f478]
def e1996 : List ℕ := [f20,f21,f23,f480,f24,f306]
def e1997 : List ℕ := [f20,f21,f481,f23,f24,f306]
def e1998 : List ℕ := [f492,f20,f21,f298,f23,f306]
def e1999 : List ℕ := [f20,f21,f493,f298,f23,f306]
def e2000 : List ℕ := [f483,f20,f21,f298,f23,f24]
def e2001 : List ℕ := [f20,f21,f485,f298,f23,f24]
def e2002 : List ℕ := [f20,f21,f298,f251,f23,f306]
def e2003 : List ℕ := [f20,f21,f298,f24,f207,f306]
def e2004 : List ℕ := [f20,f21,f298,f23,f207,f306]
def e2005 : List ℕ := [f208,f20,f21,f298,f306]
def e2006 : List ℕ := [f208,f20,f21,f298,f24,f306]
def e2007 : List ℕ := [f208,f20,f21,f298,f23,f306]
def e2008 : List ℕ := [f20,f21,f298,f209,f23,f306]
def e2009 : List ℕ := [f307,f20,f21,f298,f23,f306]
def e2010 : List ℕ := [f307,f20,f21,f298,f23,f24]
def e2011 : List ℕ := [f20,f21,f298,f23,f24,f306]
def e2012 : List ℕ := [f19,f20,f21,f298,f23,f306]
def e2013 : List ℕ := [f19,f20,f21,f298,f23,f24,f306]
def e2014 : List ℕ := [f307,f19,f20,f21,f298,f23,f24]
def e2015 : List ℕ := [f19,f20,f21,f298,f23,f308]
def e2016 : List ℕ := [f19,f20,f21,f298,f23,f308,f24]
def e2017 : List ℕ := [f131,f19,f20,f21,f298,f23,f24]
def e2018 : List ℕ := [f19,f21,f133,f298,f23,f24]
def e2019 : List ℕ := [f19,f20,f21,f133,f298,f23,f24]
def e2020 : List ℕ := [f19,f134,f21,f298,f23,f24]
def e2021 : List ℕ := [f19,f134,f20,f21,f298,f23,f24]
def e2022 : List ℕ := [f19,f20,f135,f21,f298,f23,f24]
def e2023 : List ℕ := [f78,f79,f462]
def e2024 : List ℕ := [f469,f19,f20,f21,f298,f23,f24]
def e2025 : List ℕ := [f19,f20,f21,f298,f168,f23,f24]
def e2026 : List ℕ := [f283,f19,f20,f21,f298,f23,f24]
def e2027 : List ℕ := [f19,f20,f21,f470,f298,f23,f24]
def e2028 : List ℕ := [f150,f19,f20,f21,f298,f23,f24]
def e2029 : List ℕ := [f19,f21,f298,f23,f151,f24]
def e2030 : List ℕ := [f19,f20,f21,f298,f23,f151,f24]
def e2031 : List ℕ := [f19,f152,f21,f298,f23,f24]
def e2032 : List ℕ := [f19,f152,f20,f21,f298,f23,f24]
def e2033 : List ℕ := [f19,f20,f21,f298,f153,f23,f24]
def e2034 : List ℕ := [f154,f19,f20,f21,f298,f23,f24]
def e2035 : List ℕ := [f19,f20,f21,f298,f23,f24,f155]
def e2036 : List ℕ := [f19,f156,f20,f21,f298,f23,f24]
def e2037 : List ℕ := [f19,f20,f21,f298,f23,f157,f24]
def e2038 : List ℕ := [f19,f20,f473,f21,f298,f23,f24]
def e2039 : List ℕ := [f19,f20,f21,f429,f23,f24]
def e2040 : List ℕ := [f19,f20,f21,f298,f429,f23,f24]
def e2041 : List ℕ := [f474,f19,f20,f21,f298,f23,f24]
def e2042 : List ℕ := [f19,f20,f475,f21,f23,f24]
def e2043 : List ℕ := [f19,f20,f475,f21,f298,f23,f24]
def e2044 : List ℕ := [f215,f19,f20,f21,f298,f23,f24]
def e2045 : List ℕ := [f19,f20,f298,f23,f217,f24]
def e2046 : List ℕ := [f19,f20,f21,f298,f217,f24]
def e2047 : List ℕ := [f19,f20,f21,f298,f23,f217,f24]
def e2048 : List ℕ := [f19,f20,f218,f298,f23,f24]
def e2049 : List ℕ := [f19,f20,f218,f21,f298,f23,f24]
def e2050 : List ℕ := [f19,f20,f21,f298,f219,f24]
def e2051 : List ℕ := [f19,f20,f21,f298,f219,f23,f24]
def e2052 : List ℕ := [f220,f19,f20,f21,f298,f23,f24]
def e2053 : List ℕ := [f19,f20,f21,f298,f23,f228]
def e2054 : List ℕ := [f19,f20,f21,f298,f23,f24,f228]
def e2055 : List ℕ := [f19,f20,f229,f21,f298,f23,f24]
def e2056 : List ℕ := [f19,f20,f21,f298,f23,f230]
def e2057 : List ℕ := [f19,f20,f21,f298,f23,f230,f24]
def e2058 : List ℕ := [f479,f19,f20,f21,f298,f23,f24]
def e2059 : List ℕ := [f19,f20,f21,f23,f480,f24]
def e2060 : List ℕ := [f19,f20,f21,f298,f23,f480,f24]
def e2061 : List ℕ := [f19,f20,f21,f481,f23,f24]
def e2062 : List ℕ := [f19,f20,f21,f481,f298,f23,f24]
def e2063 : List ℕ := [f19,f20,f21,f298,f482,f23,f24]
def e2064 : List ℕ := [f492,f19,f20,f21,f298,f23,f24]
def e2065 : List ℕ := [f19,f20,f21,f298,f23,f24,f484]
def e2066 : List ℕ := [f19,f20,f21,f493,f298,f23,f24]
def e2067 : List ℕ := [f19,f20,f21,f298,f23,f486,f24]
def e2068 : List ℕ := [f19,f20,f21,f298,f251,f23,f24]
def e2069 : List ℕ := [f19,f20,f21,f298,f24,f207]
def e2070 : List ℕ := [f19,f20,f21,f298,f23,f207]
def e2071 : List ℕ := [f19,f20,f21,f298,f23,f24,f207]
def e2072 : List ℕ := [f208,f19,f20,f21,f298,f24]
def e2073 : List ℕ := [f208,f19,f20,f21,f298,f23,f24]
def e2074 : List ℕ := [f19,f20,f21,f298,f209,f23]
def e2075 : List ℕ := [f19,f20,f21,f298,f209,f23,f24]
def e2076 : List ℕ := [f19,f20,f21,f298,f23,f24]
def e2077 : List ℕ := [f129,f20,f21,f22,f298,f23,f24]
def e2078 : List ℕ := [f20,f21,f287,f22,f298,f23,f24]
def e2079 : List ℕ := [f19,f20,f287,f22,f298,f23,f24]
def e2080 : List ℕ := [f288,f20,f21,f22,f298,f23,f24]
def e2081 : List ℕ := [f19,f20,f289,f22,f298,f23,f24]
def e2082 : List ℕ := [f290,f20,f21,f22,f298,f23,f24]
def e2083 : List ℕ := [f290,f19,f20,f21,f298,f23,f24]
def e2084 : List ℕ := [f299,f19,f20,f21,f298,f23,f24]
def e2085 : List ℕ := [f20,f21,f300,f22,f298,f23,f24]
def e2086 : List ℕ := [f19,f20,f21,f300,f22,f23,f24]
def e2087 : List ℕ := [f20,f21,f22,f298,f302,f24]
def e2088 : List ℕ := [f20,f21,f22,f298,f23,f302,f24]
def e2089 : List ℕ := [f19,f20,f21,f22,f298,f302,f24]
def e2090 : List ℕ := [f303,f20,f21,f22,f298,f23,f24]
def e2091 : List ℕ := [f19,f20,f21,f22,f298,f304,f24]
def e2092 : List ℕ := [f20,f21,f22,f298,f23,f306]
def e2093 : List ℕ := [f202,f20,f298,f23,f24,f306]
def e2094 : List ℕ := [f20,f22,f429,f23,f24,f306]
def e2095 : List ℕ := [f235,f20,f21,f298,f23,f306]
def e2097 : List ℕ := [f20,f21,f298,f23,f306,f203]
def e2098 : List ℕ := [f20,f21,f204,f298,f23,f306]
def e2099 : List ℕ := [f20,f21,f298,f23,f250,f306]
def e2100 : List ℕ := [f20,f21,f22,f23,f486,f306]
def e2101 : List ℕ := [f483,f20,f21,f22,f23,f24]
def e2102 : List ℕ := [f208,f20,f21,f22,f298,f306]
def e2103 : List ℕ := [f20,f21,f22,f298,f24,f488]
def e2104 : List ℕ := [f20,f21,f22,f298,f23,f24,f306]
def e2105 : List ℕ := [f19,f20,f21,f22,f298,f23,f306]
def e2106 : List ℕ := [f307,f20,f21,f22,f298,f23,f24]
def e2107 : List ℕ := [f19,f20,f21,f22,f298,f23,f308]
def e2108 : List ℕ := [f19,f21,f133,f22,f298,f23,f24]
def e2109 : List ℕ := [f19,f134,f21,f22,f298,f23,f24]
def e2110 : List ℕ := [f136,f19,f20,f21,f298,f23,f24]
def e2111 : List ℕ := [f19,f20,f21,f298,f137,f23,f24]
def e2112 : List ℕ := [f19,f148,f20,f21,f298,f23,f24]
def e2113 : List ℕ := [f19,f20,f21,f149,f298,f23,f24]
def e2114 : List ℕ := [f469,f19,f20,f21,f22,f23,f24]
def e2115 : List ℕ := [f19,f20,f21,f22,f470,f23,f24]
def e2116 : List ℕ := [f19,f21,f22,f298,f23,f151,f24]
def e2117 : List ℕ := [f19,f152,f21,f22,f298,f23,f24]
def e2118 : List ℕ := [f19,f20,f193,f21,f298,f23,f24]
def e2119 : List ℕ := [f19,f20,f22,f201,f298,f23,f24]
def e2120 : List ℕ := [f19,f20,f21,f201,f298,f23,f24]
def e2121 : List ℕ := [f202,f19,f20,f298,f23,f24]
def e2122 : List ℕ := [f202,f19,f20,f22,f298,f23,f24]
def e2123 : List ℕ := [f202,f19,f20,f21,f298,f23,f24]
def e2124 : List ℕ := [f19,f20,f214,f21,f298,f23,f24]
def e2125 : List ℕ := [f19,f20,f473,f21,f22,f23,f24]
def e2126 : List ℕ := [f19,f20,f22,f429,f23,f24]
def e2128 : List ℕ := [f71,f43,f41,f38,f39]
def e2129 : List ℕ := [f107,f41,f83,f38,f39]
def e2130 : List ℕ := [f54,f41,f38,f39]
def e2131 : List ℕ := [f54,f43,f41,f38,f39]
def e2132 : List ℕ := [f107,f54,f41,f38,f39]
def e2133 : List ℕ := [f52,f43,f41,f38,f39]
def e2134 : List ℕ := [f52,f107,f43,f38,f39]
def e2135 : List ℕ := [f72,f107,f43,f38,f39]
def e2136 : List ℕ := [f43,f494,f41,f38,f39]
def e2137 : List ℕ := [f43,f41,f38,f39,f495]
def e2138 : List ℕ := [f496,f43,f41,f38,f39]
def e2139 : List ℕ := [f43,f41,f38,f39,f497]
def e2140 : List ℕ := [f498,f43,f41,f38,f39]
def e2141 : List ℕ := [f40,f107,f41,f38,f39]
def e2142 : List ℕ := [f40,f107,f43,f38,f39]
def e2143 : List ℕ := [f107,f41,f38,f39,f264]
def e2144 : List ℕ := [f107,f273,f41,f38,f39]
def e2145 : List ℕ := [f279,f107,f41,f38,f39]
def e2146 : List ℕ := [f107,f41,f38,f499,f39]
def e2147 : List ℕ := [f107,f43,f38,f39,f270]
def e2148 : List ℕ := [f107,f43,f500,f38,f39]
def e2149 : List ℕ := [f107,f43,f38,f39,f501]
def e2150 : List ℕ := [f107,f43,f502,f38,f39]
def e2151 : List ℕ := [f107,f43,f41,f39,f63]
def e2152 : List ℕ := [f107,f43,f41,f38,f63]
def e2153 : List ℕ := [f64,f107,f43,f41,f39]
def e2154 : List ℕ := [f65,f107,f43,f41,f38]
def e2155 : List ℕ := [f107,f43,f41,f38,f39]
def e2156 : List ℕ := [f19,f20,f22,f298,f429,f23,f24]
def e2157 : List ℕ := [f19,f20,f21,f22,f429,f23,f24]
def e2158 : List ℕ := [f474,f19,f20,f22,f23,f24]
def e2159 : List ℕ := [f474,f19,f20,f22,f298,f23,f24]
def e2160 : List ℕ := [f474,f19,f20,f21,f22,f23,f24]
def e2161 : List ℕ := [f19,f20,f475,f21,f22,f23,f24]
def e2162 : List ℕ := [f19,f20,f22,f298,f23,f217,f24]
def e2163 : List ℕ := [f19,f20,f21,f22,f298,f217,f24]
def e2164 : List ℕ := [f19,f20,f218,f22,f298,f23,f24]
def e2165 : List ℕ := [f19,f20,f21,f22,f298,f219,f24]
def e2166 : List ℕ := [f19,f20,f21,f22,f298,f23,f228]
def e2167 : List ℕ := [f19,f20,f21,f22,f298,f23,f230]
def e2168 : List ℕ := [f299,f19,f20,f21,f22,f23,f24]
def e2169 : List ℕ := [f231,f19,f20,f21,f298,f23,f24]
def e2170 : List ℕ := [f19,f20,f21,f298,f23,f232,f24]
def e2171 : List ℕ := [f19,f20,f21,f233,f298,f23,f24]
def e2172 : List ℕ := [f19,f20,f21,f298,f234,f23,f24]
def e2173 : List ℕ := [f235,f19,f20,f21,f298,f23,f24]
def e2174 : List ℕ := [f19,f20,f21,f298,f23,f24,f203]
def e2175 : List ℕ := [f19,f20,f21,f204,f298,f23,f24]
def e2176 : List ℕ := [f19,f20,f21,f298,f23,f250,f24]
def e2177 : List ℕ := [f479,f19,f20,f21,f22,f23,f24]
def e2178 : List ℕ := [f19,f20,f21,f22,f23,f480,f24]
def e2179 : List ℕ := [f19,f20,f21,f22,f481,f23,f24]
def e2180 : List ℕ := [f19,f20,f21,f22,f482,f23,f24]
def e2181 : List ℕ := [f492,f19,f20,f21,f22,f23,f24]
def e2182 : List ℕ := [f19,f20,f21,f22,f23,f24,f484]
def e2183 : List ℕ := [f19,f20,f21,f22,f493,f23,f24]
def e2184 : List ℕ := [f19,f20,f21,f22,f23,f486,f24]
def e2185 : List ℕ := [f19,f20,f21,f22,f298,f24,f207]
def e2186 : List ℕ := [f19,f20,f21,f22,f298,f23,f207]
def e2187 : List ℕ := [f208,f19,f20,f21,f22,f298,f24]
def e2188 : List ℕ := [f19,f20,f21,f22,f298,f209,f23]
def e2189 : List ℕ := [f19,f20,f21,f22,f298,f23,f24]
def e2261 : List ℕ := [f18,f19,f20,f21,f300,f23,f24]
def e2262 : List ℕ := [f129,f19,f20,f21,f300,f23,f24]
def e2263 : List ℕ := [f286,f19,f20,f21,f300,f23,f24]
def e2264 : List ℕ := [f20,f21,f287,f300,f23,f24]
def e2265 : List ℕ := [f19,f20,f21,f287,f300,f23,f24]
def e2266 : List ℕ := [f288,f19,f20,f21,f300,f23,f24]
def e2267 : List ℕ := [f19,f20,f289,f21,f300,f23,f24]
def e2268 : List ℕ := [f301,f19,f20,f21,f300,f23,f24]
def e2269 : List ℕ := [f20,f21,f300,f23,f302,f24]
def e2270 : List ℕ := [f19,f20,f21,f300,f23,f302,f24]
def e2271 : List ℕ := [f303,f20,f21,f300,f23,f24]
def e2272 : List ℕ := [f303,f19,f20,f21,f300,f23,f24]
def e2273 : List ℕ := [f19,f20,f21,f300,f304,f23,f24]
def e2274 : List ℕ := [f305,f19,f20,f21,f300,f23,f24]
def e2275 : List ℕ := [f19,f20,f21,f300,f23,f306]
def e2276 : List ℕ := [f19,f20,f21,f300,f23,f24,f306]
def e2277 : List ℕ := [f307,f19,f20,f21,f300,f23,f24]
def e2278 : List ℕ := [f19,f20,f21,f300,f23,f308]
def e2279 : List ℕ := [f19,f20,f21,f300,f23,f308,f24]
def e2280 : List ℕ := [f131,f19,f20,f21,f300,f23,f24]
def e2281 : List ℕ := [f19,f21,f133,f300,f23,f24]
def e2282 : List ℕ := [f19,f20,f21,f133,f300,f23,f24]
def e2283 : List ℕ := [f19,f134,f21,f300,f23,f24]
def e2284 : List ℕ := [f19,f134,f20,f21,f300,f23,f24]
def e2285 : List ℕ := [f19,f20,f135,f21,f300,f23,f24]
def e2286 : List ℕ := [f78,f79,f50]
def e2287 : List ℕ := [f136,f19,f20,f21,f300,f23,f24]
def e2288 : List ℕ := [f19,f20,f21,f300,f508,f23,f24]
def e2289 : List ℕ := [f19,f148,f20,f21,f300,f23,f24]
def e2290 : List ℕ := [f19,f20,f21,f184,f300,f23,f24]
def e2291 : List ℕ := [f150,f19,f20,f21,f300,f23,f24]
def e2292 : List ℕ := [f19,f21,f300,f23,f151,f24]
def e2293 : List ℕ := [f19,f20,f21,f300,f23,f151,f24]
def e2294 : List ℕ := [f19,f152,f21,f300,f23,f24]
def e2295 : List ℕ := [f19,f152,f20,f21,f300,f23,f24]
def e2296 : List ℕ := [f19,f20,f21,f300,f153,f23,f24]
def e2297 : List ℕ := [f78,f79,f51]
def e2298 : List ℕ := [f154,f19,f20,f21,f300,f23,f24]
def e2299 : List ℕ := [f19,f20,f21,f300,f23,f24,f155]
def e2300 : List ℕ := [f19,f156,f20,f21,f300,f23,f24]
def e2301 : List ℕ := [f19,f20,f21,f300,f23,f157,f24]
def e2302 : List ℕ := [f19,f20,f193,f21,f300,f23,f24]
def e2303 : List ℕ := [f19,f20,f300,f509,f23,f24]
def e2304 : List ℕ := [f19,f20,f21,f509,f23,f24]
def e2305 : List ℕ := [f19,f20,f21,f300,f509,f23,f24]
def e2306 : List ℕ := [f202,f19,f20,f300,f23,f24]
def e2307 : List ℕ := [f202,f19,f20,f21,f300,f23,f24]
def e2308 : List ℕ := [f19,f20,f431,f21,f23,f24]
def e2309 : List ℕ := [f19,f20,f431,f21,f300,f23,f24]
def e2310 : List ℕ := [f215,f19,f20,f21,f300,f23,f24]
def e2311 : List ℕ := [f19,f20,f300,f23,f217,f24]
def e2312 : List ℕ := [f19,f20,f21,f300,f217,f24]
def e2313 : List ℕ := [f19,f20,f21,f300,f23,f217,f24]
def e2314 : List ℕ := [f19,f20,f218,f300,f23,f24]
def e2315 : List ℕ := [f19,f20,f218,f21,f300,f23,f24]
def e2316 : List ℕ := [f19,f20,f21,f300,f219,f24]
def e2317 : List ℕ := [f19,f20,f21,f300,f219,f23,f24]
def e2318 : List ℕ := [f220,f19,f20,f21,f300,f23,f24]
def e2319 : List ℕ := [f19,f20,f21,f300,f23,f228]
def e2320 : List ℕ := [f19,f20,f21,f300,f23,f24,f228]
def e2321 : List ℕ := [f19,f20,f229,f21,f300,f23,f24]
def e2322 : List ℕ := [f19,f20,f21,f300,f23,f230]
def e2323 : List ℕ := [f19,f20,f21,f300,f23,f230,f24]
def e2324 : List ℕ := [f231,f19,f20,f21,f300,f23,f24]
def e2325 : List ℕ := [f19,f20,f21,f23,f510,f24]
def e2326 : List ℕ := [f19,f20,f21,f300,f23,f510,f24]
def e2327 : List ℕ := [f19,f20,f21,f511,f23,f24]
def e2328 : List ℕ := [f19,f20,f21,f511,f300,f23,f24]
def e2329 : List ℕ := [f19,f20,f21,f300,f234,f23,f24]
def e2330 : List ℕ := [f235,f19,f20,f21,f300,f23,f24]
def e2331 : List ℕ := [f19,f20,f21,f300,f23,f24,f512]
def e2332 : List ℕ := [f19,f20,f21,f485,f300,f23,f24]
def e2333 : List ℕ := [f19,f20,f21,f300,f23,f250,f24]
def e2334 : List ℕ := [f19,f20,f21,f300,f251,f23,f24]
def e2335 : List ℕ := [f19,f20,f21,f300,f24,f207]
def e2336 : List ℕ := [f19,f20,f21,f300,f23,f207]
def e2337 : List ℕ := [f19,f20,f21,f300,f23,f24,f207]
def e2338 : List ℕ := [f208,f19,f20,f21,f300,f24]
def e2339 : List ℕ := [f208,f19,f20,f21,f300,f23,f24]
def e2340 : List ℕ := [f19,f20,f21,f300,f209,f23]
def e2341 : List ℕ := [f19,f20,f21,f300,f209,f23,f24]
def e2342 : List ℕ := [f20,f21,f287,f300,f22,f23,f24]
def e2343 : List ℕ := [f19,f20,f287,f300,f22,f23,f24]
def e2344 : List ℕ := [f19,f20,f289,f300,f22,f23,f24]
def e2345 : List ℕ := [f290,f19,f20,f21,f300,f23,f24]
def e2346 : List ℕ := [f299,f20,f21,f300,f22,f23,f24]
def e2347 : List ℕ := [f299,f19,f20,f21,f300,f23,f24]
def e2348 : List ℕ := [f20,f21,f300,f22,f23,f302,f24]
def e2349 : List ℕ := [f19,f20,f21,f300,f22,f302,f24]
def e2350 : List ℕ := [f303,f20,f21,f300,f22,f23,f24]
def e2351 : List ℕ := [f19,f20,f21,f300,f22,f304,f24]
def e2352 : List ℕ := [f305,f20,f21,f300,f22,f23,f24]
def e2353 : List ℕ := [f19,f20,f21,f300,f22,f23,f306]
def e2354 : List ℕ := [f20,f21,f300,f22,f23,f308,f24]
def e2355 : List ℕ := [f19,f20,f21,f300,f22,f23,f308]
def e2356 : List ℕ := [f19,f21,f133,f300,f22,f23,f24]
def e2357 : List ℕ := [f19,f134,f21,f300,f22,f23,f24]
def e2358 : List ℕ := [f19,f20,f21,f22,f508,f23,f24]
def e2359 : List ℕ := [f19,f148,f20,f21,f22,f23,f24]
def e2360 : List ℕ := [f19,f20,f21,f300,f137,f23,f24]
def e2361 : List ℕ := [f19,f20,f21,f149,f300,f23,f24]
def e2362 : List ℕ := [f19,f21,f300,f22,f23,f151,f24]
def e2363 : List ℕ := [f19,f152,f21,f300,f22,f23,f24]
def e2364 : List ℕ := [f19,f20,f193,f21,f22,f23,f24]
def e2365 : List ℕ := [f19,f20,f22,f509,f23,f24]
def e2366 : List ℕ := [f19,f20,f300,f22,f509,f23,f24]
def e2367 : List ℕ := [f19,f20,f21,f22,f509,f23,f24]
def e2368 : List ℕ := [f202,f19,f20,f22,f23,f24]
def e2369 : List ℕ := [f202,f19,f20,f300,f22,f23,f24]
def e2370 : List ℕ := [f202,f19,f20,f21,f22,f23,f24]
def e2371 : List ℕ := [f19,f20,f431,f21,f22,f23,f24]
def e2372 : List ℕ := [f19,f20,f300,f22,f201,f23,f24]
def e2373 : List ℕ := [f19,f20,f21,f300,f201,f23,f24]
def e2374 : List ℕ := [f19,f20,f214,f21,f300,f23,f24]
def e2375 : List ℕ := [f19,f20,f300,f22,f23,f217,f24]
def e2376 : List ℕ := [f19,f20,f21,f300,f22,f217,f24]
def e2377 : List ℕ := [f19,f20,f218,f300,f22,f23,f24]
def e2378 : List ℕ := [f19,f20,f21,f300,f22,f219,f24]
def e2379 : List ℕ := [f19,f20,f21,f300,f22,f23,f228]
def e2380 : List ℕ := [f19,f20,f21,f300,f22,f23,f230]
def e2381 : List ℕ := [f231,f19,f20,f21,f22,f23,f24]
def e2382 : List ℕ := [f19,f20,f21,f22,f23,f510,f24]
def e2383 : List ℕ := [f19,f20,f21,f511,f22,f23,f24]
def e2384 : List ℕ := [f19,f20,f21,f22,f234,f23,f24]
def e2385 : List ℕ := [f235,f19,f20,f21,f22,f23,f24]
def e2386 : List ℕ := [f19,f20,f21,f22,f23,f24,f512]
def e2387 : List ℕ := [f19,f20,f21,f485,f22,f23,f24]
def e2388 : List ℕ := [f19,f20,f21,f22,f23,f250,f24]
def e2389 : List ℕ := [f19,f20,f21,f300,f23,f232,f24]
def e2390 : List ℕ := [f19,f20,f21,f300,f233,f23,f24]
def e2391 : List ℕ := [f19,f20,f21,f300,f23,f24,f203]
def e2392 : List ℕ := [f19,f20,f21,f204,f300,f23,f24]
def e2393 : List ℕ := [f19,f20,f21,f300,f22,f24,f207]
def e2394 : List ℕ := [f19,f20,f21,f300,f22,f23,f207]
def e2395 : List ℕ := [f208,f19,f20,f21,f300,f22,f24]
def e2396 : List ℕ := [f19,f20,f21,f300,f22,f209,f23]
def e2397 : List ℕ := [f301,f19,f20,f21,f22,f23,f24]
def e2398 : List ℕ := [f20,f21,f22,f23,f302,f24]
def e2399 : List ℕ := [f19,f20,f21,f22,f302,f24]
def e2400 : List ℕ := [f19,f20,f21,f22,f23,f302,f24]
def e2401 : List ℕ := [f303,f20,f21,f22,f23,f24]
def e2402 : List ℕ := [f303,f19,f20,f21,f22,f23,f24]
def e2403 : List ℕ := [f19,f20,f21,f22,f304,f24]
def e2404 : List ℕ := [f19,f20,f21,f22,f304,f23,f24]
def e2405 : List ℕ := [f305,f19,f20,f21,f22,f23,f24]
def e2406 : List ℕ := [f19,f20,f21,f22,f23,f306]
def e2407 : List ℕ := [f19,f20,f21,f22,f23,f24,f306]
def e2408 : List ℕ := [f307,f19,f20,f21,f22,f23,f24]
def e2409 : List ℕ := [f19,f20,f21,f22,f23,f308]
def e2410 : List ℕ := [f19,f20,f21,f22,f23,f308,f24]
def e2411 : List ℕ := [f19,f21,f133,f22,f23,f24]
def e2412 : List ℕ := [f19,f20,f21,f133,f22,f23,f24]
def e2413 : List ℕ := [f19,f134,f21,f22,f23,f24]
def e2414 : List ℕ := [f19,f134,f20,f21,f22,f23,f24]
def e2730 : List ℕ := [f9,f30,f80,f31]
def e2734 : List ℕ := [f545,f4,f11,f7]
def e2735 : List ℕ := [f546,f20,f21,f22,f23,f24]
def e2736 : List ℕ := [f19,f546,f20,f21,f22,f23,f24]
def e2737 : List ℕ := [f136,f546,f20,f21,f22,f23,f24]
def e2738 : List ℕ := [f29,f13,f178,f11,f7]
def e2739 : List ℕ := [f136,f19,f148,f21,f22,f23,f24]
def e2740 : List ℕ := [f19,f20,f547,f22,f23,f24]
def e2741 : List ℕ := [f19,f20,f21,f547,f22,f23,f24]
def e2742 : List ℕ := [f136,f19,f20,f547,f22,f23,f24]
def e2743 : List ℕ := [f136,f19,f20,f21,f149,f23,f24]
def e2757 : List ℕ := [f20,f130,f21,f22,f548,f24]
def e2758 : List ℕ := [f19,f130,f21,f22,f548,f24]
def e2759 : List ℕ := [f129,f20,f21,f22,f548,f24]
def e2760 : List ℕ := [f281,f19,f21,f22,f548,f24]
def e2761 : List ℕ := [f20,f21,f287,f22,f548,f24]
def e2762 : List ℕ := [f19,f20,f287,f22,f548,f24]
def e2763 : List ℕ := [f288,f20,f21,f22,f548,f24]
def e2764 : List ℕ := [f19,f20,f289,f22,f548,f24]
def e2765 : List ℕ := [f19,f20,f21,f298,f548,f24]
def e2766 : List ℕ := [f19,f20,f21,f300,f548,f24]
def e2767 : List ℕ := [f20,f21,f22,f548,f549,f24]
def e2768 : List ℕ := [f19,f20,f21,f22,f549,f24]
def e2769 : List ℕ := [f303,f20,f21,f22,f548,f24]
def e2770 : List ℕ := [f19,f20,f21,f22,f550,f24]
def e2771 : List ℕ := [f19,f20,f21,f22,f548,f306]
def e2772 : List ℕ := [f19,f20,f21,f22,f548,f308]
def e2773 : List ℕ := [f19,f21,f133,f22,f548,f24]
def e2774 : List ℕ := [f19,f134,f21,f22,f548,f24]
def e2775 : List ℕ := [f19,f21,f22,f137,f548,f24]
def e2776 : List ℕ := [f19,f20,f21,f137,f548,f24]
def e2777 : List ℕ := [f19,f148,f21,f22,f548,f24]
def e2778 : List ℕ := [f19,f20,f21,f149,f548,f24]
def e2779 : List ℕ := [f19,f21,f22,f548,f151,f24]
def e2780 : List ℕ := [f19,f551,f21,f22,f548,f24]
def e2781 : List ℕ := [f154,f19,f21,f22,f548,f24]
def e2782 : List ℕ := [f19,f21,f22,f548,f157,f24]
def e2783 : List ℕ := [f19,f20,f22,f201,f548,f24]
def e2784 : List ℕ := [f19,f20,f21,f201,f548,f24]
def e2785 : List ℕ := [f202,f19,f20,f22,f548,f24]
def e2786 : List ℕ := [f19,f20,f214,f21,f548,f24]
def e2787 : List ℕ := [f19,f20,f22,f548,f552,f24]
def e2788 : List ℕ := [f19,f20,f21,f22,f552,f24]
def e2789 : List ℕ := [f19,f20,f218,f22,f548,f24]
def e2790 : List ℕ := [f19,f20,f21,f22,f553,f24]
def e2791 : List ℕ := [f19,f20,f21,f22,f548,f228]
def e2792 : List ℕ := [f19,f20,f21,f22,f548,f230]
def e2793 : List ℕ := [f19,f20,f21,f548,f232,f24]
def e2794 : List ℕ := [f19,f20,f21,f554,f548,f24]
def e2795 : List ℕ := [f235,f19,f20,f21,f548,f24]
def e2796 : List ℕ := [f19,f20,f21,f548,f250,f24]
def e2797 : List ℕ := [f19,f20,f21,f22,f24,f555]
def e2798 : List ℕ := [f19,f20,f21,f22,f548,f555]
def e2799 : List ℕ := [f556,f19,f20,f21,f22,f24]
def e2800 : List ℕ := [f19,f20,f21,f22,f209,f548]
def e2801 : List ℕ := [f19,f20,f21,f22,f548,f24]
def e2802 : List ℕ := [f19,f20,f21,f22,f23,f548,f24]
def e2803 : List ℕ := [f136,f19,f20,f21,f22,f548,f24]
def e2809 : List ℕ := [f72,f35,f252,f62,f86]
def e2810 : List ℕ := [f35,f252,f124,f86]
def e2811 : List ℕ := [f35,f252,f124,f62,f86]
def e2812 : List ℕ := [f117,f35,f252,f62,f86]
def e2813 : List ℕ := [f252,f62,f86,f104]
def e2814 : List ℕ := [f35,f252,f62,f104]
def e2815 : List ℕ := [f35,f252,f62,f86,f104]
def e2816 : List ℕ := [f77,f252,f62,f86]
def e2817 : List ℕ := [f77,f35,f252,f62,f86]
def e2818 : List ℕ := [f35,f252,f62,f118]
def e2819 : List ℕ := [f35,f252,f62,f118,f86]
def e2820 : List ℕ := [f69,f35,f252,f62,f86]
def e2821 : List ℕ := [f35,f62,f86,f318]
def e2822 : List ℕ := [f35,f252,f86,f318]
def e2823 : List ℕ := [f35,f252,f62,f86,f318]
def e2824 : List ℕ := [f35,f256,f62,f86]
def e2825 : List ℕ := [f35,f256,f252,f62,f86]
def e2826 : List ℕ := [f35,f252,f89,f86]
def e2827 : List ℕ := [f35,f252,f89,f62,f86]
def e2828 : List ℕ := [f47,f35,f252,f62,f86]
def e2829 : List ℕ := [f35,f252,f62,f86,f319]
def e2830 : List ℕ := [f320,f35,f252,f62,f86]
def e2831 : List ℕ := [f35,f252,f91,f62,f86]
def e2832 : List ℕ := [f35,f252,f261,f62,f86]
def e2833 : List ℕ := [f35,f252,f62,f86,f98]
def e2834 : List ℕ := [f99,f35,f252,f62,f86]
def e2835 : List ℕ := [f65,f35,f252,f62,f86]
def e2836 : List ℕ := [f35,f252,f62,f86]
def e2837 : List ℕ := [f252,f36,f62,f86,f558]
def e2838 : List ℕ := [f35,f36,f62,f86,f558]
def e2839 : List ℕ := [f253,f252,f62,f86,f558]
def e2840 : List ℕ := [f40,f35,f62,f86,f558]
def e2841 : List ℕ := [f252,f62,f86,f103,f558]
def e2842 : List ℕ := [f35,f252,f86,f103,f558]
def e2843 : List ℕ := [f72,f252,f62,f86,f558]
def e2844 : List ℕ := [f35,f252,f124,f86,f558]
def e2845 : List ℕ := [f252,f62,f104,f558]
def e2846 : List ℕ := [f252,f62,f86,f104,f558]
def e2847 : List ℕ := [f35,f252,f62,f104,f558]
def e2848 : List ℕ := [f77,f252,f62,f86,f558]
def e2849 : List ℕ := [f35,f252,f62,f118,f558]
def e2850 : List ℕ := [f237,f252,f62,f86,f558]
def e2851 : List ℕ := [f237,f35,f252,f62,f86]
def e2852 : List ℕ := [f35,f252,f62,f86,f147]
def e2853 : List ℕ := [f120,f35,f252,f62,f86]
def e2854 : List ℕ := [f252,f62,f86,f106,f558]
def e2855 : List ℕ := [f35,f252,f62,f86,f106]
def e2856 : List ℕ := [f35,f86,f318,f558]
def e2857 : List ℕ := [f35,f62,f86,f318,f558]
def e2858 : List ℕ := [f35,f252,f86,f318,f558]
def e2859 : List ℕ := [f35,f256,f62,f86,f558]
def e2860 : List ℕ := [f35,f252,f89,f86,f558]
def e2861 : List ℕ := [f35,f62,f86,f319,f558]
def e2862 : List ℕ := [f35,f252,f62,f319,f558]
def e2863 : List ℕ := [f320,f35,f62,f86,f558]
def e2864 : List ℕ := [f35,f252,f91,f62,f558]
def e2865 : List ℕ := [f102,f35,f62,f86,f558]
def e2866 : List ℕ := [f102,f35,f252,f62,f86]
def e2867 : List ℕ := [f35,f252,f62,f86,f559]
def e2868 : List ℕ := [f35,f328,f252,f62,f86]
def e2869 : List ℕ := [f35,f62,f86,f271,f558]
def e2870 : List ℕ := [f35,f252,f62,f86,f271]
def e2871 : List ℕ := [f35,f252,f86,f98,f558]
def e2872 : List ℕ := [f35,f252,f62,f98,f558]
def e2873 : List ℕ := [f99,f35,f252,f86,f558]
def e2874 : List ℕ := [f65,f35,f252,f62,f558]
def e2875 : List ℕ := [f385,f35,f252,f86,f558]
def e2876 : List ℕ := [f385,f35,f252,f62,f86]
def e2877 : List ℕ := [f35,f252,f62,f86,f59]
def e2878 : List ℕ := [f35,f252,f370,f62,f86]
def e2879 : List ℕ := [f35,f252,f86,f100,f558]
def e2880 : List ℕ := [f35,f252,f62,f86,f100]
def e2881 : List ℕ := [f279,f35,f252,f62,f558]
def e2882 : List ℕ := [f279,f35,f252,f62,f86]
def e2883 : List ℕ := [f35,f252,f62,f86,f274]
def e2884 : List ℕ := [f35,f252,f62,f373,f86]
def e2885 : List ℕ := [f35,f252,f62,f524,f558]
def e2886 : List ℕ := [f35,f252,f62,f86,f524]
def e2887 : List ℕ := [f35,f252,f62,f86,f558]
def e2888 : List ℕ := [f19,f20,f21,f22,f23,f560]
def e2889 : List ℕ := [f252,f62,f86,f103,f87]
def e2890 : List ℕ := [f35,f252,f86,f103,f87]
def e2891 : List ℕ := [f72,f252,f62,f86,f87]
def e2892 : List ℕ := [f35,f252,f124,f86,f87]
def e2893 : List ℕ := [f252,f62,f86,f104,f87]
def e2894 : List ℕ := [f35,f252,f62,f104,f87]
def e2895 : List ℕ := [f77,f252,f62,f86,f87]
def e2896 : List ℕ := [f35,f252,f62,f118,f87]
def e2897 : List ℕ := [f105,f252,f62,f86,f87]
def e2898 : List ℕ := [f105,f35,f252,f62,f86]
def e2899 : List ℕ := [f75,f35,f252,f62,f86]
def e2900 : List ℕ := [f252,f62,f86,f106,f87]
def e2901 : List ℕ := [f35,f62,f86,f318,f87]
def e2902 : List ℕ := [f35,f252,f86,f318,f87]
def e2903 : List ℕ := [f35,f256,f62,f86,f87]
def e2904 : List ℕ := [f35,f252,f89,f86,f87]
def e2905 : List ℕ := [f35,f62,f86,f319,f87]
def e2906 : List ℕ := [f35,f252,f62,f319,f87]
def e2907 : List ℕ := [f320,f35,f62,f86,f87]
def e2908 : List ℕ := [f35,f252,f91,f62,f87]
def e2909 : List ℕ := [f35,f252,f62,f86,f363]
def e2910 : List ℕ := [f35,f252,f62,f86,f93]
def e2911 : List ℕ := [f35,f252,f86,f98,f87]
def e2912 : List ℕ := [f35,f252,f62,f98,f87]
def e2913 : List ℕ := [f99,f35,f252,f86,f87]
def e2914 : List ℕ := [f65,f35,f252,f62,f87]
def e2915 : List ℕ := [f122,f35,f252,f86,f87]
def e2916 : List ℕ := [f122,f35,f252,f62,f86]
def e2917 : List ℕ := [f35,f252,f108,f62,f86]
def e2918 : List ℕ := [f35,f252,f86,f100,f87]
def e2919 : List ℕ := [f279,f35,f252,f62,f87]
def e2920 : List ℕ := [f35,f252,f62,f86,f101]
def e2921 : List ℕ := [f35,f252,f62,f38,f87]
def e2922 : List ℕ := [f35,f252,f62,f86,f38]
def e2923 : List ℕ := [f35,f252,f62,f86,f87]
def e2924 : List ℕ := [f252,f62,f104,f87,f558]
def e2925 : List ℕ := [f105,f252,f62,f86,f558]
def e2926 : List ℕ := [f237,f252,f62,f86,f87]
def e2927 : List ℕ := [f35,f86,f318,f87,f558]
def e2928 : List ℕ := [f35,f62,f86,f93,f558]
def e2929 : List ℕ := [f35,f62,f86,f87,f271]
def e2930 : List ℕ := [f122,f35,f252,f86,f558]
def e2931 : List ℕ := [f385,f35,f252,f86,f87]
def e2932 : List ℕ := [f35,f252,f62,f38,f558]
def e2933 : List ℕ := [f35,f252,f62,f87,f524]
def e2934 : List ℕ := [f35,f252,f62,f86,f87,f558]
def e2935 : List ℕ := [f19,f20,f21,f22,f23,f24,f560]
def e2936 : List ℕ := [f136,f19,f20,f21,f22,f23,f560]
def e2937 : List ℕ := [f136,f19,f20,f287,f22,f23,f24]
def e2938 : List ℕ := [f136,f19,f20,f289,f22,f23,f24]
def e2939 : List ℕ := [f136,f20,f21,f22,f23,f302,f24]
def e2940 : List ℕ := [f136,f19,f20,f21,f22,f302,f24]
def e2941 : List ℕ := [f136,f303,f20,f21,f22,f23,f24]
def e2942 : List ℕ := [f136,f19,f20,f21,f22,f304,f24]
def e2943 : List ℕ := [f136,f19,f20,f21,f22,f23,f306]
def e2944 : List ℕ := [f136,f19,f20,f21,f22,f23,f308]
def e2945 : List ℕ := [f136,f19,f21,f133,f22,f23,f24]
def e2946 : List ℕ := [f136,f19,f134,f21,f22,f23,f24]
def e2947 : List ℕ := [f29,f13,f11,f141,f7]
def e2948 : List ℕ := [f136,f19,f21,f22,f137,f23,f24]
def e2949 : List ℕ := [f136,f19,f20,f21,f137,f23,f24]
def e2950 : List ℕ := [f136,f19,f21,f22,f23,f151,f24]
def e2951 : List ℕ := [f136,f19,f152,f21,f22,f23,f24]
def e2952 : List ℕ := [f136,f154,f19,f21,f22,f23,f24]
def e2953 : List ℕ := [f136,f19,f21,f22,f23,f157,f24]
def e2954 : List ℕ := [f136,f19,f20,f22,f201,f23,f24]
def e2955 : List ℕ := [f136,f19,f20,f21,f201,f23,f24]
def e2956 : List ℕ := [f136,f202,f19,f20,f22,f23,f24]
def e2957 : List ℕ := [f136,f19,f20,f214,f21,f23,f24]
def e2958 : List ℕ := [f136,f19,f20,f22,f23,f217,f24]
def e2959 : List ℕ := [f136,f19,f20,f21,f22,f217,f24]
def e2960 : List ℕ := [f136,f19,f20,f218,f22,f23,f24]
def e2961 : List ℕ := [f136,f19,f20,f21,f22,f219,f24]
def e2962 : List ℕ := [f136,f19,f20,f21,f22,f23,f228]
def e2963 : List ℕ := [f136,f19,f20,f21,f22,f23,f230]
def e2964 : List ℕ := [f136,f19,f20,f21,f23,f232,f24]
def e2965 : List ℕ := [f136,f19,f20,f21,f233,f23,f24]
def e2966 : List ℕ := [f136,f235,f19,f20,f21,f23,f24]
def e2967 : List ℕ := [f136,f19,f20,f21,f23,f250,f24]
def e2968 : List ℕ := [f136,f19,f20,f21,f22,f24,f207]
def e2969 : List ℕ := [f136,f19,f20,f21,f22,f23,f207]
def e2970 : List ℕ := [f136,f208,f19,f20,f21,f22,f24]
def e2971 : List ℕ := [f136,f19,f20,f21,f22,f209,f23]
def e2972 : List ℕ := [f19,f20,f287,f22,f137,f23,f24]
def e2973 : List ℕ := [f19,f20,f289,f22,f137,f23,f24]
def e2974 : List ℕ := [f561,f19,f20,f21,f22,f23,f24]
def e2975 : List ℕ := [f358,f19,f20,f21,f22,f23,f24]
def e2976 : List ℕ := [f19,f20,f21,f22,f562,f23,f24]
def e2977 : List ℕ := [f20,f21,f22,f137,f23,f302,f24]
def e2978 : List ℕ := [f19,f20,f21,f22,f137,f302,f24]
def e2979 : List ℕ := [f303,f20,f21,f22,f137,f23,f24]
def e2980 : List ℕ := [f19,f20,f21,f22,f137,f304,f24]
def e2981 : List ℕ := [f19,f20,f21,f22,f137,f23,f306]
def e2982 : List ℕ := [f19,f20,f21,f22,f137,f23,f308]
def e2983 : List ℕ := [f19,f21,f133,f22,f137,f23,f24]
def e2984 : List ℕ := [f19,f134,f21,f22,f137,f23,f24]
def e2985 : List ℕ := [f19,f148,f20,f21,f137,f23,f24]
def e2986 : List ℕ := [f19,f21,f149,f22,f137,f23,f24]
def e2987 : List ℕ := [f19,f21,f22,f137,f23,f151,f24]
def e2988 : List ℕ := [f19,f152,f21,f22,f137,f23,f24]
def e2996 : List ℕ := [f62,f86,f103,f318,f87]
def e2997 : List ℕ := [f256,f62,f86,f103,f87]
def e2998 : List ℕ := [f252,f62,f103,f319,f87]
def e2999 : List ℕ := [f252,f91,f62,f103,f87]
def e3000 : List ℕ := [f252,f62,f322,f86,f87]
def e3001 : List ℕ := [f102,f62,f86,f103,f87]
def e3002 : List ℕ := [f102,f252,f62,f86,f103]
def e3003 : List ℕ := [f252,f62,f86,f103,f363]
def e3004 : List ℕ := [f328,f252,f62,f86,f103]
def e3005 : List ℕ := [f62,f86,f103,f93,f87]
def e3006 : List ℕ := [f252,f62,f86,f103,f93]
def e3007 : List ℕ := [f72,f252,f86,f103,f87]
def e3008 : List ℕ := [f122,f252,f62,f86,f103]
def e3009 : List ℕ := [f252,f86,f103,f59]
def e3010 : List ℕ := [f252,f86,f103,f87,f59]
def e3011 : List ℕ := [f252,f62,f86,f103,f59]
def e3012 : List ℕ := [f252,f108,f86,f103]
def e3013 : List ℕ := [f252,f108,f86,f103,f87]
def e3014 : List ℕ := [f252,f108,f62,f86,f103]
def e3015 : List ℕ := [f252,f62,f86,f103,f100]
def e3016 : List ℕ := [f252,f62,f86,f323,f87]
def e3017 : List ℕ := [f324,f252,f62,f86,f87]
def e3018 : List ℕ := [f279,f252,f62,f86,f103]
def e3019 : List ℕ := [f252,f62,f86,f103,f101]
def e3020 : List ℕ := [f252,f62,f373,f86,f103]
def e3021 : List ℕ := [f252,f62,f86,f103,f38]
def e3022 : List ℕ := [f111,f252,f62,f86,f87]
def e3023 : List ℕ := [f111,f252,f62,f86,f103]
def e3024 : List ℕ := [f252,f62,f86,f103,f112]
def e3025 : List ℕ := [f252,f62,f86,f113,f103]
def e3026 : List ℕ := [f252,f62,f86,f375,f87]
def e3027 : List ℕ := [f252,f62,f86,f103,f375]
def e3028 : List ℕ := [f47,f252,f86,f103,f147]
def e3029 : List ℕ := [f252,f103,f319,f147]
def e3030 : List ℕ := [f252,f86,f103,f319,f147]
def e3031 : List ℕ := [f320,f86,f103,f147]
def e3032 : List ℕ := [f320,f252,f86,f103,f147]
def e3033 : List ℕ := [f252,f91,f103,f147]
def e3034 : List ℕ := [f252,f91,f86,f103,f147]
def e3035 : List ℕ := [f321,f252,f86,f103,f147]
def e3036 : List ℕ := [f252,f86,f103,f94,f147]
def e3037 : List ℕ := [f42,f252,f86,f103,f147]
def e3038 : List ℕ := [f252,f322,f86,f103,f147]
def e3039 : List ℕ := [f330,f86,f103,f147]
def e3040 : List ℕ := [f330,f252,f86,f103,f147]
def e3041 : List ℕ := [f252,f86,f103,f147,f535]
def e3042 : List ℕ := [f45,f252,f86,f103,f147]
def e3043 : List ℕ := [f86,f103,f564,f147]
def e3044 : List ℕ := [f252,f86,f103,f564,f147]
def e3045 : List ℕ := [f252,f109,f86,f103,f147]
def e3046 : List ℕ := [f252,f103,f323,f147]
def e3047 : List ℕ := [f252,f86,f323,f147]
def e3048 : List ℕ := [f252,f86,f103,f323,f147]
def e3049 : List ℕ := [f110,f252,f103,f147]
def e3050 : List ℕ := [f110,f252,f86,f103,f147]
def e3051 : List ℕ := [f324,f252,f86,f147]
def e3052 : List ℕ := [f324,f252,f86,f103,f147]
def e3053 : List ℕ := [f565,f252,f103,f147]
def e3054 : List ℕ := [f565,f252,f86,f103,f147]
def e3055 : List ℕ := [f252,f86,f103,f147,f566]
def e3056 : List ℕ := [f252,f534,f86,f103,f147]
def e3057 : List ℕ := [f252,f103,f567,f147]
def e3058 : List ℕ := [f252,f86,f103,f567,f147]
def e3059 : List ℕ := [f568,f252,f86,f147]
def e3060 : List ℕ := [f568,f252,f86,f103]
def e3061 : List ℕ := [f568,f252,f86,f103,f147]
def e3062 : List ℕ := [f252,f86,f103,f147,f112]
def e3063 : List ℕ := [f252,f370,f86,f103]
def e3064 : List ℕ := [f252,f370,f86,f103,f147]
def e3065 : List ℕ := [f252,f86,f375,f147]
def e3066 : List ℕ := [f252,f86,f103,f375,f147]
def e3067 : List ℕ := [f252,f86,f103,f147]
def e3068 : List ℕ := [f69,f252,f86,f103,f147]
def e3069 : List ℕ := [f62,f86,f103,f318,f147]
def e3070 : List ℕ := [f252,f86,f103,f318,f147]
def e3071 : List ℕ := [f256,f86,f103,f147]
def e3072 : List ℕ := [f256,f62,f86,f103,f147]
def e3073 : List ℕ := [f256,f252,f86,f103,f147]
def e3074 : List ℕ := [f252,f89,f86,f103,f147]
def e3075 : List ℕ := [f252,f62,f103,f319,f147]
def e3076 : List ℕ := [f320,f62,f86,f103,f147]
def e3077 : List ℕ := [f252,f91,f62,f103,f147]
def e3078 : List ℕ := [f330,f62,f86,f103,f147]
def e3079 : List ℕ := [f330,f252,f62,f86,f103]
def e3080 : List ℕ := [f252,f62,f86,f103,f535]
def e3081 : List ℕ := [f45,f252,f62,f86,f103]
def e3082 : List ℕ := [f62,f86,f103,f564,f147]
def e3083 : List ℕ := [f252,f62,f86,f103,f564]
def e3084 : List ℕ := [f252,f261,f86,f103,f147]
def e3085 : List ℕ := [f252,f98,f103,f147]
def e3086 : List ℕ := [f252,f86,f98,f103,f147]
def e3087 : List ℕ := [f252,f62,f98,f103,f147]
def e3088 : List ℕ := [f99,f252,f86,f103,f147]
def e3089 : List ℕ := [f65,f252,f103,f147]
def e3090 : List ℕ := [f65,f252,f86,f103,f147]
def e3091 : List ℕ := [f65,f252,f62,f103,f147]
def e3092 : List ℕ := [f72,f252,f86,f103,f147]
def e3093 : List ℕ := [f72,f252,f62,f86,f147]
def e3094 : List ℕ := [f385,f252,f86,f103,f147]
def e3095 : List ℕ := [f385,f252,f62,f86,f103]
def e3096 : List ℕ := [f252,f370,f62,f86,f103]
def e3097 : List ℕ := [f252,f86,f103,f569]
def e3098 : List ℕ := [f252,f86,f103,f569,f147]
def e3099 : List ℕ := [f252,f62,f86,f103,f569]
def e3100 : List ℕ := [f252,f62,f323,f147]
def e3101 : List ℕ := [f252,f62,f103,f323,f147]
def e3102 : List ℕ := [f252,f62,f86,f323,f147]
def e3103 : List ℕ := [f110,f252,f62,f103,f147]
def e3104 : List ℕ := [f324,f252,f62,f86,f147]
def e3105 : List ℕ := [f565,f252,f62,f103,f147]
def e3106 : List ℕ := [f565,f252,f62,f86,f103]
def e3107 : List ℕ := [f252,f62,f86,f103,f566]
def e3108 : List ℕ := [f252,f62,f534,f86,f103]
def e3109 : List ℕ := [f252,f62,f103,f567,f147]
def e3110 : List ℕ := [f252,f62,f86,f103,f567]
def e3111 : List ℕ := [f568,f252,f62,f86]
def e3112 : List ℕ := [f568,f252,f62,f86,f147]
def e3113 : List ℕ := [f568,f252,f62,f86,f103]
def e3114 : List ℕ := [f252,f62,f86,f375,f147]
def e3115 : List ℕ := [f252,f62,f86,f103,f147]
def e3116 : List ℕ := [f252,f103,f319,f87,f147]
def e3117 : List ℕ := [f320,f86,f103,f87,f147]
def e3118 : List ℕ := [f252,f91,f103,f87,f147]
def e3119 : List ℕ := [f252,f86,f94,f87,f147]
def e3120 : List ℕ := [f252,f322,f86,f87,f147]
def e3121 : List ℕ := [f102,f252,f86,f103,f147]
def e3122 : List ℕ := [f252,f86,f103,f147,f363]
def e3123 : List ℕ := [f328,f252,f86,f103,f147]
def e3124 : List ℕ := [f252,f86,f103,f93,f147]
def e3125 : List ℕ := [f330,f86,f103,f87,f147]
def e3126 : List ℕ := [f86,f103,f87,f564,f147]
def e3127 : List ℕ := [f252,f103,f323,f87,f147]
def e3128 : List ℕ := [f252,f86,f323,f87,f147]
def e3129 : List ℕ := [f110,f252,f103,f87,f147]
def e3130 : List ℕ := [f324,f252,f86,f87,f147]
def e3131 : List ℕ := [f279,f252,f103,f147]
def e3132 : List ℕ := [f279,f252,f103,f87,f147]
def e3133 : List ℕ := [f279,f252,f86,f103,f147]
def e3134 : List ℕ := [f252,f86,f103,f147,f101]
def e3135 : List ℕ := [f252,f373,f86,f103,f147]
def e3136 : List ℕ := [f252,f103,f38,f147]
def e3137 : List ℕ := [f252,f103,f38,f87,f147]
def e3138 : List ℕ := [f252,f86,f103,f38,f147]
def e3139 : List ℕ := [f565,f252,f103,f87,f147]
def e3140 : List ℕ := [f252,f103,f87,f567,f147]
def e3141 : List ℕ := [f111,f252,f86,f87,f147]
def e3142 : List ℕ := [f111,f252,f86,f103,f147]
def e3143 : List ℕ := [f252,f86,f113,f103,f147]
def e3144 : List ℕ := [f252,f86,f375,f87,f147]
def e3145 : List ℕ := [f568,f252,f86,f87]
def e3146 : List ℕ := [f568,f252,f86,f87,f147]
def e3147 : List ℕ := [f568,f252,f86,f103,f87]
def e3148 : List ℕ := [f252,f370,f86,f103,f87]
def e3149 : List ℕ := [f75,f252,f86,f103]
def e3150 : List ℕ := [f75,f252,f86,f103,f147]
def e3151 : List ℕ := [f75,f252,f86,f103,f87]
def e3152 : List ℕ := [f252,f86,f103,f87,f147]
def e3153 : List ℕ := [f256,f86,f103,f87,f147]
def e3154 : List ℕ := [f62,f86,f103,f93,f147]
def e3155 : List ℕ := [f330,f62,f86,f103,f87]
def e3156 : List ℕ := [f62,f86,f103,f87,f564]
def e3157 : List ℕ := [f252,f98,f103,f87,f147]
def e3158 : List ℕ := [f65,f252,f103,f87,f147]
def e3159 : List ℕ := [f122,f252,f86,f103,f147]
def e3160 : List ℕ := [f252,f86,f103,f147,f59]
def e3161 : List ℕ := [f252,f108,f86,f103,f147]
def e3162 : List ℕ := [f252,f86,f103,f100,f147]
def e3163 : List ℕ := [f252,f86,f103,f87,f569]
def e3164 : List ℕ := [f252,f62,f323,f87,f147]
def e3165 : List ℕ := [f279,f252,f62,f103,f147]
def e3166 : List ℕ := [f252,f62,f103,f38,f147]
def e3167 : List ℕ := [f252,f62,f103,f87,f567]
def e3168 : List ℕ := [f568,f252,f62,f86,f87]
def e3169 : List ℕ := [f75,f252,f62,f86,f103]
def e3170 : List ℕ := [f252,f62,f86,f103,f87,f147]
def e3171 : List ℕ := [f19,f21,f22,f137,f23,f24,f155]
def e3177 : List ℕ := [f570,f5,f6,f141]
def e3178 : List ℕ := [f570,f5,f6,f141,f7]
def e3179 : List ℕ := [f19,f156,f21,f22,f137,f23,f24]
def e3180 : List ℕ := [f19,f20,f201,f137,f23,f24]
def e3181 : List ℕ := [f19,f20,f22,f201,f137,f23,f24]
def e3182 : List ℕ := [f19,f20,f21,f201,f137,f23,f24]
def e3183 : List ℕ := [f202,f19,f20,f22,f137,f23,f24]
def e3184 : List ℕ := [f19,f20,f214,f21,f137,f23,f24]
def e3185 : List ℕ := [f19,f20,f571,f21,f22,f23,f24]
def e3186 : List ℕ := [f19,f20,f21,f22,f572,f23,f24]
def e3187 : List ℕ := [f573,f19,f20,f21,f22,f23,f24]
def e3188 : List ℕ := [f19,f20,f574,f21,f22,f23,f24]
def e3189 : List ℕ := [f19,f20,f22,f137,f23,f217,f24]
def e3190 : List ℕ := [f19,f20,f21,f22,f137,f217,f24]
def e3191 : List ℕ := [f19,f20,f218,f22,f137,f23,f24]
def e3192 : List ℕ := [f19,f20,f21,f22,f137,f219,f24]
def e3193 : List ℕ := [f19,f20,f21,f22,f137,f23,f228]
def e3194 : List ℕ := [f19,f20,f21,f22,f137,f23,f230]
def e3195 : List ℕ := [f19,f20,f21,f137,f23,f232,f24]
def e3196 : List ℕ := [f19,f20,f21,f233,f137,f23,f24]
def e3197 : List ℕ := [f19,f20,f21,f137,f23,f24,f203]
def e3198 : List ℕ := [f19,f20,f21,f204,f137,f23,f24]
def e3199 : List ℕ := [f575,f19,f20,f21,f22,f24]
def e3200 : List ℕ := [f575,f19,f20,f21,f22,f23,f24]
def e3201 : List ℕ := [f575,f19,f20,f21,f22,f137,f24]
def e3202 : List ℕ := [f19,f20,f21,f22,f23,f576,f24]
def e3216 : List ℕ := [f30,f84,f80,f31]
def e3217 : List ℕ := [f19,f20,f21,f22,f580,f24]
def e3218 : List ℕ := [f8,f309,f581,f17]
def e3219 : List ℕ := [f8,f309,f581,f310,f17]
def e3220 : List ℕ := [f19,f20,f21,f22,f580,f23,f24]
def e3221 : List ℕ := [f19,f20,f21,f22,f580,f137,f24]
def e3222 : List ℕ := [f19,f20,f21,f22,f582,f23,f24]
def e3223 : List ℕ := [f583,f19,f20,f21,f22,f23]
def e3224 : List ℕ := [f583,f19,f20,f21,f22,f23,f24]
def e3225 : List ℕ := [f583,f19,f20,f21,f22,f137,f23]
def e3226 : List ℕ := [f1,f2,f3,f339]
def e3227 : List ℕ := [f19,f20,f21,f22,f23,f24,f246]
def e3228 : List ℕ := [f19,f20,f21,f22,f584,f23]
def e3229 : List ℕ := [f1,f2,f585]
def e3230 : List ℕ := [f1,f2,f585,f3]
def e3231 : List ℕ := [f19,f20,f21,f22,f584,f23,f24]
def e3232 : List ℕ := [f19,f20,f21,f22,f584,f137,f23]
def e3233 : List ℕ := [f19,f20,f21,f22,f23,f586,f24]
def e3234 : List ℕ := [f19,f20,f21,f22,f137,f24,f207]
def e3235 : List ℕ := [f19,f20,f21,f22,f137,f23,f207]
def e3236 : List ℕ := [f208,f19,f20,f21,f22,f137,f24]
def e3237 : List ℕ := [f19,f20,f21,f22,f137,f209,f23]
def e3238 : List ℕ := [f19,f20,f21,f22,f137,f23,f24]
def e3462 : List ℕ := [f606,f4,f11,f7]
def e3463 : List ℕ := [f20,f607,f21,f22,f23,f24]
def e3464 : List ℕ := [f148,f20,f607,f21,f22,f23,f24]
def e3465 : List ℕ := [f19,f20,f607,f21,f22,f23,f24]
def e3466 : List ℕ := [f19,f148,f20,f287,f22,f23,f24]
def e3467 : List ℕ := [f19,f148,f20,f289,f22,f23,f24]
def e3468 : List ℕ := [f148,f20,f21,f22,f23,f302,f24]
def e3469 : List ℕ := [f19,f148,f20,f21,f22,f302,f24]
def e3470 : List ℕ := [f303,f148,f20,f21,f22,f23,f24]
def e3471 : List ℕ := [f19,f148,f20,f21,f22,f304,f24]
def e3472 : List ℕ := [f19,f148,f20,f21,f22,f23,f306]
def e3473 : List ℕ := [f19,f148,f20,f21,f22,f23,f308]
def e3474 : List ℕ := [f19,f20,f21,f608,f22,f23,f24]
def e3475 : List ℕ := [f19,f609,f20,f21,f22,f23,f24]
def e3476 : List ℕ := [f19,f20,f21,f22,f23,f610,f24]
def e3477 : List ℕ := [f19,f551,f20,f21,f22,f23,f24]
def e3478 : List ℕ := [f1,f2,f3,f346]
def e3479 : List ℕ := [f19,f20,f21,f22,f23,f24,f611]
def e3480 : List ℕ := [f19,f247,f20,f21,f22,f23,f24]
def e3481 : List ℕ := [f19,f148,f21,f133,f22,f23,f24]
def e3482 : List ℕ := [f19,f148,f134,f21,f22,f23,f24]
def e3483 : List ℕ := [f0,f311,f2,f3]
def e3484 : List ℕ := [f19,f148,f21,f149,f22,f23,f24]
def e3485 : List ℕ := [f19,f148,f20,f21,f149,f23,f24]
def e3486 : List ℕ := [f19,f148,f21,f22,f23,f151,f24]
def e3487 : List ℕ := [f19,f148,f152,f21,f22,f23,f24]
def e3488 : List ℕ := [f19,f148,f21,f22,f23,f24,f155]
def e3489 : List ℕ := [f341,f0,f2,f3]
def e3490 : List ℕ := [f19,f156,f148,f21,f22,f23,f24]
def e3491 : List ℕ := [f19,f148,f20,f22,f201,f23,f24]
def e3492 : List ℕ := [f19,f148,f20,f21,f201,f23,f24]
def e3493 : List ℕ := [f202,f19,f148,f20,f22,f23,f24]
def e3494 : List ℕ := [f19,f148,f20,f214,f21,f23,f24]
def e3495 : List ℕ := [f19,f148,f20,f22,f23,f217,f24]
def e3496 : List ℕ := [f19,f148,f20,f21,f22,f217,f24]
def e3497 : List ℕ := [f19,f148,f20,f218,f22,f23,f24]
def e3498 : List ℕ := [f19,f148,f20,f21,f22,f219,f24]
def e3499 : List ℕ := [f19,f148,f20,f21,f22,f23,f228]
def e3500 : List ℕ := [f19,f148,f20,f21,f22,f23,f230]
def e3501 : List ℕ := [f19,f148,f20,f21,f23,f232,f24]
def e3502 : List ℕ := [f19,f148,f20,f21,f233,f23,f24]
def e3503 : List ℕ := [f235,f19,f148,f20,f21,f23,f24]
def e3504 : List ℕ := [f19,f148,f20,f21,f23,f250,f24]
def e3505 : List ℕ := [f19,f148,f20,f21,f22,f24,f207]
def e3506 : List ℕ := [f19,f148,f20,f21,f22,f23,f207]
def e3507 : List ℕ := [f208,f19,f148,f20,f21,f22,f24]
def e3508 : List ℕ := [f19,f148,f20,f21,f22,f209,f23]
def e3509 : List ℕ := [f19,f21,f22,f23,f151,f24]
def e3510 : List ℕ := [f19,f20,f21,f22,f23,f151,f24]
def e3511 : List ℕ := [f19,f152,f21,f22,f23,f24]
def e3512 : List ℕ := [f19,f152,f20,f21,f22,f23,f24]
def e3513 : List ℕ := [f19,f20,f21,f22,f23,f24,f155]
def e3514 : List ℕ := [f19,f156,f20,f21,f22,f23,f24]
def e3515 : List ℕ := [f19,f20,f22,f201,f23,f24]
def e3516 : List ℕ := [f19,f20,f21,f201,f23,f24]
def e3517 : List ℕ := [f19,f20,f21,f22,f201,f23,f24]
def e3518 : List ℕ := [f19,f20,f214,f21,f23,f24]
def e3519 : List ℕ := [f19,f20,f214,f21,f22,f23,f24]
def e3520 : List ℕ := [f215,f19,f20,f21,f22,f23,f24]
def e3521 : List ℕ := [f19,f20,f22,f23,f217,f24]
def e3522 : List ℕ := [f19,f20,f21,f22,f217,f24]
def e3523 : List ℕ := [f19,f20,f21,f22,f23,f217,f24]
def e3524 : List ℕ := [f19,f20,f218,f22,f23,f24]
def e3525 : List ℕ := [f19,f20,f218,f21,f22,f23,f24]
def e3526 : List ℕ := [f19,f20,f21,f22,f219,f24]
def e3527 : List ℕ := [f19,f20,f21,f22,f219,f23,f24]
def e3528 : List ℕ := [f220,f19,f20,f21,f22,f23,f24]
def e3529 : List ℕ := [f19,f20,f21,f22,f23,f228]
def e3530 : List ℕ := [f19,f20,f21,f22,f23,f24,f228]
def e3531 : List ℕ := [f19,f20,f229,f21,f22,f23,f24]
def e3532 : List ℕ := [f19,f20,f21,f22,f23,f230]
def e3533 : List ℕ := [f19,f20,f21,f22,f23,f230,f24]
def e3534 : List ℕ := [f19,f20,f21,f23,f232,f24]
def e3535 : List ℕ := [f19,f20,f21,f22,f23,f232,f24]
def e3536 : List ℕ := [f19,f20,f21,f233,f23,f24]
def e3537 : List ℕ := [f19,f20,f21,f233,f22,f23,f24]
def e3538 : List ℕ := [f19,f20,f21,f22,f23,f24,f203]
def e3539 : List ℕ := [f19,f20,f21,f204,f22,f23,f24]
def e3540 : List ℕ := [f19,f20,f21,f22,f251,f23,f24]
def e3541 : List ℕ := [f19,f20,f21,f22,f24,f207]
def e3542 : List ℕ := [f19,f20,f21,f22,f23,f207]
def e3543 : List ℕ := [f19,f20,f21,f22,f23,f24,f207]
def e3544 : List ℕ := [f208,f19,f20,f21,f22,f24]
def e3545 : List ℕ := [f208,f19,f20,f21,f22,f23,f24]
def e3546 : List ℕ := [f19,f20,f21,f22,f209,f23]
def e3547 : List ℕ := [f19,f20,f21,f22,f209,f23,f24]
def e3548 : List ℕ := [f19,f20,f21,f22,f23,f24]
theorem b0:B 12 3 e0:=viaSmall (by decide +kernel) (by decide)
theorem b16:B 12 3 e16:=viaSmall (by decide +kernel) (by decide)
theorem w17:W 12 3 e16:=widen (by decide +kernel) b16
theorem b18:B 87 7 e17:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b24:B 35 4 e22:=viaSmall (by decide +kernel) (by decide)
theorem b64:B 35 4 e56:=viaSmall (by decide +kernel) (by decide)
theorem b92:B 35 4 e87:=viaSmall (by decide +kernel) (by decide)
theorem b108:B 6 2 e102:=viaSmall (by decide +kernel) (by decide)
theorem b109:B 16 3 e103:=viaSmall (by decide +kernel) (by decide)
theorem b110:B 16 3 e104:=viaSmall (by decide +kernel) (by decide)
theorem w111:W 16 3 e104:=viaSub (ws:=[e103,e104]) (consBan b109 (consBan b110 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b120:B 35 4 e112:=viaSmall (by decide +kernel) (by decide)
theorem b121:B 35 4 e113:=viaSmall (by decide +kernel) (by decide)
theorem b125:B 35 4 e117:=viaSmall (by decide +kernel) (by decide)
theorem b137:B 35 4 e129:=viaSmall (by decide +kernel) (by decide)
theorem b138:B 35 4 e130:=viaSmall (by decide +kernel) (by decide)
theorem b161:B 35 4 e146:=viaSmall (by decide +kernel) (by decide)
theorem b165:B 35 4 e150:=viaSmall (by decide +kernel) (by decide)
theorem b171:B 35 4 e156:=viaSmall (by decide +kernel) (by decide)
theorem b173:B 35 4 e158:=viaSmall (by decide +kernel) (by decide)
theorem b175:B 35 4 e160:=viaSmall (by decide +kernel) (by decide)
theorem b185:B 35 4 e170:=viaSmall (by decide +kernel) (by decide)
theorem b204:B 16 3 e188:=viaSmall (by decide +kernel) (by decide)
theorem w205:W 16 3 e188:=widen (by decide +kernel) b204
theorem b207:B 35 4 e190:=viaSmall (by decide +kernel) (by decide)
theorem b208:B 35 4 e191:=viaSmall (by decide +kernel) (by decide)
theorem b209:B 35 4 e192:=viaSmall (by decide +kernel) (by decide)
theorem b210:B 35 4 e193:=viaSmall (by decide +kernel) (by decide)
theorem b211:B 35 4 e194:=viaSmall (by decide +kernel) (by decide)
theorem b212:B 35 4 e195:=viaSmall (by decide +kernel) (by decide)
theorem b213:B 35 4 e196:=viaSmall (by decide +kernel) (by decide)
theorem b214:B 35 4 e197:=viaSmall (by decide +kernel) (by decide)
theorem b215:B 35 4 e198:=viaSmall (by decide +kernel) (by decide)
theorem b216:B 35 4 e199:=viaSmall (by decide +kernel) (by decide)
theorem b217:B 35 4 e200:=viaSmall (by decide +kernel) (by decide)
theorem b218:B 35 4 e201:=viaSmall (by decide +kernel) (by decide)
theorem b219:B 35 4 e202:=viaSmall (by decide +kernel) (by decide)
theorem b220:B 35 4 e203:=viaSmall (by decide +kernel) (by decide)
theorem b221:B 35 4 e204:=viaSmall (by decide +kernel) (by decide)
theorem b222:B 35 4 e205:=viaSmall (by decide +kernel) (by decide)
theorem b223:B 35 4 e206:=viaSmall (by decide +kernel) (by decide)
theorem b224:B 35 4 e207:=viaSmall (by decide +kernel) (by decide)
theorem b225:B 35 4 e208:=viaSmall (by decide +kernel) (by decide)
theorem b226:B 35 4 e209:=viaSmall (by decide +kernel) (by decide)
theorem b227:B 35 4 e210:=viaSmall (by decide +kernel) (by decide)
theorem b228:B 35 4 e211:=viaSmall (by decide +kernel) (by decide)
theorem b229:B 35 4 e212:=viaSmall (by decide +kernel) (by decide)
theorem b230:B 35 4 e213:=viaSmall (by decide +kernel) (by decide)
theorem b231:B 35 4 e214:=viaSmall (by decide +kernel) (by decide)
theorem b232:B 35 4 e215:=viaSmall (by decide +kernel) (by decide)
theorem b233:B 35 4 e216:=viaSmall (by decide +kernel) (by decide)
theorem b234:B 35 4 e217:=viaSmall (by decide +kernel) (by decide)
theorem b235:B 35 4 e218:=viaSmall (by decide +kernel) (by decide)
theorem b236:B 35 4 e219:=viaSmall (by decide +kernel) (by decide)
theorem b237:B 35 4 e220:=viaSmall (by decide +kernel) (by decide)
theorem b238:B 35 4 e221:=viaSmall (by decide +kernel) (by decide)
theorem b239:B 35 4 e222:=viaSmall (by decide +kernel) (by decide)
theorem b240:B 35 4 e223:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b241:B 35 5 e224:=viaBranch (ws:=[e190,e191,e192,e193,e194,e195,e196,e197,e198,e117,e199,e200,e201,e202,e203,e204,e205,e206,e207,e208,e209,e210,e211,e212,e213,e214,e215,e216,e217,e218,e219,e220,e221,e222,e223]) (consBan b207 (consBan b208 (consBan b209 (consBan b210 (consBan b211 (consBan b212 (consBan b213 (consBan b214 (consBan b215 (consBan b125 (consBan b216 (consBan b217 (consBan b218 (consBan b219 (consBan b220 (consBan b221 (consBan b222 (consBan b223 (consBan b224 (consBan b225 (consBan b226 (consBan b227 (consBan b228 (consBan b229 (consBan b230 (consBan b231 (consBan b232 (consBan b233 (consBan b234 (consBan b235 (consBan b236 (consBan b237 (consBan b238 (consBan b239 (consBan b240 (nilBan _ _)))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b242:B 6 2 e102:=viaSmall (by decide +kernel) (by decide)
theorem b246:B 35 4 e225:=viaSmall (by decide +kernel) (by decide)
theorem b247:B 35 4 e226:=viaSmall (by decide +kernel) (by decide)
theorem b248:B 35 4 e227:=viaSmall (by decide +kernel) (by decide)
theorem b249:B 35 4 e228:=viaSmall (by decide +kernel) (by decide)
theorem b250:B 35 4 e229:=viaPerm pc0_0 pci0_0 b222 (by decide +kernel) (by decide +kernel)
theorem b251:B 35 4 e230:=viaSmall (by decide +kernel) (by decide)
theorem b252:B 35 4 e231:=viaSmall (by decide +kernel) (by decide)
theorem b253:B 35 4 e232:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b254:B 35 5 e233:=viaBranch (ws:=[e160,e208,e225,e226,e227,e228,e150,e229,e230,e231,e232]) (consBan b175 (consBan b225 (consBan b246 (consBan b247 (consBan b248 (consBan b249 (consBan b165 (consBan b250 (consBan b251 (consBan b252 (consBan b253 (nilBan _ _)))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b256:B 35 4 e235:=viaSmall (by decide +kernel) (by decide)
theorem b257:B 35 4 e236:=viaSmall (by decide +kernel) (by decide)
theorem b258:B 35 4 e224:=viaSmall (by decide +kernel) (by decide)
theorem b259:B 35 4 e237:=viaSmall (by decide +kernel) (by decide)
theorem b260:B 35 4 e238:=viaSmall (by decide +kernel) (by decide)
theorem b261:B 35 4 e239:=viaSmall (by decide +kernel) (by decide)
theorem b262:B 35 4 e240:=viaSmall (by decide +kernel) (by decide)
theorem b263:B 35 4 e241:=viaSmall (by decide +kernel) (by decide)
theorem b264:B 35 4 e242:=viaSmall (by decide +kernel) (by decide)
theorem b265:B 35 4 e243:=viaSmall (by decide +kernel) (by decide)
theorem b266:B 35 4 e244:=viaSmall (by decide +kernel) (by decide)
theorem b267:B 35 4 e245:=viaSmall (by decide +kernel) (by decide)
theorem b268:B 35 4 e246:=viaSmall (by decide +kernel) (by decide)
theorem b269:B 35 4 e247:=viaSmall (by decide +kernel) (by decide)
theorem b270:B 35 4 e248:=viaSmall (by decide +kernel) (by decide)
theorem b271:B 35 4 e249:=viaSmall (by decide +kernel) (by decide)
theorem b272:B 35 4 e250:=viaSmall (by decide +kernel) (by decide)
theorem b273:B 35 4 e251:=viaSmall (by decide +kernel) (by decide)
theorem b274:B 35 4 e252:=viaSmall (by decide +kernel) (by decide)
theorem b275:B 35 4 e253:=viaSmall (by decide +kernel) (by decide)
theorem b276:B 35 4 e254:=viaSmall (by decide +kernel) (by decide)
theorem b277:B 35 4 e255:=viaSmall (by decide +kernel) (by decide)
theorem b278:B 35 4 e256:=viaSmall (by decide +kernel) (by decide)
theorem b279:B 35 4 e257:=viaSmall (by decide +kernel) (by decide)
theorem b280:B 35 4 e258:=viaSmall (by decide +kernel) (by decide)
theorem b281:B 35 4 e259:=viaSmall (by decide +kernel) (by decide)
theorem b282:B 35 4 e260:=viaSmall (by decide +kernel) (by decide)
theorem b283:B 35 4 e261:=viaSmall (by decide +kernel) (by decide)
theorem b284:B 35 4 e262:=viaSmall (by decide +kernel) (by decide)
theorem b285:B 35 4 e263:=viaSmall (by decide +kernel) (by decide)
theorem b286:B 35 4 e264:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b287:B 35 5 e209:=viaBranch (ws:=[e235,e236,e224,e208,e237,e238,e239,e240,e241,e242,e243,e244,e245,e246,e247,e248,e249,e250,e251,e252,e253,e254,e255,e256,e257,e258,e259,e260,e261,e262,e263,e264]) (consBan b256 (consBan b257 (consBan b258 (consBan b225 (consBan b259 (consBan b260 (consBan b261 (consBan b262 (consBan b263 (consBan b264 (consBan b265 (consBan b266 (consBan b267 (consBan b268 (consBan b269 (consBan b270 (consBan b271 (consBan b272 (consBan b273 (consBan b274 (consBan b275 (consBan b276 (consBan b277 (consBan b278 (consBan b279 (consBan b280 (consBan b281 (consBan b282 (consBan b283 (consBan b284 (consBan b285 (consBan b286 (nilBan _ _))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b288:B 16 3 e265:=viaSmall (by decide +kernel) (by decide)
theorem b289:B 16 3 e266:=viaSmall (by decide +kernel) (by decide)
theorem w290:W 16 3 e266:=viaSub (ws:=[e265,e266]) (consBan b288 (consBan b289 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b303:B 87 6 e279:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b304:B 87 6 e280:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b305:B 87 6 e281:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b306:B 87 6 e282:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b307:B 35 4 e101:=viaSmall (by decide +kernel) (by decide)
theorem b308:B 35 4 e283:=viaSmall (by decide +kernel) (by decide)
theorem b309:B 35 4 e284:=viaSmall (by decide +kernel) (by decide)
theorem b310:B 35 4 e285:=viaSmall (by decide +kernel) (by decide)
theorem b311:B 35 4 e286:=viaSmall (by decide +kernel) (by decide)
theorem b312:B 35 4 e287:=viaSmall (by decide +kernel) (by decide)
theorem b313:B 35 4 e288:=viaSmall (by decide +kernel) (by decide)
theorem b314:B 35 4 e289:=viaSmall (by decide +kernel) (by decide)
theorem b315:B 35 4 e290:=viaSmall (by decide +kernel) (by decide)
theorem b316:B 35 4 e291:=viaSmall (by decide +kernel) (by decide)
theorem b317:B 35 4 e292:=viaSmall (by decide +kernel) (by decide)
theorem b318:B 35 4 e293:=viaSmall (by decide +kernel) (by decide)
theorem b319:B 35 4 e294:=viaSmall (by decide +kernel) (by decide)
theorem b320:B 35 4 e295:=viaSmall (by decide +kernel) (by decide)
theorem b321:B 35 4 e296:=viaSmall (by decide +kernel) (by decide)
theorem b322:B 35 4 e297:=viaSmall (by decide +kernel) (by decide)
theorem b323:B 35 4 e298:=viaSmall (by decide +kernel) (by decide)
theorem b324:B 35 4 e299:=viaSmall (by decide +kernel) (by decide)
theorem b325:B 35 4 e300:=viaSmall (by decide +kernel) (by decide)
theorem b326:B 35 4 e301:=viaSmall (by decide +kernel) (by decide)
theorem b327:B 35 4 e302:=viaSmall (by decide +kernel) (by decide)
theorem b328:B 35 4 e303:=viaSmall (by decide +kernel) (by decide)
theorem b329:B 35 4 e304:=viaSmall (by decide +kernel) (by decide)
theorem b330:B 35 4 e305:=viaSmall (by decide +kernel) (by decide)
theorem b331:B 35 4 e306:=viaPerm pc1_0 pci1_0 b92 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b332:B 35 5 e21:=viaBranch (ws:=[e56,e22,e101,e283,e284,e285,e286,e287,e288,e289,e290,e291,e292,e293,e294,e295,e296,e297,e298,e299,e300,e301,e302,e303,e304,e305,e306]) (consBan b64 (consBan b24 (consBan b307 (consBan b308 (consBan b309 (consBan b310 (consBan b311 (consBan b312 (consBan b313 (consBan b314 (consBan b315 (consBan b316 (consBan b317 (consBan b318 (consBan b319 (consBan b320 (consBan b321 (consBan b322 (consBan b323 (consBan b324 (consBan b325 (consBan b326 (consBan b327 (consBan b328 (consBan b329 (consBan b330 (consBan b331 (nilBan _ _)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w333:W 35 5 e21:=widen (by decide +kernel) b332
theorem b334:B 87 6 e307:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b335:B 87 6 e308:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b336:B 87 6 e309:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b337:B 87 6 e310:=viaCut pjt_9 w205 (by decide) (by decide +kernel) (by decide +kernel)
theorem w338:W 35 5 e224:=widen (by decide +kernel) b241
theorem b339:B 87 6 e311:=viaCut pjt_0 w338 (by decide) (by decide +kernel) (by decide +kernel)
theorem b343:B 20 4 e314:=viaSmall (by decide +kernel) (by decide)
theorem b344:B 20 4 e315:=viaSmall (by decide +kernel) (by decide)
theorem b346:B 20 4 e317:=viaPerm pc7_1 pci7_1 b343 (by decide +kernel) (by decide +kernel)
theorem b347:B 20 4 e318:=viaPerm pc7_1 pci7_1 b344 (by decide +kernel) (by decide +kernel)
theorem b352:B 35 4 e323:=viaSmall (by decide +kernel) (by decide)
theorem b353:B 35 4 e324:=viaSmall (by decide +kernel) (by decide)
theorem b354:B 35 4 e325:=viaSmall (by decide +kernel) (by decide)
theorem b355:B 35 4 e326:=viaSmall (by decide +kernel) (by decide)
theorem b356:B 35 4 e327:=viaSmall (by decide +kernel) (by decide)
theorem b357:B 35 4 e328:=viaSmall (by decide +kernel) (by decide)
theorem b358:B 35 4 e329:=viaSmall (by decide +kernel) (by decide)
theorem b359:B 35 4 e330:=viaSmall (by decide +kernel) (by decide)
theorem b360:B 35 4 e331:=viaSmall (by decide +kernel) (by decide)
theorem b361:B 35 4 e332:=viaSmall (by decide +kernel) (by decide)
theorem b362:B 35 4 e333:=viaSmall (by decide +kernel) (by decide)
theorem b363:B 35 4 e334:=viaSmall (by decide +kernel) (by decide)
theorem b364:B 35 4 e335:=viaSmall (by decide +kernel) (by decide)
theorem b365:B 35 4 e336:=viaSmall (by decide +kernel) (by decide)
theorem b366:B 35 4 e337:=viaSmall (by decide +kernel) (by decide)
theorem b367:B 35 4 e338:=viaPerm pc0_0 pci0_0 b185 (by decide +kernel) (by decide +kernel)
theorem b368:B 35 4 e339:=viaSmall (by decide +kernel) (by decide)
theorem b369:B 35 4 e340:=viaSmall (by decide +kernel) (by decide)
theorem b370:B 35 4 e341:=viaSmall (by decide +kernel) (by decide)
theorem b371:B 35 4 e342:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b372:B 35 5 e112:=viaBranch (ws:=[e146,e113,e224,e209,e237,e238,e323,e324,e325,e326,e327,e228,e328,e329,e330,e331,e332,e333,e334,e335,e336,e337,e338,e339,e340,e341,e342]) (consBan b161 (consBan b121 (consBan b258 (consBan b226 (consBan b259 (consBan b260 (consBan b352 (consBan b353 (consBan b354 (consBan b355 (consBan b356 (consBan b249 (consBan b357 (consBan b358 (consBan b359 (consBan b360 (consBan b361 (consBan b362 (consBan b363 (consBan b364 (consBan b365 (consBan b366 (consBan b367 (consBan b368 (consBan b369 (consBan b370 (consBan b371 (nilBan _ _)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w373:W 35 5 e233:=viaSub (ws:=[e112,e224,e233]) (consBan b372 (consBan b241 (consBan b254 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b374:B 87 6 e343:=viaCut pjt_0 w373 (by decide) (by decide +kernel) (by decide +kernel)
theorem w375:W 35 5 e209:=widen (by decide +kernel) b287
theorem b376:B 87 6 e344:=viaCut pjt_0 w375 (by decide) (by decide +kernel) (by decide +kernel)
theorem b377:B 87 6 e345:=viaCut pjt_8 w290 (by decide) (by decide +kernel) (by decide +kernel)
theorem b378:B 87 6 e346:=viaCut pjt_9 w205 (by decide) (by decide +kernel) (by decide +kernel)
theorem b379:B 87 6 e347:=viaPerm pt1 pti1 b306 (by decide +kernel) (by decide +kernel)
theorem b380:B 87 6 e348:=viaPerm pt1 pti1 b334 (by decide +kernel) (by decide +kernel)
theorem b381:B 87 6 e349:=viaPerm pt1 pti1 b335 (by decide +kernel) (by decide +kernel)
theorem b382:B 87 6 e350:=viaPerm pt1 pti1 b336 (by decide +kernel) (by decide +kernel)
theorem b383:B 87 6 e351:=viaPerm pt1 pti1 b337 (by decide +kernel) (by decide +kernel)
theorem b384:B 87 6 e352:=viaPerm pt1 pti1 b339 (by decide +kernel) (by decide +kernel)
theorem b385:B 87 6 e353:=viaPerm pt1 pti1 b374 (by decide +kernel) (by decide +kernel)
theorem b386:B 87 6 e354:=viaPerm pt1 pti1 b376 (by decide +kernel) (by decide +kernel)
theorem b387:B 87 6 e355:=viaPerm pt1 pti1 b377 (by decide +kernel) (by decide +kernel)
theorem b388:B 87 6 e356:=viaPerm pt1 pti1 b378 (by decide +kernel) (by decide +kernel)
theorem b389:B 87 6 e357:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b390:B 87 6 e358:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b391:B 87 6 e359:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b392:B 87 6 e360:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b393:B 87 6 e361:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b394:B 87 6 e362:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b395:B 87 6 e363:=viaCut pjt_9 w205 (by decide) (by decide +kernel) (by decide +kernel)
theorem b396:B 35 4 e364:=viaSmall (by decide +kernel) (by decide)
theorem b397:B 35 4 e365:=viaSmall (by decide +kernel) (by decide)
theorem b398:B 35 4 e366:=viaSmall (by decide +kernel) (by decide)
theorem b399:B 35 4 e367:=viaSmall (by decide +kernel) (by decide)
theorem b400:B 35 4 e368:=viaSmall (by decide +kernel) (by decide)
theorem b401:B 35 4 e369:=viaSmall (by decide +kernel) (by decide)
theorem b402:B 35 4 e370:=viaSmall (by decide +kernel) (by decide)
theorem b403:B 35 4 e371:=viaSmall (by decide +kernel) (by decide)
theorem b404:B 35 4 e372:=viaSmall (by decide +kernel) (by decide)
theorem b405:B 35 4 e373:=viaSmall (by decide +kernel) (by decide)
theorem b406:B 35 4 e374:=viaSmall (by decide +kernel) (by decide)
theorem b407:B 35 4 e375:=viaSmall (by decide +kernel) (by decide)
theorem b408:B 35 4 e376:=viaSmall (by decide +kernel) (by decide)
theorem b409:B 35 4 e377:=viaSmall (by decide +kernel) (by decide)
theorem b410:B 35 4 e378:=viaSmall (by decide +kernel) (by decide)
theorem b411:B 35 4 e379:=viaSmall (by decide +kernel) (by decide)
theorem b412:B 35 4 e380:=viaSmall (by decide +kernel) (by decide)
theorem b413:B 35 4 e381:=viaSmall (by decide +kernel) (by decide)
theorem b414:B 35 4 e382:=viaSmall (by decide +kernel) (by decide)
theorem b415:B 35 4 e383:=viaSmall (by decide +kernel) (by decide)
theorem b416:B 35 4 e384:=viaSmall (by decide +kernel) (by decide)
theorem b417:B 35 4 e385:=viaSmall (by decide +kernel) (by decide)
theorem b418:B 35 4 e386:=viaSmall (by decide +kernel) (by decide)
theorem b419:B 35 4 e387:=viaSmall (by decide +kernel) (by decide)
theorem b420:B 35 4 e388:=viaSmall (by decide +kernel) (by decide)
theorem b421:B 35 4 e389:=viaSmall (by decide +kernel) (by decide)
theorem b422:B 35 4 e390:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b423:B 35 5 e228:=viaBranch (ws:=[e364,e191,e244,e245,e365,e366,e367,e368,e369,e370,e371,e372,e373,e374,e375,e376,e377,e328,e378,e379,e380,e381,e382,e383,e384,e385,e386,e387,e388,e389,e390]) (consBan b396 (consBan b208 (consBan b266 (consBan b267 (consBan b397 (consBan b398 (consBan b399 (consBan b400 (consBan b401 (consBan b402 (consBan b403 (consBan b404 (consBan b405 (consBan b406 (consBan b407 (consBan b408 (consBan b409 (consBan b357 (consBan b410 (consBan b411 (consBan b412 (consBan b413 (consBan b414 (consBan b415 (consBan b416 (consBan b417 (consBan b418 (consBan b419 (consBan b420 (consBan b421 (consBan b422 (nilBan _ _)))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b424:B 35 4 e391:=viaSmall (by decide +kernel) (by decide)
theorem b425:B 35 4 e392:=viaSmall (by decide +kernel) (by decide)
theorem b426:B 35 4 e393:=viaSmall (by decide +kernel) (by decide)
theorem b427:B 35 4 e394:=viaSmall (by decide +kernel) (by decide)
theorem b428:B 35 4 e395:=viaSmall (by decide +kernel) (by decide)
theorem b429:B 35 4 e396:=viaSmall (by decide +kernel) (by decide)
theorem b430:B 35 4 e397:=viaSmall (by decide +kernel) (by decide)
theorem b431:B 35 4 e398:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b432:B 35 5 e399:=viaBranch (ws:=[e129,e246,e391,e392,e393,e377,e394,e395,e396,e397,e398]) (consBan b137 (consBan b268 (consBan b424 (consBan b425 (consBan b426 (consBan b409 (consBan b427 (consBan b428 (consBan b429 (consBan b430 (consBan b431 (nilBan _ _)))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w433:W 35 5 e399:=viaSub (ws:=[e112,e228,e399]) (consBan b372 (consBan b423 (consBan b432 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b434:B 87 6 e400:=viaCut pjt_0 w433 (by decide) (by decide +kernel) (by decide +kernel)
theorem b435:B 12 3 e401:=viaSmall (by decide +kernel) (by decide)
theorem b453:B 35 4 e419:=viaSmall (by decide +kernel) (by decide)
theorem b454:B 35 4 e420:=viaSmall (by decide +kernel) (by decide)
theorem b455:B 35 4 e421:=viaSmall (by decide +kernel) (by decide)
theorem b456:B 35 4 e422:=viaSmall (by decide +kernel) (by decide)
theorem b457:B 35 4 e423:=viaSmall (by decide +kernel) (by decide)
theorem b458:B 35 4 e424:=viaSmall (by decide +kernel) (by decide)
theorem b459:B 35 4 e425:=viaSmall (by decide +kernel) (by decide)
theorem b460:B 35 4 e426:=viaSmall (by decide +kernel) (by decide)
theorem b461:B 35 4 e427:=viaSmall (by decide +kernel) (by decide)
theorem b462:B 35 4 e428:=viaSmall (by decide +kernel) (by decide)
theorem b463:B 35 4 e429:=viaSmall (by decide +kernel) (by decide)
theorem b464:B 35 4 e430:=viaSmall (by decide +kernel) (by decide)
theorem b465:B 35 4 e431:=viaSmall (by decide +kernel) (by decide)
theorem b466:B 35 4 e432:=viaSmall (by decide +kernel) (by decide)
theorem b467:B 35 4 e433:=viaSmall (by decide +kernel) (by decide)
theorem b468:B 35 4 e434:=viaSmall (by decide +kernel) (by decide)
theorem b469:B 35 4 e435:=viaSmall (by decide +kernel) (by decide)
theorem b470:B 35 4 e436:=viaSmall (by decide +kernel) (by decide)
theorem b471:B 35 4 e437:=viaSmall (by decide +kernel) (by decide)
theorem b472:B 35 4 e438:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b473:B 35 5 e328:=viaBranch (ws:=[e247,e419,e420,e150,e192,e193,e227,e421,e422,e423,e424,e425,e426,e427,e428,e228,e377,e429,e430,e331,e431,e432,e334,e433,e434,e435,e436,e437,e438]) (consBan b269 (consBan b453 (consBan b454 (consBan b165 (consBan b209 (consBan b210 (consBan b248 (consBan b455 (consBan b456 (consBan b457 (consBan b458 (consBan b459 (consBan b460 (consBan b461 (consBan b462 (consBan b249 (consBan b409 (consBan b463 (consBan b464 (consBan b360 (consBan b465 (consBan b466 (consBan b363 (consBan b467 (consBan b468 (consBan b469 (consBan b470 (consBan b471 (consBan b472 (nilBan _ _)))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b474:B 35 4 e439:=viaSmall (by decide +kernel) (by decide)
theorem b475:B 35 4 e440:=viaSmall (by decide +kernel) (by decide)
theorem b476:B 35 4 e441:=viaSmall (by decide +kernel) (by decide)
theorem b477:B 35 4 e442:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b478:B 35 5 e443:=viaBranch (ws:=[e209,e117,e130,e194,e439,e332,e440,e377,e431,e441,e442]) (consBan b226 (consBan b125 (consBan b138 (consBan b211 (consBan b474 (consBan b361 (consBan b475 (consBan b409 (consBan b465 (consBan b476 (consBan b477 (nilBan _ _)))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w479:W 35 5 e443:=viaSub (ws:=[e328,e112,e443]) (consBan b473 (consBan b372 (consBan b478 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b480:B 87 6 e444:=viaCut pjt_0 w479 (by decide) (by decide +kernel) (by decide +kernel)
theorem b481:B 87 6 e445:=viaCut pjt_9 w205 (by decide) (by decide +kernel) (by decide +kernel)
theorem b482:B 87 6 e446:=viaPerm pt1 pti1 b389 (by decide +kernel) (by decide +kernel)
theorem b483:B 87 6 e447:=viaPerm pt1 pti1 b390 (by decide +kernel) (by decide +kernel)
theorem b484:B 87 6 e448:=viaPerm pt1 pti1 b391 (by decide +kernel) (by decide +kernel)
theorem b485:B 87 6 e449:=viaPerm pt1 pti1 b392 (by decide +kernel) (by decide +kernel)
theorem b486:B 87 6 e450:=viaPerm pt1 pti1 b393 (by decide +kernel) (by decide +kernel)
theorem b487:B 87 6 e451:=viaPerm pt1 pti1 b394 (by decide +kernel) (by decide +kernel)
theorem b488:B 87 6 e452:=viaPerm pt1 pti1 b395 (by decide +kernel) (by decide +kernel)
theorem b489:B 87 6 e453:=viaPerm pt1 pti1 b434 (by decide +kernel) (by decide +kernel)
theorem b490:B 87 6 e454:=viaPerm pt1 pti1 b480 (by decide +kernel) (by decide +kernel)
theorem b491:B 87 6 e455:=viaPerm pt1 pti1 b481 (by decide +kernel) (by decide +kernel)
theorem b492:B 87 6 e456:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b506:B 87 5 e467:=viaSmall (by decide +kernel) (by decide)
theorem b507:B 87 5 e468:=viaSmall (by decide +kernel) (by decide)
theorem w508:W 35 4 e203:=widen (by decide +kernel) b220
theorem b509:B 87 5 e469:=viaCut pjt_0 w508 (by decide) (by decide +kernel) (by decide +kernel)
theorem b510:B 87 5 e470:=viaSmall (by decide +kernel) (by decide)
theorem b511:B 87 5 e471:=viaPerm pt0 pti0 b510 (by decide +kernel) (by decide +kernel)
theorem b512:B 87 5 e472:=viaSmall (by decide +kernel) (by decide)
theorem b513:B 87 5 e473:=viaPerm pt0 pti0 b512 (by decide +kernel) (by decide +kernel)
theorem b514:B 87 5 e474:=viaSmall (by decide +kernel) (by decide)
theorem b515:B 87 5 e475:=viaSmall (by decide +kernel) (by decide)
theorem b516:B 87 5 e476:=viaSmall (by decide +kernel) (by decide)
theorem b517:B 87 5 e477:=viaSmall (by decide +kernel) (by decide)
theorem b518:B 87 5 e478:=viaPerm pt0 pti0 b506 (by decide +kernel) (by decide +kernel)
theorem b519:B 87 5 e479:=viaPerm pt0 pti0 b507 (by decide +kernel) (by decide +kernel)
theorem b520:B 87 5 e480:=viaPerm pt0 pti0 b514 (by decide +kernel) (by decide +kernel)
theorem b521:B 87 5 e481:=viaPerm pt0 pti0 b515 (by decide +kernel) (by decide +kernel)
theorem b522:B 87 5 e482:=viaPerm pt0 pti0 b516 (by decide +kernel) (by decide +kernel)
theorem b523:B 87 5 e483:=viaPerm pt0 pti0 b517 (by decide +kernel) (by decide +kernel)
theorem b524:B 87 5 e484:=viaSmall (by decide +kernel) (by decide)
theorem b525:B 87 5 e485:=viaSmall (by decide +kernel) (by decide)
theorem b526:B 87 5 e486:=viaSmall (by decide +kernel) (by decide)
theorem b527:B 87 5 e487:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b528:B 87 6 e488:=viaBranch (ws:=[e467,e468,e469,e470,e471,e472,e473,e474,e475,e476,e477,e478,e479,e480,e481,e482,e483,e484,e485,e486,e487]) (consBan b506 (consBan b507 (consBan b509 (consBan b510 (consBan b511 (consBan b512 (consBan b513 (consBan b514 (consBan b515 (consBan b516 (consBan b517 (consBan b518 (consBan b519 (consBan b520 (consBan b521 (consBan b522 (consBan b523 (consBan b524 (consBan b525 (consBan b526 (consBan b527 (nilBan _ _)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b530:B 87 6 e490:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b531:B 87 6 e491:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b542:B 87 6 e479:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b543:B 87 6 e502:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b552:B 87 6 e510:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b553:B 87 6 e511:=viaCut pjt_9 w205 (by decide) (by decide +kernel) (by decide +kernel)
theorem b554:B 87 6 e512:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem w559:W 35 5 e112:=widen (by decide +kernel) b372
theorem b560:B 87 6 e517:=viaCut pjt_0 w559 (by decide) (by decide +kernel) (by decide +kernel)
theorem b561:B 87 6 e518:=viaPerm pt1 pti1 b560 (by decide +kernel) (by decide +kernel)
theorem b562:B 87 6 e519:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b565:B 87 6 e522:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b566:B 87 6 e523:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b567:B 87 6 e524:=viaPerm pt1 pti1 b565 (by decide +kernel) (by decide +kernel)
theorem b568:B 87 6 e525:=viaPerm pt1 pti1 b566 (by decide +kernel) (by decide +kernel)
theorem b569:B 87 6 e526:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b570:B 16 3 e527:=viaSmall (by decide +kernel) (by decide)
theorem b571:B 16 3 e528:=viaSmall (by decide +kernel) (by decide)
theorem b572:B 16 3 e529:=viaSmall (by decide +kernel) (by decide)
theorem b573:B 16 3 e530:=viaSmall (by decide +kernel) (by decide)
theorem b574:B 16 3 e531:=viaSmall (by decide +kernel) (by decide)
theorem b575:B 16 3 e532:=viaSmall (by decide +kernel) (by decide)
theorem b576:B 16 3 e533:=viaSmall (by decide +kernel) (by decide)
theorem b577:B 16 3 e534:=viaSmall (by decide +kernel) (by decide)
theorem b578:B 16 3 e535:=viaSmall (by decide +kernel) (by decide)
theorem b579:B 16 3 e536:=viaSmall (by decide +kernel) (by decide)
theorem b580:B 16 3 e537:=viaSmall (by decide +kernel) (by decide)
theorem b581:B 16 3 e538:=viaSmall (by decide +kernel) (by decide)
theorem b582:B 16 3 e539:=viaSmall (by decide +kernel) (by decide)
theorem b583:B 16 3 e540:=viaSmall (by decide +kernel) (by decide)
theorem b584:B 16 3 e541:=viaSmall (by decide +kernel) (by decide)
theorem b585:B 16 3 e542:=viaSmall (by decide +kernel) (by decide)
theorem b586:B 16 3 e543:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b587:B 16 4 e544:=viaBranch (ws:=[e527,e528,e529,e530,e531,e532,e533,e534,e535,e536,e537,e538,e539,e540,e541,e542,e543]) (consBan b570 (consBan b571 (consBan b572 (consBan b573 (consBan b574 (consBan b575 (consBan b576 (consBan b577 (consBan b578 (consBan b579 (consBan b580 (consBan b581 (consBan b582 (consBan b583 (consBan b584 (consBan b585 (consBan b586 (nilBan _ _)))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w588:W 16 4 e544:=widen (by decide +kernel) b587
theorem b589:B 87 6 e545:=viaCut pjt_9 w588 (by decide) (by decide +kernel) (by decide +kernel)
theorem b590:B 16 3 e188:=viaSmall (by decide +kernel) (by decide)
theorem w591:W 16 3 e188:=widen (by decide +kernel) b590
theorem b592:B 87 6 e546:=viaCut pjt_14 w591 (by decide) (by decide +kernel) (by decide +kernel)
theorem b593:B 87 6 e547:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b609:B 87 6 e562:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b610:B 87 6 e563:=viaCut pjt_14 w591 (by decide) (by decide +kernel) (by decide +kernel)
theorem b611:B 87 6 e564:=viaPerm pt1 pti1 b569 (by decide +kernel) (by decide +kernel)
theorem b612:B 87 6 e565:=viaPerm pt1 pti1 b589 (by decide +kernel) (by decide +kernel)
theorem b613:B 87 6 e566:=viaPerm pt1 pti1 b592 (by decide +kernel) (by decide +kernel)
theorem b614:B 87 6 e567:=viaPerm pt1 pti1 b609 (by decide +kernel) (by decide +kernel)
theorem b615:B 87 6 e568:=viaPerm pt1 pti1 b610 (by decide +kernel) (by decide +kernel)
theorem b616:B 87 6 e569:=viaPerm pt1 pti1 b593 (by decide +kernel) (by decide +kernel)
theorem b617:B 87 6 e570:=viaCut pjt_9 w205 (by decide) (by decide +kernel) (by decide +kernel)
theorem b667:B 87 5 e618:=viaSmall (by decide +kernel) (by decide)
theorem b668:B 87 5 e619:=viaPerm pt1 pti1 b667 (by decide +kernel) (by decide +kernel)
theorem b669:B 87 5 e620:=viaSmall (by decide +kernel) (by decide)
theorem b670:B 87 5 e621:=viaSmall (by decide +kernel) (by decide)
theorem b671:B 87 5 e622:=viaSmall (by decide +kernel) (by decide)
theorem b672:B 87 5 e623:=viaSmall (by decide +kernel) (by decide)
theorem b673:B 87 5 e624:=viaPerm pt1 pti1 b520 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b674:B 87 6 e625:=viaBranch (ws:=[e618,e619,e620,e621,e622,e623,e480,e624]) (consBan b667 (consBan b668 (consBan b669 (consBan b670 (consBan b671 (consBan b672 (consBan b520 (consBan b673 (nilBan _ _))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b675:B 87 6 e626:=viaCut pjt_9 w205 (by decide) (by decide +kernel) (by decide +kernel)
theorem b676:B 87 6 e627:=viaPerm pt1 pti1 b675 (by decide +kernel) (by decide +kernel)
theorem b677:B 87 6 e628:=viaPerm pt1 pti1 b492 (by decide +kernel) (by decide +kernel)
theorem b678:B 87 6 e629:=viaPerm pt1 pti1 b528 (by decide +kernel) (by decide +kernel)
theorem b679:B 87 6 e630:=viaPerm pt1 pti1 b530 (by decide +kernel) (by decide +kernel)
theorem b680:B 87 6 e631:=viaPerm pt1 pti1 b531 (by decide +kernel) (by decide +kernel)
theorem b681:B 87 6 e632:=viaPerm pt1 pti1 b542 (by decide +kernel) (by decide +kernel)
theorem b682:B 87 6 e633:=viaPerm pt1 pti1 b543 (by decide +kernel) (by decide +kernel)
theorem b683:B 87 6 e634:=viaPerm pt1 pti1 b552 (by decide +kernel) (by decide +kernel)
theorem b684:B 87 6 e635:=viaPerm pt1 pti1 b553 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b685:B 87 7 e636:=viaBranch (ws:=[e279,e280,e281,e282,e307,e308,e309,e310,e311,e343,e344,e345,e346,e347,e348,e349,e350,e351,e352,e353,e354,e355,e356,e357,e358,e359,e360,e361,e362,e363,e400,e444,e445,e446,e447,e448,e449,e450,e451,e452,e453,e454,e455,e456,e488,e490,e491,e479,e502,e510,e511,e512,e517,e518,e519,e522,e523,e524,e525,e526,e545,e546,e547,e562,e563,e564,e565,e566,e567,e568,e569,e570,e625,e626,e627,e628,e629,e630,e631,e632,e633,e634,e635]) (consBan b303 (consBan b304 (consBan b305 (consBan b306 (consBan b334 (consBan b335 (consBan b336 (consBan b337 (consBan b339 (consBan b374 (consBan b376 (consBan b377 (consBan b378 (consBan b379 (consBan b380 (consBan b381 (consBan b382 (consBan b383 (consBan b384 (consBan b385 (consBan b386 (consBan b387 (consBan b388 (consBan b389 (consBan b390 (consBan b391 (consBan b392 (consBan b393 (consBan b394 (consBan b395 (consBan b434 (consBan b480 (consBan b481 (consBan b482 (consBan b483 (consBan b484 (consBan b485 (consBan b486 (consBan b487 (consBan b488 (consBan b489 (consBan b490 (consBan b491 (consBan b492 (consBan b528 (consBan b530 (consBan b531 (consBan b542 (consBan b543 (consBan b552 (consBan b553 (consBan b554 (consBan b560 (consBan b561 (consBan b562 (consBan b565 (consBan b566 (consBan b567 (consBan b568 (consBan b569 (consBan b589 (consBan b592 (consBan b593 (consBan b609 (consBan b610 (consBan b611 (consBan b612 (consBan b613 (consBan b614 (consBan b615 (consBan b616 (consBan b617 (consBan b674 (consBan b675 (consBan b676 (consBan b677 (consBan b678 (consBan b679 (consBan b680 (consBan b681 (consBan b682 (consBan b683 (consBan b684 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b694:B 35 4 e645:=viaSmall (by decide +kernel) (by decide)
theorem b695:B 35 4 e646:=viaSmall (by decide +kernel) (by decide)
theorem b754:B 87 5 e697:=viaSmall (by decide +kernel) (by decide)
theorem b755:B 87 5 e698:=viaSmall (by decide +kernel) (by decide)
theorem b756:B 87 5 e699:=viaSmall (by decide +kernel) (by decide)
theorem b757:B 87 5 e700:=viaSmall (by decide +kernel) (by decide)
theorem b758:B 87 5 e701:=viaPerm pt1 pti1 b756 (by decide +kernel) (by decide +kernel)
theorem b759:B 87 5 e702:=viaPerm pt1 pti1 b757 (by decide +kernel) (by decide +kernel)
theorem b760:B 87 5 e703:=viaSmall (by decide +kernel) (by decide)
theorem b761:B 87 5 e704:=viaSmall (by decide +kernel) (by decide)
theorem b762:B 87 5 e705:=viaPerm pt1 pti1 b760 (by decide +kernel) (by decide +kernel)
theorem b763:B 87 5 e706:=viaPerm pt1 pti1 b761 (by decide +kernel) (by decide +kernel)
theorem b764:B 87 5 e707:=viaSmall (by decide +kernel) (by decide)
theorem b765:B 87 5 e708:=viaSmall (by decide +kernel) (by decide)
theorem b766:B 87 5 e709:=viaSmall (by decide +kernel) (by decide)
theorem b767:B 87 5 e710:=viaSmall (by decide +kernel) (by decide)
theorem b768:B 87 5 e711:=viaSmall (by decide +kernel) (by decide)
theorem b769:B 87 5 e712:=viaPerm pt1 pti1 b768 (by decide +kernel) (by decide +kernel)
theorem b770:B 87 5 e713:=viaSmall (by decide +kernel) (by decide)
theorem b771:B 87 5 e714:=viaPerm pt1 pti1 b770 (by decide +kernel) (by decide +kernel)
theorem b772:B 87 5 e715:=viaSmall (by decide +kernel) (by decide)
theorem b773:B 87 5 e716:=viaSmall (by decide +kernel) (by decide)
theorem b774:B 87 5 e717:=viaPerm pt1 pti1 b772 (by decide +kernel) (by decide +kernel)
theorem b775:B 87 5 e718:=viaPerm pt1 pti1 b773 (by decide +kernel) (by decide +kernel)
theorem b776:B 87 5 e719:=viaPerm pt1 pti1 b764 (by decide +kernel) (by decide +kernel)
theorem b777:B 87 5 e720:=viaPerm pt1 pti1 b765 (by decide +kernel) (by decide +kernel)
theorem b778:B 87 5 e721:=viaPerm pt1 pti1 b766 (by decide +kernel) (by decide +kernel)
theorem b779:B 87 5 e722:=viaPerm pt1 pti1 b767 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b780:B 87 6 e723:=viaBranch (ws:=[e697,e698,e699,e700,e701,e702,e703,e704,e705,e706,e707,e708,e709,e710,e711,e712,e713,e714,e715,e716,e717,e718,e719,e720,e721,e722]) (consBan b754 (consBan b755 (consBan b756 (consBan b757 (consBan b758 (consBan b759 (consBan b760 (consBan b761 (consBan b762 (consBan b763 (consBan b764 (consBan b765 (consBan b766 (consBan b767 (consBan b768 (consBan b769 (consBan b770 (consBan b771 (consBan b772 (consBan b773 (consBan b774 (consBan b775 (consBan b776 (consBan b777 (consBan b778 (consBan b779 (nilBan _ _))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b781:B 87 6 e698:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b782:B 87 6 e724:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b783:B 12 2 e16:=viaSmall (by decide +kernel) (by decide)
theorem w784:W 12 2 e16:=widen (by decide +kernel) b783
theorem b785:B 87 6 e725:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b786:B 87 6 e726:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b787:B 87 6 e727:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b788:B 87 6 e728:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b789:B 87 6 e729:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b790:B 87 6 e730:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b791:B 87 6 e731:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b792:B 35 4 e732:=viaSmall (by decide +kernel) (by decide)
theorem b793:B 35 4 e733:=viaSmall (by decide +kernel) (by decide)
theorem b794:B 35 4 e734:=viaSmall (by decide +kernel) (by decide)
theorem b795:B 35 4 e735:=viaSmall (by decide +kernel) (by decide)
theorem b796:B 35 4 e736:=viaSmall (by decide +kernel) (by decide)
theorem b797:B 35 4 e737:=viaSmall (by decide +kernel) (by decide)
theorem b798:B 35 4 e738:=viaSmall (by decide +kernel) (by decide)
theorem b799:B 35 4 e739:=viaSmall (by decide +kernel) (by decide)
theorem b800:B 35 4 e740:=viaSmall (by decide +kernel) (by decide)
theorem b801:B 35 4 e741:=viaSmall (by decide +kernel) (by decide)
theorem b802:B 35 4 e742:=viaSmall (by decide +kernel) (by decide)
theorem b803:B 35 4 e743:=viaSmall (by decide +kernel) (by decide)
theorem b804:B 35 4 e744:=viaSmall (by decide +kernel) (by decide)
theorem b805:B 35 4 e745:=viaSmall (by decide +kernel) (by decide)
theorem b806:B 35 4 e641:=viaSmall (by decide +kernel) (by decide)
theorem b807:B 35 4 e746:=viaSmall (by decide +kernel) (by decide)
theorem b808:B 35 4 e747:=viaSmall (by decide +kernel) (by decide)
theorem b809:B 35 4 e748:=viaSmall (by decide +kernel) (by decide)
theorem b810:B 35 4 e749:=viaSmall (by decide +kernel) (by decide)
theorem b811:B 35 4 e750:=viaSmall (by decide +kernel) (by decide)
theorem b812:B 35 4 e751:=viaSmall (by decide +kernel) (by decide)
theorem b813:B 35 4 e752:=viaSmall (by decide +kernel) (by decide)
theorem b814:B 35 4 e753:=viaSmall (by decide +kernel) (by decide)
theorem b815:B 35 4 e754:=viaSmall (by decide +kernel) (by decide)
theorem b816:B 35 4 e755:=viaSmall (by decide +kernel) (by decide)
theorem b817:B 35 4 e756:=viaSmall (by decide +kernel) (by decide)
theorem b818:B 35 4 e757:=viaSmall (by decide +kernel) (by decide)
theorem b819:B 35 4 e758:=viaSmall (by decide +kernel) (by decide)
theorem b820:B 35 4 e759:=viaSmall (by decide +kernel) (by decide)
theorem b821:B 35 4 e760:=viaSmall (by decide +kernel) (by decide)
theorem b822:B 35 4 e761:=viaSmall (by decide +kernel) (by decide)
theorem b823:B 35 4 e762:=viaSmall (by decide +kernel) (by decide)
theorem b824:B 35 4 e763:=viaSmall (by decide +kernel) (by decide)
theorem b825:B 35 4 e764:=viaSmall (by decide +kernel) (by decide)
theorem b826:B 35 4 e765:=viaSmall (by decide +kernel) (by decide)
theorem b827:B 35 4 e766:=viaSmall (by decide +kernel) (by decide)
theorem b828:B 35 4 e767:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b829:B 35 5 e768:=viaBranch (ws:=[e732,e733,e734,e735,e736,e737,e738,e739,e740,e741,e742,e743,e744,e745,e641,e746,e747,e748,e749,e750,e751,e752,e753,e754,e755,e756,e757,e758,e759,e760,e761,e762,e763,e764,e765,e766,e767]) (consBan b792 (consBan b793 (consBan b794 (consBan b795 (consBan b796 (consBan b797 (consBan b798 (consBan b799 (consBan b800 (consBan b801 (consBan b802 (consBan b803 (consBan b804 (consBan b805 (consBan b806 (consBan b807 (consBan b808 (consBan b809 (consBan b810 (consBan b811 (consBan b812 (consBan b813 (consBan b814 (consBan b815 (consBan b816 (consBan b817 (consBan b818 (consBan b819 (consBan b820 (consBan b821 (consBan b822 (consBan b823 (consBan b824 (consBan b825 (consBan b826 (consBan b827 (consBan b828 (nilBan _ _)))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w830:W 35 5 e768:=widen (by decide +kernel) b829
theorem b831:B 87 6 e769:=viaCut pjt_1 w830 (by decide) (by decide +kernel) (by decide +kernel)
theorem b832:B 87 6 e770:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b833:B 87 6 e771:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b834:B 87 6 e772:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b835:B 87 6 e773:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b836:B 87 6 e774:=viaPerm pt1 pti1 b785 (by decide +kernel) (by decide +kernel)
theorem b837:B 87 6 e775:=viaPerm pt1 pti1 b786 (by decide +kernel) (by decide +kernel)
theorem b838:B 87 6 e776:=viaPerm pt1 pti1 b787 (by decide +kernel) (by decide +kernel)
theorem b839:B 87 6 e777:=viaPerm pt1 pti1 b788 (by decide +kernel) (by decide +kernel)
theorem b840:B 87 6 e778:=viaPerm pt1 pti1 b789 (by decide +kernel) (by decide +kernel)
theorem b841:B 87 6 e779:=viaPerm pt1 pti1 b790 (by decide +kernel) (by decide +kernel)
theorem b842:B 87 6 e780:=viaPerm pt1 pti1 b791 (by decide +kernel) (by decide +kernel)
theorem b843:B 87 6 e781:=viaPerm pt1 pti1 b831 (by decide +kernel) (by decide +kernel)
theorem b844:B 87 6 e782:=viaPerm pt1 pti1 b832 (by decide +kernel) (by decide +kernel)
theorem b845:B 87 6 e783:=viaPerm pt1 pti1 b833 (by decide +kernel) (by decide +kernel)
theorem b846:B 87 6 e784:=viaPerm pt1 pti1 b834 (by decide +kernel) (by decide +kernel)
theorem b847:B 87 6 e785:=viaPerm pt1 pti1 b835 (by decide +kernel) (by decide +kernel)
theorem b848:B 87 6 e786:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b849:B 87 6 e787:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b850:B 87 6 e788:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b851:B 87 6 e789:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b852:B 87 6 e790:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b853:B 87 6 e791:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b854:B 16 3 e103:=viaSmall (by decide +kernel) (by decide)
theorem b855:B 16 3 e104:=viaSmall (by decide +kernel) (by decide)
theorem w856:W 16 3 e104:=viaSub (ws:=[e103,e104]) (consBan b854 (consBan b855 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b857:B 87 6 e792:=viaCut pjt_16 w856 (by decide) (by decide +kernel) (by decide +kernel)
theorem b858:B 20 4 e793:=viaSmall (by decide +kernel) (by decide)
theorem b859:B 20 4 e794:=viaSmall (by decide +kernel) (by decide)
theorem w860:W 20 4 e318:=viaSub (ws:=[e794,e317,e318]) (consBan b859 (consBan b346 (consBan b347 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b861:B 87 6 e795:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem w862:W 12 3 e0:=viaSub (ws:=[e16,e0]) (consBan b16 (consBan b0 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b863:B 87 6 e796:=viaCut pjt_18 w862 (by decide) (by decide +kernel) (by decide +kernel)
theorem b864:B 12 3 e797:=viaPerm pc18_1 pci18_1 b0 (by decide +kernel) (by decide +kernel)
theorem w865:W 12 3 e797:=viaSub (ws:=[e16,e797]) (consBan b16 (consBan b864 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b866:B 87 6 e798:=viaCut pjt_18 w865 (by decide) (by decide +kernel) (by decide +kernel)
theorem b867:B 87 6 e799:=viaPerm pt1 pti1 b848 (by decide +kernel) (by decide +kernel)
theorem b868:B 87 6 e800:=viaPerm pt1 pti1 b849 (by decide +kernel) (by decide +kernel)
theorem b869:B 87 6 e801:=viaPerm pt1 pti1 b850 (by decide +kernel) (by decide +kernel)
theorem b870:B 87 6 e802:=viaPerm pt1 pti1 b851 (by decide +kernel) (by decide +kernel)
theorem b871:B 87 6 e803:=viaPerm pt1 pti1 b852 (by decide +kernel) (by decide +kernel)
theorem b872:B 87 6 e804:=viaPerm pt1 pti1 b853 (by decide +kernel) (by decide +kernel)
theorem b873:B 87 6 e805:=viaPerm pt1 pti1 b857 (by decide +kernel) (by decide +kernel)
theorem b874:B 87 6 e806:=viaPerm pt1 pti1 b861 (by decide +kernel) (by decide +kernel)
theorem b875:B 87 6 e807:=viaPerm pt1 pti1 b863 (by decide +kernel) (by decide +kernel)
theorem b876:B 87 6 e808:=viaPerm pt1 pti1 b866 (by decide +kernel) (by decide +kernel)
theorem b877:B 87 6 e809:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b878:B 87 6 e810:=viaPerm pt0 pti0 b530 (by decide +kernel) (by decide +kernel)
theorem b879:B 87 6 e811:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b880:B 87 6 e812:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b881:B 87 6 e813:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b882:B 87 6 e814:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b883:B 87 6 e815:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b884:B 87 6 e816:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b885:B 87 6 e817:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b886:B 87 6 e818:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b887:B 87 6 e819:=viaPerm pt1 pti1 b886 (by decide +kernel) (by decide +kernel)
theorem b888:B 87 6 e820:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b889:B 87 6 e821:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b890:B 87 6 e822:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b891:B 87 6 e823:=viaPerm pt1 pti1 b889 (by decide +kernel) (by decide +kernel)
theorem b892:B 87 6 e824:=viaPerm pt1 pti1 b890 (by decide +kernel) (by decide +kernel)
theorem b893:B 87 6 e825:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b894:B 87 6 e826:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b895:B 87 6 e827:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b896:B 87 6 e828:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b897:B 87 6 e829:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b898:B 87 6 e830:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b899:B 87 6 e831:=viaPerm pt1 pti1 b893 (by decide +kernel) (by decide +kernel)
theorem b900:B 87 6 e832:=viaPerm pt1 pti1 b894 (by decide +kernel) (by decide +kernel)
theorem b901:B 87 6 e833:=viaPerm pt1 pti1 b895 (by decide +kernel) (by decide +kernel)
theorem b902:B 87 6 e834:=viaPerm pt1 pti1 b897 (by decide +kernel) (by decide +kernel)
theorem b903:B 87 6 e835:=viaPerm pt1 pti1 b898 (by decide +kernel) (by decide +kernel)
theorem b904:B 87 6 e836:=viaPerm pt1 pti1 b896 (by decide +kernel) (by decide +kernel)
theorem b905:B 16 3 e837:=viaSmall (by decide +kernel) (by decide)
theorem b906:B 16 3 e838:=viaSmall (by decide +kernel) (by decide)
theorem w907:W 16 3 e838:=viaSub (ws:=[e837,e838]) (consBan b905 (consBan b906 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b908:B 87 6 e839:=viaCut pjt_17 w907 (by decide) (by decide +kernel) (by decide +kernel)
theorem b909:B 20 4 e840:=viaSmall (by decide +kernel) (by decide)
theorem b910:B 20 4 e841:=viaSmall (by decide +kernel) (by decide)
theorem w911:W 20 4 e841:=viaSub (ws:=[e793,e840,e841]) (consBan b858 (consBan b909 (consBan b910 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b912:B 87 6 e842:=viaCut pjt_11 w911 (by decide) (by decide +kernel) (by decide +kernel)
theorem b913:B 12 3 e843:=viaPerm pc18_2 pci18_2 b0 (by decide +kernel) (by decide +kernel)
theorem w914:W 12 3 e843:=viaSub (ws:=[e16,e843]) (consBan b16 (consBan b913 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b915:B 87 6 e844:=viaCut pjt_18 w914 (by decide) (by decide +kernel) (by decide +kernel)
theorem b916:B 87 6 e845:=viaPerm pt1 pti1 b915 (by decide +kernel) (by decide +kernel)
theorem b917:B 87 6 e846:=viaPerm pt1 pti1 b877 (by decide +kernel) (by decide +kernel)
theorem b918:B 87 6 e847:=viaPerm pt1 pti1 b878 (by decide +kernel) (by decide +kernel)
theorem b919:B 87 6 e848:=viaPerm pt1 pti1 b879 (by decide +kernel) (by decide +kernel)
theorem b920:B 87 6 e849:=viaPerm pt1 pti1 b880 (by decide +kernel) (by decide +kernel)
theorem b921:B 87 6 e850:=viaPerm pt1 pti1 b881 (by decide +kernel) (by decide +kernel)
theorem b922:B 87 6 e851:=viaPerm pt1 pti1 b882 (by decide +kernel) (by decide +kernel)
theorem b923:B 87 6 e852:=viaPerm pt1 pti1 b883 (by decide +kernel) (by decide +kernel)
theorem b924:B 87 6 e853:=viaPerm pt1 pti1 b884 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b925:B 87 7 e697:=viaBranch (ws:=[e723,e698,e724,e725,e726,e727,e728,e729,e730,e731,e769,e770,e771,e772,e773,e774,e775,e776,e777,e778,e779,e780,e781,e782,e783,e784,e785,e786,e787,e788,e789,e790,e791,e792,e795,e796,e798,e799,e800,e801,e802,e803,e804,e805,e806,e807,e808,e809,e810,e811,e812,e813,e814,e815,e816,e817,e818,e819,e820,e821,e822,e823,e824,e825,e826,e827,e828,e829,e830,e831,e832,e833,e834,e835,e836,e839,e842,e844,e845,e846,e847,e848,e849,e850,e851,e852,e853]) (consBan b780 (consBan b781 (consBan b782 (consBan b785 (consBan b786 (consBan b787 (consBan b788 (consBan b789 (consBan b790 (consBan b791 (consBan b831 (consBan b832 (consBan b833 (consBan b834 (consBan b835 (consBan b836 (consBan b837 (consBan b838 (consBan b839 (consBan b840 (consBan b841 (consBan b842 (consBan b843 (consBan b844 (consBan b845 (consBan b846 (consBan b847 (consBan b848 (consBan b849 (consBan b850 (consBan b851 (consBan b852 (consBan b853 (consBan b857 (consBan b861 (consBan b863 (consBan b866 (consBan b867 (consBan b868 (consBan b869 (consBan b870 (consBan b871 (consBan b872 (consBan b873 (consBan b874 (consBan b875 (consBan b876 (consBan b877 (consBan b878 (consBan b879 (consBan b880 (consBan b881 (consBan b882 (consBan b883 (consBan b884 (consBan b885 (consBan b886 (consBan b887 (consBan b888 (consBan b889 (consBan b890 (consBan b891 (consBan b892 (consBan b893 (consBan b894 (consBan b895 (consBan b896 (consBan b897 (consBan b898 (consBan b899 (consBan b900 (consBan b901 (consBan b902 (consBan b903 (consBan b904 (consBan b908 (consBan b912 (consBan b915 (consBan b916 (consBan b917 (consBan b918 (consBan b919 (consBan b920 (consBan b921 (consBan b922 (consBan b923 (consBan b924 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b940:B 35 4 e863:=viaSmall (by decide +kernel) (by decide)
theorem b941:B 35 4 e864:=viaSmall (by decide +kernel) (by decide)
theorem b942:B 35 4 e865:=viaSmall (by decide +kernel) (by decide)
theorem b943:B 35 4 e866:=viaSmall (by decide +kernel) (by decide)
theorem b944:B 35 4 e867:=viaSmall (by decide +kernel) (by decide)
theorem b945:B 35 4 e868:=viaSmall (by decide +kernel) (by decide)
theorem b946:B 35 4 e869:=viaSmall (by decide +kernel) (by decide)
theorem b947:B 35 4 e870:=viaSmall (by decide +kernel) (by decide)
theorem b948:B 35 4 e871:=viaSmall (by decide +kernel) (by decide)
theorem b949:B 35 4 e872:=viaSmall (by decide +kernel) (by decide)
theorem b950:B 35 4 e873:=viaSmall (by decide +kernel) (by decide)
theorem b951:B 35 4 e874:=viaSmall (by decide +kernel) (by decide)
theorem b952:B 35 4 e875:=viaSmall (by decide +kernel) (by decide)
theorem b953:B 35 4 e876:=viaSmall (by decide +kernel) (by decide)
theorem b954:B 35 4 e877:=viaSmall (by decide +kernel) (by decide)
theorem b955:B 35 4 e878:=viaSmall (by decide +kernel) (by decide)
theorem b956:B 35 4 e879:=viaSmall (by decide +kernel) (by decide)
theorem b957:B 35 4 e880:=viaSmall (by decide +kernel) (by decide)
theorem b958:B 35 4 e881:=viaSmall (by decide +kernel) (by decide)
theorem b959:B 35 4 e882:=viaSmall (by decide +kernel) (by decide)
theorem b960:B 35 4 e883:=viaSmall (by decide +kernel) (by decide)
theorem b961:B 35 4 e884:=viaSmall (by decide +kernel) (by decide)
theorem b962:B 35 4 e885:=viaSmall (by decide +kernel) (by decide)
theorem b963:B 35 4 e886:=viaSmall (by decide +kernel) (by decide)
theorem b964:B 35 4 e887:=viaSmall (by decide +kernel) (by decide)
theorem b965:B 35 4 e888:=viaSmall (by decide +kernel) (by decide)
theorem b966:B 35 4 e889:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b967:B 35 5 e890:=viaBranch (ws:=[e863,e864,e865,e866,e867,e868,e869,e870,e871,e872,e873,e874,e875,e876,e877,e878,e879,e880,e881,e882,e883,e884,e885,e886,e887,e888,e889]) (consBan b940 (consBan b941 (consBan b942 (consBan b943 (consBan b944 (consBan b945 (consBan b946 (consBan b947 (consBan b948 (consBan b949 (consBan b950 (consBan b951 (consBan b952 (consBan b953 (consBan b954 (consBan b955 (consBan b956 (consBan b957 (consBan b958 (consBan b959 (consBan b960 (consBan b961 (consBan b962 (consBan b963 (consBan b964 (consBan b965 (consBan b966 (nilBan _ _)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w969:W 6 2 e102:=widen (by decide +kernel) b242
theorem b975:B 35 4 e890:=viaSmall (by decide +kernel) (by decide)
theorem b982:B 6 2 e102:=viaSmall (by decide +kernel) (by decide)
theorem b1024:B 87 6 e940:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1025:B 87 6 e941:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1026:B 87 6 e942:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1027:B 87 6 e943:=viaCut pjt_12 w111 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1028:B 87 6 e944:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1029:B 87 6 e945:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1030:B 87 6 e946:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1031:B 87 6 e947:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1032:B 87 6 e948:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1033:B 87 6 e949:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1034:B 87 6 e950:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1035:B 87 6 e951:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1036:B 87 6 e952:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1041:B 35 4 e957:=viaSmall (by decide +kernel) (by decide)
theorem b1042:B 35 4 e958:=viaSmall (by decide +kernel) (by decide)
theorem b1043:B 35 4 e959:=viaSmall (by decide +kernel) (by decide)
theorem b1044:B 35 4 e960:=viaSmall (by decide +kernel) (by decide)
theorem b1045:B 35 4 e961:=viaSmall (by decide +kernel) (by decide)
theorem b1046:B 35 4 e962:=viaSmall (by decide +kernel) (by decide)
theorem b1047:B 35 4 e963:=viaSmall (by decide +kernel) (by decide)
theorem b1048:B 35 4 e964:=viaSmall (by decide +kernel) (by decide)
theorem b1049:B 35 4 e965:=viaSmall (by decide +kernel) (by decide)
theorem b1050:B 35 4 e966:=viaSmall (by decide +kernel) (by decide)
theorem b1051:B 35 4 e967:=viaSmall (by decide +kernel) (by decide)
theorem b1052:B 35 4 e968:=viaSmall (by decide +kernel) (by decide)
theorem b1053:B 35 4 e969:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1054:B 35 5 e970:=viaBranch (ws:=[e957,e739,e958,e959,e960,e961,e962,e294,e963,e964,e965,e966,e967,e968,e969]) (consBan b1041 (consBan b799 (consBan b1042 (consBan b1043 (consBan b1044 (consBan b1045 (consBan b1046 (consBan b319 (consBan b1047 (consBan b1048 (consBan b1049 (consBan b1050 (consBan b1051 (consBan b1052 (consBan b1053 (nilBan _ _)))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w1055:W 35 5 e970:=viaSub (ws:=[e21,e768,e970]) (consBan b332 (consBan b829 (consBan b1054 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b1056:B 87 6 e971:=viaCut pjt_1 w1055 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1057:B 87 6 e972:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1058:B 87 6 e973:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1059:B 12 3 e974:=viaSmall (by decide +kernel) (by decide)
theorem b1060:B 12 3 e975:=viaSmall (by decide +kernel) (by decide)
theorem b1061:B 12 3 e976:=viaSmall (by decide +kernel) (by decide)
theorem b1062:B 12 3 e977:=viaSmall (by decide +kernel) (by decide)
theorem b1063:B 12 3 e978:=viaSmall (by decide +kernel) (by decide)
theorem b1064:B 12 3 e979:=viaSmall (by decide +kernel) (by decide)
theorem b1065:B 12 3 e980:=viaSmall (by decide +kernel) (by decide)
theorem b1066:B 12 3 e981:=viaSmall (by decide +kernel) (by decide)
theorem b1067:B 12 3 e982:=viaSmall (by decide +kernel) (by decide)
theorem b1068:B 12 3 e983:=viaSmall (by decide +kernel) (by decide)
theorem b1069:B 12 3 e984:=viaSmall (by decide +kernel) (by decide)
theorem b1070:B 12 3 e985:=viaSmall (by decide +kernel) (by decide)
theorem b1071:B 12 3 e986:=viaSmall (by decide +kernel) (by decide)
theorem b1072:B 12 3 e987:=viaSmall (by decide +kernel) (by decide)
theorem b1073:B 12 3 e988:=viaSmall (by decide +kernel) (by decide)
theorem b1074:B 12 3 e989:=viaSmall (by decide +kernel) (by decide)
theorem b1075:B 12 3 e990:=viaSmall (by decide +kernel) (by decide)
theorem b1076:B 12 3 e991:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1077:B 12 4 e992:=viaBranch (ws:=[e974,e975,e976,e977,e978,e401,e979,e980,e981,e982,e983,e984,e985,e986,e987,e988,e989,e990,e991]) (consBan b1059 (consBan b1060 (consBan b1061 (consBan b1062 (consBan b1063 (consBan b435 (consBan b1064 (consBan b1065 (consBan b1066 (consBan b1067 (consBan b1068 (consBan b1069 (consBan b1070 (consBan b1071 (consBan b1072 (consBan b1073 (consBan b1074 (consBan b1075 (consBan b1076 (nilBan _ _)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w1078:W 12 4 e992:=widen (by decide +kernel) b1077
theorem b1079:B 87 6 e993:=viaCut pjt_10 w1078 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1080:B 87 6 e994:=viaCut pjt_9 w205 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1081:B 87 6 e995:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1082:B 87 6 e996:=viaPerm pt1 pti1 b1029 (by decide +kernel) (by decide +kernel)
theorem b1083:B 87 6 e997:=viaPerm pt1 pti1 b1030 (by decide +kernel) (by decide +kernel)
theorem b1084:B 87 6 e998:=viaPerm pt1 pti1 b1031 (by decide +kernel) (by decide +kernel)
theorem b1085:B 87 6 e999:=viaPerm pt1 pti1 b1032 (by decide +kernel) (by decide +kernel)
theorem b1086:B 87 6 e1000:=viaPerm pt1 pti1 b1033 (by decide +kernel) (by decide +kernel)
theorem b1087:B 87 6 e1001:=viaPerm pt1 pti1 b1034 (by decide +kernel) (by decide +kernel)
theorem b1088:B 87 6 e1002:=viaPerm pt1 pti1 b1035 (by decide +kernel) (by decide +kernel)
theorem b1089:B 87 6 e1003:=viaPerm pt1 pti1 b1036 (by decide +kernel) (by decide +kernel)
theorem b1090:B 87 6 e1004:=viaPerm pt1 pti1 b1056 (by decide +kernel) (by decide +kernel)
theorem b1091:B 87 6 e1005:=viaPerm pt1 pti1 b1057 (by decide +kernel) (by decide +kernel)
theorem b1092:B 87 6 e1006:=viaPerm pt1 pti1 b1058 (by decide +kernel) (by decide +kernel)
theorem b1093:B 87 6 e1007:=viaPerm pt1 pti1 b1079 (by decide +kernel) (by decide +kernel)
theorem b1094:B 87 6 e1008:=viaPerm pt1 pti1 b1080 (by decide +kernel) (by decide +kernel)
theorem b1095:B 87 6 e1009:=viaPerm pt1 pti1 b1081 (by decide +kernel) (by decide +kernel)
theorem b1096:B 87 6 e1010:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1097:B 87 6 e1011:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1098:B 87 6 e1012:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1099:B 87 6 e1013:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1100:B 87 6 e1014:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1101:B 87 6 e1015:=viaCut pjt_16 w856 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1102:B 87 6 e1016:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1103:B 87 6 e1017:=viaCut pjt_18 w862 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1104:B 87 6 e1018:=viaCut pjt_18 w865 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1105:B 87 6 e1019:=viaPerm pt1 pti1 b1097 (by decide +kernel) (by decide +kernel)
theorem b1106:B 87 6 e1020:=viaPerm pt1 pti1 b1098 (by decide +kernel) (by decide +kernel)
theorem b1107:B 87 6 e1021:=viaPerm pt1 pti1 b1099 (by decide +kernel) (by decide +kernel)
theorem b1108:B 87 6 e1022:=viaPerm pt1 pti1 b1100 (by decide +kernel) (by decide +kernel)
theorem b1109:B 87 6 e1023:=viaPerm pt1 pti1 b1101 (by decide +kernel) (by decide +kernel)
theorem b1110:B 87 6 e1024:=viaPerm pt1 pti1 b1102 (by decide +kernel) (by decide +kernel)
theorem b1111:B 87 6 e1025:=viaPerm pt1 pti1 b1103 (by decide +kernel) (by decide +kernel)
theorem b1112:B 87 6 e1026:=viaPerm pt1 pti1 b1104 (by decide +kernel) (by decide +kernel)
theorem b1113:B 87 6 e1027:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1114:B 87 6 e1028:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1115:B 87 6 e1029:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1116:B 87 6 e1030:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1117:B 16 3 e1031:=viaSmall (by decide +kernel) (by decide)
theorem b1118:B 16 3 e1032:=viaSmall (by decide +kernel) (by decide)
theorem w1119:W 16 3 e1032:=viaSub (ws:=[e1031,e1032]) (consBan b1117 (consBan b1118 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1120:B 87 6 e1033:=viaCut pjt_9 w1119 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1121:B 87 6 e1034:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1122:B 87 6 e1035:=viaCut pjt_18 w862 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1123:B 87 6 e1036:=viaCut pjt_18 w865 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1124:B 87 6 e1037:=viaPerm pt1 pti1 b1113 (by decide +kernel) (by decide +kernel)
theorem b1125:B 87 6 e1038:=viaPerm pt1 pti1 b1114 (by decide +kernel) (by decide +kernel)
theorem b1126:B 87 6 e1039:=viaPerm pt1 pti1 b1115 (by decide +kernel) (by decide +kernel)
theorem b1127:B 87 6 e1040:=viaPerm pt1 pti1 b1116 (by decide +kernel) (by decide +kernel)
theorem b1128:B 87 6 e1041:=viaPerm pt1 pti1 b1120 (by decide +kernel) (by decide +kernel)
theorem b1129:B 87 6 e1042:=viaPerm pt1 pti1 b1121 (by decide +kernel) (by decide +kernel)
theorem b1130:B 87 6 e1043:=viaPerm pt1 pti1 b1122 (by decide +kernel) (by decide +kernel)
theorem b1131:B 87 6 e1044:=viaPerm pt1 pti1 b1123 (by decide +kernel) (by decide +kernel)
theorem b1132:B 87 6 e1045:=viaPerm pt0 pti0 b531 (by decide +kernel) (by decide +kernel)
theorem b1133:B 87 6 e1046:=viaPerm pt0 pti0 b880 (by decide +kernel) (by decide +kernel)
theorem b1134:B 87 6 e1047:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1135:B 87 6 e1048:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1136:B 87 6 e1049:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1137:B 87 6 e1050:=viaPerm pt1 pti1 b1136 (by decide +kernel) (by decide +kernel)
theorem b1138:B 87 6 e1051:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1139:B 87 6 e1052:=viaPerm pt1 pti1 b1138 (by decide +kernel) (by decide +kernel)
theorem b1140:B 87 6 e1053:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1141:B 87 6 e1054:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1142:B 87 6 e1055:=viaPerm pt1 pti1 b1140 (by decide +kernel) (by decide +kernel)
theorem b1143:B 87 6 e1056:=viaPerm pt1 pti1 b1141 (by decide +kernel) (by decide +kernel)
theorem b1144:B 87 6 e1057:=viaPerm pt1 pti1 b1132 (by decide +kernel) (by decide +kernel)
theorem b1145:B 87 6 e1058:=viaPerm pt1 pti1 b1133 (by decide +kernel) (by decide +kernel)
theorem b1146:B 87 6 e1059:=viaPerm pt1 pti1 b1134 (by decide +kernel) (by decide +kernel)
theorem b1147:B 87 6 e1060:=viaPerm pt1 pti1 b1135 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1148:B 87 7 e1061:=viaBranch (ws:=[e940,e941,e279,e281,e942,e723,e943,e724,e944,e945,e946,e947,e948,e949,e950,e951,e952,e971,e972,e973,e993,e994,e995,e996,e997,e998,e999,e1000,e1001,e1002,e1003,e1004,e1005,e1006,e1007,e1008,e1009,e1010,e1011,e1012,e1013,e1014,e1015,e1016,e1017,e1018,e1019,e1020,e1021,e1022,e1023,e1024,e1025,e1026,e1027,e1028,e1029,e1030,e1033,e1034,e1035,e1036,e1037,e1038,e1039,e1040,e1041,e1042,e1043,e1044,e1045,e1046,e1047,e1048,e1049,e1050,e1051,e1052,e1053,e1054,e1055,e1056,e1057,e1058,e1059,e1060]) (consBan b1024 (consBan b1025 (consBan b303 (consBan b305 (consBan b1026 (consBan b780 (consBan b1027 (consBan b782 (consBan b1028 (consBan b1029 (consBan b1030 (consBan b1031 (consBan b1032 (consBan b1033 (consBan b1034 (consBan b1035 (consBan b1036 (consBan b1056 (consBan b1057 (consBan b1058 (consBan b1079 (consBan b1080 (consBan b1081 (consBan b1082 (consBan b1083 (consBan b1084 (consBan b1085 (consBan b1086 (consBan b1087 (consBan b1088 (consBan b1089 (consBan b1090 (consBan b1091 (consBan b1092 (consBan b1093 (consBan b1094 (consBan b1095 (consBan b1096 (consBan b1097 (consBan b1098 (consBan b1099 (consBan b1100 (consBan b1101 (consBan b1102 (consBan b1103 (consBan b1104 (consBan b1105 (consBan b1106 (consBan b1107 (consBan b1108 (consBan b1109 (consBan b1110 (consBan b1111 (consBan b1112 (consBan b1113 (consBan b1114 (consBan b1115 (consBan b1116 (consBan b1120 (consBan b1121 (consBan b1122 (consBan b1123 (consBan b1124 (consBan b1125 (consBan b1126 (consBan b1127 (consBan b1128 (consBan b1129 (consBan b1130 (consBan b1131 (consBan b1132 (consBan b1133 (consBan b1134 (consBan b1135 (consBan b1136 (consBan b1137 (consBan b1138 (consBan b1139 (consBan b1140 (consBan b1141 (consBan b1142 (consBan b1143 (consBan b1144 (consBan b1145 (consBan b1146 (consBan b1147 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1229:B 16 3 e1112:=viaSmall (by decide +kernel) (by decide)
theorem w1230:W 16 3 e1112:=widen (by decide +kernel) b1229
theorem b1244:B 87 6 e636:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1245:B 87 6 e1127:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1246:B 87 6 e1128:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1247:B 87 6 e1129:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1248:B 87 6 e1130:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1249:B 87 6 e1131:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1250:B 87 6 e1132:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1251:B 87 6 e1133:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1252:B 87 6 e1134:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1253:B 87 6 e1135:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1254:B 87 6 e1136:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1255:B 87 6 e1137:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1256:B 87 6 e1138:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1257:B 87 6 e1139:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1258:B 87 6 e1140:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1259:B 87 6 e1141:=viaPerm pt1 pti1 b1245 (by decide +kernel) (by decide +kernel)
theorem b1260:B 87 6 e1142:=viaPerm pt1 pti1 b1246 (by decide +kernel) (by decide +kernel)
theorem b1261:B 87 6 e1143:=viaPerm pt1 pti1 b1247 (by decide +kernel) (by decide +kernel)
theorem b1262:B 87 6 e1144:=viaPerm pt1 pti1 b1248 (by decide +kernel) (by decide +kernel)
theorem b1263:B 87 6 e1145:=viaPerm pt1 pti1 b1249 (by decide +kernel) (by decide +kernel)
theorem b1264:B 87 6 e1146:=viaPerm pt1 pti1 b1250 (by decide +kernel) (by decide +kernel)
theorem b1265:B 87 6 e1147:=viaPerm pt1 pti1 b1251 (by decide +kernel) (by decide +kernel)
theorem b1266:B 87 6 e1148:=viaPerm pt1 pti1 b1252 (by decide +kernel) (by decide +kernel)
theorem b1267:B 87 6 e1149:=viaPerm pt1 pti1 b1253 (by decide +kernel) (by decide +kernel)
theorem b1268:B 87 6 e1150:=viaPerm pt1 pti1 b1254 (by decide +kernel) (by decide +kernel)
theorem b1269:B 87 6 e1151:=viaPerm pt1 pti1 b1255 (by decide +kernel) (by decide +kernel)
theorem b1270:B 87 6 e1152:=viaPerm pt1 pti1 b1256 (by decide +kernel) (by decide +kernel)
theorem b1271:B 87 6 e1153:=viaPerm pt1 pti1 b1257 (by decide +kernel) (by decide +kernel)
theorem b1272:B 87 6 e1154:=viaPerm pt1 pti1 b1258 (by decide +kernel) (by decide +kernel)
theorem b1273:B 87 6 e1155:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1274:B 87 6 e1156:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1275:B 87 6 e1157:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1276:B 87 6 e1158:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1277:B 87 6 e1159:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1278:B 87 6 e1160:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1279:B 87 6 e1161:=viaCut pjt_9 w1230 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1280:B 87 6 e1162:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1281:B 87 6 e1163:=viaCut pjt_18 w862 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1282:B 87 6 e1164:=viaCut pjt_9 w1230 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1283:B 87 6 e1165:=viaPerm pt1 pti1 b1273 (by decide +kernel) (by decide +kernel)
theorem b1284:B 87 6 e1166:=viaPerm pt1 pti1 b1274 (by decide +kernel) (by decide +kernel)
theorem b1285:B 87 6 e1167:=viaPerm pt1 pti1 b1275 (by decide +kernel) (by decide +kernel)
theorem b1286:B 87 6 e1168:=viaPerm pt1 pti1 b1276 (by decide +kernel) (by decide +kernel)
theorem b1287:B 87 6 e1169:=viaPerm pt1 pti1 b1277 (by decide +kernel) (by decide +kernel)
theorem b1288:B 87 6 e1170:=viaPerm pt1 pti1 b1278 (by decide +kernel) (by decide +kernel)
theorem b1289:B 87 6 e1171:=viaPerm pt1 pti1 b1279 (by decide +kernel) (by decide +kernel)
theorem b1290:B 87 6 e1172:=viaPerm pt1 pti1 b1280 (by decide +kernel) (by decide +kernel)
theorem b1291:B 87 6 e1173:=viaPerm pt1 pti1 b1281 (by decide +kernel) (by decide +kernel)
theorem b1292:B 87 6 e1174:=viaPerm pt1 pti1 b1282 (by decide +kernel) (by decide +kernel)
theorem b1293:B 87 6 e1175:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1294:B 87 6 e468:=viaPerm pt0 pti0 b542 (by decide +kernel) (by decide +kernel)
theorem b1295:B 87 6 e1176:=viaPerm pt0 pti0 b881 (by decide +kernel) (by decide +kernel)
theorem b1296:B 87 6 e1177:=viaPerm pt0 pti0 b1134 (by decide +kernel) (by decide +kernel)
theorem b1297:B 87 6 e1178:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1298:B 87 6 e1179:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1299:B 87 6 e1180:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1300:B 87 6 e1181:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1301:B 87 6 e1182:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1302:B 87 6 e1183:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1303:B 87 6 e1184:=viaPerm pt1 pti1 b1302 (by decide +kernel) (by decide +kernel)
theorem b1304:B 87 6 e1185:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1305:B 87 6 e1186:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1306:B 87 6 e1187:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1307:B 87 6 e1188:=viaPerm pt1 pti1 b1305 (by decide +kernel) (by decide +kernel)
theorem b1308:B 87 6 e1189:=viaPerm pt1 pti1 b1306 (by decide +kernel) (by decide +kernel)
theorem b1309:B 87 6 e1190:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1310:B 87 6 e1191:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1311:B 87 6 e1192:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1312:B 87 6 e1193:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1313:B 87 6 e1194:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1314:B 87 6 e1195:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1315:B 87 6 e1196:=viaPerm pt1 pti1 b1309 (by decide +kernel) (by decide +kernel)
theorem b1316:B 87 6 e1197:=viaPerm pt1 pti1 b1310 (by decide +kernel) (by decide +kernel)
theorem b1317:B 87 6 e1198:=viaPerm pt1 pti1 b1311 (by decide +kernel) (by decide +kernel)
theorem b1318:B 87 6 e1199:=viaPerm pt1 pti1 b1313 (by decide +kernel) (by decide +kernel)
theorem b1319:B 87 6 e1200:=viaPerm pt1 pti1 b1314 (by decide +kernel) (by decide +kernel)
theorem b1320:B 87 6 e1201:=viaPerm pt1 pti1 b1312 (by decide +kernel) (by decide +kernel)
theorem b1321:B 87 6 e1202:=viaCut pjt_9 w1230 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1322:B 87 6 e1203:=viaCut pjt_11 w911 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1323:B 87 6 e1204:=viaCut pjt_9 w1230 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1324:B 87 6 e1205:=viaPerm pt1 pti1 b1323 (by decide +kernel) (by decide +kernel)
theorem b1325:B 87 6 e1206:=viaPerm pt1 pti1 b1293 (by decide +kernel) (by decide +kernel)
theorem b1326:B 87 6 e1207:=viaPerm pt1 pti1 b1294 (by decide +kernel) (by decide +kernel)
theorem b1327:B 87 6 e1208:=viaPerm pt1 pti1 b1295 (by decide +kernel) (by decide +kernel)
theorem b1328:B 87 6 e1209:=viaPerm pt1 pti1 b1296 (by decide +kernel) (by decide +kernel)
theorem b1329:B 87 6 e1210:=viaPerm pt1 pti1 b1297 (by decide +kernel) (by decide +kernel)
theorem b1330:B 87 6 e1211:=viaPerm pt1 pti1 b1298 (by decide +kernel) (by decide +kernel)
theorem b1331:B 87 6 e1212:=viaPerm pt1 pti1 b1299 (by decide +kernel) (by decide +kernel)
theorem b1332:B 87 6 e1213:=viaPerm pt1 pti1 b1300 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1333:B 87 7 e280:=viaBranch (ws:=[e636,e279,e281,e1127,e1128,e1129,e1130,e1131,e1132,e1133,e1134,e1135,e1136,e1137,e1138,e1139,e1140,e1141,e1142,e1143,e1144,e1145,e1146,e1147,e1148,e1149,e1150,e1151,e1152,e1153,e1154,e1155,e1156,e1157,e1158,e1159,e1160,e1161,e1162,e1163,e1164,e1165,e1166,e1167,e1168,e1169,e1170,e1171,e1172,e1173,e1174,e1175,e468,e1176,e1177,e1178,e1179,e1180,e1181,e1182,e1183,e1184,e1185,e1186,e1187,e1188,e1189,e1190,e1191,e1192,e1193,e1194,e1195,e1196,e1197,e1198,e1199,e1200,e1201,e1202,e1203,e1204,e1205,e1206,e1207,e1208,e1209,e1210,e1211,e1212,e1213]) (consBan b1244 (consBan b303 (consBan b305 (consBan b1245 (consBan b1246 (consBan b1247 (consBan b1248 (consBan b1249 (consBan b1250 (consBan b1251 (consBan b1252 (consBan b1253 (consBan b1254 (consBan b1255 (consBan b1256 (consBan b1257 (consBan b1258 (consBan b1259 (consBan b1260 (consBan b1261 (consBan b1262 (consBan b1263 (consBan b1264 (consBan b1265 (consBan b1266 (consBan b1267 (consBan b1268 (consBan b1269 (consBan b1270 (consBan b1271 (consBan b1272 (consBan b1273 (consBan b1274 (consBan b1275 (consBan b1276 (consBan b1277 (consBan b1278 (consBan b1279 (consBan b1280 (consBan b1281 (consBan b1282 (consBan b1283 (consBan b1284 (consBan b1285 (consBan b1286 (consBan b1287 (consBan b1288 (consBan b1289 (consBan b1290 (consBan b1291 (consBan b1292 (consBan b1293 (consBan b1294 (consBan b1295 (consBan b1296 (consBan b1297 (consBan b1298 (consBan b1299 (consBan b1300 (consBan b1301 (consBan b1302 (consBan b1303 (consBan b1304 (consBan b1305 (consBan b1306 (consBan b1307 (consBan b1308 (consBan b1309 (consBan b1310 (consBan b1311 (consBan b1312 (consBan b1313 (consBan b1314 (consBan b1315 (consBan b1316 (consBan b1317 (consBan b1318 (consBan b1319 (consBan b1320 (consBan b1321 (consBan b1322 (consBan b1323 (consBan b1324 (consBan b1325 (consBan b1326 (consBan b1327 (consBan b1328 (consBan b1329 (consBan b1330 (consBan b1331 (consBan b1332 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1334:B 87 7 e1010:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1377:B 35 4 e1253:=viaSmall (by decide +kernel) (by decide)
theorem b1399:B 87 6 e697:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1400:B 87 6 e1274:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1401:B 87 6 e1275:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1402:B 87 6 e1276:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1403:B 87 6 e1277:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1404:B 87 6 e1278:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1405:B 87 6 e1279:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1406:B 87 6 e1280:=viaCut pjt_12 w111 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1407:B 87 6 e1281:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1408:B 87 6 e1282:=viaCut pjt_18 w862 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1409:B 87 6 e1283:=viaCut pjt_18 w865 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1410:B 87 6 e1284:=viaPerm pt1 pti1 b1400 (by decide +kernel) (by decide +kernel)
theorem b1411:B 87 6 e1285:=viaPerm pt1 pti1 b1401 (by decide +kernel) (by decide +kernel)
theorem b1412:B 87 6 e1286:=viaPerm pt1 pti1 b1402 (by decide +kernel) (by decide +kernel)
theorem b1413:B 87 6 e1287:=viaPerm pt1 pti1 b1403 (by decide +kernel) (by decide +kernel)
theorem b1414:B 87 6 e1288:=viaPerm pt1 pti1 b1404 (by decide +kernel) (by decide +kernel)
theorem b1415:B 87 6 e1289:=viaPerm pt1 pti1 b1405 (by decide +kernel) (by decide +kernel)
theorem b1416:B 87 6 e1290:=viaPerm pt1 pti1 b1406 (by decide +kernel) (by decide +kernel)
theorem b1417:B 87 6 e1291:=viaPerm pt1 pti1 b1407 (by decide +kernel) (by decide +kernel)
theorem b1418:B 87 6 e1292:=viaPerm pt1 pti1 b1408 (by decide +kernel) (by decide +kernel)
theorem b1419:B 87 6 e1293:=viaPerm pt1 pti1 b1409 (by decide +kernel) (by decide +kernel)
theorem b1420:B 87 6 e1294:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1421:B 87 6 e1295:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1422:B 87 6 e1296:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1423:B 87 6 e1297:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1424:B 87 6 e1298:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1425:B 87 6 e1299:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1426:B 87 6 e1300:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1427:B 87 6 e1301:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1428:B 87 6 e1302:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1429:B 87 6 e1303:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1430:B 87 6 e1304:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1431:B 87 6 e1305:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1432:B 87 6 e1306:=viaPerm pt1 pti1 b1420 (by decide +kernel) (by decide +kernel)
theorem b1433:B 87 6 e1307:=viaPerm pt1 pti1 b1421 (by decide +kernel) (by decide +kernel)
theorem b1434:B 87 6 e1308:=viaPerm pt1 pti1 b1422 (by decide +kernel) (by decide +kernel)
theorem b1435:B 87 6 e1309:=viaPerm pt1 pti1 b1423 (by decide +kernel) (by decide +kernel)
theorem b1436:B 87 6 e1310:=viaPerm pt1 pti1 b1424 (by decide +kernel) (by decide +kernel)
theorem b1437:B 87 6 e1311:=viaPerm pt1 pti1 b1425 (by decide +kernel) (by decide +kernel)
theorem b1438:B 87 6 e1312:=viaPerm pt1 pti1 b1426 (by decide +kernel) (by decide +kernel)
theorem b1439:B 87 6 e1313:=viaPerm pt1 pti1 b1427 (by decide +kernel) (by decide +kernel)
theorem b1440:B 87 6 e1314:=viaPerm pt1 pti1 b1428 (by decide +kernel) (by decide +kernel)
theorem b1441:B 87 6 e1315:=viaPerm pt1 pti1 b1429 (by decide +kernel) (by decide +kernel)
theorem b1442:B 87 6 e1316:=viaPerm pt1 pti1 b1430 (by decide +kernel) (by decide +kernel)
theorem b1443:B 87 6 e1317:=viaPerm pt1 pti1 b1431 (by decide +kernel) (by decide +kernel)
theorem b1444:B 87 6 e1318:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1445:B 87 6 e1319:=viaPerm pt0 pti0 b552 (by decide +kernel) (by decide +kernel)
theorem b1446:B 87 6 e1320:=viaPerm pt0 pti0 b883 (by decide +kernel) (by decide +kernel)
theorem b1447:B 87 6 e1321:=viaPerm pt0 pti0 b1135 (by decide +kernel) (by decide +kernel)
theorem b1448:B 87 6 e1322:=viaPerm pt0 pti0 b1299 (by decide +kernel) (by decide +kernel)
theorem b1449:B 87 6 e1323:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1450:B 87 6 e1324:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1451:B 87 6 e1325:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1452:B 87 6 e1326:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1453:B 87 6 e1327:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1454:B 87 6 e1328:=viaPerm pt1 pti1 b1453 (by decide +kernel) (by decide +kernel)
theorem b1455:B 87 6 e1329:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1456:B 87 6 e1330:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1457:B 87 6 e1331:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1458:B 87 6 e1332:=viaPerm pt1 pti1 b1456 (by decide +kernel) (by decide +kernel)
theorem b1459:B 87 6 e1333:=viaPerm pt1 pti1 b1457 (by decide +kernel) (by decide +kernel)
theorem b1460:B 87 6 e1334:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1461:B 87 6 e1335:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1462:B 87 6 e1336:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1463:B 87 6 e1337:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1464:B 87 6 e1338:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1465:B 87 6 e1339:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1466:B 87 6 e1340:=viaPerm pt1 pti1 b1460 (by decide +kernel) (by decide +kernel)
theorem b1467:B 87 6 e1341:=viaPerm pt1 pti1 b1461 (by decide +kernel) (by decide +kernel)
theorem b1468:B 87 6 e1342:=viaPerm pt1 pti1 b1462 (by decide +kernel) (by decide +kernel)
theorem b1469:B 87 6 e1343:=viaPerm pt1 pti1 b1464 (by decide +kernel) (by decide +kernel)
theorem b1470:B 87 6 e1344:=viaPerm pt1 pti1 b1465 (by decide +kernel) (by decide +kernel)
theorem b1471:B 87 6 e1345:=viaPerm pt1 pti1 b1463 (by decide +kernel) (by decide +kernel)
theorem b1472:B 87 6 e1346:=viaCut pjt_17 w907 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1473:B 87 6 e1347:=viaCut pjt_11 w911 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1474:B 87 6 e1348:=viaCut pjt_18 w914 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1475:B 87 6 e1349:=viaPerm pt1 pti1 b1474 (by decide +kernel) (by decide +kernel)
theorem b1476:B 87 6 e1350:=viaPerm pt1 pti1 b1444 (by decide +kernel) (by decide +kernel)
theorem b1477:B 87 6 e1351:=viaPerm pt1 pti1 b1445 (by decide +kernel) (by decide +kernel)
theorem b1478:B 87 6 e1352:=viaPerm pt1 pti1 b1446 (by decide +kernel) (by decide +kernel)
theorem b1479:B 87 6 e1353:=viaPerm pt1 pti1 b1447 (by decide +kernel) (by decide +kernel)
theorem b1480:B 87 6 e1354:=viaPerm pt1 pti1 b1448 (by decide +kernel) (by decide +kernel)
theorem b1481:B 87 6 e1355:=viaPerm pt1 pti1 b1449 (by decide +kernel) (by decide +kernel)
theorem b1482:B 87 6 e1356:=viaPerm pt1 pti1 b1450 (by decide +kernel) (by decide +kernel)
theorem b1483:B 87 6 e1357:=viaPerm pt1 pti1 b1451 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1484:B 87 7 e698:=viaBranch (ws:=[e697,e723,e724,e1274,e1275,e1276,e1277,e1278,e1279,e1280,e1281,e1282,e1283,e1284,e1285,e1286,e1287,e1288,e1289,e1290,e1291,e1292,e1293,e1294,e1295,e1296,e1297,e1298,e1299,e1300,e1301,e1302,e1303,e1304,e1305,e1306,e1307,e1308,e1309,e1310,e1311,e1312,e1313,e1314,e1315,e1316,e1317,e1318,e1319,e1320,e1321,e1322,e1323,e1324,e1325,e1326,e1327,e1328,e1329,e1330,e1331,e1332,e1333,e1334,e1335,e1336,e1337,e1338,e1339,e1340,e1341,e1342,e1343,e1344,e1345,e1346,e1347,e1348,e1349,e1350,e1351,e1352,e1353,e1354,e1355,e1356,e1357]) (consBan b1399 (consBan b780 (consBan b782 (consBan b1400 (consBan b1401 (consBan b1402 (consBan b1403 (consBan b1404 (consBan b1405 (consBan b1406 (consBan b1407 (consBan b1408 (consBan b1409 (consBan b1410 (consBan b1411 (consBan b1412 (consBan b1413 (consBan b1414 (consBan b1415 (consBan b1416 (consBan b1417 (consBan b1418 (consBan b1419 (consBan b1420 (consBan b1421 (consBan b1422 (consBan b1423 (consBan b1424 (consBan b1425 (consBan b1426 (consBan b1427 (consBan b1428 (consBan b1429 (consBan b1430 (consBan b1431 (consBan b1432 (consBan b1433 (consBan b1434 (consBan b1435 (consBan b1436 (consBan b1437 (consBan b1438 (consBan b1439 (consBan b1440 (consBan b1441 (consBan b1442 (consBan b1443 (consBan b1444 (consBan b1445 (consBan b1446 (consBan b1447 (consBan b1448 (consBan b1449 (consBan b1450 (consBan b1451 (consBan b1452 (consBan b1453 (consBan b1454 (consBan b1455 (consBan b1456 (consBan b1457 (consBan b1458 (consBan b1459 (consBan b1460 (consBan b1461 (consBan b1462 (consBan b1463 (consBan b1464 (consBan b1465 (consBan b1466 (consBan b1467 (consBan b1468 (consBan b1469 (consBan b1470 (consBan b1471 (consBan b1472 (consBan b1473 (consBan b1474 (consBan b1475 (consBan b1476 (consBan b1477 (consBan b1478 (consBan b1479 (consBan b1480 (consBan b1481 (consBan b1482 (consBan b1483 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1485:B 87 6 e1061:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1486:B 87 6 e17:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1487:B 87 6 e1358:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1488:B 87 6 e1359:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1489:B 87 6 e1360:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1490:B 87 6 e1361:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1491:B 87 6 e1362:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1492:B 87 6 e1363:=viaCut pjt_12 w111 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1493:B 87 6 e1364:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1494:B 87 6 e1365:=viaCut pjt_18 w862 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1495:B 87 6 e1366:=viaCut pjt_18 w865 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1496:B 87 6 e1367:=viaPerm pt1 pti1 b1488 (by decide +kernel) (by decide +kernel)
theorem b1497:B 87 6 e1368:=viaPerm pt1 pti1 b1489 (by decide +kernel) (by decide +kernel)
theorem b1498:B 87 6 e1369:=viaPerm pt1 pti1 b1490 (by decide +kernel) (by decide +kernel)
theorem b1499:B 87 6 e1370:=viaPerm pt1 pti1 b1491 (by decide +kernel) (by decide +kernel)
theorem b1500:B 87 6 e1371:=viaPerm pt1 pti1 b1492 (by decide +kernel) (by decide +kernel)
theorem b1501:B 87 6 e1372:=viaPerm pt1 pti1 b1493 (by decide +kernel) (by decide +kernel)
theorem b1502:B 87 6 e1373:=viaPerm pt1 pti1 b1494 (by decide +kernel) (by decide +kernel)
theorem b1503:B 87 6 e1374:=viaPerm pt1 pti1 b1495 (by decide +kernel) (by decide +kernel)
theorem b1504:B 87 6 e1375:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1505:B 87 6 e1376:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1506:B 87 6 e1377:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1507:B 87 6 e1378:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1508:B 87 6 e1379:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1509:B 87 6 e1380:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1510:B 87 6 e1381:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1511:B 87 6 e1382:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1512:B 87 6 e1383:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1513:B 87 6 e1384:=viaPerm pt1 pti1 b1507 (by decide +kernel) (by decide +kernel)
theorem b1514:B 87 6 e1385:=viaPerm pt1 pti1 b1508 (by decide +kernel) (by decide +kernel)
theorem b1515:B 87 6 e1386:=viaPerm pt1 pti1 b1509 (by decide +kernel) (by decide +kernel)
theorem b1516:B 87 6 e1387:=viaPerm pt1 pti1 b1510 (by decide +kernel) (by decide +kernel)
theorem b1517:B 87 6 e1388:=viaPerm pt1 pti1 b1511 (by decide +kernel) (by decide +kernel)
theorem b1518:B 87 6 e1389:=viaPerm pt1 pti1 b1512 (by decide +kernel) (by decide +kernel)
theorem b1519:B 87 6 e1390:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1520:B 87 6 e1391:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1521:B 87 6 e1392:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1522:B 87 6 e1393:=viaCut pjt_18 w862 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1523:B 87 6 e1394:=viaPerm pt1 pti1 b1519 (by decide +kernel) (by decide +kernel)
theorem b1524:B 87 6 e1395:=viaPerm pt1 pti1 b1520 (by decide +kernel) (by decide +kernel)
theorem b1525:B 87 6 e1396:=viaPerm pt1 pti1 b1521 (by decide +kernel) (by decide +kernel)
theorem b1526:B 87 6 e1397:=viaPerm pt1 pti1 b1522 (by decide +kernel) (by decide +kernel)
theorem b1527:B 87 6 e1398:=viaPerm pt0 pti0 b553 (by decide +kernel) (by decide +kernel)
theorem b1528:B 87 6 e1399:=viaPerm pt0 pti0 b884 (by decide +kernel) (by decide +kernel)
theorem b1529:B 87 6 e1400:=viaPerm pt0 pti0 b1300 (by decide +kernel) (by decide +kernel)
theorem b1530:B 87 6 e1401:=viaPerm pt0 pti0 b1451 (by decide +kernel) (by decide +kernel)
theorem b1531:B 87 6 e1402:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1532:B 87 6 e1403:=viaPerm pt1 pti1 b1531 (by decide +kernel) (by decide +kernel)
theorem b1533:B 87 6 e1404:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1534:B 87 6 e1405:=viaPerm pt1 pti1 b1533 (by decide +kernel) (by decide +kernel)
theorem b1535:B 87 6 e1406:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1536:B 87 6 e1407:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1537:B 87 6 e1408:=viaPerm pt1 pti1 b1535 (by decide +kernel) (by decide +kernel)
theorem b1538:B 87 6 e1409:=viaPerm pt1 pti1 b1536 (by decide +kernel) (by decide +kernel)
theorem b1539:B 87 6 e1410:=viaPerm pt1 pti1 b1527 (by decide +kernel) (by decide +kernel)
theorem b1540:B 87 6 e1411:=viaPerm pt1 pti1 b1528 (by decide +kernel) (by decide +kernel)
theorem b1541:B 87 6 e1412:=viaPerm pt1 pti1 b1529 (by decide +kernel) (by decide +kernel)
theorem b1542:B 87 6 e1413:=viaPerm pt1 pti1 b1530 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1543:B 87 7 e944:=viaBranch (ws:=[e636,e1061,e943,e17,e1358,e1359,e1360,e1361,e1362,e1363,e1364,e1365,e1366,e1367,e1368,e1369,e1370,e1371,e1372,e1373,e1374,e723,e724,e1375,e1376,e1377,e1378,e1379,e1380,e1381,e1382,e1383,e1384,e1385,e1386,e1387,e1388,e1389,e1274,e1390,e1391,e1279,e1280,e1392,e1393,e1283,e1284,e1394,e1395,e1289,e1290,e1396,e1397,e1293,e1398,e1399,e1400,e1401,e1402,e1403,e1404,e1405,e1406,e1407,e1408,e1409,e1410,e1411,e1412,e1413]) (consBan b1244 (consBan b1485 (consBan b1027 (consBan b1486 (consBan b1487 (consBan b1488 (consBan b1489 (consBan b1490 (consBan b1491 (consBan b1492 (consBan b1493 (consBan b1494 (consBan b1495 (consBan b1496 (consBan b1497 (consBan b1498 (consBan b1499 (consBan b1500 (consBan b1501 (consBan b1502 (consBan b1503 (consBan b780 (consBan b782 (consBan b1504 (consBan b1505 (consBan b1506 (consBan b1507 (consBan b1508 (consBan b1509 (consBan b1510 (consBan b1511 (consBan b1512 (consBan b1513 (consBan b1514 (consBan b1515 (consBan b1516 (consBan b1517 (consBan b1518 (consBan b1400 (consBan b1519 (consBan b1520 (consBan b1405 (consBan b1406 (consBan b1521 (consBan b1522 (consBan b1409 (consBan b1410 (consBan b1523 (consBan b1524 (consBan b1415 (consBan b1416 (consBan b1525 (consBan b1526 (consBan b1419 (consBan b1527 (consBan b1528 (consBan b1529 (consBan b1530 (consBan b1531 (consBan b1532 (consBan b1533 (consBan b1534 (consBan b1535 (consBan b1536 (consBan b1537 (consBan b1538 (consBan b1539 (consBan b1540 (consBan b1541 (consBan b1542 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1544:B 87 7 e1414:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1546:B 16 3 e1416:=viaPerm pc9_0 pci9_0 b204 (by decide +kernel) (by decide +kernel)
theorem w1547:W 16 3 e1416:=widen (by decide +kernel) b1546
theorem b1556:B 35 4 e1425:=viaSmall (by decide +kernel) (by decide)
theorem b1557:B 35 4 e1426:=viaSmall (by decide +kernel) (by decide)
theorem b1564:B 35 4 e1433:=viaSmall (by decide +kernel) (by decide)
theorem b1566:B 35 4 e1435:=viaSmall (by decide +kernel) (by decide)
theorem b1591:B 35 4 e1460:=viaSmall (by decide +kernel) (by decide)
theorem b1592:B 35 4 e1461:=viaSmall (by decide +kernel) (by decide)
theorem b1602:B 35 4 e1471:=viaSmall (by decide +kernel) (by decide)
theorem b1604:B 35 4 e1473:=viaSmall (by decide +kernel) (by decide)
theorem b1618:B 35 4 e1487:=viaSmall (by decide +kernel) (by decide)
theorem b1621:B 35 4 e1490:=viaSmall (by decide +kernel) (by decide)
theorem b1623:B 35 4 e1492:=viaSmall (by decide +kernel) (by decide)
theorem b1632:B 35 4 e1447:=viaSmall (by decide +kernel) (by decide)
theorem b1649:B 35 4 e1517:=viaSmall (by decide +kernel) (by decide)
theorem b1658:B 35 4 e1485:=viaSmall (by decide +kernel) (by decide)
theorem b1682:B 35 4 e1548:=viaSmall (by decide +kernel) (by decide)
theorem b1695:B 87 6 e1560:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1696:B 87 6 e1561:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1697:B 87 6 e1562:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1698:B 87 6 e1563:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1699:B 87 6 e1564:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1700:B 87 6 e1565:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1701:B 87 6 e1566:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1702:B 87 6 e1567:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1703:B 87 6 e1568:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1704:B 87 6 e1569:=viaCut pjt_9 w1547 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1705:B 20 4 e1570:=viaSmall (by decide +kernel) (by decide)
theorem b1706:B 20 4 e1571:=viaSmall (by decide +kernel) (by decide)
theorem b1707:B 20 4 e1572:=viaSmall (by decide +kernel) (by decide)
theorem w1708:W 20 4 e1572:=viaSub (ws:=[e1570,e1571,e1572]) (consBan b1705 (consBan b1706 (consBan b1707 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b1709:B 87 6 e1573:=viaCut pjt_6 w1708 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1710:B 87 6 e1574:=viaCut pjt_18 w862 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1711:B 87 6 e1575:=viaCut pjt_9 w1547 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1712:B 87 6 e1576:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1713:B 87 6 e1577:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1714:B 87 6 e1578:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1715:B 87 6 e1579:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1716:B 87 6 e1580:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1717:B 87 6 e1581:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1718:B 16 3 e1031:=viaSmall (by decide +kernel) (by decide)
theorem b1719:B 16 3 e1032:=viaSmall (by decide +kernel) (by decide)
theorem w1720:W 16 3 e1032:=viaSub (ws:=[e1031,e1032]) (consBan b1718 (consBan b1719 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1721:B 87 6 e1582:=viaCut pjt_14 w1720 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1722:B 20 4 e1583:=viaPerm pc11_0 pci11_0 b909 (by decide +kernel) (by decide +kernel)
theorem b1723:B 20 4 e1584:=viaPerm pc11_0 pci11_0 b910 (by decide +kernel) (by decide +kernel)
theorem w1724:W 20 4 e1584:=viaSub (ws:=[e793,e1583,e1584]) (consBan b858 (consBan b1722 (consBan b1723 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b1725:B 87 6 e1585:=viaCut pjt_11 w1724 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1726:B 12 3 e1586:=viaPerm pc18_0 pci18_0 b0 (by decide +kernel) (by decide +kernel)
theorem w1727:W 12 3 e1586:=viaSub (ws:=[e16,e1586]) (consBan b16 (consBan b1726 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1728:B 87 6 e1587:=viaCut pjt_18 w1727 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1729:B 12 3 e1588:=viaPerm pc18_0 pci18_0 b864 (by decide +kernel) (by decide +kernel)
theorem w1730:W 12 3 e1588:=viaSub (ws:=[e16,e1588]) (consBan b16 (consBan b1729 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1731:B 87 6 e1589:=viaCut pjt_18 w1730 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1732:B 87 6 e1590:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1733:B 87 6 e1591:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1734:B 87 6 e1592:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1735:B 87 6 e1593:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1736:B 87 6 e1594:=viaPerm pt0 pti0 b786 (by decide +kernel) (by decide +kernel)
theorem b1737:B 87 6 e1595:=viaPerm pt0 pti0 b1031 (by decide +kernel) (by decide +kernel)
theorem b1738:B 87 6 e1596:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1739:B 87 6 e1597:=viaPerm pt0 pti0 b1422 (by decide +kernel) (by decide +kernel)
theorem b1740:B 87 6 e1598:=viaPerm pt0 pti0 b1508 (by decide +kernel) (by decide +kernel)
theorem b1741:B 87 6 e1599:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1783:B 87 5 e1640:=viaSmall (by decide +kernel) (by decide)
theorem b1792:B 87 4 e1647:=viaSmall (by decide +kernel) (by decide)
theorem b1793:B 87 4 e1648:=viaSmall (by decide +kernel) (by decide)
theorem b1794:B 87 4 e1649:=viaSmall (by decide +kernel) (by decide)
theorem b1795:B 87 4 e1650:=viaSmall (by decide +kernel) (by decide)
theorem b1796:B 87 4 e1651:=viaSmall (by decide +kernel) (by decide)
theorem b1797:B 87 4 e1652:=viaSmall (by decide +kernel) (by decide)
theorem b1798:B 87 4 e1653:=viaSmall (by decide +kernel) (by decide)
theorem b1799:B 87 4 e1654:=viaSmall (by decide +kernel) (by decide)
theorem b1800:B 87 4 e1655:=viaSmall (by decide +kernel) (by decide)
theorem b1801:B 87 4 e1656:=viaSmall (by decide +kernel) (by decide)
theorem b1802:B 87 4 e1657:=viaSmall (by decide +kernel) (by decide)
theorem b1803:B 87 4 e1658:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1804:B 87 5 e1659:=viaBranch (ws:=[e1647,e1648,e1649,e1650,e1651,e1652,e1653,e1654,e1655,e1656,e1657,e1658]) (consBan b1792 (consBan b1793 (consBan b1794 (consBan b1795 (consBan b1796 (consBan b1797 (consBan b1798 (consBan b1799 (consBan b1800 (consBan b1801 (consBan b1802 (consBan b1803 (nilBan _ _))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1805:B 87 5 e1660:=viaSmall (by decide +kernel) (by decide)
theorem b1806:B 87 5 e1661:=viaSmall (by decide +kernel) (by decide)
theorem b1807:B 87 5 e1648:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1808:B 87 5 e1662:=viaSmall (by decide +kernel) (by decide)
theorem b1809:B 87 5 e1663:=viaSmall (by decide +kernel) (by decide)
theorem b1810:B 87 5 e1664:=viaSmall (by decide +kernel) (by decide)
theorem b1811:B 87 5 e1665:=viaSmall (by decide +kernel) (by decide)
theorem b1812:B 87 5 e1666:=viaSmall (by decide +kernel) (by decide)
theorem b1813:B 87 5 e1667:=viaSmall (by decide +kernel) (by decide)
theorem b1814:B 87 5 e1668:=viaSmall (by decide +kernel) (by decide)
theorem b1815:B 87 5 e1669:=viaSmall (by decide +kernel) (by decide)
theorem b1816:B 87 5 e1670:=viaSmall (by decide +kernel) (by decide)
theorem b1817:B 87 5 e1671:=viaSmall (by decide +kernel) (by decide)
theorem b1819:B 87 5 e1672:=viaCut pjt_11 w1724 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1820:B 87 5 e1673:=viaSmall (by decide +kernel) (by decide)
theorem b1821:B 87 5 e1674:=viaPerm pt4 pti4 b1820 (by decide +kernel) (by decide +kernel)
theorem b1822:B 87 5 e1675:=viaSmall (by decide +kernel) (by decide)
theorem b1823:B 87 5 e1676:=viaSmall (by decide +kernel) (by decide)
theorem b1824:B 87 5 e1677:=viaSmall (by decide +kernel) (by decide)
theorem b1825:B 87 5 e1678:=viaSmall (by decide +kernel) (by decide)
theorem b1826:B 87 5 e1679:=viaSmall (by decide +kernel) (by decide)
theorem b1827:B 87 5 e1680:=viaSmall (by decide +kernel) (by decide)
theorem b1828:B 87 5 e1681:=viaSmall (by decide +kernel) (by decide)
theorem b1829:B 87 5 e1682:=viaSmall (by decide +kernel) (by decide)
theorem b1830:B 87 5 e1683:=viaSmall (by decide +kernel) (by decide)
theorem b1831:B 87 5 e1684:=viaPerm pt4 pti4 b1830 (by decide +kernel) (by decide +kernel)
theorem b1832:B 87 5 e1685:=viaPerm pt4 pti4 b1813 (by decide +kernel) (by decide +kernel)
theorem b1833:B 87 5 e1686:=viaPerm pt4 pti4 b1814 (by decide +kernel) (by decide +kernel)
theorem b1834:B 87 5 e1687:=viaPerm pt4 pti4 b1816 (by decide +kernel) (by decide +kernel)
theorem b1835:B 87 5 e1688:=viaPerm pt4 pti4 b1815 (by decide +kernel) (by decide +kernel)
theorem b1836:B 87 5 e1689:=viaPerm pt4 pti4 b1822 (by decide +kernel) (by decide +kernel)
theorem b1837:B 87 5 e1690:=viaPerm pt4 pti4 b1823 (by decide +kernel) (by decide +kernel)
theorem b1838:B 87 5 e1691:=viaPerm pt4 pti4 b1824 (by decide +kernel) (by decide +kernel)
theorem b1839:B 87 5 e1692:=viaPerm pt4 pti4 b1826 (by decide +kernel) (by decide +kernel)
theorem b1840:B 87 5 e1693:=viaPerm pt4 pti4 b1827 (by decide +kernel) (by decide +kernel)
theorem b1841:B 87 5 e1694:=viaPerm pt4 pti4 b1825 (by decide +kernel) (by decide +kernel)
theorem b1842:B 87 5 e1695:=viaPerm pt4 pti4 b1809 (by decide +kernel) (by decide +kernel)
theorem b1843:B 87 5 e1696:=viaPerm pt4 pti4 b1810 (by decide +kernel) (by decide +kernel)
theorem b1844:B 87 5 e1697:=viaPerm pt4 pti4 b1812 (by decide +kernel) (by decide +kernel)
theorem b1845:B 87 5 e1698:=viaPerm pt4 pti4 b1811 (by decide +kernel) (by decide +kernel)
theorem b1846:B 87 5 e1699:=viaPerm pt4 pti4 b1783 (by decide +kernel) (by decide +kernel)
theorem b1847:B 87 5 e1700:=viaPerm pt4 pti4 b1804 (by decide +kernel) (by decide +kernel)
theorem b1848:B 87 5 e1701:=viaPerm pt4 pti4 b1805 (by decide +kernel) (by decide +kernel)
theorem b1849:B 87 5 e1702:=viaPerm pt4 pti4 b1807 (by decide +kernel) (by decide +kernel)
theorem b1850:B 87 5 e1703:=viaPerm pt4 pti4 b1808 (by decide +kernel) (by decide +kernel)
theorem b1851:B 87 5 e1704:=viaPerm pt4 pti4 b1806 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1852:B 87 6 e1705:=viaBranch (ws:=[e1640,e1659,e1660,e1661,e1648,e1662,e1663,e1664,e1665,e1666,e1667,e1668,e1669,e1670,e1671,e1672,e1673,e1674,e1675,e1676,e1677,e1678,e1679,e1680,e1681,e1682,e1683,e1684,e1685,e1686,e1687,e1688,e1689,e1690,e1691,e1692,e1693,e1694,e1695,e1696,e1697,e1698,e1699,e1700,e1701,e1702,e1703,e1704]) (consBan b1783 (consBan b1804 (consBan b1805 (consBan b1806 (consBan b1807 (consBan b1808 (consBan b1809 (consBan b1810 (consBan b1811 (consBan b1812 (consBan b1813 (consBan b1814 (consBan b1815 (consBan b1816 (consBan b1817 (consBan b1819 (consBan b1820 (consBan b1821 (consBan b1822 (consBan b1823 (consBan b1824 (consBan b1825 (consBan b1826 (consBan b1827 (consBan b1828 (consBan b1829 (consBan b1830 (consBan b1831 (consBan b1832 (consBan b1833 (consBan b1834 (consBan b1835 (consBan b1836 (consBan b1837 (consBan b1838 (consBan b1839 (consBan b1840 (consBan b1841 (consBan b1842 (consBan b1843 (consBan b1844 (consBan b1845 (consBan b1846 (consBan b1847 (consBan b1848 (consBan b1849 (consBan b1850 (consBan b1851 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1853:B 87 6 e1706:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1854:B 87 6 e1707:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1855:B 87 6 e1708:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1856:B 87 6 e1709:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1857:B 87 6 e1710:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1858:B 87 6 e1711:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1859:B 87 6 e1712:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1860:B 87 6 e1713:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1861:B 35 4 e1714:=viaSmall (by decide +kernel) (by decide)
theorem b1862:B 35 4 e1715:=viaSmall (by decide +kernel) (by decide)
theorem b1863:B 35 4 e1716:=viaSmall (by decide +kernel) (by decide)
theorem b1864:B 35 4 e1717:=viaSmall (by decide +kernel) (by decide)
theorem b1865:B 35 4 e1718:=viaSmall (by decide +kernel) (by decide)
theorem b1866:B 35 4 e1719:=viaSmall (by decide +kernel) (by decide)
theorem b1867:B 35 4 e1720:=viaSmall (by decide +kernel) (by decide)
theorem b1868:B 35 4 e1721:=viaSmall (by decide +kernel) (by decide)
theorem b1869:B 35 4 e1722:=viaSmall (by decide +kernel) (by decide)
theorem b1870:B 35 4 e1723:=viaSmall (by decide +kernel) (by decide)
theorem b1871:B 35 4 e1724:=viaSmall (by decide +kernel) (by decide)
theorem b1872:B 35 4 e1725:=viaSmall (by decide +kernel) (by decide)
theorem b1873:B 35 4 e1726:=viaSmall (by decide +kernel) (by decide)
theorem b1874:B 35 4 e1727:=viaSmall (by decide +kernel) (by decide)
theorem b1875:B 35 4 e1728:=viaSmall (by decide +kernel) (by decide)
theorem b1876:B 35 4 e1729:=viaSmall (by decide +kernel) (by decide)
theorem b1877:B 35 4 e1730:=viaSmall (by decide +kernel) (by decide)
theorem b1878:B 35 4 e1731:=viaSmall (by decide +kernel) (by decide)
theorem b1879:B 35 4 e1732:=viaSmall (by decide +kernel) (by decide)
theorem b1880:B 35 4 e1733:=viaSmall (by decide +kernel) (by decide)
theorem b1881:B 35 4 e1734:=viaSmall (by decide +kernel) (by decide)
theorem b1882:B 35 4 e1735:=viaSmall (by decide +kernel) (by decide)
theorem b1883:B 35 4 e1736:=viaSmall (by decide +kernel) (by decide)
theorem b1884:B 35 4 e1737:=viaSmall (by decide +kernel) (by decide)
theorem b1885:B 35 4 e1738:=viaPerm pc0_0 pci0_0 b1623 (by decide +kernel) (by decide +kernel)
theorem b1886:B 35 4 e1739:=viaSmall (by decide +kernel) (by decide)
theorem b1887:B 35 4 e1740:=viaSmall (by decide +kernel) (by decide)
theorem b1888:B 35 4 e1741:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1889:B 35 5 e1742:=viaBranch (ws:=[e1435,e1473,e1517,e1548,e1714,e1715,e1716,e1717,e1718,e1719,e1720,e1721,e1722,e1723,e1724,e1725,e1726,e1727,e1728,e1729,e1730,e1731,e1732,e1733,e1734,e1735,e1736,e1737,e1738,e1739,e1740,e1741]) (consBan b1566 (consBan b1604 (consBan b1649 (consBan b1682 (consBan b1861 (consBan b1862 (consBan b1863 (consBan b1864 (consBan b1865 (consBan b1866 (consBan b1867 (consBan b1868 (consBan b1869 (consBan b1870 (consBan b1871 (consBan b1872 (consBan b1873 (consBan b1874 (consBan b1875 (consBan b1876 (consBan b1877 (consBan b1878 (consBan b1879 (consBan b1880 (consBan b1881 (consBan b1882 (consBan b1883 (consBan b1884 (consBan b1885 (consBan b1886 (consBan b1887 (consBan b1888 (nilBan _ _))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w1890:W 35 5 e1742:=widen (by decide +kernel) b1889
theorem b1891:B 87 6 e1743:=viaCut pjt_0 w1890 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1892:B 87 6 e1744:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1893:B 87 6 e1745:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1894:B 87 6 e1746:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1895:B 87 6 e1747:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1896:B 87 6 e1748:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1897:B 87 6 e1749:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1898:B 87 6 e1750:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1899:B 87 6 e1751:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1900:B 87 6 e1752:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1901:B 87 6 e1753:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1902:B 87 6 e1754:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1903:B 87 6 e1755:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1904:B 87 6 e1756:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1905:B 87 6 e1757:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1906:B 87 6 e1758:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1907:B 87 6 e1759:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1908:B 87 6 e1760:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1909:B 87 6 e1761:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1910:B 87 6 e1762:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1911:B 87 6 e1763:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1912:B 87 6 e1764:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1913:B 87 6 e1765:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1914:B 87 6 e1766:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1915:B 87 6 e1767:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1916:B 87 6 e1768:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1917:B 87 6 e1769:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1918:B 87 6 e1770:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1919:B 87 6 e1771:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1920:B 87 6 e1772:=viaCut pjt_9 w1547 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1921:B 87 6 e1773:=viaCut pjt_11 w911 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1922:B 87 6 e1774:=viaCut pjt_9 w1547 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1923:B 12 3 e1775:=viaPerm pc18_0 pci18_0 b913 (by decide +kernel) (by decide +kernel)
theorem w1924:W 12 3 e1775:=viaSub (ws:=[e16,e1775]) (consBan b16 (consBan b1923 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b1925:B 87 6 e1776:=viaCut pjt_18 w1924 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1926:B 87 6 e1777:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1927:B 87 6 e1778:=viaPerm pt2 pti2 b560 (by decide +kernel) (by decide +kernel)
theorem b1928:B 87 6 e1779:=viaPerm pt2 pti2 b886 (by decide +kernel) (by decide +kernel)
theorem b1929:B 87 6 e1780:=viaPerm pt2 pti2 b1136 (by decide +kernel) (by decide +kernel)
theorem b1930:B 87 6 e1781:=viaPerm pt2 pti2 b1302 (by decide +kernel) (by decide +kernel)
theorem b1931:B 87 6 e1782:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1932:B 87 6 e1783:=viaPerm pt2 pti2 b1453 (by decide +kernel) (by decide +kernel)
theorem b1933:B 87 6 e1784:=viaPerm pt2 pti2 b1531 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b1934:B 87 7 e1785:=viaBranch (ws:=[e1560,e1561,e1562,e1563,e1564,e358,e1565,e1566,e1567,e1568,e1569,e1573,e1574,e1575,e1576,e1577,e1578,e1579,e1580,e1581,e1582,e1585,e1587,e1589,e1590,e1591,e1592,e1593,e1594,e1595,e1596,e1597,e1598,e1599,e1705,e1706,e1707,e1708,e1709,e1710,e1711,e1712,e1713,e1743,e1744,e1745,e1746,e1747,e1748,e1749,e1750,e1751,e1752,e1753,e1754,e1755,e1756,e1757,e1758,e1759,e1760,e1761,e1762,e1763,e1764,e1765,e1766,e1767,e1768,e1769,e1770,e1771,e1772,e1773,e1774,e1776,e1777,e1778,e1779,e1780,e1781,e1782,e1783,e1784]) (consBan b1695 (consBan b1696 (consBan b1697 (consBan b1698 (consBan b1699 (consBan b390 (consBan b1700 (consBan b1701 (consBan b1702 (consBan b1703 (consBan b1704 (consBan b1709 (consBan b1710 (consBan b1711 (consBan b1712 (consBan b1713 (consBan b1714 (consBan b1715 (consBan b1716 (consBan b1717 (consBan b1721 (consBan b1725 (consBan b1728 (consBan b1731 (consBan b1732 (consBan b1733 (consBan b1734 (consBan b1735 (consBan b1736 (consBan b1737 (consBan b1738 (consBan b1739 (consBan b1740 (consBan b1741 (consBan b1852 (consBan b1853 (consBan b1854 (consBan b1855 (consBan b1856 (consBan b1857 (consBan b1858 (consBan b1859 (consBan b1860 (consBan b1891 (consBan b1892 (consBan b1893 (consBan b1894 (consBan b1895 (consBan b1896 (consBan b1897 (consBan b1898 (consBan b1899 (consBan b1900 (consBan b1901 (consBan b1902 (consBan b1903 (consBan b1904 (consBan b1905 (consBan b1906 (consBan b1907 (consBan b1908 (consBan b1909 (consBan b1910 (consBan b1911 (consBan b1912 (consBan b1913 (consBan b1914 (consBan b1915 (consBan b1916 (consBan b1917 (consBan b1918 (consBan b1919 (consBan b1920 (consBan b1921 (consBan b1922 (consBan b1925 (consBan b1926 (consBan b1927 (consBan b1928 (consBan b1929 (consBan b1930 (consBan b1931 (consBan b1932 (consBan b1933 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b1935:B 87 7 e1786:=viaPerm pt0 pti0 b1934 (by decide +kernel) (by decide +kernel)
theorem b1936:B 87 7 e1787:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1943:B 87 6 e1794:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1944:B 87 6 e1795:=viaCut pjt_1 w333 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1945:B 87 6 e1796:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1946:B 87 6 e1797:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1947:B 87 6 e1798:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1948:B 87 6 e1785:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1949:B 87 6 e1799:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1950:B 87 6 e1800:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1951:B 87 6 e1801:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1952:B 87 6 e1802:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1953:B 87 6 e1803:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1954:B 87 6 e1804:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1955:B 87 6 e1805:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1956:B 87 6 e1806:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1957:B 87 6 e1807:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1958:B 87 6 e1808:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1959:B 87 6 e1809:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1960:B 87 6 e1810:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1961:B 87 6 e1811:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1962:B 87 6 e1812:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1963:B 87 6 e1813:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1964:B 87 6 e1814:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1965:B 87 6 e1815:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1966:B 87 6 e1816:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1967:B 87 6 e1817:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1968:B 87 6 e1818:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1969:B 87 6 e1819:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1970:B 87 6 e1820:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1971:B 87 6 e1821:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1972:B 87 6 e1822:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1973:B 16 3 e1823:=viaPerm pc9_0 pci9_0 b1229 (by decide +kernel) (by decide +kernel)
theorem w1974:W 16 3 e1823:=widen (by decide +kernel) b1973
theorem b1975:B 87 6 e1824:=viaCut pjt_9 w1974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1976:B 87 6 e1825:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1977:B 87 6 e1826:=viaCut pjt_18 w862 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1978:B 87 6 e1827:=viaCut pjt_9 w1974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1979:B 87 6 e1828:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1980:B 87 6 e1829:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1981:B 87 6 e1830:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1982:B 87 6 e1831:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1983:B 87 6 e1832:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1984:B 87 6 e1833:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1985:B 87 6 e1834:=viaCut pjt_17 w907 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1986:B 87 6 e1835:=viaCut pjt_11 w1724 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1987:B 87 6 e1836:=viaCut pjt_18 w1727 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1988:B 87 6 e1837:=viaCut pjt_18 w1730 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1989:B 87 6 e1838:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1990:B 87 6 e1839:=viaPerm pt0 pti0 b1033 (by decide +kernel) (by decide +kernel)
theorem b1991:B 87 6 e1840:=viaPerm pt0 pti0 b789 (by decide +kernel) (by decide +kernel)
theorem b1992:B 87 6 e1841:=viaPerm pt0 pti0 b1035 (by decide +kernel) (by decide +kernel)
theorem b1993:B 87 6 e1842:=viaPerm pt0 pti0 b1251 (by decide +kernel) (by decide +kernel)
theorem b1994:B 87 6 e1843:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1995:B 87 6 e1844:=viaPerm pt0 pti0 b1426 (by decide +kernel) (by decide +kernel)
theorem b1996:B 87 6 e1845:=viaPerm pt0 pti0 b1510 (by decide +kernel) (by decide +kernel)
theorem b1997:B 87 6 e1846:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1998:B 87 6 e1847:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b1999:B 87 6 e1848:=viaPerm pt4 pti4 b1858 (by decide +kernel) (by decide +kernel)
theorem b2000:B 87 6 e1849:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2001:B 87 6 e1850:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2002:B 87 6 e1851:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2003:B 87 6 e1852:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2004:B 87 6 e1853:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2005:B 87 6 e1854:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2006:B 87 6 e1855:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2007:B 87 6 e1856:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2008:B 87 6 e1857:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2009:B 87 6 e1858:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2010:B 87 6 e1859:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2011:B 87 6 e1860:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2012:B 87 6 e1861:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2013:B 87 6 e1862:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2014:B 87 6 e1863:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2015:B 87 6 e1864:=viaCut pjt_9 w1974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2016:B 87 6 e1865:=viaCut pjt_11 w911 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2017:B 87 6 e1866:=viaCut pjt_9 w1974 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2018:B 87 6 e1867:=viaCut pjt_18 w1924 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2019:B 87 6 e1868:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2020:B 87 6 e1869:=viaPerm pt2 pti2 b565 (by decide +kernel) (by decide +kernel)
theorem b2021:B 87 6 e1870:=viaPerm pt2 pti2 b889 (by decide +kernel) (by decide +kernel)
theorem b2022:B 87 6 e1871:=viaPerm pt2 pti2 b1138 (by decide +kernel) (by decide +kernel)
theorem b2023:B 87 6 e1872:=viaPerm pt2 pti2 b1305 (by decide +kernel) (by decide +kernel)
theorem b2024:B 87 6 e1873:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2025:B 87 6 e1874:=viaPerm pt2 pti2 b1456 (by decide +kernel) (by decide +kernel)
theorem b2026:B 87 6 e1875:=viaPerm pt2 pti2 b1533 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2027:B 87 7 e1591:=viaBranch (ws:=[e1794,e1795,e1796,e1797,e1131,e1798,e1298,e1380,e1785,e1590,e1592,e1799,e1800,e1801,e1802,e1803,e1804,e1805,e1806,e1807,e1808,e1809,e1810,e1811,e1812,e1813,e1814,e1815,e1816,e1817,e1818,e1819,e1820,e1821,e1822,e1824,e1825,e1826,e1827,e1828,e1829,e1830,e1831,e1832,e1833,e1834,e1835,e1836,e1837,e1838,e1839,e1840,e1841,e1842,e1843,e1844,e1845,e1846,e1847,e1848,e1849,e1850,e1851,e1852,e1853,e1854,e1855,e1856,e1857,e1858,e1859,e1860,e1861,e1862,e1863,e1864,e1865,e1866,e1867,e1868,e1869,e1870,e1871,e1872,e1873,e1874,e1875]) (consBan b1943 (consBan b1944 (consBan b1945 (consBan b1946 (consBan b1249 (consBan b1947 (consBan b1424 (consBan b1509 (consBan b1948 (consBan b1732 (consBan b1734 (consBan b1949 (consBan b1950 (consBan b1951 (consBan b1952 (consBan b1953 (consBan b1954 (consBan b1955 (consBan b1956 (consBan b1957 (consBan b1958 (consBan b1959 (consBan b1960 (consBan b1961 (consBan b1962 (consBan b1963 (consBan b1964 (consBan b1965 (consBan b1966 (consBan b1967 (consBan b1968 (consBan b1969 (consBan b1970 (consBan b1971 (consBan b1972 (consBan b1975 (consBan b1976 (consBan b1977 (consBan b1978 (consBan b1979 (consBan b1980 (consBan b1981 (consBan b1982 (consBan b1983 (consBan b1984 (consBan b1985 (consBan b1986 (consBan b1987 (consBan b1988 (consBan b1989 (consBan b1990 (consBan b1991 (consBan b1992 (consBan b1993 (consBan b1994 (consBan b1995 (consBan b1996 (consBan b1997 (consBan b1998 (consBan b1999 (consBan b2000 (consBan b2001 (consBan b2002 (consBan b2003 (consBan b2004 (consBan b2005 (consBan b2006 (consBan b2007 (consBan b2008 (consBan b2009 (consBan b2010 (consBan b2011 (consBan b2012 (consBan b2013 (consBan b2014 (consBan b2015 (consBan b2016 (consBan b2017 (consBan b2018 (consBan b2019 (consBan b2020 (consBan b2021 (consBan b2022 (consBan b2023 (consBan b2024 (consBan b2025 (consBan b2026 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2028:B 87 7 e1876:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2029:B 87 7 e1877:=viaPerm pt0 pti0 b2027 (by decide +kernel) (by decide +kernel)
theorem b2030:B 87 7 e1878:=viaPerm pt0 pti0 b2028 (by decide +kernel) (by decide +kernel)
theorem b2031:B 87 7 e1879:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2037:B 87 6 e1885:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2038:B 87 6 e1886:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2039:B 87 6 e1887:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2040:B 87 6 e1888:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2041:B 87 6 e1889:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2042:B 87 6 e1890:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2043:B 87 6 e1891:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2044:B 87 6 e1892:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2045:B 6 3 e1893:=viaSmall (by decide +kernel) (by decide)
theorem w2046:W 6 3 e1893:=widen (by decide +kernel) b2045
theorem b2047:B 87 6 e1894:=viaCut pjt_20 w2046 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2048:B 87 6 e1895:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2049:B 87 6 e1896:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2050:B 87 6 e1897:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2051:B 87 6 e1898:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2052:B 87 6 e1899:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2053:B 87 6 e1900:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2054:B 87 6 e1901:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2075:B 87 5 e1922:=viaSmall (by decide +kernel) (by decide)
theorem b2076:B 87 5 e1923:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2077:B 87 5 e1924:=viaSmall (by decide +kernel) (by decide)
theorem b2078:B 87 5 e1925:=viaSmall (by decide +kernel) (by decide)
theorem b2079:B 87 5 e1926:=viaSmall (by decide +kernel) (by decide)
theorem b2080:B 87 5 e1927:=viaSmall (by decide +kernel) (by decide)
theorem b2081:B 87 5 e1928:=viaSmall (by decide +kernel) (by decide)
theorem b2082:B 87 5 e1929:=viaSmall (by decide +kernel) (by decide)
theorem b2083:B 87 5 e1930:=viaSmall (by decide +kernel) (by decide)
theorem b2084:B 87 5 e1931:=viaSmall (by decide +kernel) (by decide)
theorem b2085:B 87 5 e1932:=viaPerm pt1 pti1 b2075 (by decide +kernel) (by decide +kernel)
theorem b2086:B 87 5 e1933:=viaPerm pt1 pti1 b2076 (by decide +kernel) (by decide +kernel)
theorem b2087:B 87 5 e1934:=viaPerm pt1 pti1 b2077 (by decide +kernel) (by decide +kernel)
theorem b2088:B 87 5 e1935:=viaPerm pt1 pti1 b2078 (by decide +kernel) (by decide +kernel)
theorem b2089:B 87 5 e1936:=viaPerm pt1 pti1 b2079 (by decide +kernel) (by decide +kernel)
theorem b2090:B 87 5 e1937:=viaPerm pt1 pti1 b2080 (by decide +kernel) (by decide +kernel)
theorem b2091:B 87 5 e1938:=viaPerm pt1 pti1 b2081 (by decide +kernel) (by decide +kernel)
theorem b2092:B 87 5 e1939:=viaPerm pt1 pti1 b2082 (by decide +kernel) (by decide +kernel)
theorem b2093:B 87 5 e1940:=viaPerm pt1 pti1 b2083 (by decide +kernel) (by decide +kernel)
theorem b2094:B 87 5 e1941:=viaPerm pt1 pti1 b2084 (by decide +kernel) (by decide +kernel)
theorem b2095:B 87 5 e1942:=viaSmall (by decide +kernel) (by decide)
theorem b2096:B 87 5 e1943:=viaSmall (by decide +kernel) (by decide)
theorem b2097:B 87 5 e1944:=viaSmall (by decide +kernel) (by decide)
theorem b2098:B 87 5 e1945:=viaSmall (by decide +kernel) (by decide)
theorem b2099:B 87 5 e1946:=viaSmall (by decide +kernel) (by decide)
theorem b2100:B 87 5 e1947:=viaSmall (by decide +kernel) (by decide)
theorem b2101:B 87 5 e1948:=viaPerm pt1 pti1 b2100 (by decide +kernel) (by decide +kernel)
theorem b2102:B 87 5 e1949:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2103:B 87 5 e1950:=viaSmall (by decide +kernel) (by decide)
theorem b2104:B 87 5 e1951:=viaSmall (by decide +kernel) (by decide)
theorem b2105:B 87 5 e1952:=viaPerm pt1 pti1 b2103 (by decide +kernel) (by decide +kernel)
theorem b2106:B 87 5 e1953:=viaPerm pt1 pti1 b2104 (by decide +kernel) (by decide +kernel)
theorem b2107:B 87 5 e1954:=viaSmall (by decide +kernel) (by decide)
theorem b2108:B 87 5 e1955:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2109:B 87 5 e1956:=viaSmall (by decide +kernel) (by decide)
theorem b2110:B 87 5 e1957:=viaSmall (by decide +kernel) (by decide)
theorem b2111:B 87 5 e1958:=viaSmall (by decide +kernel) (by decide)
theorem b2112:B 87 5 e1959:=viaSmall (by decide +kernel) (by decide)
theorem b2113:B 87 5 e1960:=viaPerm pt1 pti1 b2107 (by decide +kernel) (by decide +kernel)
theorem b2114:B 87 5 e1961:=viaPerm pt1 pti1 b2108 (by decide +kernel) (by decide +kernel)
theorem b2115:B 87 5 e1962:=viaPerm pt1 pti1 b2109 (by decide +kernel) (by decide +kernel)
theorem b2116:B 87 5 e1963:=viaPerm pt1 pti1 b2111 (by decide +kernel) (by decide +kernel)
theorem b2117:B 87 5 e1964:=viaPerm pt1 pti1 b2112 (by decide +kernel) (by decide +kernel)
theorem b2118:B 87 5 e1965:=viaPerm pt1 pti1 b2110 (by decide +kernel) (by decide +kernel)
theorem b2119:B 87 5 e1966:=viaSmall (by decide +kernel) (by decide)
theorem b2120:B 87 5 e1967:=viaSmall (by decide +kernel) (by decide)
theorem b2121:B 87 5 e1968:=viaSmall (by decide +kernel) (by decide)
theorem b2122:B 87 5 e1969:=viaPerm pt1 pti1 b2121 (by decide +kernel) (by decide +kernel)
theorem b2123:B 87 5 e1970:=viaPerm pt1 pti1 b2095 (by decide +kernel) (by decide +kernel)
theorem b2124:B 87 5 e1971:=viaPerm pt1 pti1 b2096 (by decide +kernel) (by decide +kernel)
theorem b2125:B 87 5 e1972:=viaPerm pt1 pti1 b2097 (by decide +kernel) (by decide +kernel)
theorem b2126:B 87 5 e1973:=viaPerm pt1 pti1 b2098 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2127:B 87 6 e1974:=viaBranch (ws:=[e1922,e1923,e1924,e1925,e1926,e1927,e1928,e1929,e1930,e1931,e1932,e1933,e1934,e1935,e1936,e1937,e1938,e1939,e1940,e1941,e1942,e1943,e1944,e1945,e1946,e1947,e1948,e1949,e1950,e1951,e1952,e1953,e1954,e1955,e1956,e1957,e1958,e1959,e1960,e1961,e1962,e1963,e1964,e1965,e1966,e1967,e1968,e1969,e1970,e1971,e1972,e1973]) (consBan b2075 (consBan b2076 (consBan b2077 (consBan b2078 (consBan b2079 (consBan b2080 (consBan b2081 (consBan b2082 (consBan b2083 (consBan b2084 (consBan b2085 (consBan b2086 (consBan b2087 (consBan b2088 (consBan b2089 (consBan b2090 (consBan b2091 (consBan b2092 (consBan b2093 (consBan b2094 (consBan b2095 (consBan b2096 (consBan b2097 (consBan b2098 (consBan b2099 (consBan b2100 (consBan b2101 (consBan b2102 (consBan b2103 (consBan b2104 (consBan b2105 (consBan b2106 (consBan b2107 (consBan b2108 (consBan b2109 (consBan b2110 (consBan b2111 (consBan b2112 (consBan b2113 (consBan b2114 (consBan b2115 (consBan b2116 (consBan b2117 (consBan b2118 (consBan b2119 (consBan b2120 (consBan b2121 (consBan b2122 (consBan b2123 (consBan b2124 (consBan b2125 (consBan b2126 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2129:B 87 5 e1976:=viaSmall (by decide +kernel) (by decide)
theorem b2130:B 87 5 e1977:=viaSmall (by decide +kernel) (by decide)
theorem b2131:B 87 5 e1978:=viaSmall (by decide +kernel) (by decide)
theorem b2132:B 87 5 e1979:=viaSmall (by decide +kernel) (by decide)
theorem b2133:B 87 5 e1980:=viaSmall (by decide +kernel) (by decide)
theorem b2134:B 87 5 e1981:=viaSmall (by decide +kernel) (by decide)
theorem b2135:B 87 5 e1982:=viaSmall (by decide +kernel) (by decide)
theorem b2136:B 87 5 e1983:=viaSmall (by decide +kernel) (by decide)
theorem b2137:B 87 5 e1984:=viaSmall (by decide +kernel) (by decide)
theorem b2138:B 87 5 e1985:=viaSmall (by decide +kernel) (by decide)
theorem b2139:B 87 5 e1986:=viaSmall (by decide +kernel) (by decide)
theorem b2140:B 87 5 e1987:=viaSmall (by decide +kernel) (by decide)
theorem b2141:B 87 5 e1988:=viaSmall (by decide +kernel) (by decide)
theorem b2142:B 87 5 e1989:=viaSmall (by decide +kernel) (by decide)
theorem b2143:B 87 5 e1990:=viaSmall (by decide +kernel) (by decide)
theorem b2144:B 87 5 e1991:=viaSmall (by decide +kernel) (by decide)
theorem b2145:B 87 5 e1992:=viaSmall (by decide +kernel) (by decide)
theorem b2146:B 87 5 e1993:=viaSmall (by decide +kernel) (by decide)
theorem b2147:B 87 5 e1994:=viaSmall (by decide +kernel) (by decide)
theorem b2148:B 87 5 e1995:=viaSmall (by decide +kernel) (by decide)
theorem b2149:B 87 5 e1996:=viaSmall (by decide +kernel) (by decide)
theorem b2150:B 87 5 e1997:=viaSmall (by decide +kernel) (by decide)
theorem b2151:B 87 5 e1998:=viaSmall (by decide +kernel) (by decide)
theorem b2152:B 87 5 e1999:=viaSmall (by decide +kernel) (by decide)
theorem b2153:B 87 5 e2000:=viaSmall (by decide +kernel) (by decide)
theorem b2154:B 87 5 e2001:=viaSmall (by decide +kernel) (by decide)
theorem b2155:B 87 5 e2002:=viaSmall (by decide +kernel) (by decide)
theorem b2156:B 87 5 e2003:=viaSmall (by decide +kernel) (by decide)
theorem b2157:B 87 5 e2004:=viaSmall (by decide +kernel) (by decide)
theorem b2158:B 87 5 e2005:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2159:B 87 5 e2006:=viaSmall (by decide +kernel) (by decide)
theorem b2160:B 87 5 e2007:=viaSmall (by decide +kernel) (by decide)
theorem b2161:B 87 5 e2008:=viaSmall (by decide +kernel) (by decide)
theorem b2162:B 87 5 e2009:=viaSmall (by decide +kernel) (by decide)
theorem b2163:B 87 5 e2010:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2164:B 87 6 e2011:=viaBranch (ws:=[e1976,e1977,e1978,e1979,e1980,e1981,e1982,e1983,e1984,e1985,e1986,e1987,e1988,e1989,e1990,e1991,e1992,e1993,e1994,e1995,e1996,e1997,e1998,e1967,e1999,e1969,e2000,e2001,e2002,e2003,e2004,e2005,e2006,e2007,e2008,e2009,e2010]) (consBan b2129 (consBan b2130 (consBan b2131 (consBan b2132 (consBan b2133 (consBan b2134 (consBan b2135 (consBan b2136 (consBan b2137 (consBan b2138 (consBan b2139 (consBan b2140 (consBan b2141 (consBan b2142 (consBan b2143 (consBan b2144 (consBan b2145 (consBan b2146 (consBan b2147 (consBan b2148 (consBan b2149 (consBan b2150 (consBan b2151 (consBan b2120 (consBan b2152 (consBan b2122 (consBan b2153 (consBan b2154 (consBan b2155 (consBan b2156 (consBan b2157 (consBan b2158 (consBan b2159 (consBan b2160 (consBan b2161 (consBan b2162 (consBan b2163 (nilBan _ _)))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2165:B 87 6 e2012:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2166:B 87 6 e2013:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2167:B 87 6 e2010:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2168:B 87 6 e2014:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2169:B 87 6 e2015:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2170:B 87 6 e2016:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2171:B 87 6 e2017:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2172:B 87 6 e2018:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2173:B 87 6 e2019:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2174:B 87 6 e2020:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2175:B 87 6 e2021:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2176:B 87 6 e2022:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2177:B 6 2 e2023:=viaSmall (by decide +kernel) (by decide)
theorem w2178:W 6 2 e2023:=viaSub (ws:=[e102,e2023]) (consBan b108 (consBan b2177 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2179:B 87 6 e2024:=viaCut pjt_29 w2178 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2180:B 87 6 e2025:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2181:B 6 2 e2023:=viaSmall (by decide +kernel) (by decide)
theorem w2182:W 6 2 e2023:=viaSub (ws:=[e102,e2023]) (consBan b982 (consBan b2181 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2183:B 87 6 e2026:=viaCut pjt_20 w2182 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2184:B 87 6 e2027:=viaCut pjt_18 w865 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2185:B 87 6 e2028:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2186:B 87 6 e2029:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2187:B 87 6 e2030:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2188:B 87 6 e2031:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2189:B 87 6 e2032:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2190:B 87 6 e2033:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2191:B 87 6 e2034:=viaCut pjt_29 w2178 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2192:B 87 6 e2035:=viaCut pjt_29 w2178 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2193:B 87 6 e2036:=viaCut pjt_29 w2178 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2194:B 87 6 e2037:=viaCut pjt_29 w2178 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2195:B 87 6 e2038:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2196:B 87 6 e2039:=viaPerm pt0 pti0 b849 (by decide +kernel) (by decide +kernel)
theorem b2197:B 87 6 e2040:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2198:B 87 6 e2041:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2199:B 87 6 e2042:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2200:B 87 6 e2043:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2201:B 87 6 e2044:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2202:B 87 6 e2045:=viaPerm pt3 pti3 b1713 (by decide +kernel) (by decide +kernel)
theorem b2203:B 87 6 e2046:=viaPerm pt4 pti4 b1915 (by decide +kernel) (by decide +kernel)
theorem b2204:B 87 6 e2047:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2205:B 87 6 e2048:=viaPerm pt3 pti3 b1980 (by decide +kernel) (by decide +kernel)
theorem b2206:B 87 6 e2049:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2207:B 87 6 e2050:=viaPerm pt4 pti4 b2010 (by decide +kernel) (by decide +kernel)
theorem b2208:B 87 6 e2051:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2209:B 87 6 e2052:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2210:B 87 6 e2053:=viaPerm pt3 pti3 b2186 (by decide +kernel) (by decide +kernel)
theorem b2211:B 87 6 e2054:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2212:B 87 6 e2055:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2213:B 87 6 e2056:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2214:B 87 6 e2057:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2215:B 87 6 e2058:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2216:B 87 6 e2059:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2217:B 87 6 e2060:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2218:B 87 6 e2061:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2219:B 87 6 e2062:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2220:B 87 6 e2063:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2221:B 87 6 e2064:=viaCut pjt_29 w2178 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2222:B 87 6 e2065:=viaCut pjt_11 w911 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2223:B 87 6 e2066:=viaCut pjt_18 w914 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2224:B 87 6 e2067:=viaCut pjt_29 w2178 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2225:B 87 6 e2068:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2226:B 87 6 e2069:=viaPerm pt2 pti2 b589 (by decide +kernel) (by decide +kernel)
theorem b2227:B 87 6 e2070:=viaPerm pt2 pti2 b894 (by decide +kernel) (by decide +kernel)
theorem b2228:B 87 6 e2071:=viaPerm pt2 pti2 b1140 (by decide +kernel) (by decide +kernel)
theorem b2229:B 87 6 e2072:=viaPerm pt2 pti2 b1310 (by decide +kernel) (by decide +kernel)
theorem b2230:B 87 6 e2073:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2231:B 87 6 e2074:=viaPerm pt2 pti2 b1461 (by decide +kernel) (by decide +kernel)
theorem b2232:B 87 6 e2075:=viaPerm pt2 pti2 b1535 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2233:B 87 7 e2076:=viaBranch (ws:=[e1885,e972,e1886,e1382,e1887,e1888,e1889,e1890,e1891,e1892,e1894,e1895,e1896,e1897,e1898,e1899,e1900,e1901,e1974,e2011,e2012,e2013,e2010,e2014,e2015,e2016,e2017,e2018,e2019,e2020,e2021,e2022,e2024,e2025,e2026,e2027,e2028,e2029,e2030,e2031,e2032,e2033,e2034,e2035,e2036,e2037,e2038,e2039,e2040,e2041,e2042,e2043,e2044,e2045,e2046,e2047,e2048,e2049,e2050,e2051,e2052,e2053,e2054,e2055,e2056,e2057,e2058,e2059,e2060,e2061,e2062,e2063,e2064,e2065,e2066,e2067,e2068,e2069,e2070,e2071,e2072,e2073,e2074,e2075]) (consBan b2037 (consBan b1057 (consBan b2038 (consBan b1511 (consBan b2039 (consBan b2040 (consBan b2041 (consBan b2042 (consBan b2043 (consBan b2044 (consBan b2047 (consBan b2048 (consBan b2049 (consBan b2050 (consBan b2051 (consBan b2052 (consBan b2053 (consBan b2054 (consBan b2127 (consBan b2164 (consBan b2165 (consBan b2166 (consBan b2167 (consBan b2168 (consBan b2169 (consBan b2170 (consBan b2171 (consBan b2172 (consBan b2173 (consBan b2174 (consBan b2175 (consBan b2176 (consBan b2179 (consBan b2180 (consBan b2183 (consBan b2184 (consBan b2185 (consBan b2186 (consBan b2187 (consBan b2188 (consBan b2189 (consBan b2190 (consBan b2191 (consBan b2192 (consBan b2193 (consBan b2194 (consBan b2195 (consBan b2196 (consBan b2197 (consBan b2198 (consBan b2199 (consBan b2200 (consBan b2201 (consBan b2202 (consBan b2203 (consBan b2204 (consBan b2205 (consBan b2206 (consBan b2207 (consBan b2208 (consBan b2209 (consBan b2210 (consBan b2211 (consBan b2212 (consBan b2213 (consBan b2214 (consBan b2215 (consBan b2216 (consBan b2217 (consBan b2218 (consBan b2219 (consBan b2220 (consBan b2221 (consBan b2222 (consBan b2223 (consBan b2224 (consBan b2225 (consBan b2226 (consBan b2227 (consBan b2228 (consBan b2229 (consBan b2230 (consBan b2231 (consBan b2232 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2234:B 87 6 e2077:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2235:B 87 6 e2078:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2236:B 87 6 e2079:=viaPerm pt0 pti0 b1696 (by decide +kernel) (by decide +kernel)
theorem b2237:B 87 6 e2080:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2238:B 87 6 e2081:=viaPerm pt0 pti0 b1970 (by decide +kernel) (by decide +kernel)
theorem b2239:B 87 6 e2082:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2240:B 87 6 e2083:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2241:B 87 6 e2084:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2242:B 87 6 e2085:=viaCut pjt_16 w856 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2243:B 87 6 e2086:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2244:B 87 6 e2087:=viaPerm pt2 pti2 b1891 (by decide +kernel) (by decide +kernel)
theorem b2245:B 87 6 e2088:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2246:B 87 6 e2089:=viaPerm pt2 pti2 b1892 (by decide +kernel) (by decide +kernel)
theorem b2247:B 87 6 e2090:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2248:B 87 6 e2091:=viaPerm pt2 pti2 b2006 (by decide +kernel) (by decide +kernel)
theorem b2249:B 87 6 e2092:=viaPerm pt1 pti1 b2164 (by decide +kernel) (by decide +kernel)
theorem b2250:B 87 5 e2093:=viaSmall (by decide +kernel) (by decide)
theorem b2251:B 87 5 e2094:=viaSmall (by decide +kernel) (by decide)
theorem b2252:B 87 5 e2095:=viaSmall (by decide +kernel) (by decide)
theorem b2254:B 87 5 e2097:=viaCut pjt_11 w911 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2255:B 87 5 e2098:=viaSmall (by decide +kernel) (by decide)
theorem b2256:B 87 5 e2099:=viaPerm pt1 pti1 b2255 (by decide +kernel) (by decide +kernel)
theorem b2257:B 87 5 e2100:=viaPerm pt1 pti1 b2154 (by decide +kernel) (by decide +kernel)
theorem b2258:B 87 5 e2101:=viaSmall (by decide +kernel) (by decide)
theorem b2259:B 87 5 e2102:=viaPerm pt1 pti1 b2250 (by decide +kernel) (by decide +kernel)
theorem b2260:B 87 5 e2103:=viaPerm pt1 pti1 b2251 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2261:B 87 6 e2104:=viaBranch (ws:=[e2093,e2094,e2095,e2097,e2098,e2099,e2001,e2100,e2101,e2102,e2103]) (consBan b2250 (consBan b2251 (consBan b2252 (consBan b2254 (consBan b2255 (consBan b2256 (consBan b2154 (consBan b2257 (consBan b2258 (consBan b2259 (consBan b2260 (nilBan _ _)))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2262:B 87 6 e2105:=viaPerm pt1 pti1 b2166 (by decide +kernel) (by decide +kernel)
theorem b2263:B 87 6 e2106:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2264:B 87 6 e2107:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2265:B 87 6 e2108:=viaPerm pt0 pti0 b2173 (by decide +kernel) (by decide +kernel)
theorem b2266:B 87 6 e2109:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2267:B 87 6 e2110:=viaCut pjt_29 w2178 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2268:B 87 6 e2111:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2269:B 87 6 e2112:=viaCut pjt_29 w2178 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2270:B 87 6 e2113:=viaCut pjt_18 w865 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2271:B 87 6 e2114:=viaCut pjt_12 w111 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2272:B 87 6 e2115:=viaCut pjt_18 w865 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2273:B 87 6 e2116:=viaPerm pt2 pti2 b2211 (by decide +kernel) (by decide +kernel)
theorem b2274:B 87 6 e2117:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2275:B 87 6 e2118:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2276:B 87 6 e2119:=viaPerm pt0 pti0 b334 (by decide +kernel) (by decide +kernel)
theorem b2277:B 87 6 e2120:=viaPerm pt0 pti0 b1098 (by decide +kernel) (by decide +kernel)
theorem b2278:B 87 6 e2121:=viaPerm pt0 pti0 b1274 (by decide +kernel) (by decide +kernel)
theorem b2279:B 87 6 e2122:=viaPerm pt0 pti0 b1275 (by decide +kernel) (by decide +kernel)
theorem b2280:B 87 6 e2123:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2281:B 87 6 e2124:=viaPerm pt0 pti0 b1519 (by decide +kernel) (by decide +kernel)
theorem b2282:B 87 6 e2125:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2283:B 87 6 e2126:=viaPerm pt0 pti0 b390 (by decide +kernel) (by decide +kernel)
theorem b2285:B 35 4 e2128:=viaSmall (by decide +kernel) (by decide)
theorem b2286:B 35 4 e2129:=viaSmall (by decide +kernel) (by decide)
theorem b2287:B 35 4 e2130:=viaSmall (by decide +kernel) (by decide)
theorem b2288:B 35 4 e2131:=viaSmall (by decide +kernel) (by decide)
theorem b2289:B 35 4 e2132:=viaSmall (by decide +kernel) (by decide)
theorem b2290:B 35 4 e2133:=viaSmall (by decide +kernel) (by decide)
theorem b2291:B 35 4 e2134:=viaSmall (by decide +kernel) (by decide)
theorem b2292:B 35 4 e2135:=viaSmall (by decide +kernel) (by decide)
theorem b2293:B 35 4 e2136:=viaSmall (by decide +kernel) (by decide)
theorem b2294:B 35 4 e2137:=viaSmall (by decide +kernel) (by decide)
theorem b2295:B 35 4 e2138:=viaSmall (by decide +kernel) (by decide)
theorem b2296:B 35 4 e2139:=viaSmall (by decide +kernel) (by decide)
theorem b2297:B 35 4 e2140:=viaSmall (by decide +kernel) (by decide)
theorem b2298:B 35 4 e2141:=viaSmall (by decide +kernel) (by decide)
theorem b2299:B 35 4 e2142:=viaSmall (by decide +kernel) (by decide)
theorem b2300:B 35 4 e2143:=viaSmall (by decide +kernel) (by decide)
theorem b2301:B 35 4 e2144:=viaSmall (by decide +kernel) (by decide)
theorem b2302:B 35 4 e2145:=viaSmall (by decide +kernel) (by decide)
theorem b2303:B 35 4 e2146:=viaSmall (by decide +kernel) (by decide)
theorem b2304:B 35 4 e2147:=viaSmall (by decide +kernel) (by decide)
theorem b2305:B 35 4 e2148:=viaSmall (by decide +kernel) (by decide)
theorem b2306:B 35 4 e2149:=viaSmall (by decide +kernel) (by decide)
theorem b2307:B 35 4 e2150:=viaSmall (by decide +kernel) (by decide)
theorem b2308:B 35 4 e2151:=viaSmall (by decide +kernel) (by decide)
theorem b2309:B 35 4 e2152:=viaSmall (by decide +kernel) (by decide)
theorem b2310:B 35 4 e2153:=viaSmall (by decide +kernel) (by decide)
theorem b2311:B 35 4 e2154:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2312:B 35 5 e2155:=viaBranch (ws:=[e2128,e2129,e2130,e2131,e2132,e2133,e2134,e2135,e2136,e2137,e2138,e2139,e2140,e2141,e2142,e2143,e2144,e2145,e2146,e2147,e2148,e2149,e2150,e2151,e2152,e2153,e2154]) (consBan b2285 (consBan b2286 (consBan b2287 (consBan b2288 (consBan b2289 (consBan b2290 (consBan b2291 (consBan b2292 (consBan b2293 (consBan b2294 (consBan b2295 (consBan b2296 (consBan b2297 (consBan b2298 (consBan b2299 (consBan b2300 (consBan b2301 (consBan b2302 (consBan b2303 (consBan b2304 (consBan b2305 (consBan b2306 (consBan b2307 (consBan b2308 (consBan b2309 (consBan b2310 (consBan b2311 (nilBan _ _)))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w2313:W 35 5 e2155:=widen (by decide +kernel) b2312
theorem b2314:B 87 6 e2156:=viaCut pjt_2 w2313 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2315:B 87 6 e2157:=viaPerm pt0 pti0 b1114 (by decide +kernel) (by decide +kernel)
theorem b2316:B 87 6 e2158:=viaPerm pt0 pti0 b1249 (by decide +kernel) (by decide +kernel)
theorem b2317:B 87 6 e2159:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2318:B 87 6 e2160:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2319:B 87 6 e2161:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2320:B 87 6 e2162:=viaPerm pt3 pti3 b1714 (by decide +kernel) (by decide +kernel)
theorem b2321:B 87 6 e2163:=viaPerm pt4 pti4 b1916 (by decide +kernel) (by decide +kernel)
theorem b2322:B 87 6 e2164:=viaPerm pt3 pti3 b1981 (by decide +kernel) (by decide +kernel)
theorem b2323:B 87 6 e2165:=viaPerm pt4 pti4 b2011 (by decide +kernel) (by decide +kernel)
theorem b2324:B 87 6 e2166:=viaPerm pt3 pti3 b2187 (by decide +kernel) (by decide +kernel)
theorem b2325:B 87 6 e2167:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2326:B 87 6 e2168:=viaPerm pt0 pti0 b1491 (by decide +kernel) (by decide +kernel)
theorem b2327:B 87 6 e2169:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2328:B 87 6 e2170:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2329:B 87 6 e2171:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2330:B 87 6 e2172:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2331:B 87 6 e2173:=viaCut pjt_20 w2182 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2332:B 87 6 e2174:=viaCut pjt_11 w911 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2333:B 87 6 e2175:=viaCut pjt_18 w914 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2334:B 87 6 e2176:=viaCut pjt_29 w2178 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2335:B 87 6 e2177:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2336:B 87 6 e2178:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2337:B 87 6 e2179:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2338:B 87 6 e2180:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2339:B 87 6 e2181:=viaCut pjt_17 w907 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2340:B 87 6 e2182:=viaCut pjt_11 w911 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2341:B 87 6 e2183:=viaCut pjt_18 w914 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2342:B 87 6 e2184:=viaCut pjt_18 w1924 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2343:B 87 6 e2185:=viaPerm pt2 pti2 b592 (by decide +kernel) (by decide +kernel)
theorem b2344:B 87 6 e2186:=viaPerm pt2 pti2 b895 (by decide +kernel) (by decide +kernel)
theorem b2345:B 87 6 e2187:=viaPerm pt2 pti2 b1311 (by decide +kernel) (by decide +kernel)
theorem b2346:B 87 6 e2188:=viaPerm pt2 pti2 b1462 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2347:B 87 7 e2189:=viaBranch (ws:=[e769,e971,e770,e2077,e1303,e2078,e2079,e2080,e2081,e2082,e2083,e2084,e1894,e2085,e1896,e2086,e2087,e2088,e2089,e2090,e2091,e2092,e2104,e2105,e2106,e2107,e2108,e2109,e2110,e2111,e2112,e2113,e2114,e1034,e1365,e2115,e2116,e2117,e2118,e2119,e2120,e2121,e2122,e2123,e2124,e2125,e2126,e2156,e2157,e2158,e2159,e2160,e2161,e2162,e2163,e2164,e2165,e2166,e2167,e2168,e2169,e2170,e2171,e2172,e2173,e2174,e2175,e2176,e2177,e2178,e2179,e2180,e2181,e2182,e2183,e2184,e2185,e2186,e2187,e2188]) (consBan b831 (consBan b1056 (consBan b832 (consBan b2234 (consBan b1429 (consBan b2235 (consBan b2236 (consBan b2237 (consBan b2238 (consBan b2239 (consBan b2240 (consBan b2241 (consBan b2047 (consBan b2242 (consBan b2049 (consBan b2243 (consBan b2244 (consBan b2245 (consBan b2246 (consBan b2247 (consBan b2248 (consBan b2249 (consBan b2261 (consBan b2262 (consBan b2263 (consBan b2264 (consBan b2265 (consBan b2266 (consBan b2267 (consBan b2268 (consBan b2269 (consBan b2270 (consBan b2271 (consBan b1121 (consBan b1494 (consBan b2272 (consBan b2273 (consBan b2274 (consBan b2275 (consBan b2276 (consBan b2277 (consBan b2278 (consBan b2279 (consBan b2280 (consBan b2281 (consBan b2282 (consBan b2283 (consBan b2314 (consBan b2315 (consBan b2316 (consBan b2317 (consBan b2318 (consBan b2319 (consBan b2320 (consBan b2321 (consBan b2322 (consBan b2323 (consBan b2324 (consBan b2325 (consBan b2326 (consBan b2327 (consBan b2328 (consBan b2329 (consBan b2330 (consBan b2331 (consBan b2332 (consBan b2333 (consBan b2334 (consBan b2335 (consBan b2336 (consBan b2337 (consBan b2338 (consBan b2339 (consBan b2340 (consBan b2341 (consBan b2342 (consBan b2343 (consBan b2344 (consBan b2345 (consBan b2346 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2348:B 87 7 e2168:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2422:B 87 6 e2261:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2423:B 87 6 e2262:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2424:B 87 6 e2263:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2425:B 87 6 e2264:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2426:B 87 6 e2265:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2427:B 87 6 e2266:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2428:B 87 6 e2267:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2429:B 87 6 e2076:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2430:B 87 6 e2268:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2431:B 87 6 e2269:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2432:B 87 6 e2270:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2433:B 87 6 e2271:=viaPerm pt1 pti1 b1967 (by decide +kernel) (by decide +kernel)
theorem b2434:B 87 6 e2272:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2435:B 87 6 e2273:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2436:B 87 6 e2274:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2437:B 87 6 e2275:=viaPerm pt1 pti1 b2169 (by decide +kernel) (by decide +kernel)
theorem b2438:B 87 6 e2276:=viaPerm pt1 pti1 b2264 (by decide +kernel) (by decide +kernel)
theorem b2439:B 87 6 e2277:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2440:B 87 6 e2278:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2441:B 87 6 e2279:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2442:B 87 6 e2280:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2443:B 87 6 e2281:=viaPerm pt0 pti0 b2174 (by decide +kernel) (by decide +kernel)
theorem b2444:B 87 6 e2282:=viaPerm pt0 pti0 b2266 (by decide +kernel) (by decide +kernel)
theorem b2445:B 87 6 e2283:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2446:B 87 6 e2284:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2447:B 87 6 e2285:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2448:B 6 2 e2286:=viaSmall (by decide +kernel) (by decide)
theorem w2449:W 6 2 e2286:=viaSub (ws:=[e102,e2286]) (consBan b108 (consBan b2448 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2450:B 87 6 e2287:=viaCut pjt_29 w2449 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2451:B 87 6 e2288:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2452:B 87 6 e2289:=viaCut pjt_29 w2449 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2453:B 87 6 e2290:=viaCut pjt_18 w865 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2454:B 87 6 e2291:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2455:B 87 6 e2292:=viaPerm pt2 pti2 b2213 (by decide +kernel) (by decide +kernel)
theorem b2456:B 87 6 e2293:=viaPerm pt2 pti2 b2325 (by decide +kernel) (by decide +kernel)
theorem b2457:B 87 6 e2294:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2458:B 87 6 e2295:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2459:B 87 6 e2296:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2460:B 6 2 e2297:=viaSmall (by decide +kernel) (by decide)
theorem w2461:W 6 2 e2297:=viaSub (ws:=[e102,e2297]) (consBan b982 (consBan b2460 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b2462:B 87 6 e2298:=viaCut pjt_20 w2461 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2463:B 87 6 e2299:=viaCut pjt_29 w2449 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2464:B 87 6 e2300:=viaCut pjt_29 w2449 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2465:B 87 6 e2301:=viaCut pjt_20 w2461 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2466:B 87 6 e2302:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2467:B 87 6 e2303:=viaCut pjt_2 w2313 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2468:B 87 6 e2304:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2469:B 87 6 e2305:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2470:B 87 6 e2306:=viaPerm pt0 pti0 b1276 (by decide +kernel) (by decide +kernel)
theorem b2471:B 87 6 e2307:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2472:B 87 6 e2308:=viaPerm pt0 pti0 b1403 (by decide +kernel) (by decide +kernel)
theorem b2473:B 87 6 e2309:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2474:B 87 6 e2310:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2475:B 87 6 e2311:=viaPerm pt3 pti3 b1715 (by decide +kernel) (by decide +kernel)
theorem b2476:B 87 6 e2312:=viaPerm pt4 pti4 b1917 (by decide +kernel) (by decide +kernel)
theorem b2477:B 87 6 e2313:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2478:B 87 6 e2314:=viaPerm pt3 pti3 b1982 (by decide +kernel) (by decide +kernel)
theorem b2479:B 87 6 e2315:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2480:B 87 6 e2316:=viaPerm pt4 pti4 b2012 (by decide +kernel) (by decide +kernel)
theorem b2481:B 87 6 e2317:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2482:B 87 6 e2318:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2483:B 87 6 e2319:=viaPerm pt3 pti3 b2188 (by decide +kernel) (by decide +kernel)
theorem b2484:B 87 6 e2320:=viaPerm pt3 pti3 b2274 (by decide +kernel) (by decide +kernel)
theorem b2485:B 87 6 e2321:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2486:B 87 6 e2322:=viaPerm pt3 pti3 b2457 (by decide +kernel) (by decide +kernel)
theorem b2487:B 87 6 e2323:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2488:B 87 6 e2324:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2489:B 87 6 e2325:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2490:B 87 6 e2326:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2491:B 87 6 e2327:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2492:B 87 6 e2328:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2493:B 87 6 e2329:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2494:B 87 6 e2330:=viaCut pjt_20 w2461 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2495:B 87 6 e2331:=viaCut pjt_11 w911 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2496:B 87 6 e2332:=viaCut pjt_18 w914 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2497:B 87 6 e2333:=viaCut pjt_20 w2461 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2498:B 87 6 e2334:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2499:B 87 6 e2335:=viaPerm pt2 pti2 b609 (by decide +kernel) (by decide +kernel)
theorem b2500:B 87 6 e2336:=viaPerm pt2 pti2 b897 (by decide +kernel) (by decide +kernel)
theorem b2501:B 87 6 e2337:=viaPerm pt2 pti2 b1141 (by decide +kernel) (by decide +kernel)
theorem b2502:B 87 6 e2338:=viaPerm pt2 pti2 b1313 (by decide +kernel) (by decide +kernel)
theorem b2503:B 87 6 e2339:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2504:B 87 6 e2340:=viaPerm pt2 pti2 b1464 (by decide +kernel) (by decide +kernel)
theorem b2505:B 87 6 e2341:=viaPerm pt2 pti2 b1536 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2506:B 87 7 e1895:=viaBranch (ws:=[e2261,e993,e995,e1139,e2262,e1383,e2263,e2264,e2265,e1803,e2266,e2267,e1894,e2076,e1896,e2268,e2269,e2270,e2271,e2272,e2273,e2274,e2275,e2276,e2277,e2278,e2279,e2280,e2281,e2282,e2283,e2284,e2285,e2287,e2288,e2289,e2290,e2291,e2292,e2293,e2294,e2295,e2296,e2298,e2299,e2300,e2301,e2302,e2303,e2304,e2305,e2306,e2307,e2308,e2309,e2310,e2311,e2312,e2313,e2314,e2315,e2316,e2317,e2318,e2319,e2320,e2321,e2322,e2323,e2324,e2325,e2326,e2327,e2328,e2329,e2330,e2331,e2332,e2333,e2334,e2335,e2336,e2337,e2338,e2339,e2340,e2341]) (consBan b2422 (consBan b1079 (consBan b1081 (consBan b1257 (consBan b2423 (consBan b1512 (consBan b2424 (consBan b2425 (consBan b2426 (consBan b1953 (consBan b2427 (consBan b2428 (consBan b2047 (consBan b2429 (consBan b2049 (consBan b2430 (consBan b2431 (consBan b2432 (consBan b2433 (consBan b2434 (consBan b2435 (consBan b2436 (consBan b2437 (consBan b2438 (consBan b2439 (consBan b2440 (consBan b2441 (consBan b2442 (consBan b2443 (consBan b2444 (consBan b2445 (consBan b2446 (consBan b2447 (consBan b2450 (consBan b2451 (consBan b2452 (consBan b2453 (consBan b2454 (consBan b2455 (consBan b2456 (consBan b2457 (consBan b2458 (consBan b2459 (consBan b2462 (consBan b2463 (consBan b2464 (consBan b2465 (consBan b2466 (consBan b2467 (consBan b2468 (consBan b2469 (consBan b2470 (consBan b2471 (consBan b2472 (consBan b2473 (consBan b2474 (consBan b2475 (consBan b2476 (consBan b2477 (consBan b2478 (consBan b2479 (consBan b2480 (consBan b2481 (consBan b2482 (consBan b2483 (consBan b2484 (consBan b2485 (consBan b2486 (consBan b2487 (consBan b2488 (consBan b2489 (consBan b2490 (consBan b2491 (consBan b2492 (consBan b2493 (consBan b2494 (consBan b2495 (consBan b2496 (consBan b2497 (consBan b2498 (consBan b2499 (consBan b2500 (consBan b2501 (consBan b2502 (consBan b2503 (consBan b2504 (consBan b2505 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2507:B 87 6 e2342:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2508:B 87 6 e2343:=viaPerm pt0 pti0 b1697 (by decide +kernel) (by decide +kernel)
theorem b2509:B 87 6 e2344:=viaPerm pt0 pti0 b1971 (by decide +kernel) (by decide +kernel)
theorem b2510:B 87 6 e2189:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2511:B 87 6 e2345:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2512:B 87 6 e2346:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2513:B 87 6 e2347:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2514:B 87 6 e2348:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2515:B 87 6 e2349:=viaPerm pt2 pti2 b1895 (by decide +kernel) (by decide +kernel)
theorem b2516:B 87 6 e2350:=viaPerm pt1 pti1 b1968 (by decide +kernel) (by decide +kernel)
theorem b2517:B 87 6 e2351:=viaPerm pt2 pti2 b2008 (by decide +kernel) (by decide +kernel)
theorem b2518:B 87 6 e2352:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2519:B 87 6 e2353:=viaPerm pt1 pti1 b2170 (by decide +kernel) (by decide +kernel)
theorem b2520:B 16 3 e1105:=viaSmall (by decide +kernel) (by decide)
theorem w2521:W 16 3 e1105:=widen (by decide +kernel) b2520
theorem b2522:B 87 6 e2354:=viaCut pjt_9 w2521 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2523:B 87 6 e2355:=viaPerm pt1 pti1 b2441 (by decide +kernel) (by decide +kernel)
theorem b2524:B 87 6 e2356:=viaPerm pt0 pti0 b2175 (by decide +kernel) (by decide +kernel)
theorem b2525:B 87 6 e2357:=viaPerm pt0 pti0 b2446 (by decide +kernel) (by decide +kernel)
theorem b2526:B 87 6 e2358:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2527:B 87 6 e2359:=viaPerm pt0 pti0 b1495 (by decide +kernel) (by decide +kernel)
theorem b2528:B 87 6 e2360:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2529:B 87 6 e2361:=viaCut pjt_18 w865 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2530:B 87 6 e2362:=viaPerm pt2 pti2 b2214 (by decide +kernel) (by decide +kernel)
theorem b2531:B 87 6 e2363:=viaPerm pt2 pti2 b2487 (by decide +kernel) (by decide +kernel)
theorem b2532:B 87 6 e2364:=viaPerm pt0 pti0 b1486 (by decide +kernel) (by decide +kernel)
theorem b2533:B 87 6 e2365:=viaCut pjt_2 w2313 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2534:B 87 6 e2366:=viaCut pjt_2 w2313 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2535:B 87 6 e2367:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2536:B 87 6 e2368:=viaPerm pt0 pti0 b304 (by decide +kernel) (by decide +kernel)
theorem b2537:B 87 6 e2369:=viaPerm pt0 pti0 b1277 (by decide +kernel) (by decide +kernel)
theorem b2538:B 87 6 e2370:=viaPerm pt0 pti0 b1096 (by decide +kernel) (by decide +kernel)
theorem b2539:B 87 6 e2371:=viaPerm pt0 pti0 b1490 (by decide +kernel) (by decide +kernel)
theorem b2540:B 87 6 e2372:=viaPerm pt0 pti0 b335 (by decide +kernel) (by decide +kernel)
theorem b2541:B 87 6 e2373:=viaPerm pt0 pti0 b1099 (by decide +kernel) (by decide +kernel)
theorem b2542:B 87 6 e2374:=viaPerm pt0 pti0 b1520 (by decide +kernel) (by decide +kernel)
theorem b2543:B 87 6 e2375:=viaPerm pt3 pti3 b1716 (by decide +kernel) (by decide +kernel)
theorem b2544:B 87 6 e2376:=viaPerm pt4 pti4 b1918 (by decide +kernel) (by decide +kernel)
theorem b2545:B 87 6 e2377:=viaPerm pt3 pti3 b1983 (by decide +kernel) (by decide +kernel)
theorem b2546:B 87 6 e2378:=viaPerm pt4 pti4 b2013 (by decide +kernel) (by decide +kernel)
theorem b2547:B 87 6 e2379:=viaPerm pt3 pti3 b2189 (by decide +kernel) (by decide +kernel)
theorem b2548:B 87 6 e2380:=viaPerm pt3 pti3 b2458 (by decide +kernel) (by decide +kernel)
theorem b2549:B 87 6 e1879:=viaPerm pt0 pti0 b1488 (by decide +kernel) (by decide +kernel)
theorem b2550:B 87 6 e2381:=viaPerm pt0 pti0 b1496 (by decide +kernel) (by decide +kernel)
theorem b2551:B 87 6 e2382:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2552:B 87 6 e2383:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2553:B 87 6 e2384:=viaPerm pt0 pti0 b1499 (by decide +kernel) (by decide +kernel)
theorem b2554:B 87 6 e2385:=viaPerm pt0 pti0 b1500 (by decide +kernel) (by decide +kernel)
theorem b2555:B 87 6 e2386:=viaCut pjt_11 w911 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2556:B 87 6 e2387:=viaPerm pt1 pti1 b2342 (by decide +kernel) (by decide +kernel)
theorem b2557:B 87 6 e2388:=viaPerm pt0 pti0 b1503 (by decide +kernel) (by decide +kernel)
theorem b2558:B 87 6 e2389:=viaPerm pt4 pti4 b2329 (by decide +kernel) (by decide +kernel)
theorem b2559:B 87 6 e2390:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2560:B 87 6 e2391:=viaCut pjt_11 w911 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2561:B 87 6 e2392:=viaCut pjt_18 w914 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2562:B 87 6 e2393:=viaPerm pt2 pti2 b610 (by decide +kernel) (by decide +kernel)
theorem b2563:B 87 6 e2394:=viaPerm pt2 pti2 b898 (by decide +kernel) (by decide +kernel)
theorem b2564:B 87 6 e2395:=viaPerm pt2 pti2 b1314 (by decide +kernel) (by decide +kernel)
theorem b2565:B 87 6 e2396:=viaPerm pt2 pti2 b1465 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2566:B 87 7 e2086:=viaBranch (ws:=[e994,e773,e1140,e1305,e2342,e2343,e1804,e2344,e2085,e2189,e2345,e1894,e1896,e2346,e2347,e2348,e2349,e2350,e2351,e2352,e2353,e2354,e2355,e2356,e2357,e1363,e2358,e2359,e1036,e2287,e2360,e2289,e2361,e2362,e2363,e2364,e2365,e2366,e2367,e2368,e2369,e2370,e2371,e2302,e2372,e2373,e2306,e2307,e2374,e2375,e2376,e2377,e2378,e2379,e2380,e1879,e2381,e2382,e2383,e2384,e2385,e2386,e2387,e2388,e2324,e2389,e2390,e2329,e2330,e2391,e2392,e2333,e2393,e2394,e2395,e2396]) (consBan b1080 (consBan b835 (consBan b1258 (consBan b1431 (consBan b2507 (consBan b2508 (consBan b1954 (consBan b2509 (consBan b2242 (consBan b2510 (consBan b2511 (consBan b2047 (consBan b2049 (consBan b2512 (consBan b2513 (consBan b2514 (consBan b2515 (consBan b2516 (consBan b2517 (consBan b2518 (consBan b2519 (consBan b2522 (consBan b2523 (consBan b2524 (consBan b2525 (consBan b1492 (consBan b2526 (consBan b2527 (consBan b1123 (consBan b2450 (consBan b2528 (consBan b2452 (consBan b2529 (consBan b2530 (consBan b2531 (consBan b2532 (consBan b2533 (consBan b2534 (consBan b2535 (consBan b2536 (consBan b2537 (consBan b2538 (consBan b2539 (consBan b2466 (consBan b2540 (consBan b2541 (consBan b2470 (consBan b2471 (consBan b2542 (consBan b2543 (consBan b2544 (consBan b2545 (consBan b2546 (consBan b2547 (consBan b2548 (consBan b2549 (consBan b2550 (consBan b2551 (consBan b2552 (consBan b2553 (consBan b2554 (consBan b2555 (consBan b2556 (consBan b2557 (consBan b2488 (consBan b2558 (consBan b2559 (consBan b2493 (consBan b2494 (consBan b2560 (consBan b2561 (consBan b2497 (consBan b2562 (consBan b2563 (consBan b2564 (consBan b2565 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2567:B 87 7 e2397:=viaPerm pt1 pti1 b1544 (by decide +kernel) (by decide +kernel)
theorem b2568:B 87 7 e2398:=viaPerm pt1 pti1 b1934 (by decide +kernel) (by decide +kernel)
theorem b2569:B 87 7 e2399:=viaPerm pt1 pti1 b1935 (by decide +kernel) (by decide +kernel)
theorem b2570:B 87 7 e2400:=viaPerm pt1 pti1 b1936 (by decide +kernel) (by decide +kernel)
theorem b2571:B 87 7 e2401:=viaPerm pt1 pti1 b2027 (by decide +kernel) (by decide +kernel)
theorem b2572:B 87 7 e2402:=viaPerm pt1 pti1 b2028 (by decide +kernel) (by decide +kernel)
theorem b2573:B 87 7 e2403:=viaPerm pt1 pti1 b2029 (by decide +kernel) (by decide +kernel)
theorem b2574:B 87 7 e2404:=viaPerm pt1 pti1 b2030 (by decide +kernel) (by decide +kernel)
theorem b2575:B 87 7 e2405:=viaPerm pt1 pti1 b2031 (by decide +kernel) (by decide +kernel)
theorem b2576:B 87 7 e2406:=viaPerm pt1 pti1 b2233 (by decide +kernel) (by decide +kernel)
theorem b2577:B 87 7 e2407:=viaPerm pt1 pti1 b2347 (by decide +kernel) (by decide +kernel)
theorem b2578:B 87 7 e2408:=viaPerm pt1 pti1 b2348 (by decide +kernel) (by decide +kernel)
theorem b2579:B 87 7 e2409:=viaPerm pt1 pti1 b2506 (by decide +kernel) (by decide +kernel)
theorem b2580:B 87 7 e2410:=viaPerm pt1 pti1 b2566 (by decide +kernel) (by decide +kernel)
theorem b2581:B 87 7 e1359:=viaPerm pt0 pti0 b2031 (by decide +kernel) (by decide +kernel)
theorem b2582:B 87 7 e2411:=viaPerm pt0 pti0 b2233 (by decide +kernel) (by decide +kernel)
theorem b2583:B 87 7 e2412:=viaPerm pt0 pti0 b2347 (by decide +kernel) (by decide +kernel)
theorem b2584:B 87 7 e2413:=viaPerm pt0 pti0 b2506 (by decide +kernel) (by decide +kernel)
theorem b2585:B 87 7 e2414:=viaPerm pt0 pti0 b2566 (by decide +kernel) (by decide +kernel)
theorem b2586:B 87 7 e1362:=viaPerm pt0 pti0 b2348 (by decide +kernel) (by decide +kernel)
theorem b2926:B 20 4 e2734:=viaSmall (by decide +kernel) (by decide)
theorem w2927:W 20 4 e2734:=widen (by decide +kernel) b2926
theorem b2928:B 87 6 e2735:=viaCut pjt_6 w2927 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2929:B 87 6 e2736:=viaCut pjt_16 w856 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2930:B 87 6 e2737:=viaCut pjt_16 w856 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2931:B 20 4 e2738:=viaSmall (by decide +kernel) (by decide)
theorem w2932:W 20 4 e2738:=widen (by decide +kernel) b2931
theorem b2933:B 87 6 e2739:=viaCut pjt_6 w2932 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2934:B 87 6 e2740:=viaPerm pt0 pti0 b2928 (by decide +kernel) (by decide +kernel)
theorem b2935:B 87 6 e2741:=viaPerm pt0 pti0 b2929 (by decide +kernel) (by decide +kernel)
theorem b2936:B 87 6 e2742:=viaPerm pt0 pti0 b2930 (by decide +kernel) (by decide +kernel)
theorem b2937:B 87 6 e2743:=viaPerm pt0 pti0 b2933 (by decide +kernel) (by decide +kernel)
theorem b2952:B 87 5 e2757:=viaSmall (by decide +kernel) (by decide)
theorem b2953:B 87 5 e2758:=viaSmall (by decide +kernel) (by decide)
theorem b2954:B 87 5 e2759:=viaSmall (by decide +kernel) (by decide)
theorem b2955:B 87 5 e2760:=viaSmall (by decide +kernel) (by decide)
theorem b2956:B 87 5 e2761:=viaSmall (by decide +kernel) (by decide)
theorem b2957:B 87 5 e2762:=viaPerm pt0 pti0 b2956 (by decide +kernel) (by decide +kernel)
theorem b2958:B 87 5 e2763:=viaSmall (by decide +kernel) (by decide)
theorem b2959:B 87 5 e2764:=viaPerm pt0 pti0 b2958 (by decide +kernel) (by decide +kernel)
theorem b2960:B 87 5 e2765:=viaSmall (by decide +kernel) (by decide)
theorem b2961:B 87 5 e2766:=viaSmall (by decide +kernel) (by decide)
theorem b2962:B 87 5 e2767:=viaSmall (by decide +kernel) (by decide)
theorem b2963:B 87 5 e2768:=viaSmall (by decide +kernel) (by decide)
theorem b2964:B 87 5 e2769:=viaSmall (by decide +kernel) (by decide)
theorem b2965:B 87 5 e2770:=viaSmall (by decide +kernel) (by decide)
theorem b2966:B 87 5 e2771:=viaSmall (by decide +kernel) (by decide)
theorem b2967:B 87 5 e2772:=viaSmall (by decide +kernel) (by decide)
theorem b2968:B 87 5 e2773:=viaPerm pt0 pti0 b2960 (by decide +kernel) (by decide +kernel)
theorem b2969:B 87 5 e2774:=viaPerm pt0 pti0 b2961 (by decide +kernel) (by decide +kernel)
theorem b2970:B 87 5 e2775:=viaSmall (by decide +kernel) (by decide)
theorem b2971:B 87 5 e2776:=viaPerm pt0 pti0 b2970 (by decide +kernel) (by decide +kernel)
theorem b2972:B 87 5 e2777:=viaSmall (by decide +kernel) (by decide)
theorem b2973:B 87 5 e2778:=viaPerm pt0 pti0 b2972 (by decide +kernel) (by decide +kernel)
theorem b2974:B 87 5 e2779:=viaPerm pt2 pti2 b2153 (by decide +kernel) (by decide +kernel)
theorem b2975:B 87 5 e2780:=viaSmall (by decide +kernel) (by decide)
theorem b2976:B 87 5 e2781:=viaSmall (by decide +kernel) (by decide)
theorem b2977:B 87 5 e2782:=viaSmall (by decide +kernel) (by decide)
theorem b2978:B 87 5 e2783:=viaPerm pt0 pti0 b2952 (by decide +kernel) (by decide +kernel)
theorem b2979:B 87 5 e2784:=viaPerm pt0 pti0 b2953 (by decide +kernel) (by decide +kernel)
theorem b2980:B 87 5 e2785:=viaPerm pt0 pti0 b2954 (by decide +kernel) (by decide +kernel)
theorem b2981:B 87 5 e2786:=viaPerm pt0 pti0 b2955 (by decide +kernel) (by decide +kernel)
theorem b2982:B 87 5 e2787:=viaPerm pt0 pti0 b2962 (by decide +kernel) (by decide +kernel)
theorem b2983:B 87 5 e2788:=viaPerm pt0 pti0 b2963 (by decide +kernel) (by decide +kernel)
theorem b2984:B 87 5 e2789:=viaPerm pt0 pti0 b2964 (by decide +kernel) (by decide +kernel)
theorem b2985:B 87 5 e2790:=viaPerm pt0 pti0 b2965 (by decide +kernel) (by decide +kernel)
theorem b2986:B 87 5 e2791:=viaPerm pt0 pti0 b2966 (by decide +kernel) (by decide +kernel)
theorem b2987:B 87 5 e2792:=viaPerm pt0 pti0 b2967 (by decide +kernel) (by decide +kernel)
theorem b2988:B 87 5 e2793:=viaPerm pt0 pti0 b2974 (by decide +kernel) (by decide +kernel)
theorem b2989:B 87 5 e2794:=viaPerm pt0 pti0 b2975 (by decide +kernel) (by decide +kernel)
theorem b2990:B 87 5 e2795:=viaPerm pt0 pti0 b2976 (by decide +kernel) (by decide +kernel)
theorem b2991:B 87 5 e2796:=viaPerm pt0 pti0 b2977 (by decide +kernel) (by decide +kernel)
theorem b2992:B 87 5 e2797:=viaSmall (by decide +kernel) (by decide)
theorem b2993:B 87 5 e2798:=viaSmall (by decide +kernel) (by decide)
theorem b2994:B 87 5 e2799:=viaSmall (by decide +kernel) (by decide)
theorem b2995:B 87 5 e2800:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b2996:B 87 6 e2801:=viaBranch (ws:=[e2757,e2758,e2759,e2760,e2761,e2762,e2763,e2764,e2765,e2766,e2767,e2768,e2769,e2770,e2771,e2772,e2773,e2774,e2775,e2776,e2777,e2778,e2779,e2780,e2781,e2782,e2783,e2784,e2785,e2786,e2787,e2788,e2789,e2790,e2791,e2792,e2793,e2794,e2795,e2796,e2797,e2798,e2799,e2800]) (consBan b2952 (consBan b2953 (consBan b2954 (consBan b2955 (consBan b2956 (consBan b2957 (consBan b2958 (consBan b2959 (consBan b2960 (consBan b2961 (consBan b2962 (consBan b2963 (consBan b2964 (consBan b2965 (consBan b2966 (consBan b2967 (consBan b2968 (consBan b2969 (consBan b2970 (consBan b2971 (consBan b2972 (consBan b2973 (consBan b2974 (consBan b2975 (consBan b2976 (consBan b2977 (consBan b2978 (consBan b2979 (consBan b2980 (consBan b2981 (consBan b2982 (consBan b2983 (consBan b2984 (consBan b2985 (consBan b2986 (consBan b2987 (consBan b2988 (consBan b2989 (consBan b2990 (consBan b2991 (consBan b2992 (consBan b2993 (consBan b2994 (consBan b2995 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b2997:B 87 6 e2802:=viaCut pjt_9 w1119 (by decide) (by decide +kernel) (by decide +kernel)
theorem b2998:B 87 6 e2803:=viaCut pjt_12 w111 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3004:B 35 4 e858:=viaSmall (by decide +kernel) (by decide)
theorem b3005:B 35 4 e859:=viaSmall (by decide +kernel) (by decide)
theorem b3006:B 35 4 e860:=viaSmall (by decide +kernel) (by decide)
theorem b3007:B 35 4 e861:=viaSmall (by decide +kernel) (by decide)
theorem b3008:B 35 4 e862:=viaSmall (by decide +kernel) (by decide)
theorem b3009:B 35 4 e891:=viaPerm pc0_0 pci0_0 b975 (by decide +kernel) (by decide +kernel)
theorem b3010:B 35 4 e892:=viaSmall (by decide +kernel) (by decide)
theorem b3011:B 35 4 e2809:=viaSmall (by decide +kernel) (by decide)
theorem b3012:B 35 4 e2810:=viaPerm pc0_0 pci0_0 b959 (by decide +kernel) (by decide +kernel)
theorem b3013:B 35 4 e2811:=viaPerm pc0_0 pci0_0 b3011 (by decide +kernel) (by decide +kernel)
theorem b3014:B 35 4 e2812:=viaSmall (by decide +kernel) (by decide)
theorem b3015:B 35 4 e2813:=viaSmall (by decide +kernel) (by decide)
theorem b3016:B 35 4 e2814:=viaSmall (by decide +kernel) (by decide)
theorem b3017:B 35 4 e2815:=viaSmall (by decide +kernel) (by decide)
theorem b3018:B 35 4 e2816:=viaSmall (by decide +kernel) (by decide)
theorem b3019:B 35 4 e2817:=viaSmall (by decide +kernel) (by decide)
theorem b3020:B 35 4 e2818:=viaSmall (by decide +kernel) (by decide)
theorem b3021:B 35 4 e2819:=viaSmall (by decide +kernel) (by decide)
theorem b3022:B 35 4 e2820:=viaPerm pc0_0 pci0_0 b3014 (by decide +kernel) (by decide +kernel)
theorem b3023:B 35 4 e2821:=viaPerm pc0_0 pci0_0 b3016 (by decide +kernel) (by decide +kernel)
theorem b3024:B 35 4 e2822:=viaPerm pc0_0 pci0_0 b3015 (by decide +kernel) (by decide +kernel)
theorem b3025:B 35 4 e2823:=viaPerm pc0_0 pci0_0 b3017 (by decide +kernel) (by decide +kernel)
theorem b3026:B 35 4 e2824:=viaPerm pc0_0 pci0_0 b3020 (by decide +kernel) (by decide +kernel)
theorem b3027:B 35 4 e2825:=viaPerm pc0_0 pci0_0 b3021 (by decide +kernel) (by decide +kernel)
theorem b3028:B 35 4 e2826:=viaPerm pc0_0 pci0_0 b3018 (by decide +kernel) (by decide +kernel)
theorem b3029:B 35 4 e2827:=viaPerm pc0_0 pci0_0 b3019 (by decide +kernel) (by decide +kernel)
theorem b3030:B 35 4 e2828:=viaSmall (by decide +kernel) (by decide)
theorem b3031:B 35 4 e2829:=viaSmall (by decide +kernel) (by decide)
theorem b3032:B 35 4 e2830:=viaSmall (by decide +kernel) (by decide)
theorem b3033:B 35 4 e2831:=viaPerm pc0_0 pci0_0 b3032 (by decide +kernel) (by decide +kernel)
theorem b3034:B 35 4 e2832:=viaPerm pc0_0 pci0_0 b3004 (by decide +kernel) (by decide +kernel)
theorem b3035:B 35 4 e2833:=viaPerm pc0_0 pci0_0 b3005 (by decide +kernel) (by decide +kernel)
theorem b3036:B 35 4 e2834:=viaPerm pc0_0 pci0_0 b3006 (by decide +kernel) (by decide +kernel)
theorem b3037:B 35 4 e2835:=viaPerm pc0_0 pci0_0 b3007 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3038:B 35 5 e2836:=viaBranch (ws:=[e858,e859,e860,e861,e862,e890,e891,e892,e882,e2809,e2810,e2811,e2812,e2813,e2814,e2815,e2816,e2817,e2818,e2819,e2820,e2821,e2822,e2823,e2824,e2825,e2826,e2827,e2828,e2829,e2830,e2831,e2832,e2833,e2834,e2835]) (consBan b3004 (consBan b3005 (consBan b3006 (consBan b3007 (consBan b3008 (consBan b975 (consBan b3009 (consBan b3010 (consBan b959 (consBan b3011 (consBan b3012 (consBan b3013 (consBan b3014 (consBan b3015 (consBan b3016 (consBan b3017 (consBan b3018 (consBan b3019 (consBan b3020 (consBan b3021 (consBan b3022 (consBan b3023 (consBan b3024 (consBan b3025 (consBan b3026 (consBan b3027 (consBan b3028 (consBan b3029 (consBan b3030 (consBan b3031 (consBan b3032 (consBan b3033 (consBan b3034 (consBan b3035 (consBan b3036 (consBan b3037 (nilBan _ _))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3039:B 35 4 e2837:=viaSmall (by decide +kernel) (by decide)
theorem b3040:B 35 4 e2838:=viaSmall (by decide +kernel) (by decide)
theorem b3041:B 35 4 e2839:=viaSmall (by decide +kernel) (by decide)
theorem b3042:B 35 4 e2840:=viaSmall (by decide +kernel) (by decide)
theorem b3043:B 35 4 e2841:=viaSmall (by decide +kernel) (by decide)
theorem b3044:B 35 4 e2842:=viaPerm pc0_0 pci0_0 b3043 (by decide +kernel) (by decide +kernel)
theorem b3045:B 35 4 e2843:=viaSmall (by decide +kernel) (by decide)
theorem b3046:B 35 4 e2844:=viaPerm pc0_0 pci0_0 b3045 (by decide +kernel) (by decide +kernel)
theorem b3047:B 35 4 e2845:=viaSmall (by decide +kernel) (by decide)
theorem b3048:B 35 4 e2846:=viaSmall (by decide +kernel) (by decide)
theorem b3049:B 35 4 e2847:=viaSmall (by decide +kernel) (by decide)
theorem b3050:B 35 4 e2848:=viaSmall (by decide +kernel) (by decide)
theorem b3051:B 35 4 e2849:=viaSmall (by decide +kernel) (by decide)
theorem b3052:B 35 4 e2850:=viaSmall (by decide +kernel) (by decide)
theorem b3053:B 35 4 e2851:=viaSmall (by decide +kernel) (by decide)
theorem b3054:B 35 4 e2852:=viaSmall (by decide +kernel) (by decide)
theorem b3055:B 35 4 e2853:=viaSmall (by decide +kernel) (by decide)
theorem b3056:B 35 4 e2854:=viaSmall (by decide +kernel) (by decide)
theorem b3057:B 35 4 e2855:=viaSmall (by decide +kernel) (by decide)
theorem b3058:B 35 4 e2856:=viaPerm pc0_0 pci0_0 b3047 (by decide +kernel) (by decide +kernel)
theorem b3059:B 35 4 e2857:=viaPerm pc0_0 pci0_0 b3049 (by decide +kernel) (by decide +kernel)
theorem b3060:B 35 4 e2858:=viaPerm pc0_0 pci0_0 b3048 (by decide +kernel) (by decide +kernel)
theorem b3061:B 35 4 e2859:=viaPerm pc0_0 pci0_0 b3051 (by decide +kernel) (by decide +kernel)
theorem b3062:B 35 4 e2860:=viaPerm pc0_0 pci0_0 b3050 (by decide +kernel) (by decide +kernel)
theorem b3063:B 35 4 e2861:=viaSmall (by decide +kernel) (by decide)
theorem b3064:B 35 4 e2862:=viaPerm pc0_0 pci0_0 b3063 (by decide +kernel) (by decide +kernel)
theorem b3065:B 35 4 e2863:=viaSmall (by decide +kernel) (by decide)
theorem b3066:B 35 4 e2864:=viaPerm pc0_0 pci0_0 b3065 (by decide +kernel) (by decide +kernel)
theorem b3067:B 35 4 e2865:=viaSmall (by decide +kernel) (by decide)
theorem b3068:B 35 4 e2866:=viaSmall (by decide +kernel) (by decide)
theorem b3069:B 35 4 e2867:=viaSmall (by decide +kernel) (by decide)
theorem b3070:B 35 4 e2868:=viaSmall (by decide +kernel) (by decide)
theorem b3071:B 35 4 e2869:=viaSmall (by decide +kernel) (by decide)
theorem b3072:B 35 4 e2870:=viaSmall (by decide +kernel) (by decide)
theorem b3073:B 35 4 e2871:=viaPerm pc0_0 pci0_0 b3039 (by decide +kernel) (by decide +kernel)
theorem b3074:B 35 4 e2872:=viaPerm pc0_0 pci0_0 b3040 (by decide +kernel) (by decide +kernel)
theorem b3075:B 35 4 e2873:=viaPerm pc0_0 pci0_0 b3041 (by decide +kernel) (by decide +kernel)
theorem b3076:B 35 4 e2874:=viaPerm pc0_0 pci0_0 b3042 (by decide +kernel) (by decide +kernel)
theorem b3077:B 35 4 e2875:=viaPerm pc0_0 pci0_0 b3052 (by decide +kernel) (by decide +kernel)
theorem b3078:B 35 4 e2876:=viaPerm pc0_0 pci0_0 b3053 (by decide +kernel) (by decide +kernel)
theorem b3079:B 35 4 e2877:=viaPerm pc0_0 pci0_0 b3054 (by decide +kernel) (by decide +kernel)
theorem b3080:B 35 4 e2878:=viaPerm pc0_0 pci0_0 b3055 (by decide +kernel) (by decide +kernel)
theorem b3081:B 35 4 e2879:=viaPerm pc0_0 pci0_0 b3056 (by decide +kernel) (by decide +kernel)
theorem b3082:B 35 4 e2880:=viaPerm pc0_0 pci0_0 b3057 (by decide +kernel) (by decide +kernel)
theorem b3083:B 35 4 e2881:=viaPerm pc0_0 pci0_0 b3067 (by decide +kernel) (by decide +kernel)
theorem b3084:B 35 4 e2882:=viaPerm pc0_0 pci0_0 b3068 (by decide +kernel) (by decide +kernel)
theorem b3085:B 35 4 e2883:=viaPerm pc0_0 pci0_0 b3069 (by decide +kernel) (by decide +kernel)
theorem b3086:B 35 4 e2884:=viaPerm pc0_0 pci0_0 b3070 (by decide +kernel) (by decide +kernel)
theorem b3087:B 35 4 e2885:=viaPerm pc0_0 pci0_0 b3071 (by decide +kernel) (by decide +kernel)
theorem b3088:B 35 4 e2886:=viaPerm pc0_0 pci0_0 b3072 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3089:B 35 5 e2887:=viaBranch (ws:=[e2837,e2838,e2839,e2840,e2841,e2842,e2843,e2844,e2845,e2846,e2847,e2848,e2849,e2850,e2851,e2852,e2853,e2854,e2855,e2856,e2857,e2858,e2859,e2860,e2861,e2862,e2863,e2864,e2865,e2866,e2867,e2868,e2869,e2870,e2871,e2872,e2873,e2874,e2875,e2876,e2877,e2878,e2879,e2880,e2881,e2882,e2883,e2884,e2885,e2886]) (consBan b3039 (consBan b3040 (consBan b3041 (consBan b3042 (consBan b3043 (consBan b3044 (consBan b3045 (consBan b3046 (consBan b3047 (consBan b3048 (consBan b3049 (consBan b3050 (consBan b3051 (consBan b3052 (consBan b3053 (consBan b3054 (consBan b3055 (consBan b3056 (consBan b3057 (consBan b3058 (consBan b3059 (consBan b3060 (consBan b3061 (consBan b3062 (consBan b3063 (consBan b3064 (consBan b3065 (consBan b3066 (consBan b3067 (consBan b3068 (consBan b3069 (consBan b3070 (consBan b3071 (consBan b3072 (consBan b3073 (consBan b3074 (consBan b3075 (consBan b3076 (consBan b3077 (consBan b3078 (consBan b3079 (consBan b3080 (consBan b3081 (consBan b3082 (consBan b3083 (consBan b3084 (consBan b3085 (consBan b3086 (consBan b3087 (consBan b3088 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w3090:W 35 5 e2887:=viaSub (ws:=[e2836,e2887]) (consBan b3038 (consBan b3089 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b3091:B 87 6 e2888:=viaCut pjt_0 w3090 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3092:B 35 4 e2889:=viaSmall (by decide +kernel) (by decide)
theorem b3093:B 35 4 e2890:=viaPerm pc0_0 pci0_0 b3092 (by decide +kernel) (by decide +kernel)
theorem b3094:B 35 4 e2891:=viaSmall (by decide +kernel) (by decide)
theorem b3095:B 35 4 e2892:=viaPerm pc0_0 pci0_0 b3094 (by decide +kernel) (by decide +kernel)
theorem b3096:B 35 4 e2893:=viaSmall (by decide +kernel) (by decide)
theorem b3097:B 35 4 e2894:=viaSmall (by decide +kernel) (by decide)
theorem b3098:B 35 4 e2895:=viaSmall (by decide +kernel) (by decide)
theorem b3099:B 35 4 e2896:=viaSmall (by decide +kernel) (by decide)
theorem b3100:B 35 4 e2897:=viaSmall (by decide +kernel) (by decide)
theorem b3101:B 35 4 e2898:=viaSmall (by decide +kernel) (by decide)
theorem b3102:B 35 4 e2899:=viaSmall (by decide +kernel) (by decide)
theorem b3103:B 35 4 e2900:=viaSmall (by decide +kernel) (by decide)
theorem b3104:B 35 4 e2901:=viaPerm pc0_0 pci0_0 b3097 (by decide +kernel) (by decide +kernel)
theorem b3105:B 35 4 e2902:=viaPerm pc0_0 pci0_0 b3096 (by decide +kernel) (by decide +kernel)
theorem b3106:B 35 4 e2903:=viaPerm pc0_0 pci0_0 b3099 (by decide +kernel) (by decide +kernel)
theorem b3107:B 35 4 e2904:=viaPerm pc0_0 pci0_0 b3098 (by decide +kernel) (by decide +kernel)
theorem b3108:B 35 4 e2905:=viaSmall (by decide +kernel) (by decide)
theorem b3109:B 35 4 e2906:=viaPerm pc0_0 pci0_0 b3108 (by decide +kernel) (by decide +kernel)
theorem b3110:B 35 4 e2907:=viaSmall (by decide +kernel) (by decide)
theorem b3111:B 35 4 e2908:=viaPerm pc0_0 pci0_0 b3110 (by decide +kernel) (by decide +kernel)
theorem b3112:B 35 4 e2909:=viaSmall (by decide +kernel) (by decide)
theorem b3113:B 35 4 e2910:=viaSmall (by decide +kernel) (by decide)
theorem b3114:B 35 4 e2911:=viaPerm pc0_0 pci0_0 b694 (by decide +kernel) (by decide +kernel)
theorem b3115:B 35 4 e2912:=viaPerm pc0_0 pci0_0 b120 (by decide +kernel) (by decide +kernel)
theorem b3116:B 35 4 e2913:=viaPerm pc0_0 pci0_0 b695 (by decide +kernel) (by decide +kernel)
theorem b3117:B 35 4 e2914:=viaPerm pc0_0 pci0_0 b121 (by decide +kernel) (by decide +kernel)
theorem b3118:B 35 4 e2915:=viaPerm pc0_0 pci0_0 b3100 (by decide +kernel) (by decide +kernel)
theorem b3119:B 35 4 e2916:=viaPerm pc0_0 pci0_0 b3101 (by decide +kernel) (by decide +kernel)
theorem b3120:B 35 4 e2917:=viaPerm pc0_0 pci0_0 b3102 (by decide +kernel) (by decide +kernel)
theorem b3121:B 35 4 e2918:=viaPerm pc0_0 pci0_0 b3103 (by decide +kernel) (by decide +kernel)
theorem b3122:B 35 4 e2919:=viaPerm pc0_0 pci0_0 b171 (by decide +kernel) (by decide +kernel)
theorem b3123:B 35 4 e2920:=viaPerm pc0_0 pci0_0 b3112 (by decide +kernel) (by decide +kernel)
theorem b3124:B 35 4 e2921:=viaPerm pc0_0 pci0_0 b173 (by decide +kernel) (by decide +kernel)
theorem b3125:B 35 4 e2922:=viaPerm pc0_0 pci0_0 b3113 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3126:B 35 5 e2923:=viaBranch (ws:=[e645,e112,e646,e113,e2889,e2890,e2891,e2892,e2893,e2894,e2895,e2896,e2897,e2898,e2852,e2899,e2900,e2855,e2901,e2902,e2903,e2904,e2905,e2906,e2907,e2908,e156,e2866,e2909,e2868,e158,e2910,e2911,e2912,e2913,e2914,e2915,e2916,e2877,e2917,e2918,e2880,e2919,e2882,e2920,e2884,e2921,e2922]) (consBan b694 (consBan b120 (consBan b695 (consBan b121 (consBan b3092 (consBan b3093 (consBan b3094 (consBan b3095 (consBan b3096 (consBan b3097 (consBan b3098 (consBan b3099 (consBan b3100 (consBan b3101 (consBan b3054 (consBan b3102 (consBan b3103 (consBan b3057 (consBan b3104 (consBan b3105 (consBan b3106 (consBan b3107 (consBan b3108 (consBan b3109 (consBan b3110 (consBan b3111 (consBan b171 (consBan b3068 (consBan b3112 (consBan b3070 (consBan b173 (consBan b3113 (consBan b3114 (consBan b3115 (consBan b3116 (consBan b3117 (consBan b3118 (consBan b3119 (consBan b3079 (consBan b3120 (consBan b3121 (consBan b3082 (consBan b3122 (consBan b3084 (consBan b3123 (consBan b3086 (consBan b3124 (consBan b3125 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3127:B 35 4 e2924:=viaSmall (by decide +kernel) (by decide)
theorem b3128:B 35 4 e2925:=viaSmall (by decide +kernel) (by decide)
theorem b3129:B 35 4 e2926:=viaSmall (by decide +kernel) (by decide)
theorem b3130:B 35 4 e2927:=viaPerm pc0_0 pci0_0 b3127 (by decide +kernel) (by decide +kernel)
theorem b3131:B 35 4 e2928:=viaSmall (by decide +kernel) (by decide)
theorem b3132:B 35 4 e2929:=viaSmall (by decide +kernel) (by decide)
theorem b3133:B 35 4 e2930:=viaPerm pc0_0 pci0_0 b3128 (by decide +kernel) (by decide +kernel)
theorem b3134:B 35 4 e2931:=viaPerm pc0_0 pci0_0 b3129 (by decide +kernel) (by decide +kernel)
theorem b3135:B 35 4 e2932:=viaPerm pc0_0 pci0_0 b3131 (by decide +kernel) (by decide +kernel)
theorem b3136:B 35 4 e2933:=viaPerm pc0_0 pci0_0 b3132 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3137:B 35 5 e2934:=viaBranch (ws:=[e2924,e2925,e2854,e2926,e2900,e2927,e2865,e2928,e156,e2929,e2930,e2879,e2931,e2918,e2881,e2932,e2919,e2933,e862]) (consBan b3127 (consBan b3128 (consBan b3056 (consBan b3129 (consBan b3103 (consBan b3130 (consBan b3067 (consBan b3131 (consBan b171 (consBan b3132 (consBan b3133 (consBan b3081 (consBan b3134 (consBan b3121 (consBan b3083 (consBan b3135 (consBan b3122 (consBan b3136 (consBan b3008 (nilBan _ _)))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w3138:W 35 5 e2934:=viaSub (ws:=[e2836,e2923,e2887,e2934]) (consBan b3038 (consBan b3126 (consBan b3089 (consBan b3137 (nilBan _ _))))) (by decide) (by decide +kernel)
theorem b3139:B 87 6 e2935:=viaCut pjt_0 w3138 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3140:B 87 6 e2936:=viaCut pjt_16 w856 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3141:B 87 6 e2937:=viaPerm pt0 pti0 b1704 (by decide +kernel) (by decide +kernel)
theorem b3142:B 87 6 e2938:=viaPerm pt0 pti0 b1975 (by decide +kernel) (by decide +kernel)
theorem b3143:B 87 6 e2939:=viaPerm pt1 pti1 b1721 (by decide +kernel) (by decide +kernel)
theorem b3144:B 87 6 e2940:=viaPerm pt2 pti2 b1920 (by decide +kernel) (by decide +kernel)
theorem b3145:B 87 6 e2941:=viaPerm pt1 pti1 b1985 (by decide +kernel) (by decide +kernel)
theorem b3146:B 87 6 e2942:=viaPerm pt2 pti2 b2015 (by decide +kernel) (by decide +kernel)
theorem b3147:B 87 6 e2943:=viaPerm pt1 pti1 b2191 (by decide +kernel) (by decide +kernel)
theorem b3148:B 87 6 e2944:=viaPerm pt1 pti1 b2462 (by decide +kernel) (by decide +kernel)
theorem b3149:B 87 6 e2945:=viaPerm pt0 pti0 b2267 (by decide +kernel) (by decide +kernel)
theorem b3150:B 87 6 e2946:=viaPerm pt0 pti0 b2450 (by decide +kernel) (by decide +kernel)
theorem b3151:B 20 4 e2947:=viaSmall (by decide +kernel) (by decide)
theorem w3152:W 20 4 e2947:=widen (by decide +kernel) b3151
theorem b3153:B 87 6 e2948:=viaCut pjt_6 w3152 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3154:B 87 6 e2949:=viaPerm pt0 pti0 b3153 (by decide +kernel) (by decide +kernel)
theorem b3155:B 87 6 e2950:=viaPerm pt2 pti2 b2331 (by decide +kernel) (by decide +kernel)
theorem b3156:B 87 6 e2951:=viaPerm pt2 pti2 b2494 (by decide +kernel) (by decide +kernel)
theorem b3157:B 6 1 e102:=viaSmall (by decide +kernel) (by decide)
theorem w3158:W 6 1 e102:=widen (by decide +kernel) b3157
theorem b3159:B 87 6 e2952:=viaCut pjt_33 w3158 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3160:B 87 6 e2953:=viaCut pjt_33 w3158 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3161:B 87 6 e2954:=viaPerm pt0 pti0 b337 (by decide +kernel) (by decide +kernel)
theorem b3162:B 87 6 e2955:=viaPerm pt0 pti0 b1101 (by decide +kernel) (by decide +kernel)
theorem b3163:B 87 6 e2956:=viaPerm pt0 pti0 b1279 (by decide +kernel) (by decide +kernel)
theorem b3164:B 87 6 e2957:=viaPerm pt0 pti0 b1406 (by decide +kernel) (by decide +kernel)
theorem b3165:B 87 6 e2958:=viaPerm pt0 pti0 b3143 (by decide +kernel) (by decide +kernel)
theorem b3166:B 87 6 e2959:=viaPerm pt0 pti0 b3144 (by decide +kernel) (by decide +kernel)
theorem b3167:B 87 6 e2960:=viaPerm pt0 pti0 b3145 (by decide +kernel) (by decide +kernel)
theorem b3168:B 87 6 e2961:=viaPerm pt0 pti0 b3146 (by decide +kernel) (by decide +kernel)
theorem b3169:B 87 6 e2962:=viaPerm pt0 pti0 b3147 (by decide +kernel) (by decide +kernel)
theorem b3170:B 87 6 e2963:=viaPerm pt0 pti0 b3148 (by decide +kernel) (by decide +kernel)
theorem b3171:B 87 6 e2964:=viaPerm pt0 pti0 b3155 (by decide +kernel) (by decide +kernel)
theorem b3172:B 87 6 e2965:=viaPerm pt0 pti0 b3156 (by decide +kernel) (by decide +kernel)
theorem b3173:B 87 6 e2966:=viaPerm pt0 pti0 b3159 (by decide +kernel) (by decide +kernel)
theorem b3174:B 87 6 e2967:=viaPerm pt0 pti0 b3160 (by decide +kernel) (by decide +kernel)
theorem b3175:B 87 6 e2968:=viaPerm pt2 pti2 b617 (by decide +kernel) (by decide +kernel)
theorem b3176:B 87 6 e2969:=viaPerm pt2 pti2 b908 (by decide +kernel) (by decide +kernel)
theorem b3177:B 87 6 e2970:=viaPerm pt2 pti2 b1321 (by decide +kernel) (by decide +kernel)
theorem b3178:B 87 6 e2971:=viaPerm pt2 pti2 b1472 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3179:B 87 7 e1363:=viaBranch (ws:=[e2735,e2736,e2737,e2359,e2739,e2740,e2741,e2742,e1366,e2743,e2801,e2802,e2803,e2888,e2935,e2936,e310,e1015,e1161,e1280,e1569,e2937,e1824,e2938,e2110,e2287,e2939,e2940,e2941,e2942,e2943,e2944,e2945,e2946,e2948,e2949,e2950,e2951,e2952,e2953,e2954,e2955,e2956,e2957,e2958,e2959,e2960,e2961,e2962,e2963,e2964,e2965,e2966,e2967,e2968,e2969,e2970,e2971]) (consBan b2928 (consBan b2929 (consBan b2930 (consBan b2527 (consBan b2933 (consBan b2934 (consBan b2935 (consBan b2936 (consBan b1495 (consBan b2937 (consBan b2996 (consBan b2997 (consBan b2998 (consBan b3091 (consBan b3139 (consBan b3140 (consBan b337 (consBan b1101 (consBan b1279 (consBan b1406 (consBan b1704 (consBan b3141 (consBan b1975 (consBan b3142 (consBan b2267 (consBan b2450 (consBan b3143 (consBan b3144 (consBan b3145 (consBan b3146 (consBan b3147 (consBan b3148 (consBan b3149 (consBan b3150 (consBan b3153 (consBan b3154 (consBan b3155 (consBan b3156 (consBan b3159 (consBan b3160 (consBan b3161 (consBan b3162 (consBan b3163 (consBan b3164 (consBan b3165 (consBan b3166 (consBan b3167 (consBan b3168 (consBan b3169 (consBan b3170 (consBan b3171 (consBan b3172 (consBan b3173 (consBan b3174 (consBan b3175 (consBan b3176 (consBan b3177 (consBan b3178 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3180:B 87 6 e2972:=viaPerm pt0 pti0 b1709 (by decide +kernel) (by decide +kernel)
theorem b3181:B 87 6 e2973:=viaPerm pt0 pti0 b1976 (by decide +kernel) (by decide +kernel)
theorem b3182:B 87 6 e2974:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3183:B 87 6 e2975:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3184:B 87 6 e2976:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3185:B 87 6 e2977:=viaPerm pt1 pti1 b1725 (by decide +kernel) (by decide +kernel)
theorem b3186:B 87 6 e2978:=viaPerm pt2 pti2 b1921 (by decide +kernel) (by decide +kernel)
theorem b3187:B 87 6 e2979:=viaPerm pt1 pti1 b1986 (by decide +kernel) (by decide +kernel)
theorem b3188:B 87 6 e2980:=viaPerm pt2 pti2 b2016 (by decide +kernel) (by decide +kernel)
theorem b3189:B 87 6 e2981:=viaPerm pt1 pti1 b2192 (by decide +kernel) (by decide +kernel)
theorem b3190:B 87 6 e2982:=viaPerm pt1 pti1 b2463 (by decide +kernel) (by decide +kernel)
theorem b3191:B 87 6 e2983:=viaPerm pt0 pti0 b2268 (by decide +kernel) (by decide +kernel)
theorem b3192:B 87 6 e2984:=viaPerm pt0 pti0 b2528 (by decide +kernel) (by decide +kernel)
theorem b3193:B 87 6 e2985:=viaCut pjt_12 w111 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3194:B 87 6 e2986:=viaPerm pt0 pti0 b3193 (by decide +kernel) (by decide +kernel)
theorem b3195:B 87 6 e2987:=viaPerm pt2 pti2 b2332 (by decide +kernel) (by decide +kernel)
theorem b3196:B 87 6 e2988:=viaPerm pt2 pti2 b2560 (by decide +kernel) (by decide +kernel)
theorem b3207:B 35 4 e2996:=viaSmall (by decide +kernel) (by decide)
theorem b3208:B 35 4 e2997:=viaSmall (by decide +kernel) (by decide)
theorem b3209:B 35 4 e2998:=viaPerm pc0_0 pci0_0 b1658 (by decide +kernel) (by decide +kernel)
theorem b3210:B 35 4 e2999:=viaPerm pc0_0 pci0_0 b1602 (by decide +kernel) (by decide +kernel)
theorem b3211:B 35 4 e3000:=viaSmall (by decide +kernel) (by decide)
theorem b3212:B 35 4 e3001:=viaSmall (by decide +kernel) (by decide)
theorem b3213:B 35 4 e3002:=viaSmall (by decide +kernel) (by decide)
theorem b3214:B 35 4 e3003:=viaSmall (by decide +kernel) (by decide)
theorem b3215:B 35 4 e3004:=viaSmall (by decide +kernel) (by decide)
theorem b3216:B 35 4 e3005:=viaSmall (by decide +kernel) (by decide)
theorem b3217:B 35 4 e3006:=viaSmall (by decide +kernel) (by decide)
theorem b3218:B 35 4 e3007:=viaSmall (by decide +kernel) (by decide)
theorem b3219:B 35 4 e3008:=viaSmall (by decide +kernel) (by decide)
theorem b3220:B 35 4 e3009:=viaSmall (by decide +kernel) (by decide)
theorem b3221:B 35 4 e3010:=viaSmall (by decide +kernel) (by decide)
theorem b3222:B 35 4 e3011:=viaSmall (by decide +kernel) (by decide)
theorem b3223:B 35 4 e3012:=viaSmall (by decide +kernel) (by decide)
theorem b3224:B 35 4 e3013:=viaSmall (by decide +kernel) (by decide)
theorem b3225:B 35 4 e3014:=viaSmall (by decide +kernel) (by decide)
theorem b3226:B 35 4 e3015:=viaSmall (by decide +kernel) (by decide)
theorem b3227:B 35 4 e3016:=viaSmall (by decide +kernel) (by decide)
theorem b3228:B 35 4 e3017:=viaSmall (by decide +kernel) (by decide)
theorem b3229:B 35 4 e3018:=viaSmall (by decide +kernel) (by decide)
theorem b3230:B 35 4 e3019:=viaSmall (by decide +kernel) (by decide)
theorem b3231:B 35 4 e3020:=viaSmall (by decide +kernel) (by decide)
theorem b3232:B 35 4 e3021:=viaSmall (by decide +kernel) (by decide)
theorem b3233:B 35 4 e3022:=viaSmall (by decide +kernel) (by decide)
theorem b3234:B 35 4 e3023:=viaSmall (by decide +kernel) (by decide)
theorem b3235:B 35 4 e3024:=viaSmall (by decide +kernel) (by decide)
theorem b3236:B 35 4 e3025:=viaSmall (by decide +kernel) (by decide)
theorem b3237:B 35 4 e3026:=viaSmall (by decide +kernel) (by decide)
theorem b3238:B 35 4 e3027:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3239:B 35 5 e2889:=viaBranch (ws:=[e2996,e2997,e1447,e2998,e1433,e2999,e191,e1253,e198,e3000,e3001,e3002,e3003,e3004,e3005,e3006,e3007,e2891,e3008,e3009,e3010,e3011,e3012,e3013,e3014,e3015,e3016,e3017,e3018,e3019,e3020,e3021,e3022,e3023,e3024,e3025,e3026,e3027]) (consBan b3207 (consBan b3208 (consBan b1632 (consBan b3209 (consBan b1564 (consBan b3210 (consBan b208 (consBan b1377 (consBan b215 (consBan b3211 (consBan b3212 (consBan b3213 (consBan b3214 (consBan b3215 (consBan b3216 (consBan b3217 (consBan b3218 (consBan b3094 (consBan b3219 (consBan b3220 (consBan b3221 (consBan b3222 (consBan b3223 (consBan b3224 (consBan b3225 (consBan b3226 (consBan b3227 (consBan b3228 (consBan b3229 (consBan b3230 (consBan b3231 (consBan b3232 (consBan b3233 (consBan b3234 (consBan b3235 (consBan b3236 (consBan b3237 (consBan b3238 (nilBan _ _))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3240:B 35 4 e3028:=viaSmall (by decide +kernel) (by decide)
theorem b3241:B 35 4 e3029:=viaPerm pc0_0 pci0_0 b1556 (by decide +kernel) (by decide +kernel)
theorem b3242:B 35 4 e3030:=viaSmall (by decide +kernel) (by decide)
theorem b3243:B 35 4 e3031:=viaSmall (by decide +kernel) (by decide)
theorem b3244:B 35 4 e3032:=viaSmall (by decide +kernel) (by decide)
theorem b3245:B 35 4 e3033:=viaSmall (by decide +kernel) (by decide)
theorem b3246:B 35 4 e3034:=viaSmall (by decide +kernel) (by decide)
theorem b3247:B 35 4 e3035:=viaSmall (by decide +kernel) (by decide)
theorem b3248:B 35 4 e3036:=viaSmall (by decide +kernel) (by decide)
theorem b3249:B 35 4 e3037:=viaSmall (by decide +kernel) (by decide)
theorem b3250:B 35 4 e3038:=viaSmall (by decide +kernel) (by decide)
theorem b3251:B 35 4 e3039:=viaSmall (by decide +kernel) (by decide)
theorem b3252:B 35 4 e3040:=viaSmall (by decide +kernel) (by decide)
theorem b3253:B 35 4 e3041:=viaSmall (by decide +kernel) (by decide)
theorem b3254:B 35 4 e3042:=viaSmall (by decide +kernel) (by decide)
theorem b3255:B 35 4 e3043:=viaSmall (by decide +kernel) (by decide)
theorem b3256:B 35 4 e3044:=viaSmall (by decide +kernel) (by decide)
theorem b3257:B 35 4 e3045:=viaSmall (by decide +kernel) (by decide)
theorem b3258:B 35 4 e3046:=viaSmall (by decide +kernel) (by decide)
theorem b3259:B 35 4 e3047:=viaSmall (by decide +kernel) (by decide)
theorem b3260:B 35 4 e3048:=viaSmall (by decide +kernel) (by decide)
theorem b3261:B 35 4 e3049:=viaSmall (by decide +kernel) (by decide)
theorem b3262:B 35 4 e3050:=viaSmall (by decide +kernel) (by decide)
theorem b3263:B 35 4 e3051:=viaSmall (by decide +kernel) (by decide)
theorem b3264:B 35 4 e3052:=viaSmall (by decide +kernel) (by decide)
theorem b3265:B 35 4 e3053:=viaSmall (by decide +kernel) (by decide)
theorem b3266:B 35 4 e3054:=viaSmall (by decide +kernel) (by decide)
theorem b3267:B 35 4 e3055:=viaSmall (by decide +kernel) (by decide)
theorem b3268:B 35 4 e3056:=viaSmall (by decide +kernel) (by decide)
theorem b3269:B 35 4 e3057:=viaSmall (by decide +kernel) (by decide)
theorem b3270:B 35 4 e3058:=viaSmall (by decide +kernel) (by decide)
theorem b3271:B 35 4 e3059:=viaSmall (by decide +kernel) (by decide)
theorem b3272:B 35 4 e3060:=viaSmall (by decide +kernel) (by decide)
theorem b3273:B 35 4 e3061:=viaSmall (by decide +kernel) (by decide)
theorem b3274:B 35 4 e3062:=viaSmall (by decide +kernel) (by decide)
theorem b3275:B 35 4 e3063:=viaSmall (by decide +kernel) (by decide)
theorem b3276:B 35 4 e3064:=viaSmall (by decide +kernel) (by decide)
theorem b3277:B 35 4 e3065:=viaSmall (by decide +kernel) (by decide)
theorem b3278:B 35 4 e3066:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3279:B 35 5 e3067:=viaBranch (ws:=[e3028,e1460,e3029,e3030,e3031,e3032,e3033,e3034,e3035,e3036,e3037,e3038,e3039,e3040,e3041,e3042,e3043,e3044,e3045,e3046,e3047,e3048,e3049,e3050,e3051,e3052,e3053,e3054,e3055,e3056,e3057,e3058,e3059,e3060,e3061,e3062,e3063,e3064,e3065,e3066]) (consBan b3240 (consBan b1591 (consBan b3241 (consBan b3242 (consBan b3243 (consBan b3244 (consBan b3245 (consBan b3246 (consBan b3247 (consBan b3248 (consBan b3249 (consBan b3250 (consBan b3251 (consBan b3252 (consBan b3253 (consBan b3254 (consBan b3255 (consBan b3256 (consBan b3257 (consBan b3258 (consBan b3259 (consBan b3260 (consBan b3261 (consBan b3262 (consBan b3263 (consBan b3264 (consBan b3265 (consBan b3266 (consBan b3267 (consBan b3268 (consBan b3269 (consBan b3270 (consBan b3271 (consBan b3272 (consBan b3273 (consBan b3274 (consBan b3275 (consBan b3276 (consBan b3277 (consBan b3278 (nilBan _ _))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3280:B 35 4 e3068:=viaSmall (by decide +kernel) (by decide)
theorem b3281:B 35 4 e3069:=viaSmall (by decide +kernel) (by decide)
theorem b3282:B 35 4 e3070:=viaSmall (by decide +kernel) (by decide)
theorem b3283:B 35 4 e3071:=viaSmall (by decide +kernel) (by decide)
theorem b3284:B 35 4 e3072:=viaSmall (by decide +kernel) (by decide)
theorem b3285:B 35 4 e3073:=viaSmall (by decide +kernel) (by decide)
theorem b3286:B 35 4 e3074:=viaSmall (by decide +kernel) (by decide)
theorem b3287:B 35 4 e3075:=viaPerm pc0_0 pci0_0 b1621 (by decide +kernel) (by decide +kernel)
theorem b3288:B 35 4 e3076:=viaSmall (by decide +kernel) (by decide)
theorem b3289:B 35 4 e3077:=viaSmall (by decide +kernel) (by decide)
theorem b3290:B 35 4 e3078:=viaSmall (by decide +kernel) (by decide)
theorem b3291:B 35 4 e3079:=viaSmall (by decide +kernel) (by decide)
theorem b3292:B 35 4 e3080:=viaSmall (by decide +kernel) (by decide)
theorem b3293:B 35 4 e3081:=viaSmall (by decide +kernel) (by decide)
theorem b3294:B 35 4 e3082:=viaSmall (by decide +kernel) (by decide)
theorem b3295:B 35 4 e3083:=viaSmall (by decide +kernel) (by decide)
theorem b3296:B 35 4 e3084:=viaSmall (by decide +kernel) (by decide)
theorem b3297:B 35 4 e3085:=viaPerm pc0_0 pci0_0 b227 (by decide +kernel) (by decide +kernel)
theorem b3298:B 35 4 e3086:=viaSmall (by decide +kernel) (by decide)
theorem b3299:B 35 4 e3087:=viaPerm pc0_0 pci0_0 b251 (by decide +kernel) (by decide +kernel)
theorem b3300:B 35 4 e3088:=viaSmall (by decide +kernel) (by decide)
theorem b3301:B 35 4 e3089:=viaSmall (by decide +kernel) (by decide)
theorem b3302:B 35 4 e3090:=viaSmall (by decide +kernel) (by decide)
theorem b3303:B 35 4 e3091:=viaSmall (by decide +kernel) (by decide)
theorem b3304:B 35 4 e3092:=viaSmall (by decide +kernel) (by decide)
theorem b3305:B 35 4 e3093:=viaSmall (by decide +kernel) (by decide)
theorem b3306:B 35 4 e3094:=viaSmall (by decide +kernel) (by decide)
theorem b3307:B 35 4 e3095:=viaSmall (by decide +kernel) (by decide)
theorem b3308:B 35 4 e3096:=viaSmall (by decide +kernel) (by decide)
theorem b3309:B 35 4 e3097:=viaSmall (by decide +kernel) (by decide)
theorem b3310:B 35 4 e3098:=viaSmall (by decide +kernel) (by decide)
theorem b3311:B 35 4 e3099:=viaSmall (by decide +kernel) (by decide)
theorem b3312:B 35 4 e3100:=viaPerm pc0_0 pci0_0 b410 (by decide +kernel) (by decide +kernel)
theorem b3313:B 35 4 e3101:=viaSmall (by decide +kernel) (by decide)
theorem b3314:B 35 4 e3102:=viaSmall (by decide +kernel) (by decide)
theorem b3315:B 35 4 e3103:=viaSmall (by decide +kernel) (by decide)
theorem b3316:B 35 4 e3104:=viaSmall (by decide +kernel) (by decide)
theorem b3317:B 35 4 e3105:=viaSmall (by decide +kernel) (by decide)
theorem b3318:B 35 4 e3106:=viaSmall (by decide +kernel) (by decide)
theorem b3319:B 35 4 e3107:=viaSmall (by decide +kernel) (by decide)
theorem b3320:B 35 4 e3108:=viaSmall (by decide +kernel) (by decide)
theorem b3321:B 35 4 e3109:=viaSmall (by decide +kernel) (by decide)
theorem b3322:B 35 4 e3110:=viaSmall (by decide +kernel) (by decide)
theorem b3323:B 35 4 e3111:=viaSmall (by decide +kernel) (by decide)
theorem b3324:B 35 4 e3112:=viaSmall (by decide +kernel) (by decide)
theorem b3325:B 35 4 e3113:=viaSmall (by decide +kernel) (by decide)
theorem b3326:B 35 4 e3114:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3327:B 35 5 e3115:=viaBranch (ws:=[e3068,e3069,e3070,e3071,e3072,e3073,e3074,e1487,e3075,e3076,e3077,e3078,e3079,e3080,e3081,e3082,e3083,e3084,e3085,e3086,e3087,e3088,e3089,e3090,e3091,e3092,e3093,e3094,e3095,e3062,e3024,e3063,e3064,e3096,e3097,e3098,e3099,e3100,e3101,e3102,e3103,e3104,e3105,e3106,e3107,e3108,e3109,e3110,e3111,e3112,e3113,e3114,e3027]) (consBan b3280 (consBan b3281 (consBan b3282 (consBan b3283 (consBan b3284 (consBan b3285 (consBan b3286 (consBan b1618 (consBan b3287 (consBan b3288 (consBan b3289 (consBan b3290 (consBan b3291 (consBan b3292 (consBan b3293 (consBan b3294 (consBan b3295 (consBan b3296 (consBan b3297 (consBan b3298 (consBan b3299 (consBan b3300 (consBan b3301 (consBan b3302 (consBan b3303 (consBan b3304 (consBan b3305 (consBan b3306 (consBan b3307 (consBan b3274 (consBan b3235 (consBan b3275 (consBan b3276 (consBan b3308 (consBan b3309 (consBan b3310 (consBan b3311 (consBan b3312 (consBan b3313 (consBan b3314 (consBan b3315 (consBan b3316 (consBan b3317 (consBan b3318 (consBan b3319 (consBan b3320 (consBan b3321 (consBan b3322 (consBan b3323 (consBan b3324 (consBan b3325 (consBan b3326 (consBan b3238 (nilBan _ _)))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3328:B 35 4 e3116:=viaPerm pc0_0 pci0_0 b1557 (by decide +kernel) (by decide +kernel)
theorem b3329:B 35 4 e3117:=viaSmall (by decide +kernel) (by decide)
theorem b3330:B 35 4 e3118:=viaSmall (by decide +kernel) (by decide)
theorem b3331:B 35 4 e3119:=viaSmall (by decide +kernel) (by decide)
theorem b3332:B 35 4 e3120:=viaSmall (by decide +kernel) (by decide)
theorem b3333:B 35 4 e3121:=viaSmall (by decide +kernel) (by decide)
theorem b3334:B 35 4 e3122:=viaSmall (by decide +kernel) (by decide)
theorem b3335:B 35 4 e3123:=viaSmall (by decide +kernel) (by decide)
theorem b3336:B 35 4 e3124:=viaSmall (by decide +kernel) (by decide)
theorem b3337:B 35 4 e3125:=viaSmall (by decide +kernel) (by decide)
theorem b3338:B 35 4 e3126:=viaSmall (by decide +kernel) (by decide)
theorem b3339:B 35 4 e3127:=viaSmall (by decide +kernel) (by decide)
theorem b3340:B 35 4 e3128:=viaSmall (by decide +kernel) (by decide)
theorem b3341:B 35 4 e3129:=viaSmall (by decide +kernel) (by decide)
theorem b3342:B 35 4 e3130:=viaSmall (by decide +kernel) (by decide)
theorem b3343:B 35 4 e3131:=viaSmall (by decide +kernel) (by decide)
theorem b3344:B 35 4 e3132:=viaSmall (by decide +kernel) (by decide)
theorem b3345:B 35 4 e3133:=viaSmall (by decide +kernel) (by decide)
theorem b3346:B 35 4 e3134:=viaSmall (by decide +kernel) (by decide)
theorem b3347:B 35 4 e3135:=viaSmall (by decide +kernel) (by decide)
theorem b3348:B 35 4 e3136:=viaSmall (by decide +kernel) (by decide)
theorem b3349:B 35 4 e3137:=viaSmall (by decide +kernel) (by decide)
theorem b3350:B 35 4 e3138:=viaSmall (by decide +kernel) (by decide)
theorem b3351:B 35 4 e3139:=viaSmall (by decide +kernel) (by decide)
theorem b3352:B 35 4 e3140:=viaSmall (by decide +kernel) (by decide)
theorem b3353:B 35 4 e3141:=viaSmall (by decide +kernel) (by decide)
theorem b3354:B 35 4 e3142:=viaSmall (by decide +kernel) (by decide)
theorem b3355:B 35 4 e3143:=viaSmall (by decide +kernel) (by decide)
theorem b3356:B 35 4 e3144:=viaSmall (by decide +kernel) (by decide)
theorem b3357:B 35 4 e3145:=viaSmall (by decide +kernel) (by decide)
theorem b3358:B 35 4 e3146:=viaSmall (by decide +kernel) (by decide)
theorem b3359:B 35 4 e3147:=viaSmall (by decide +kernel) (by decide)
theorem b3360:B 35 4 e3148:=viaSmall (by decide +kernel) (by decide)
theorem b3361:B 35 4 e3149:=viaPerm pc0_0 pci0_0 b3223 (by decide +kernel) (by decide +kernel)
theorem b3362:B 35 4 e3150:=viaSmall (by decide +kernel) (by decide)
theorem b3363:B 35 4 e3151:=viaPerm pc0_0 pci0_0 b3224 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3364:B 35 5 e3152:=viaBranch (ws:=[e1461,e3116,e3117,e3118,e3119,e3120,e3121,e3122,e3123,e3124,e3125,e3126,e3127,e3128,e3129,e3130,e3131,e3132,e3133,e3134,e3135,e3136,e3137,e3138,e3139,e3140,e3141,e3142,e3062,e3143,e3065,e3144,e3066,e3145,e3146,e3147,e3148,e3149,e3150,e3151]) (consBan b1592 (consBan b3328 (consBan b3329 (consBan b3330 (consBan b3331 (consBan b3332 (consBan b3333 (consBan b3334 (consBan b3335 (consBan b3336 (consBan b3337 (consBan b3338 (consBan b3339 (consBan b3340 (consBan b3341 (consBan b3342 (consBan b3343 (consBan b3344 (consBan b3345 (consBan b3346 (consBan b3347 (consBan b3348 (consBan b3349 (consBan b3350 (consBan b3351 (consBan b3352 (consBan b3353 (consBan b3354 (consBan b3274 (consBan b3355 (consBan b3277 (consBan b3356 (consBan b3278 (consBan b3357 (consBan b3358 (consBan b3359 (consBan b3360 (consBan b3361 (consBan b3362 (consBan b3363 (nilBan _ _))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3365:B 35 4 e3153:=viaSmall (by decide +kernel) (by decide)
theorem b3366:B 35 4 e3154:=viaSmall (by decide +kernel) (by decide)
theorem b3367:B 35 4 e3155:=viaSmall (by decide +kernel) (by decide)
theorem b3368:B 35 4 e3156:=viaSmall (by decide +kernel) (by decide)
theorem b3369:B 35 4 e3157:=viaPerm pc0_0 pci0_0 b228 (by decide +kernel) (by decide +kernel)
theorem b3370:B 35 4 e3158:=viaSmall (by decide +kernel) (by decide)
theorem b3371:B 35 4 e3159:=viaSmall (by decide +kernel) (by decide)
theorem b3372:B 35 4 e3160:=viaSmall (by decide +kernel) (by decide)
theorem b3373:B 35 4 e3161:=viaSmall (by decide +kernel) (by decide)
theorem b3374:B 35 4 e3162:=viaSmall (by decide +kernel) (by decide)
theorem b3375:B 35 4 e3163:=viaSmall (by decide +kernel) (by decide)
theorem b3376:B 35 4 e3164:=viaPerm pc0_0 pci0_0 b411 (by decide +kernel) (by decide +kernel)
theorem b3377:B 35 4 e3165:=viaSmall (by decide +kernel) (by decide)
theorem b3378:B 35 4 e3166:=viaSmall (by decide +kernel) (by decide)
theorem b3379:B 35 4 e3167:=viaSmall (by decide +kernel) (by decide)
theorem b3380:B 35 4 e3168:=viaSmall (by decide +kernel) (by decide)
theorem b3381:B 35 4 e3169:=viaSmall (by decide +kernel) (by decide)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3382:B 35 5 e3170:=viaBranch (ws:=[e3153,e371,e3154,e3155,e3156,e3157,e3158,e3159,e3160,e3161,e3162,e3148,e3163,e3164,e3165,e3166,e3167,e3114,e3168,e3026,e3169]) (consBan b3365 (consBan b403 (consBan b3366 (consBan b3367 (consBan b3368 (consBan b3369 (consBan b3370 (consBan b3371 (consBan b3372 (consBan b3373 (consBan b3374 (consBan b3360 (consBan b3375 (consBan b3376 (consBan b3377 (consBan b3378 (consBan b3379 (consBan b3326 (consBan b3380 (consBan b3237 (consBan b3381 (nilBan _ _)))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w3383:W 35 5 e3170:=viaSub (ws:=[e890,e2889,e3067,e3115,e3152,e3170]) (consBan b967 (consBan b3239 (consBan b3279 (consBan b3327 (consBan b3364 (consBan b3382 (nilBan _ _))))))) (by decide) (by decide +kernel)
theorem b3384:B 87 6 e3171:=viaCut pjt_0 w3383 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3390:B 20 4 e3177:=viaSmall (by decide +kernel) (by decide)
theorem b3391:B 20 4 e3178:=viaSmall (by decide +kernel) (by decide)
theorem w3392:W 20 4 e3178:=viaSub (ws:=[e3177,e317,e3178]) (consBan b3390 (consBan b346 (consBan b3391 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b3393:B 87 6 e3179:=viaCut pjt_7 w3392 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3394:B 87 6 e3180:=viaPerm pt0 pti0 b339 (by decide +kernel) (by decide +kernel)
theorem b3395:B 87 6 e3181:=viaPerm pt0 pti0 b374 (by decide +kernel) (by decide +kernel)
theorem b3396:B 87 6 e3182:=viaPerm pt0 pti0 b1102 (by decide +kernel) (by decide +kernel)
theorem b3397:B 87 6 e3183:=viaPerm pt0 pti0 b1280 (by decide +kernel) (by decide +kernel)
theorem b3398:B 87 6 e3184:=viaPerm pt0 pti0 b1521 (by decide +kernel) (by decide +kernel)
theorem b3399:B 87 6 e3185:=viaPerm pt0 pti0 b3182 (by decide +kernel) (by decide +kernel)
theorem b3400:B 87 6 e3186:=viaPerm pt0 pti0 b1121 (by decide +kernel) (by decide +kernel)
theorem b3401:B 87 6 e3187:=viaPerm pt0 pti0 b3183 (by decide +kernel) (by decide +kernel)
theorem b3402:B 87 6 e3188:=viaPerm pt0 pti0 b3184 (by decide +kernel) (by decide +kernel)
theorem b3403:B 87 6 e3189:=viaPerm pt0 pti0 b3185 (by decide +kernel) (by decide +kernel)
theorem b3404:B 87 6 e3190:=viaPerm pt0 pti0 b3186 (by decide +kernel) (by decide +kernel)
theorem b3405:B 87 6 e3191:=viaPerm pt0 pti0 b3187 (by decide +kernel) (by decide +kernel)
theorem b3406:B 87 6 e3192:=viaPerm pt0 pti0 b3188 (by decide +kernel) (by decide +kernel)
theorem b3407:B 87 6 e3193:=viaPerm pt0 pti0 b3189 (by decide +kernel) (by decide +kernel)
theorem b3408:B 87 6 e3194:=viaPerm pt0 pti0 b3190 (by decide +kernel) (by decide +kernel)
theorem b3409:B 87 6 e3195:=viaPerm pt0 pti0 b3195 (by decide +kernel) (by decide +kernel)
theorem b3410:B 87 6 e3196:=viaPerm pt0 pti0 b3196 (by decide +kernel) (by decide +kernel)
theorem b3411:B 87 6 e3197:=viaPerm pt0 pti0 b3384 (by decide +kernel) (by decide +kernel)
theorem b3412:B 87 6 e3198:=viaPerm pt0 pti0 b3393 (by decide +kernel) (by decide +kernel)
theorem b3413:B 87 6 e3199:=viaCut pjt_18 w17 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3414:B 87 6 e3200:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3415:B 16 4 e2730:=viaSmall (by decide +kernel) (by decide)
theorem w3416:W 16 4 e2730:=widen (by decide +kernel) b3415
theorem b3417:B 87 6 e3201:=viaCut pjt_16 w3416 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3418:B 87 6 e3202:=viaPerm pt2 pti2 b2340 (by decide +kernel) (by decide +kernel)
theorem b3432:B 16 4 e3216:=viaSmall (by decide +kernel) (by decide)
theorem w3433:W 16 4 e3216:=widen (by decide +kernel) b3432
theorem b3434:B 87 6 e3217:=viaCut pjt_16 w3433 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3436:B 20 4 e3218:=viaSmall (by decide +kernel) (by decide)
theorem b3437:B 20 4 e3219:=viaSmall (by decide +kernel) (by decide)
theorem w3438:W 20 4 e3219:=viaSub (ws:=[e3218,e793,e3219]) (consBan b3436 (consBan b858 (consBan b3437 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b3439:B 87 6 e3220:=viaCut pjt_11 w3438 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3440:B 87 6 e3221:=viaCut pjt_16 w3433 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3441:B 87 6 e3222:=viaCut pjt_18 w784 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3442:B 87 6 e3223:=viaCut pjt_23 w969 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3443:B 87 6 e3224:=viaCut pjt_17 w907 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3444:B 6 1 e102:=viaSmall (by decide +kernel) (by decide)
theorem w3445:W 6 1 e102:=widen (by decide +kernel) b3444
theorem b3446:B 87 6 e3225:=viaCut pjt_23 w3445 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3447:B 12 3 e3226:=viaSmall (by decide +kernel) (by decide)
theorem w3448:W 12 3 e3226:=viaSub (ws:=[e16,e3226]) (consBan b16 (consBan b3447 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b3449:B 87 6 e3227:=viaCut pjt_18 w3448 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3450:B 87 6 e3228:=viaCut pjt_23 w969 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3451:B 12 3 e3229:=viaSmall (by decide +kernel) (by decide)
theorem b3452:B 12 3 e3230:=viaSmall (by decide +kernel) (by decide)
theorem w3453:W 12 3 e3230:=viaSub (ws:=[e3229,e16,e3230]) (consBan b3451 (consBan b16 (consBan b3452 (nilBan _ _)))) (by decide) (by decide +kernel)
theorem b3454:B 87 6 e3231:=viaCut pjt_18 w3453 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3455:B 87 6 e3232:=viaCut pjt_23 w3445 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3456:B 87 6 e3233:=viaCut pjt_17 w907 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3457:B 87 6 e3234:=viaPerm pt2 pti2 b674 (by decide +kernel) (by decide +kernel)
theorem b3458:B 87 6 e3235:=viaPerm pt2 pti2 b912 (by decide +kernel) (by decide +kernel)
theorem b3459:B 87 6 e3236:=viaPerm pt2 pti2 b1322 (by decide +kernel) (by decide +kernel)
theorem b3460:B 87 6 e3237:=viaPerm pt2 pti2 b1473 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3461:B 87 7 e3238:=viaBranch (ws:=[e311,e343,e1016,e1162,e1392,e1573,e2972,e1825,e2973,e2111,e2360,e2974,e1034,e2975,e2976,e2977,e2978,e2979,e2980,e2981,e2982,e2983,e2984,e2948,e2949,e2985,e2986,e1366,e2987,e2988,e3171,e3179,e3180,e3181,e3182,e3183,e3184,e3185,e3186,e3187,e3188,e3189,e3190,e3191,e3192,e3193,e3194,e2359,e3195,e3196,e3197,e3198,e3199,e3200,e3201,e3202,e3217,e3220,e3221,e3222,e3223,e3224,e3225,e3227,e3228,e3231,e3232,e3233,e3234,e3235,e3236,e3237]) (consBan b339 (consBan b374 (consBan b1102 (consBan b1280 (consBan b1521 (consBan b1709 (consBan b3180 (consBan b1976 (consBan b3181 (consBan b2268 (consBan b2528 (consBan b3182 (consBan b1121 (consBan b3183 (consBan b3184 (consBan b3185 (consBan b3186 (consBan b3187 (consBan b3188 (consBan b3189 (consBan b3190 (consBan b3191 (consBan b3192 (consBan b3153 (consBan b3154 (consBan b3193 (consBan b3194 (consBan b1495 (consBan b3195 (consBan b3196 (consBan b3384 (consBan b3393 (consBan b3394 (consBan b3395 (consBan b3396 (consBan b3397 (consBan b3398 (consBan b3399 (consBan b3400 (consBan b3401 (consBan b3402 (consBan b3403 (consBan b3404 (consBan b3405 (consBan b3406 (consBan b3407 (consBan b3408 (consBan b2527 (consBan b3409 (consBan b3410 (consBan b3411 (consBan b3412 (consBan b3413 (consBan b3414 (consBan b3417 (consBan b3418 (consBan b3434 (consBan b3439 (consBan b3440 (consBan b3441 (consBan b3442 (consBan b3443 (consBan b3446 (consBan b3449 (consBan b3450 (consBan b3454 (consBan b3455 (consBan b3456 (consBan b3457 (consBan b3458 (consBan b3459 (consBan b3460 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3711:B 20 4 e3462:=viaPerm pc6_0 pci6_0 b2926 (by decide +kernel) (by decide +kernel)
theorem w3712:W 20 4 e3462:=widen (by decide +kernel) b3711
theorem b3713:B 87 6 e3463:=viaCut pjt_6 w3712 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3714:B 87 6 e3464:=viaCut pjt_8 w290 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3715:B 87 6 e3465:=viaCut pjt_18 w862 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3716:B 87 6 e3466:=viaPerm pt0 pti0 b1711 (by decide +kernel) (by decide +kernel)
theorem b3717:B 87 6 e3467:=viaPerm pt0 pti0 b1978 (by decide +kernel) (by decide +kernel)
theorem b3718:B 87 6 e3468:=viaPerm pt1 pti1 b1728 (by decide +kernel) (by decide +kernel)
theorem b3719:B 87 6 e3469:=viaPerm pt2 pti2 b1922 (by decide +kernel) (by decide +kernel)
theorem b3720:B 87 6 e3470:=viaPerm pt1 pti1 b1987 (by decide +kernel) (by decide +kernel)
theorem b3721:B 87 6 e3471:=viaPerm pt2 pti2 b2017 (by decide +kernel) (by decide +kernel)
theorem b3722:B 87 6 e3472:=viaPerm pt1 pti1 b2193 (by decide +kernel) (by decide +kernel)
theorem b3723:B 87 6 e3473:=viaPerm pt1 pti1 b2464 (by decide +kernel) (by decide +kernel)
theorem b3724:B 87 6 e3474:=viaCut pjt_18 w862 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3725:B 87 6 e3475:=viaPerm pt0 pti0 b1123 (by decide +kernel) (by decide +kernel)
theorem b3726:B 87 6 e3238:=viaCut pjt_7 w860 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3727:B 87 6 e3476:=viaCut pjt_18 w862 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3728:B 87 6 e3477:=viaPerm pt2 pti2 b2556 (by decide +kernel) (by decide +kernel)
theorem b3729:B 12 3 e3478:=viaSmall (by decide +kernel) (by decide)
theorem w3730:W 12 3 e3478:=viaSub (ws:=[e16,e3478]) (consBan b16 (consBan b3729 (nilBan _ _))) (by decide) (by decide +kernel)
theorem b3731:B 87 6 e3479:=viaCut pjt_18 w3730 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3732:B 87 6 e3480:=viaPerm pt3 pti3 b3456 (by decide +kernel) (by decide +kernel)
theorem b3733:B 87 6 e3481:=viaPerm pt0 pti0 b2270 (by decide +kernel) (by decide +kernel)
theorem b3734:B 87 6 e3482:=viaPerm pt0 pti0 b2529 (by decide +kernel) (by decide +kernel)
theorem b3735:B 12 3 e3483:=viaSmall (by decide +kernel) (by decide)
theorem w3736:W 12 3 e3483:=widen (by decide +kernel) b3735
theorem b3737:B 87 6 e3484:=viaCut pjt_18 w3736 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3738:B 87 6 e3485:=viaPerm pt0 pti0 b3737 (by decide +kernel) (by decide +kernel)
theorem b3739:B 87 6 e3486:=viaPerm pt2 pti2 b2333 (by decide +kernel) (by decide +kernel)
theorem b3740:B 87 6 e3487:=viaPerm pt2 pti2 b2561 (by decide +kernel) (by decide +kernel)
theorem b3741:B 87 6 e3488:=viaPerm pt1 pti1 b3393 (by decide +kernel) (by decide +kernel)
theorem b3742:B 12 3 e3489:=viaSmall (by decide +kernel) (by decide)
theorem w3743:W 12 3 e3489:=widen (by decide +kernel) b3742
theorem b3744:B 87 6 e3490:=viaCut pjt_18 w3743 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3745:B 87 6 e3491:=viaPerm pt0 pti0 b378 (by decide +kernel) (by decide +kernel)
theorem b3746:B 87 6 e3492:=viaPerm pt0 pti0 b1104 (by decide +kernel) (by decide +kernel)
theorem b3747:B 87 6 e3493:=viaPerm pt0 pti0 b1282 (by decide +kernel) (by decide +kernel)
theorem b3748:B 87 6 e3494:=viaPerm pt0 pti0 b1409 (by decide +kernel) (by decide +kernel)
theorem b3749:B 87 6 e3495:=viaPerm pt3 pti3 b1731 (by decide +kernel) (by decide +kernel)
theorem b3750:B 87 6 e3496:=viaPerm pt4 pti4 b1925 (by decide +kernel) (by decide +kernel)
theorem b3751:B 87 6 e3497:=viaPerm pt3 pti3 b1988 (by decide +kernel) (by decide +kernel)
theorem b3752:B 87 6 e3498:=viaPerm pt4 pti4 b2018 (by decide +kernel) (by decide +kernel)
theorem b3753:B 87 6 e3499:=viaPerm pt3 pti3 b2194 (by decide +kernel) (by decide +kernel)
theorem b3754:B 87 6 e3500:=viaPerm pt3 pti3 b2465 (by decide +kernel) (by decide +kernel)
theorem b3755:B 87 6 e3501:=viaPerm pt4 pti4 b2334 (by decide +kernel) (by decide +kernel)
theorem b3756:B 87 6 e3502:=viaPerm pt4 pti4 b2497 (by decide +kernel) (by decide +kernel)
theorem b3757:B 87 6 e3503:=viaPerm pt3 pti3 b3160 (by decide +kernel) (by decide +kernel)
theorem b3758:B 6 1 e102:=viaSmall (by decide +kernel) (by decide)
theorem w3759:W 6 1 e102:=widen (by decide +kernel) b3758
theorem b3760:B 87 6 e3504:=viaCut pjt_29 w3759 (by decide) (by decide +kernel) (by decide +kernel)
theorem b3761:B 87 6 e3505:=viaPerm pt2 pti2 b675 (by decide +kernel) (by decide +kernel)
theorem b3762:B 87 6 e3506:=viaPerm pt2 pti2 b915 (by decide +kernel) (by decide +kernel)
theorem b3763:B 87 6 e3507:=viaPerm pt2 pti2 b1323 (by decide +kernel) (by decide +kernel)
theorem b3764:B 87 6 e3508:=viaPerm pt2 pti2 b1474 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3765:B 87 7 e2359:=viaBranch (ws:=[e17,e3463,e3464,e3465,e280,e1163,e1010,e1365,e344,e345,e1017,e1393,e1574,e3466,e1826,e3467,e2112,e2289,e3468,e3469,e3470,e3471,e3472,e3473,e1363,e2739,e1359,e3474,e3475,e1362,e3238,e2985,e1367,e3476,e3477,e1370,e1371,e3479,e3480,e1374,e3481,e3482,e3484,e3485,e3486,e3487,e3488,e3490,e3491,e3492,e3493,e3494,e3495,e3496,e3497,e3498,e3499,e3500,e3501,e3502,e3503,e3504,e3505,e3506,e3507,e3508]) (consBan b1486 (consBan b3713 (consBan b3714 (consBan b3715 (consBan b304 (consBan b1281 (consBan b1096 (consBan b1494 (consBan b376 (consBan b377 (consBan b1103 (consBan b1522 (consBan b1710 (consBan b3716 (consBan b1977 (consBan b3717 (consBan b2269 (consBan b2452 (consBan b3718 (consBan b3719 (consBan b3720 (consBan b3721 (consBan b3722 (consBan b3723 (consBan b1492 (consBan b2933 (consBan b1488 (consBan b3724 (consBan b3725 (consBan b1491 (consBan b3726 (consBan b3193 (consBan b1496 (consBan b3727 (consBan b3728 (consBan b1499 (consBan b1500 (consBan b3731 (consBan b3732 (consBan b1503 (consBan b3733 (consBan b3734 (consBan b3737 (consBan b3738 (consBan b3739 (consBan b3740 (consBan b3741 (consBan b3744 (consBan b3745 (consBan b3746 (consBan b3747 (consBan b3748 (consBan b3749 (consBan b3750 (consBan b3751 (consBan b3752 (consBan b3753 (consBan b3754 (consBan b3755 (consBan b3756 (consBan b3757 (consBan b3760 (consBan b3761 (consBan b3762 (consBan b3763 (consBan b3764 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b3766:B 87 7 e1366:=viaPerm pt0 pti0 b3765 (by decide +kernel) (by decide +kernel)
theorem b3767:B 87 7 e1367:=viaPerm pt1 pti1 b2581 (by decide +kernel) (by decide +kernel)
theorem b3768:B 87 7 e3509:=viaPerm pt1 pti1 b2582 (by decide +kernel) (by decide +kernel)
theorem b3769:B 87 7 e3510:=viaPerm pt1 pti1 b2583 (by decide +kernel) (by decide +kernel)
theorem b3770:B 87 7 e3511:=viaPerm pt1 pti1 b2584 (by decide +kernel) (by decide +kernel)
theorem b3771:B 87 7 e3512:=viaPerm pt1 pti1 b2585 (by decide +kernel) (by decide +kernel)
theorem b3772:B 87 7 e1370:=viaPerm pt1 pti1 b2586 (by decide +kernel) (by decide +kernel)
theorem b3773:B 87 7 e1371:=viaPerm pt1 pti1 b3179 (by decide +kernel) (by decide +kernel)
theorem b3774:B 87 7 e3513:=viaPerm pt1 pti1 b3461 (by decide +kernel) (by decide +kernel)
theorem b3775:B 87 7 e3514:=viaPerm pt1 pti1 b3765 (by decide +kernel) (by decide +kernel)
theorem b3776:B 87 7 e1374:=viaPerm pt1 pti1 b3766 (by decide +kernel) (by decide +kernel)
theorem b3777:B 87 7 e2364:=viaPerm pt0 pti0 b18 (by decide +kernel) (by decide +kernel)
theorem b3778:B 87 7 e3515:=viaPerm pt0 pti0 b685 (by decide +kernel) (by decide +kernel)
theorem b3779:B 87 7 e3516:=viaPerm pt0 pti0 b925 (by decide +kernel) (by decide +kernel)
theorem b3780:B 87 7 e3517:=viaPerm pt0 pti0 b1148 (by decide +kernel) (by decide +kernel)
theorem b3781:B 87 7 e2368:=viaPerm pt0 pti0 b1333 (by decide +kernel) (by decide +kernel)
theorem b3782:B 87 7 e2370:=viaPerm pt0 pti0 b1334 (by decide +kernel) (by decide +kernel)
theorem b3783:B 87 7 e3518:=viaPerm pt0 pti0 b1484 (by decide +kernel) (by decide +kernel)
theorem b3784:B 87 7 e3519:=viaPerm pt0 pti0 b1543 (by decide +kernel) (by decide +kernel)
theorem b3785:B 87 7 e3520:=viaPerm pt0 pti0 b2567 (by decide +kernel) (by decide +kernel)
theorem b3786:B 87 7 e3521:=viaPerm pt0 pti0 b2568 (by decide +kernel) (by decide +kernel)
theorem b3787:B 87 7 e3522:=viaPerm pt0 pti0 b2569 (by decide +kernel) (by decide +kernel)
theorem b3788:B 87 7 e3523:=viaPerm pt0 pti0 b2570 (by decide +kernel) (by decide +kernel)
theorem b3789:B 87 7 e3524:=viaPerm pt0 pti0 b2571 (by decide +kernel) (by decide +kernel)
theorem b3790:B 87 7 e3525:=viaPerm pt0 pti0 b2572 (by decide +kernel) (by decide +kernel)
theorem b3791:B 87 7 e3526:=viaPerm pt0 pti0 b2573 (by decide +kernel) (by decide +kernel)
theorem b3792:B 87 7 e3527:=viaPerm pt0 pti0 b2574 (by decide +kernel) (by decide +kernel)
theorem b3793:B 87 7 e3528:=viaPerm pt0 pti0 b2575 (by decide +kernel) (by decide +kernel)
theorem b3794:B 87 7 e3529:=viaPerm pt0 pti0 b2576 (by decide +kernel) (by decide +kernel)
theorem b3795:B 87 7 e3530:=viaPerm pt0 pti0 b2577 (by decide +kernel) (by decide +kernel)
theorem b3796:B 87 7 e3531:=viaPerm pt0 pti0 b2578 (by decide +kernel) (by decide +kernel)
theorem b3797:B 87 7 e3532:=viaPerm pt0 pti0 b2579 (by decide +kernel) (by decide +kernel)
theorem b3798:B 87 7 e3533:=viaPerm pt0 pti0 b2580 (by decide +kernel) (by decide +kernel)
theorem b3799:B 87 7 e2381:=viaPerm pt0 pti0 b3767 (by decide +kernel) (by decide +kernel)
theorem b3800:B 87 7 e3534:=viaPerm pt0 pti0 b3768 (by decide +kernel) (by decide +kernel)
theorem b3801:B 87 7 e3535:=viaPerm pt0 pti0 b3769 (by decide +kernel) (by decide +kernel)
theorem b3802:B 87 7 e3536:=viaPerm pt0 pti0 b3770 (by decide +kernel) (by decide +kernel)
theorem b3803:B 87 7 e3537:=viaPerm pt0 pti0 b3771 (by decide +kernel) (by decide +kernel)
theorem b3804:B 87 7 e2384:=viaPerm pt0 pti0 b3772 (by decide +kernel) (by decide +kernel)
theorem b3805:B 87 7 e2385:=viaPerm pt0 pti0 b3773 (by decide +kernel) (by decide +kernel)
theorem b3806:B 87 7 e3538:=viaPerm pt0 pti0 b3774 (by decide +kernel) (by decide +kernel)
theorem b3807:B 87 7 e3539:=viaPerm pt0 pti0 b3775 (by decide +kernel) (by decide +kernel)
theorem b3808:B 87 7 e2388:=viaPerm pt0 pti0 b3776 (by decide +kernel) (by decide +kernel)
theorem b3809:B 87 7 e3540:=viaPerm pt1 pti1 b3777 (by decide +kernel) (by decide +kernel)
theorem b3810:B 87 7 e3541:=viaPerm pt1 pti1 b3778 (by decide +kernel) (by decide +kernel)
theorem b3811:B 87 7 e3542:=viaPerm pt1 pti1 b3779 (by decide +kernel) (by decide +kernel)
theorem b3812:B 87 7 e3543:=viaPerm pt1 pti1 b3780 (by decide +kernel) (by decide +kernel)
theorem b3813:B 87 7 e3544:=viaPerm pt1 pti1 b3781 (by decide +kernel) (by decide +kernel)
theorem b3814:B 87 7 e3545:=viaPerm pt1 pti1 b3782 (by decide +kernel) (by decide +kernel)
theorem b3815:B 87 7 e3546:=viaPerm pt1 pti1 b3783 (by decide +kernel) (by decide +kernel)
theorem b3816:B 87 7 e3547:=viaPerm pt1 pti1 b3784 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b3817:B 87 8 e3548:=viaBranch (ws:=[e17,e636,e697,e1061,e280,e1010,e698,e944,e1414,e1785,e1786,e1787,e1591,e1876,e1877,e1878,e1879,e2076,e2189,e2168,e1895,e2086,e2397,e2398,e2399,e2400,e2401,e2402,e2403,e2404,e2405,e2406,e2407,e2408,e2409,e2410,e1359,e2411,e2412,e2413,e2414,e1362,e1363,e3238,e2359,e1366,e1367,e3509,e3510,e3511,e3512,e1370,e1371,e3513,e3514,e1374,e2364,e3515,e3516,e3517,e2368,e2370,e3518,e3519,e3520,e3521,e3522,e3523,e3524,e3525,e3526,e3527,e3528,e3529,e3530,e3531,e3532,e3533,e2381,e3534,e3535,e3536,e3537,e2384,e2385,e3538,e3539,e2388,e3540,e3541,e3542,e3543,e3544,e3545,e3546,e3547]) (consBan b18 (consBan b685 (consBan b925 (consBan b1148 (consBan b1333 (consBan b1334 (consBan b1484 (consBan b1543 (consBan b1544 (consBan b1934 (consBan b1935 (consBan b1936 (consBan b2027 (consBan b2028 (consBan b2029 (consBan b2030 (consBan b2031 (consBan b2233 (consBan b2347 (consBan b2348 (consBan b2506 (consBan b2566 (consBan b2567 (consBan b2568 (consBan b2569 (consBan b2570 (consBan b2571 (consBan b2572 (consBan b2573 (consBan b2574 (consBan b2575 (consBan b2576 (consBan b2577 (consBan b2578 (consBan b2579 (consBan b2580 (consBan b2581 (consBan b2582 (consBan b2583 (consBan b2584 (consBan b2585 (consBan b2586 (consBan b3179 (consBan b3461 (consBan b3765 (consBan b3766 (consBan b3767 (consBan b3768 (consBan b3769 (consBan b3770 (consBan b3771 (consBan b3772 (consBan b3773 (consBan b3774 (consBan b3775 (consBan b3776 (consBan b3777 (consBan b3778 (consBan b3779 (consBan b3780 (consBan b3781 (consBan b3782 (consBan b3783 (consBan b3784 (consBan b3785 (consBan b3786 (consBan b3787 (consBan b3788 (consBan b3789 (consBan b3790 (consBan b3791 (consBan b3792 (consBan b3793 (consBan b3794 (consBan b3795 (consBan b3796 (consBan b3797 (consBan b3798 (consBan b3799 (consBan b3800 (consBan b3801 (consBan b3802 (consBan b3803 (consBan b3804 (consBan b3805 (consBan b3806 (consBan b3807 (consBan b3808 (consBan b3809 (consBan b3810 (consBan b3811 (consBan b3812 (consBan b3813 (consBan b3814 (consBan b3815 (consBan b3816 (nilBan _ _))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem sixWide : Wide 87 8 e3548 := widen (by decide +kernel) b3817
def certRows : List Nat := [9,9,9,9,9,9,9,9,9,10,10,10,10,10,10,10,10,10,17,17,17,17,17,17,17,17,17,20,20,20,20,20,20,20,20,20,24,24,24,24,24,24,24,24,24,24,24,34,34,34,34,34,34,34,34,34,36,36,36,36,36,36,36,36,36,40,40,40,40,40,40,40,40,40,40,40,48,48,48,48,48,48,48,48,48,48,48,0,3,5,7,8,12,16,18,33,0,3,6,7,8,12,18,32,33,0,3,5,7,8,12,16,18,33,0,5,6,7,12,16,18,32,33,0,3,5,6,7,8,12,16,18,32,33,0,3,6,7,8,12,18,32,33,0,5,6,7,12,16,18,32,33,0,3,5,6,7,8,12,16,18,32,33,0,3,5,6,7,8,12,16,18,32,33]
def certEtat : List ℕ := e3548
def certM : Nat := 87
def certFuel : Nat := 8

end PEqualNP.Outside.L_meta_31665.ArchivedClique

namespace PEqualNP.Outside.L_meta_31665.Reduce
namespace CliqueCertificate
open PEqualNP.Outside.L_meta_31665.ArchivedClique
def rows : List Nat := certRows
def pack (w : BitVec 64) := actL rows (canon w).toNat
private def mix (s t : Bool) (a b : BitVec 64) : BitVec 64 :=
  if s then (if t then a ||| b else b ^^^ (a &&& b))
  else if t then a ^^^ (a &&& b) else a &&& b
private theorem mix_correct (x y : BitVec 64) :
    canon (x &&& y) = mix (x.getLsbD 0) (y.getLsbD 0) (canon x) (canon y) := by
  cases hx : x.getLsbD 0 <;> cases hy : y.getLsbD 0 <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    cases hp : x.getLsbD i <;> cases hq : y.getLsbD i <;>
    simp only [canon, mix, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor,
      BitVec.getLsbD_or, hx, hy, hp, hq, decide_eq_true hi, Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true] <;> rfl
private theorem pack_mix (s t : Bool) (a b : BitVec 64) :
    actL rows (mix s t a b).toNat = combine (opIndex s t) (actL rows a.toNat) (actL rows b.toNat) := by
  cases s <;> cases t <;> simp [mix, opIndex, combine, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_or, actL_and, actL_or, actL_xor]
private theorem canon_signed (s : Bool) (x : BitVec 64) : canon (signed s x) = canon x := by
  cases s; rfl; exact canon_not x
private theorem pack_gate (s t : Bool) (a b : BitVec 64) :
    ∃ d < 4, pack (gate s t a b) = combine d (pack a) (pack b) := by
  let x := signed s a; let y := signed t b
  refine ⟨opIndex (x.getLsbD 0) (y.getLsbD 0), op_lt _ _, ?_⟩
  change actL rows (canon (canon (x &&& y))).toNat = _
  rw [canon_canon, mix_correct, pack_mix]; simp [x, y, pack, canon_signed]
private theorem word_sep : Good certM (pack cliqueGoal) := by
  intro i hi
  have h : ∀ j : Fin certM, (pack cliqueGoal).testBit j.val ≠ (pack cliqueGoal).testBit (certM+j.val) := by decide +kernel
  exact h ⟨i,hi⟩
theorem possible {k S} (h : Path cliqueGoal k S) {av : List Nat}
    (carry : ∀ w∈S, pack w ∈ av) : Possible certM k av := by
  apply h (fun n T => ∀ av : List Nat, (∀ w∈T, pack w ∈ av) → Possible certM n av) ?_ ?_ av carry
  · intro v yes; refine ⟨0,{pack cliqueGoal},le_rfl,?_,?_⟩
    · exact PEqualNP.Outside.L_meta_31665.ArchivedClique.Live.done word_sep (by decide +kernel)
    · simpa using yes cliqueGoal (by simp)
  · intro k a b U s t _ _ _ ih v yes
    obtain ⟨d,hd,hop⟩ := pack_gate s t a b
    have future : Possible certM k (v ++ [combine d (pack a) (pack b)]) := by
      apply ih; intro w hw; rcases Finset.mem_insert.mp hw with rfl | old
      · simp [hop]
      · exact List.mem_append_left _ (yes w (by simp [old]))
    obtain ⟨n,T,le,live,mem⟩ := pullPaid hd (yes _ (by simp)) (yes _ (by simp)) future
    refine ⟨n,T,?_,live,mem⟩; cases h : charge v (combine d (pack a) (pack b)) <;> simp [h] at le <;> omega
theorem lower (k : Nat) (T : Finset (BitVec 64)) (raw : T ⊆ cliqueRaw.toFinset)
    (path : Path cliqueGoal k T) : 9 ≤ k := by
  by_contra! short
  have tick : ∀ w∈cliqueRaw, pack w ∈ certEtat := by simp [cliqueRaw]; decide +kernel
  obtain ⟨n,S,le,live,inc⟩ := possible path (fun w hw => tick w (List.mem_toFinset.mp (raw hw)))
  exact sixWide ⟨n,S,by omega,live,inc⟩
end CliqueCertificate
end PEqualNP.Outside.L_meta_31665.Reduce

theorem PEqualNP.Outside.L_meta_31665 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  apply PEqualNP.Outside.L_meta_31665.Frame.finish
  intro gs o legal computes hn
  obtain ⟨b,n,hlen,live⟩ := PEqualNP.Outside.L_meta_31665.freely_chain gs o legal computes hn
  obtain ⟨k,hk,T,sub,path⟩ := PEqualNP.Outside.L_meta_31665.Reduce.to_six live
  have low := PEqualNP.Outside.L_meta_31665.Reduce.CliqueCertificate.lower k T sub path
  omega
