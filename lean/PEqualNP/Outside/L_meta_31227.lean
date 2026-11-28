import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31227.Frame
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List ℕ := [0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7]
def target (x : Fin 8 → Bool) := decide (∃ i < edges.length / 2,
  (List.ofFn x).getD (edges.getD (2*i) 0) false = true ∧
  (List.ofFn x).getD (edges.getD (2*i+1) 0) false = true)

def witness : List Gate := [
  ⟨.or, [3, 7]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.and, [9, 10]⟩,
  ⟨.or, [1, 9]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.and, [0, 8]⟩,
  ⟨.or, [13, 14]⟩,
  ⟨.and, [4, 5]⟩,
  ⟨.or, [11, 15]⟩,
  ⟨.or, [12, 16]⟩,
  ⟨.or, [0, 18]⟩,
  ⟨.and, [17, 19]⟩]

theorem good : ∀ g ∈ witness, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

theorem correct : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness,20⟩ (List.ofFn x) = target x := by
  decide +kernel

theorem finish (lower : ∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,o⟩ →
    (∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) →
    (∃ g ∈ gs, g.op = .not) → 13 ≤ gs.length) : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o fan _ computes
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · exact ⟨witness, 20, good, lower gs o fan computes hn, correct⟩
  · refine ⟨gs, o, ?_, le_rfl, computes⟩
    intro g hg
    obtain ⟨op, len⟩ := fan g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),len⟩

end PEqualNP.Outside.L_meta_31227.Frame

namespace PEqualNP.Outside.L_meta_31227.Reduce
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
end PEqualNP.Outside.L_meta_31227.Reduce

namespace PEqualNP.Outside.L_meta_31227
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Word := BitVec 256
def ones : Word := BitVec.allOnes 256
def goal : Word := 0xfffffffffffffffffffefffefffefaa0fffffffffffefff0fffefffefffefaa0
def roots : List Word := [
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
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

def assignment (r : Fin 256) : Fin 8 → Bool := fun i => r.val.testBit (([6,0,1,7,2,3,4,5] : List Nat).get i)
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

def witnesses (i : Fin 8) : Fin 256 × Fin 256 := ([(4,68),(4,5),(16,18),(64,192),(1,5),(1,9),(1,17),(1,33)] : List (Fin 256 × Fin 256)).get i
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

end PEqualNP.Outside.L_meta_31227

namespace PEqualNP.Outside.L_meta_31227.Reduce
open PEqualNP.Outside.L_meta_31227

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
end PEqualNP.Outside.L_meta_31227.Reduce

namespace PEqualNP.Outside.L_meta_31227.Reduce
open PEqualNP.Outside.L_meta_31227

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
def cliqueGoal : BitVec 64 := 0xfffefffefffefaa0
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
  if e then ([(0,64),(4,5),(16,18),(1,5),(1,9),(1,17),(1,33)] : List _).get v
  else ([(4,68),(4,5),(16,18),(1,5),(1,9),(1,17),(1,33)] : List _).get v
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
end PEqualNP.Outside.L_meta_31227.Reduce

namespace PEqualNP.Outside.L_meta_31227.ArchivedClique
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
def pc13_0 : Projection 30 30 := pick [0,1,3,2,4,10,11,13,12,14,5,6,8,7,9,20,21,23,22,24,15,16,18,17,19,25,26,28,27,29] rfl (by decide +kernel) (by decide)
def pci13_0 : Projection 30 30 := pick [0,1,3,2,4,10,11,13,12,14,5,6,8,7,9,20,21,23,22,24,15,16,18,17,19,25,26,28,27,29] rfl (by decide +kernel) (by decide)
def pc13_1 : Projection 30 30 := pick [5,7,6,8,9,0,2,1,3,4,10,12,11,13,14,15,17,16,18,19,25,27,26,28,29,20,22,21,23,24] rfl (by decide +kernel) (by decide)
def pci13_1 : Projection 30 30 := pick [5,7,6,8,9,0,2,1,3,4,10,12,11,13,14,15,17,16,18,19,25,27,26,28,29,20,22,21,23,24] rfl (by decide +kernel) (by decide)
def pc13_10 : Projection 30 30 := pick [1,0,2,3,4,16,15,17,18,19,21,20,22,23,24,6,5,7,8,9,11,10,12,13,14,26,25,27,28,29] rfl (by decide +kernel) (by decide)
def pci13_10 : Projection 30 30 := pick [1,0,2,3,4,16,15,17,18,19,21,20,22,23,24,6,5,7,8,9,11,10,12,13,14,26,25,27,28,29] rfl (by decide +kernel) (by decide)
def pjt_13 : Projection 96 30 := pick [1,3,5,8,0,11,13,15,18,10,64,66,68,70,63,21,23,25,28,20,79,81,83,85,78,88,90,92,94,87] rfl (by decide +kernel) (by decide)
def pj13_23 : Projection 30 12 := pick [16,17,18,19,21,22,23,24,26,27,28,29] rfl (by decide +kernel) (by decide)
def f1 : ℕ := 0x1110ff
def f2 : ℕ := 0x222f0f
def f3 : ℕ := 0x444ff0
def f4 : ℕ := 0x1f
def f5 : ℕ := 0x84210840007fff
def f6 : ℕ := 0x108421081ff801f
def f7 : ℕ := 0x21084213e0f83e0
def f8 : ℕ := 0x42108423ff07c00
def f9 : ℕ := 0x18c6318c1ffffff
def f10 : ℕ := 0x84210840007fe0
def f11 : ℕ := 0x108421081ff8000
def f12 : ℕ := 0x294a5297e0fffff
def f13 : ℕ := 0x84210840007c1f
def f14 : ℕ := 0x4a5294a7ff07fff
def f15 : ℕ := 0x842108400003ff
def f16 : ℕ := 0x318c631bfff83ff
def f17 : ℕ := 0x108421081f0001f
def f18 : ℕ := 0x5294a52bffffc1f
def f19 : ℕ := 0x1084210800f801f
def f20 : ℕ := 0xf83e0
def f21 : ℕ := 0x39ce739ffffffff
def f22 : ℕ := 0x18c6318c1f07c1f
def f23 : ℕ := 0x21084213e000000
def f24 : ℕ := 0x1f07c00
def f25 : ℕ := 0x5ad6b5affffffff
def f26 : ℕ := 0x18c6318c00f83ff
def f27 : ℕ := 0x42108423e000000
def f28 : ℕ := 0x3e0
def f29 : ℕ := 0x21084213e0f8000
def f30 : ℕ := 0x7c00
def f31 : ℕ := 0x42108423ff00000
def f32 : ℕ := 0xf8000
def f33 : ℕ := 0x21084213e0003e0
def f34 : ℕ := 0x1f00000
def f35 : ℕ := 0x42108423e007c00
def f36 : ℕ := 0x3e000000
def f37 : ℕ := 0x6318c633fffffe0
def f38 : ℕ := 0x2108421000f83e0
def f39 : ℕ := 0x421084201f07c00
def f40 : ℕ := 0x30182030180c10180601806000000ff8000007fc00fffff
def f41 : ℕ := 0xc06040c0603020601806018007fc000003fe0003ff003ff
def f42 : ℕ := 0x2a150e2a150a87150541505400003f0000001f8000000000
def f43 : ℕ := 0x30180830180c041806018060ff8000007fc000003ffffc00
def f44 : ℕ := 0x8040208060301860280a0280000000007fffffffc0000000
def f45 : ℕ := 0xc06030c040201040300c0300ffffffff8000000000000000
def e1 : List ℕ := [f1,f2,f3]
def e2 : List ℕ := [f4,f5,f6,f7,f8]
def e3 : List ℕ := [f4,f9,f7,f8]
def e4 : List ℕ := [f4,f6,f9,f7,f8]
def e5 : List ℕ := [f4,f5,f9,f7,f8]
def e6 : List ℕ := [f10,f5,f9,f7,f8]
def e7 : List ℕ := [f11,f6,f9,f7,f8]
def e8 : List ℕ := [f5,f11,f6,f7,f8]
def e9 : List ℕ := [f6,f9,f7,f12,f8]
def e10 : List ℕ := [f13,f6,f9,f7,f8]
def e11 : List ℕ := [f6,f9,f7,f8,f14]
def e12 : List ℕ := [f15,f6,f9,f7,f8]
def e13 : List ℕ := [f10,f5,f6,f7,f8]
def e14 : List ℕ := [f5,f9,f7,f16,f8]
def e15 : List ℕ := [f5,f17,f9,f7,f8]
def e16 : List ℕ := [f5,f9,f7,f8,f18]
def e17 : List ℕ := [f5,f19,f9,f7,f8]
def e18 : List ℕ := [f20,f5,f6,f7,f8]
def e19 : List ℕ := [f5,f6,f7,f21,f8]
def e20 : List ℕ := [f5,f6,f22,f7,f8]
def e21 : List ℕ := [f5,f6,f23,f7,f8]
def e22 : List ℕ := [f24,f5,f6,f7,f8]
def e23 : List ℕ := [f5,f6,f7,f8,f25]
def e24 : List ℕ := [f5,f6,f26,f7,f8]
def e25 : List ℕ := [f5,f6,f7,f27,f8]
def e26 : List ℕ := [f5,f6,f9,f7,f8]
def e27 : List ℕ := [f28,f5,f6,f7,f8]
def e28 : List ℕ := [f5,f6,f7,f12,f8]
def e29 : List ℕ := [f13,f5,f6,f7,f8]
def e30 : List ℕ := [f5,f6,f29,f7,f8]
def e31 : List ℕ := [f30,f5,f6,f7,f8]
def e32 : List ℕ := [f5,f6,f7,f8,f14]
def e33 : List ℕ := [f15,f5,f6,f7,f8]
def e34 : List ℕ := [f5,f6,f7,f31,f8]
def e35 : List ℕ := [f32,f5,f6,f7,f8]
def e36 : List ℕ := [f5,f6,f7,f16,f8]
def e37 : List ℕ := [f5,f17,f6,f7,f8]
def e38 : List ℕ := [f5,f6,f33,f7,f8]
def e39 : List ℕ := [f34,f5,f6,f7,f8]
def e40 : List ℕ := [f5,f6,f7,f8,f18]
def e41 : List ℕ := [f5,f19,f6,f7,f8]
def e42 : List ℕ := [f5,f6,f7,f35,f8]
def e43 : List ℕ := [f36,f5,f6,f7,f8]
def e44 : List ℕ := [f5,f6,f7,f8,f37]
def e45 : List ℕ := [f5,f6,f38,f7,f8]
def e46 : List ℕ := [f5,f6,f7,f39,f8]
def e47 : List ℕ := [f5,f6,f7,f8]
def e48 : List ℕ := [f40,f41,f42,f43,f44,f45]
theorem b7:B 12 3 e1:=viaSmall (by decide +kernel) (by decide)
theorem w8:W 12 3 e1:=widen (by decide +kernel) b7
theorem b9:B 30 5 e2:=viaCut pj13_23 w8 (by decide) (by decide +kernel) (by decide +kernel)
theorem b10:B 30 4 e3:=viaSmall (by decide +kernel) (by decide)
theorem b11:B 30 4 e4:=viaSmall (by decide +kernel) (by decide)
theorem b12:B 30 4 e5:=viaPerm pc13_10 pci13_10 b11 (by decide +kernel) (by decide +kernel)
theorem b13:B 30 4 e6:=viaSmall (by decide +kernel) (by decide)
theorem b14:B 30 4 e7:=viaPerm pc13_10 pci13_10 b13 (by decide +kernel) (by decide +kernel)
theorem b15:B 30 4 e8:=viaSmall (by decide +kernel) (by decide)
theorem b16:B 30 4 e9:=viaSmall (by decide +kernel) (by decide)
theorem b17:B 30 4 e10:=viaSmall (by decide +kernel) (by decide)
theorem b18:B 30 4 e11:=viaPerm pc13_0 pci13_0 b16 (by decide +kernel) (by decide +kernel)
theorem b19:B 30 4 e12:=viaPerm pc13_0 pci13_0 b17 (by decide +kernel) (by decide +kernel)
theorem b20:B 30 4 e13:=viaPerm pc13_10 pci13_10 b15 (by decide +kernel) (by decide +kernel)
theorem b21:B 30 4 e14:=viaPerm pc13_10 pci13_10 b16 (by decide +kernel) (by decide +kernel)
theorem b22:B 30 4 e15:=viaPerm pc13_10 pci13_10 b17 (by decide +kernel) (by decide +kernel)
theorem b23:B 30 4 e16:=viaPerm pc13_0 pci13_0 b21 (by decide +kernel) (by decide +kernel)
theorem b24:B 30 4 e17:=viaPerm pc13_0 pci13_0 b22 (by decide +kernel) (by decide +kernel)
theorem b25:B 30 4 e18:=viaSmall (by decide +kernel) (by decide)
theorem b26:B 30 4 e19:=viaSmall (by decide +kernel) (by decide)
theorem b27:B 30 4 e20:=viaSmall (by decide +kernel) (by decide)
theorem b28:B 30 4 e21:=viaSmall (by decide +kernel) (by decide)
theorem b29:B 30 4 e22:=viaPerm pc13_0 pci13_0 b25 (by decide +kernel) (by decide +kernel)
theorem b30:B 30 4 e23:=viaPerm pc13_0 pci13_0 b26 (by decide +kernel) (by decide +kernel)
theorem b31:B 30 4 e24:=viaPerm pc13_0 pci13_0 b27 (by decide +kernel) (by decide +kernel)
theorem b32:B 30 4 e25:=viaPerm pc13_0 pci13_0 b28 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b33:B 30 5 e26:=viaBranch (ws:=[e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,e20,e21,e22,e23,e24,e25]) (consBan b10 (consBan b11 (consBan b12 (consBan b13 (consBan b14 (consBan b15 (consBan b16 (consBan b17 (consBan b18 (consBan b19 (consBan b20 (consBan b21 (consBan b22 (consBan b23 (consBan b24 (consBan b25 (consBan b26 (consBan b27 (consBan b28 (consBan b29 (consBan b30 (consBan b31 (consBan b32 (nilBan _ _)))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem b34:B 30 5 e13:=viaCut pj13_23 w8 (by decide) (by decide +kernel) (by decide +kernel)
theorem b35:B 30 5 e8:=viaPerm pc13_10 pci13_10 b34 (by decide +kernel) (by decide +kernel)
theorem b36:B 30 5 e27:=viaPerm pc13_1 pci13_1 b9 (by decide +kernel) (by decide +kernel)
theorem b37:B 30 5 e28:=viaPerm pc13_1 pci13_1 b33 (by decide +kernel) (by decide +kernel)
theorem b38:B 30 5 e29:=viaPerm pc13_1 pci13_1 b34 (by decide +kernel) (by decide +kernel)
theorem b39:B 30 5 e30:=viaPerm pc13_1 pci13_1 b35 (by decide +kernel) (by decide +kernel)
theorem b40:B 30 5 e31:=viaPerm pc13_0 pci13_0 b36 (by decide +kernel) (by decide +kernel)
theorem b41:B 30 5 e32:=viaPerm pc13_0 pci13_0 b37 (by decide +kernel) (by decide +kernel)
theorem b42:B 30 5 e33:=viaPerm pc13_0 pci13_0 b38 (by decide +kernel) (by decide +kernel)
theorem b43:B 30 5 e34:=viaPerm pc13_0 pci13_0 b39 (by decide +kernel) (by decide +kernel)
theorem b44:B 30 5 e35:=viaPerm pc13_10 pci13_10 b36 (by decide +kernel) (by decide +kernel)
theorem b45:B 30 5 e36:=viaPerm pc13_10 pci13_10 b37 (by decide +kernel) (by decide +kernel)
theorem b46:B 30 5 e37:=viaPerm pc13_10 pci13_10 b38 (by decide +kernel) (by decide +kernel)
theorem b47:B 30 5 e38:=viaPerm pc13_1 pci13_1 b46 (by decide +kernel) (by decide +kernel)
theorem b48:B 30 5 e39:=viaPerm pc13_0 pci13_0 b44 (by decide +kernel) (by decide +kernel)
theorem b49:B 30 5 e40:=viaPerm pc13_0 pci13_0 b45 (by decide +kernel) (by decide +kernel)
theorem b50:B 30 5 e41:=viaPerm pc13_0 pci13_0 b46 (by decide +kernel) (by decide +kernel)
theorem b51:B 30 5 e42:=viaPerm pc13_0 pci13_0 b47 (by decide +kernel) (by decide +kernel)
theorem b52:B 30 5 e43:=viaPerm pc13_1 pci13_1 b48 (by decide +kernel) (by decide +kernel)
theorem b53:B 30 5 e44:=viaPerm pc13_1 pci13_1 b49 (by decide +kernel) (by decide +kernel)
theorem b54:B 30 5 e45:=viaPerm pc13_1 pci13_1 b50 (by decide +kernel) (by decide +kernel)
theorem b55:B 30 5 e46:=viaPerm pc13_0 pci13_0 b54 (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem b56:B 30 6 e47:=viaBranch (ws:=[e2,e26,e13,e8,e27,e28,e29,e30,e31,e32,e33,e34,e35,e36,e37,e38,e39,e40,e41,e42,e43,e44,e45,e46]) (consBan b9 (consBan b33 (consBan b34 (consBan b35 (consBan b36 (consBan b37 (consBan b38 (consBan b39 (consBan b40 (consBan b41 (consBan b42 (consBan b43 (consBan b44 (consBan b45 (consBan b46 (consBan b47 (consBan b48 (consBan b49 (consBan b50 (consBan b51 (consBan b52 (consBan b53 (consBan b54 (consBan b55 (nilBan _ _))))))))))))))))))))))))) (by decide) (by decide +kernel) (by decide +kernel)
theorem w57:W 30 6 e47:=widen (by decide +kernel) b56
theorem b58:B 96 8 e48:=viaCut pjt_13 w57 (by decide) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 10000 in set_option maxHeartbeats 4000000 in
theorem sixWide : Wide 96 8 e48 := widen (by decide +kernel) b58
def certRows : List Nat := [5,5,5,5,5,5,5,5,5,5,9,9,9,9,9,9,9,9,9,9,12,12,12,12,12,12,12,12,12,12,17,17,17,17,17,17,17,17,17,18,18,18,18,18,18,20,20,20,20,20,20,20,20,20,24,24,24,24,24,24,24,24,24,33,33,33,33,33,33,33,33,33,34,34,34,34,34,34,36,36,36,36,36,36,36,36,36,40,40,40,40,40,40,40,40,40,0,1,3,4,6,8,10,16,32,48,0,1,3,4,6,8,10,16,32,48,0,1,3,4,6,8,10,16,32,48,0,1,3,4,6,8,10,16,48,0,3,6,10,16,48,0,1,3,4,6,8,10,16,48,0,1,3,4,6,8,10,16,48,0,1,3,4,6,8,10,32,48,0,3,6,10,32,48,0,1,3,4,6,8,10,32,48,0,1,3,4,6,8,10,32,48]
def certEtat : List ℕ := e48
def certM : Nat := 96
def certFuel : Nat := 8

end PEqualNP.Outside.L_meta_31227.ArchivedClique

namespace PEqualNP.Outside.L_meta_31227.Reduce
namespace CliqueCertificate
open PEqualNP.Outside.L_meta_31227.ArchivedClique
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
    · exact PEqualNP.Outside.L_meta_31227.ArchivedClique.Live.done word_sep (by decide +kernel)
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
end PEqualNP.Outside.L_meta_31227.Reduce

theorem PEqualNP.Outside.L_meta_31227 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 4, 5, 1, 6, 2, 6, 4, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  apply PEqualNP.Outside.L_meta_31227.Frame.finish
  intro gs o legal computes hn
  obtain ⟨b,n,hlen,live⟩ := PEqualNP.Outside.L_meta_31227.freely_chain gs o legal computes hn
  obtain ⟨k,hk,T,sub,path⟩ := PEqualNP.Outside.L_meta_31227.Reduce.to_six live
  have low := PEqualNP.Outside.L_meta_31227.Reduce.CliqueCertificate.lower k T sub path
  omega
