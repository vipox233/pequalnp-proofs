import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46566

def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)

def decodeNode (parentWidth width packed index : Nat) : Nat × Nat :=
  let entry := unpack packed width index
  (entry &&& ((1 <<< parentWidth) - 1), entry >>> parentWidth)

def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start

theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)

theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩

def rootWords (base : List Nat) (token : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun word _ next bits =>
      let tail := next (bits >>> 1)
      if bits &&& 1 == 0 then tail else word :: tail) base token

def rootState (base : List Nat) (fuel token : Nat) : (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (fuel, rootWords base token, [])

def insertWord (w : Nat) (ws : List Nat) : List Nat :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws

def childState (mask token : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 3
  let a := token / (4 * 3 * 64)
  let b := (token / (4 * 3)) % 64
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if op == 2 || keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)

def gateToken (a b op keep : Nat) : Nat := ((a * 64 + b) * 3 + op) * 4 + keep

def stockWord (mask : Nat) (stock : List Nat) (needed : List Nat) (word : Nat) : List Nat :=
  let v := word &&& mask
  if v == 0 || v == mask || stock.contains v || needed.contains v then needed
  else v :: needed

def recipeStart (mask : Nat) (stock words : List Nat) : List Nat :=
  (List.rec (motive := fun _ => List Nat → List Nat) id
    (fun word _ next seen => next (stockWord mask stock seen word)) words) []

def recipeClosure (mask : Nat) (stock : List Nat) (history : List (Nat × Nat × Nat))
    (start : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) id
    (fun (out, a, b) _ next seen =>
      next (if seen.contains (out &&& mask) then stockWord mask stock (stockWord mask stock seen a) b else seen))
    history start

def recipeNeeded (mask : Nat) (stock words : List Nat) (history : List (Nat × Nat × Nat)) :
    List Nat :=
  recipeClosure mask stock history (recipeStart mask stock words)

def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask

def flatCount (mask : Nat) (words : List Nat) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words

def availableB (mask : Nat) (bank : List Nat) (w : Nat) : Bool :=
  w == 0 || w == mask || bank.contains w

def recipeGate (mask : Nat) (bank : List Nat) (w a b : Nat) : Bool :=
  availableB mask bank a &&
    ((w == mask ^^^ a) || (availableB mask bank b && (w == a &&& b || w == a ||| b)))

def replayRecipes (mask : Nat) (needed : List Nat) (recipes : List (Nat × Nat × Nat))
    (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := w &&& mask
      if needed.contains v && !availableB mask bank v &&
          recipeGate mask bank v (a &&& mask) (b &&& mask) then
        v :: next (v :: bank)
      else next bank) recipes bank

def boundCloses (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    (let remaining := fuel - flatCount mask ws
     if remaining < lower then
       let start := recipeStart mask stock ws
       if start.length + remaining < lower then
         let needed := recipeClosure mask stock history start
         if needed.length + remaining < lower then
           let replay := replayRecipes mask needed history.reverse stock
           (replay.length + remaining < lower) &&
             ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask))
         else false
       else false
     else false)

def knownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  List.rec false (fun bound _ later => boundCloses target state bound || later) bounds

def AvailableWord (mask : Nat) (bank : List Nat) (word : Nat) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank

def GateWord (mask : Nat) (bank : List Nat) (out : Nat) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))

def WordBuilds (mask : Nat) (roots : List Nat) : List Nat → Prop
  | [] => True
  | w :: ws => GateWord mask roots w ∧ WordBuilds mask (w :: roots) ws

def Lower (mask : Nat) (roots : List Nat) (target : Nat) (minimum : Nat) : Prop :=
  ∀ values, WordBuilds mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length

def Known (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ bound ∈ bounds, Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1

theorem restrictWord (mask : Nat) (word : Nat) : word &&& mask &&& mask = word &&& mask := by
  simp

theorem projectGate {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots : List Nat} {out : Nat} (gate : GateWord mask roots out) :
    GateWord cut (roots.map (· &&& cut)) (out &&& cut) := by
  have av {word : Nat} (ha : AvailableWord mask roots word) :
      AvailableWord cut (roots.map (· &&& cut)) (word &&& cut) := by
    rcases ha with rfl | rfl | hm
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl submask)
    · exact Or.inr (Or.inr (List.mem_map_of_mem hm))
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · refine Or.inl ⟨a &&& cut, av ha, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have cutAt := congrArg (fun n : Nat => n.testBit i) submask
    simp only [Nat.testBit_and, Nat.testBit_xor] at cutAt ⊢
    cases h : cut.testBit i
    · simp
    · simp [h] at cutAt
      simp [cutAt]
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases cut.testBit i <;> simp
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases cut.testBit i <;> simp

theorem projectBuilds {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots values : List Nat} (builds : WordBuilds mask roots values) :
    WordBuilds cut (roots.map (· &&& cut)) (values.map (· &&& cut)) := by
  induction values generalizing roots with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨projectGate submask builds.1, ih builds.2⟩

theorem availableWeaken {mask : Nat} {small big : List Nat} {w : Nat}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (av : AvailableWord mask small w) : AvailableWord mask big w := by
  rcases av with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h

theorem gateWeaken {mask : Nat} {small big : List Nat} {out : Nat}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (gate : GateWord mask small out) : GateWord mask big out := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq⟩
  · exact Or.inl ⟨a, availableWeaken sub ha, rfl⟩
  · exact Or.inr ⟨a, b, availableWeaken sub ha, availableWeaken sub hb, eq⟩

theorem extendKnown {bound : (Nat × List Nat × Nat × Nat)} {bounds : List (Nat × List Nat × Nat × Nat)}
    (old : Known bounds)
    (new : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1) :
    Known (bound :: bounds) := by
  intro x h
  rcases List.mem_cons.mp h with rfl | h
  · exact new
  · exact old _ h

def AgreesAt (i j : Nat) (word : Nat) : Prop :=
  word.testBit i = word.testBit j

theorem agreesAvailable {i j mask : Nat} {bank : List Nat} {word : Nat}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (av : AvailableWord mask bank word) : AgreesAt i j word := by
  rcases av with rfl | rfl | h
  · simp [AgreesAt]
  · exact m
  · exact all _ h

theorem agreesGate {i j mask : Nat} {bank : List Nat} {word : Nat}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (gate : GateWord mask bank word) : AgreesAt i j word := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · simp only [AgreesAt, Nat.testBit_xor] at m ⊢
    rw [m, show a.testBit i = a.testBit j from agreesAvailable m all ha]
  · subst word
    simp only [AgreesAt, Nat.testBit_and]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]
  · subst word
    simp only [AgreesAt, Nat.testBit_or]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]

theorem agreesBuilds {i j mask : Nat} {roots values : List Nat} {word : Nat}
    (m : AgreesAt i j mask) (all : ∀ w ∈ roots, AgreesAt i j w)
    (builds : WordBuilds mask roots values)
    (av : AvailableWord mask (values ++ roots) word) : AgreesAt i j word := by
  induction values generalizing roots with
  | nil => exact agreesAvailable m all av
  | cons v vs ih =>
    have vg := agreesGate m all builds.1
    have hc : ∀ w ∈ v :: roots, AgreesAt i j w := by
      intro w h
      rcases List.mem_cons.mp h with rfl | mem
      · exact vg
      · exact all _ mem
    apply ih hc builds.2
    rcases av with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by
        simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using h))

theorem buildsMap {m n : Nat} (f : Nat → Nat)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots : List Nat} {bank : List Nat}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    {values : List Nat} (h : WordBuilds m roots values) :
    WordBuilds n bank (values.map f) := by
  have av {bank roots : List Nat} {v : Nat}
      (src : ∀ v ∈ roots, AvailableWord n bank (f v))
      (h : AvailableWord m roots v) : AvailableWord n bank (f v) := by
    rcases h with rfl | rfl | hv
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ hv
  induction values generalizing roots bank with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_, ih ?_ h.2⟩
    · rcases h.1 with ⟨a, ha, eq⟩ | ⟨a, b, ha, hb, eq | eq⟩
      · exact Or.inl ⟨f a, av supply ha, eq ▸ invert a⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inl (eq ▸ meet a b)⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inr (eq ▸ join a b)⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem lowerMap {m n : Nat} (f : Nat → Nat)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Nat} {goal : Nat} {minimum : Nat}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    (bound : Lower n bank (f goal) minimum) :
    Lower m roots goal minimum := by
  intro values build hit
  suffices AvailableWord n (values.map f ++ bank) (f goal) by
    simpa using bound (values.map f) (buildsMap f zero ones invert meet join supply build) this
  rcases hit with rfl | rfl | mem
  · exact Or.inl zero
  · exact Or.inr (Or.inl ones)
  · rcases List.mem_append.mp mem with hv | hr
    · exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_map_of_mem hv)))
    · exact availableWeaken (fun w hw => Or.inr (Or.inr (List.mem_append_right _ hw))) (supply _ hr)

theorem buildsWeaken {mask : Nat} {small big values : List Nat}
    (supply : ∀ w ∈ small, AvailableWord mask big w) (build : WordBuilds mask small values) :
    WordBuilds mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateWeaken supply build.1, ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem gateBuildsIndex {mask : Nat} (bank values : List Nat)
    (legal : ∀ i, i < values.length →
      GateWord mask (bank ++ values.take i) (values.getD i 0)) :
    WordBuilds mask bank values := by
  induction values generalizing bank with
  | nil => trivial
  | cons v vs ih =>
    have first := legal 0 (by simp)
    have tail : ∀ i, i < vs.length →
        GateWord mask ((bank ++ [v]) ++ vs.take i) (vs.getD i 0) := by
      intro i hi
      simpa [List.take_succ_cons, List.append_assoc] using
        legal (i + 1) (by simpa using hi)
    refine ⟨by simpa using first, buildsWeaken ?_ (ih (bank ++ [v]) tail)⟩
    intro w mem
    exact Or.inr (Or.inr (by simpa [or_comm] using mem))

theorem lowerWeaken {mask goal minimum : Nat} {old new : List Nat}
    (lower : Lower mask old goal minimum) (supply : ∀ w ∈ new, AvailableWord mask old w) :
    Lower mask new goal minimum := by
  apply lowerMap id rfl rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) supply
  exact lower

def properWord (mask word : Nat) : Prop := word ≠ 0 ∧ word ≠ mask

def binWord (isOr : Bool) (a b : Nat) : Nat :=
  if isOr then a ||| b else a &&& b

theorem binWord_comm (d : Bool) (a b : Nat) : binWord d a b = binWord d b a := by
  cases d <;> simp [binWord, Nat.land_comm, Nat.lor_comm]

variable {mask : Nat} {target : Nat}

def LiveWord (mask : Nat) (target : Nat) : Nat → Nat → Finset (Nat) → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ properWord mask target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset (Nat)) (a : Nat), t=u+1 ∧ S=insert a U ∧ properWord mask a ∧
      (mask ^^^ a) ∉ insert a U ∧ LiveWord mask target k u (insert ((mask ^^^ a)) U)) ∨
    (∃ (U : Finset (Nat)) (a b : Nat) (d : Bool), S=insert a (insert b U) ∧ properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      binWord d a b ∉ insert a (insert b U) ∧ LiveWord mask target k t (insert (binWord d a b) U))
theorem LiveWord.stop {target : Nat} (hp : properWord mask target) : LiveWord mask target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem LiveWord.unary {target : Nat} {k t : Nat} {U : Finset (Nat)} {a : Nat} (ha : properWord mask a)
    (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)) :
    LiveWord mask target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem LiveWord.binary {target : Nat} {k t : Nat} {U : Finset (Nat)} {a b : Nat} {d : Bool}
    (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)) :
    LiveWord mask target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem LiveWord.ind {target : Nat} {motive : ∀ (k t : Nat) (S : Finset (Nat)), LiveWord mask target k t S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 0 {target} (LiveWord.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset (Nat)} {a : Nat} (ha : properWord mask a)
      (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)),
      motive k t (insert ((mask ^^^ a)) U) tail → motive (k+1) (t+1) (insert a U) (LiveWord.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset (Nat)} {a b : Nat} {d : Bool}
      (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)),
      motive k t (insert (binWord d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (LiveWord.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset (Nat)} (h : LiveWord mask target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

theorem liveWordProper {k t S} (h : LiveWord mask target k t S) : ∀ a ∈ S, properWord mask a := by
  induction h using LiveWord.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem liveWordSize {k t S} (h : LiveWord mask target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using LiveWord.ind with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : (mask ^^^ a) ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : binWord d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

def wordRep (mask : Nat) (ws : List Nat) (w : Nat) : Prop :=
  w ∈ ws ∨ ¬properWord mask w

def wordWitness (mask : Nat) (ws : List Nat) (w : Nat) : Prop :=
  (∃ a ∈ ws, properWord mask a ∧ w = mask ^^^ a) ∨
  ∃ d a b, a ∈ ws ∧ b ∈ ws ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ w = binWord d a b

theorem pullWord {w : List (Nat)} {z : Nat} {k t S} (h : LiveWord mask target k t S)
    (hz : wordRep mask w z ∨ wordWitness mask w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ LiveWord mask target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveWordProper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase ((mask ^^^ a))
        have ht : LiveWord mask target k t (insert ((mask ^^^ a)) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : (mask ^^^ a) ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (binWord d a b)
        have ht : LiveWord mask target k t (insert (binWord d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : binWord d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

def Masked (mask word : Nat) : Prop := word &&& mask = word

theorem maskedAvailable {bank : List Nat} {word : Nat}
    (all : ∀ w ∈ bank, Masked mask w) (aw : AvailableWord mask bank word) :
    Masked mask word := by
  rcases aw with rfl | rfl | hw
  · simp [Masked]
  · simp [Masked]
  · exact all _ hw

theorem maskedGate {bank : List Nat} {out : Nat}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateWord mask bank out) :
    Masked mask out := by
  rcases g with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, ea | ea⟩
  · have h := projectGate (mask := mask) (cut := mask) (by simp)
      (roots := bank) (out := mask ^^^ a) (Or.inl ⟨a, ha, rfl⟩)
    have ma := maskedAvailable all ha
    unfold Masked at ma ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bit := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
    cases hm : mask.testBit i <;> simp_all
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    simp only [Masked] at ma mb ⊢
    rw [Nat.land_assoc, mb]
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    unfold Masked at ma mb ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bitA := congrArg (fun n : Nat => n.testBit i) ma
    have bitB := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at bitA bitB ⊢
    cases hm : mask.testBit i <;> simp_all

def binaryWitness (mask : Nat) (bank : List Nat) (out : Nat) : Prop :=
  ∃ d a b, a ∈ bank ∧ b ∈ bank ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ out = binWord d a b

theorem classifyBinary {bank : List Nat}
    (all : ∀ w ∈ bank, Masked mask w) (d : Bool) {a b : Nat}
    (ha : AvailableWord mask bank a) (hb : AvailableWord mask bank b) :
    wordRep mask bank (binWord d a b) ∨ binaryWitness mask bank (binWord d a b) := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Nat} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  have ma : a &&& mask = a := maskedAvailable all ha
  have mb : b &&& mask = b := maskedAvailable all hb
  have absorbA : a ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  have absorbB : b ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  rcases classify ha with rfl | hma | ⟨ha', pa⟩
  · rw [binWord_comm]
    cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, wordRep] using
          (Or.inl hv : wordRep mask bank b))
  · rw [hma, binWord_comm]
    cases d
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, mb, wordRep] using
          (Or.inl hv : wordRep mask bank b))
    · exact Or.inl (by simpa [binWord, absorbB] using cm)
  rcases classify hb with rfl | hmb | ⟨hb', pb⟩
  · cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · exact Or.inl (by simpa [binWord, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
  · rw [hmb]
    cases d
    · exact Or.inl (by simpa [binWord, ma, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
    · exact Or.inl (by simpa [binWord, absorbA] using cm)
  by_cases eq : a = b
  · subst b
    cases d <;> exact Or.inl (by simpa [binWord, wordRep] using
      (Or.inl ha' : wordRep mask bank a))
  exact Or.inr ⟨d, a, b, ha', hb', pa, pb, eq, rfl⟩

theorem classifyWord {bank : List Nat} {out : Nat}
    (all : ∀ w ∈ bank, Masked mask w) (gate : GateWord mask bank out) :
    wordRep mask bank out ∨ wordWitness mask bank out := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Nat} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, h | h⟩
  · rcases classify ha with rfl | hma | ⟨hm, hp⟩
    · exact Or.inl (by simpa using cm)
    · exact Or.inl (by simpa [hma] using c0)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  · subst out; exact (classifyBinary all false ha hb).imp id Or.inr
  · subst out; exact (classifyBinary all true ha hb).imp id Or.inr

theorem extractWordLive {roots values : List Nat}
    (all : ∀ w ∈ roots, Masked mask w) (builds : WordBuilds mask roots values)
    (hit : AvailableWord mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k t S, k ≤ values.length ∧ LiveWord mask target k t S ∧ ∀ w ∈ S, w ∈ roots := by
  have hm := (hit.resolve_left p.1).resolve_left p.2
  induction values generalizing roots with
  | nil =>
    exact ⟨0, 0, {target}, Nat.zero_le _, LiveWord.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate all builds.1
      · exact all _ hv
    have ht : AvailableWord mask (ws ++ w :: roots) target := by
      exact Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hm))
    obtain ⟨k, t, S, hk, live, sub⟩ :=
      ih next builds.2 ht ((ht.resolve_left p.1).resolve_left p.2)
    have available : ∀ v ∈ S, v ∈ roots ++ [w] := by
      intro v h
      simpa [or_comm] using sub v h
    obtain ⟨k', t', S', hk', hl, hsub⟩ := pullWord live (classifyWord all builds.1) available
    exact ⟨k', t', S', by simp only [List.length_cons]; omega, hl, hsub⟩

theorem insertWordMem {x w : Nat} {ws : List Nat} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih, or_assoc, or_left_comm]

theorem insertWordNodup {w : Nat} {ws : List Nat} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh, nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem, hnot.1.symm, hn.1], ih hn.2 hnot.2⟩

theorem insertWordSet (w : Nat) (ws : List Nat) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]

theorem eraseWordSet {ws : List Nat} (nd : ws.Nodup) (w : Nat) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff, and_comm]

theorem gateTokenFields {a b op keep : Nat} (hb : b < 64) (ho : op < 3) (hk : keep < 4) :
    gateToken a b op keep % 4 = keep ∧
    gateToken a b op keep / 4 % 3 = op ∧
    gateToken a b op keep / (4 * 3 * 64) = a ∧
    gateToken a b op keep / (4 * 3) % 64 = b := by
  unfold gateToken
  omega

def keepWord (save : Bool) (w : Nat) (ws : List Nat) : List Nat :=
  if save then ws else ws.erase w

theorem keepNodup {ws : List Nat} (nd : ws.Nodup) (save : Bool) (w : Nat) :
    (keepWord save w ws).Nodup := by
  cases save
  · exact nd.erase _
  · exact nd

theorem keepSubset (save : Bool) (w : Nat) (ws : List Nat) :
    ∀ v ∈ keepWord save w ws, v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h

theorem keepSet {ws : List Nat} (nd : ws.Nodup) {w : Nat} {U : Finset Nat}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord, hw, eq, Finset.insert_eq_of_mem hw]
  · simp [keepWord, hw, eraseWordSet nd, eq]

theorem keepPairSet {ws : List Nat} (nd : ws.Nodup) {a b : Nat} {U : Finset Nat}
    (ab : a ≠ b) (eq : ws.toFinset = insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset = U := by
  have x : decide (a ∈ insert b U) = decide (a ∈ U) := by simp [ab]
  have h := keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h

theorem getWord {ws : List Nat} {x : Nat} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0 = x := by
  have inb := List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb

theorem unaryChild {mask fuel a : Nat} {ws : List Nat}
    {history : List (Nat × Nat × Nat)} {x : Nat} {keep : Nat}
    (ha : a < ws.length) (ha64 : a < 64) (hf : fuel ≠ 0) (hk : keep < 2)
    (hx : ws.getD a 0 = x) (p : properWord mask (mask ^^^ x)) (fresh : mask ^^^ x ∉ ws) :
    childState mask (gateToken a a 2 keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (mask ^^^ x) (keepWord (keep.testBit 0) x ws),
        (mask ^^^ x, x, x) :: history) := by
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) ha64 (by decide : 2 < 3) (by omega : keep < 4)
  simp only [childState, ke, op, aa, bb, hx]
  simp [hf, Nat.not_le_of_lt ha, Nat.not_le_of_lt hk, p.1, p.2, fresh, keepWord]

theorem binaryChild {mask fuel a b : Nat} {ws : List Nat}
    {history : List (Nat × Nat × Nat)} {x y : Nat} {keep : Nat}
    (d : Bool) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (binWord d x y)) (fresh : binWord d x y ∉ ws) :
    childState mask (gateToken a b (if d then 1 else 0) keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (binWord d x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (binWord d x y, x, y) :: history) := by
  have oh : (if d then 1 else 0) < 3 := by cases d <;> decide
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) hb64 oh hk
  simp only [childState, ke, op, aa, bb, hx, hy]
  cases d <;>
    simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, binWord, properWord]

def WordViable (mask : Nat) (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Prop :=
  state.2.1.Nodup ∧ ∃ k t, k ≤ state.1 ∧ LiveWord mask target k t state.2.1.toFinset

def HasChild (mask : Nat) (state child : (Nat × List Nat × List (Nat × Nat × Nat))) : Prop :=
  ∃ a b op keep, a < state.2.1.length ∧
    ((a = b ∧ op = 2 ∧ keep < 2) ∨
      (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4)) ∧
    childState mask (gateToken a b op keep) state = some child

theorem unaryProgress {mask fuel k t : Nat} {x target : Nat} {U : Finset Nat} {ws : List Nat}
    {history : List (Nat × Nat × Nat)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x U) (fresh : mask ^^^ x ∉ insert x U)
    (tail : LiveWord mask target k t (insert (mask ^^^ x) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  have xm : x ∈ ws := by
    rw [← List.mem_toFinset, he]
    simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hx : ws.getD a 0 = x := getWord xm
  have p := liveWordProper tail (mask ^^^ x) (Finset.mem_insert_self _ _)
  let save := decide (x ∈ U)
  let keep := if save then 1 else 0
  have keepLt : keep < 2 := by dsimp [keep]; split <;> decide
  have keepBit : keep.testBit 0 = save := by
    unfold keep
    cases save <;> decide
  have fn : mask ^^^ x ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord save x ws
  let child : (Nat × List Nat × List (Nat × Nat × Nat)) := (fuel - 1, insertWord (mask ^^^ x) rest, (mask ^^^ x, x, x) :: history)
  refine ⟨child, ⟨a, a, 2, keep, ha, Or.inl ⟨rfl, rfl, keepLt⟩, ?_⟩, ?_⟩
  · have eq := unaryChild (fuel := fuel) (history := history) ha (by omega) (by omega) keepLt hx p fn
    rw [keepBit] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup nd save x) (fun h => fn (keepSubset save x ws _ h)),
      k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord (mask ^^^ x) rest).toFinset
    rw [insertWordSet, keepSet nd he]
    exact tail

theorem binaryProgress {mask fuel k t : Nat} {x y target : Nat} {d : Bool} {U : Finset Nat}
    {ws : List Nat} {history : List (Nat × Nat × Nat)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (tail : LiveWord mask target k t (insert (binWord d x y) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := binWord d x y
  have p := liveWordProper tail v (Finset.mem_insert_self _ _)
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep
    cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : (Nat × List Nat × List (Nat × Nat × Nat)) := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, if d then 1 else 0, keep, ha, Or.inr ⟨hab, hb, ?_, keepLt⟩, ?_⟩, ?_⟩
  · cases d <;> decide
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail

theorem wordProgress {mask : Nat} {target : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (width : state.2.1.length ≤ 64) (h : WordViable mask target state) :
    target ∈ state.2.1 ∨ ∃ child, HasChild mask state child ∧ WordViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, t, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    left
    change ws.toFinset = {target} at eq
    rw [← List.mem_toFinset, eq]
    simp
  | succ k =>
    right
    rcases live with ⟨u,U,x,_,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · exact unaryProgress nd width cap eq fresh tail
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same
      apply xy
      rw [← getWord xm, same, getWord ym]
    by_cases h : ws.idxOf x < ws.idxOf y
    · exact binaryProgress nd width cap eq xy h fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : binWord d y x ∉ insert y (insert x U) := by
        rw [binWord_comm d y x, Finset.insert_comm]; exact fresh
      have tail' : LiveWord mask target k t (insert (binWord d y x) U) := by
        rw [binWord_comm d y x]; exact tail
      exact binaryProgress nd width cap eq' xy.symm (by omega) fresh' tail'

theorem rootWordSublist (base : List Nat) (token : Nat) : (rootWords base token).Sublist base := by
  induction base generalizing token with
  | nil => exact List.Sublist.slnil
  | cons w ws ih =>
    change (if token &&& 1 == 0 then rootWords ws (token >>> 1)
      else w :: rootWords ws (token >>> 1)).Sublist (w :: ws)
    split
    · exact (ih _).cons _
    · exact (ih _).cons₂ _

theorem rootToken (base : List Nat) (S : Finset Nat) :
    ∃ token < 2 ^ base.length, (rootWords base token).toFinset = base.toFinset ∩ S := by
  induction base with
  | nil => exact ⟨0, by simp, by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token, htoken, ih⟩ := ih
    let bit : Nat := if w ∈ S then 1 else 0
    have hbit : bit < 2 := by dsimp [bit]; split <;> decide
    let code := 2 * token + bit
    have low : code &&& 1 = bit := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code >>> 1 = token := by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2 = token
      dsimp [code]
      omega
    refine ⟨code, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      dsimp [code]
      omega
    · change (if code &&& 1 == 0 then rootWords ws (code >>> 1)
        else w :: rootWords ws (code >>> 1)).toFinset = _
      rw [low, high]
      by_cases hw : w ∈ S
      · simp [bit, hw, ih]
      · simp [bit, hw, ih]

theorem liveAgrees {i j k t : Nat} {S : Finset Nat}
    (h : LiveWord mask target k t S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S, AgreesAt i j w) : AgreesAt i j target := by
  induction h using LiveWord.ind with
  | stop => exact all _ (Finset.mem_singleton_self _)
  | @unary k t U a pa fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp only [AgreesAt, Nat.testBit_xor]
      rw [show mask.testBit i = mask.testBit j from m,
        show a.testBit i = a.testBit j from all a (Finset.mem_insert_self _ _)]
    · exact all _ (Finset.mem_insert_of_mem hw)
  | @binary k t U a b d pa pb ab fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have aa : a.testBit i = a.testBit j := all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i = b.testBit j := all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      cases d <;> simp [AgreesAt, binWord, Nat.testBit_and, Nat.testBit_or, aa, bb]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i = true) :
    mask.testBit i = true := by
  have h := congrArg (fun n : Nat => n.testBit i) mt
  simpa [Nat.testBit_and, ht] using h

variable {rows : Nat}

def fullMask (rows : Nat) : Nat := 2 ^ rows - 1

theorem toNatMasked (v : BitVec rows) : Masked (fullMask rows) v.toNat := by
  unfold Masked fullMask
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt v.isLt]

theorem notNat (v : BitVec rows) : (~~~v).toNat = fullMask rows ^^^ v.toNat := by
  rw [← BitVec.xor_allOnes, BitVec.toNat_xor, Nat.xor_comm, BitVec.toNat_allOnes]
  rfl

theorem gateOfAvailable {bank : List Nat} {w : Nat}
    (av : AvailableWord mask bank w) : GateWord mask bank w :=
  Or.inr ⟨w, 0, av, Or.inl rfl, Or.inr (by simp)⟩

theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))

def buildable (m g : Nat) : Nat → Finset (Nat) → Prop
  | 0, s => g ∈ s
  | n+1, s => buildable m g n s ∨
    (∃ a ∈ s, buildable m g n (insert (m ^^^ a) s)) ∨
    (∃ a ∈ s, ∃ b ∈ s, ∃ d, buildable m g n (insert (binWord d a b) s))

theorem supplyPool {m g : Nat} {n s q} (sub : s ⊆ q) (h : buildable m g n s) : buildable m g n q := by
  induction n generalizing s q with
  | zero => exact sub h
  | succ n ih =>
    rcases h with h | ⟨a,ha,h⟩ | ⟨a,ha,b,hb,d,h⟩
    · exact Or.inl (ih sub h)
    · exact Or.inr (Or.inl ⟨a,sub ha,ih (Finset.insert_subset_insert _ sub) h⟩)
    · exact Or.inr (Or.inr ⟨a,sub ha,b,sub hb,d,ih (Finset.insert_subset_insert _ sub) h⟩)

theorem supplyMore {m g : Nat} {n l s} (le : n ≤ l) (h : buildable m g n s) : buildable m g l s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

abbrev maskedFlat (m a : Nat) : Prop := a &&& m = 0 ∨ a &&& m = m

def flatSet (m : Nat) (s : Finset (Nat)) := s.filter (maskedFlat m)
def visibleWords (m : Nat) (s : Finset (Nat)) := s.image fun w => w &&& m

theorem flIns {m a : Nat} {s : Finset (Nat)} (ha : a ∉ s) :
    (flatSet m (insert a s)).card = (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases f : maskedFlat m a <;> simp [flatSet,Finset.filter_insert,f,ha]

theorem flLe (m a : Nat) (s : Finset (Nat)) :
    (flatSet m (insert a s)).card ≤ (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases old : a ∈ s
  · rw [Finset.insert_eq_of_mem old]
    omega
  · rw [flIns old]

theorem prIns (m a : Nat) (s : Finset (Nat)) :
    visibleWords m (insert a s) = insert (a &&& m) (visibleWords m s) := Finset.image_insert ..

theorem cofNot {mask m : Nat} (sub : mask &&& m = m) (a : Nat) :
    (mask ^^^ a) &&& m = m ^^^ (a &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun w : Nat => w.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at h ⊢
  cases he : m.testBit i
  · simp
  · have hm : mask.testBit i = true := by simpa [he] using h
    simp [hm]

theorem cofBinary (m a b : Nat) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp

theorem flNot {mask m : Nat} (sub : mask &&& m = m) (a : Nat) :
    maskedFlat m (mask ^^^ a) ↔ maskedFlat m a := by
  unfold maskedFlat
  rw [cofNot sub]
  constructor <;> intro h
  · rcases h with h | h
    · right
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
    · left
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
  · rcases h with h | h <;> simp [h]

theorem flBoth {m a b : Nat} {d : Bool} (ha : maskedFlat m a) (hb : maskedFlat m b) :
    maskedFlat m (binWord d a b) := by
  unfold maskedFlat at *
  rw [cofBinary]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> cases d <;>
    simp [binWord, ha, hb]

theorem simpleBin {m a b : Nat} {d : Bool} (h : maskedFlat m a ∨ maskedFlat m b) :
    binWord d a b &&& m = 0 ∨ binWord d a b &&& m = m ∨
      binWord d a b &&& m = a &&& m ∨ binWord d a b &&& m = b &&& m := by
  rw [cofBinary]
  have top1 (x : Nat) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]
    simp
  have top2 (x : Nat) : m ||| (x &&& m) = m := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and]
    cases x.testBit i <;> cases m.testBit i <;> rfl
  have right1 (x : Nat) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Nat) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  rcases h with (ha|ha)|(hb|hb) <;> cases d <;>
    simp [binWord, *, top1, top2, right1, right2]

def projectedStock (m : Nat) (s : Finset (Nat)) := insert 0 (insert m (visibleWords m s))

theorem maskedBuild {goal : Nat} {k t s} (run : LiveWord mask goal k t s) (m : Nat) (submask : mask &&& m = m) (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n+(flatSet m s).card ≤ k ∧ buildable m (goal &&& m) n (projectedStock m s) := by
  induction run using LiveWord.ind with
  | stop =>
    refine ⟨0,?_,?_⟩
    · simp only [flatSet, Finset.filter_singleton, properGoal, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · change goal &&& m ∈ projectedStock m {goal}
      simp [projectedStock,visibleWords]
  | @unary k t u a pa fresh tail ih =>
    obtain ⟨n,cap,built⟩ := ih
    have nn : (mask ^^^ a) ∉ u := fun h => fresh (Finset.mem_insert_of_mem h)
    rw [flIns nn] at cap
    have card := flLe m a u
    have old : a &&& m ∈ projectedStock m (insert a u) := by simp [projectedStock,prIns]
    have sub : projectedStock m u ⊆ projectedStock m (insert a u) := by
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.image_subset_image (Finset.subset_insert ..)))
    by_cases f : maskedFlat m a
    · have ff := (flNot submask a).mpr f
      simp only [f,ff,ite_true] at cap card
      refine ⟨n,by omega,supplyPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with rfl|rfl|rfl|h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rcases ff with e|e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inr h))
    · have nf := mt (flNot submask a).mp f
      simp only [f,nf,ite_false] at cap card
      refine ⟨n+1,by omega,Or.inr (Or.inl ⟨_,old,supplyPool ?_ built⟩)⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rw [cofNot submask] at hw
      tauto
  | @binary k t u a b d pa pb ab fresh tail ih =>
    let v := binWord d a b
    obtain ⟨n,cap,built⟩ := ih
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n+(flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k+1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa,fb,ite_true,ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBoth fa fb; simp only [vf,ite_true] at cap; omega | omega | tauto
      refine ⟨n,budget,supplyPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with e|e|e|e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · subst w
        have cases := simpleBin (d := d) simple
        tauto
      · tauto
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa,fb,ite_false] at ca cb
      refine ⟨n+1,by omega,Or.inr (Or.inr ⟨a &&& m,?_,b &&& m,?_,d,supplyPool ?_ built⟩)⟩
      · simp [projectedStock,prIns]
      · simp [projectedStock,prIns]
      · intro w hw
        simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
        rw [cofBinary] at hw
        tauto

theorem availableB_spec {mask : Nat} {bank : List Nat} {v : Nat} :
    availableB mask bank v = true ↔ AvailableWord mask bank v := by
  simp [availableB, AvailableWord, or_assoc]

theorem recipeGate_spec {mask : Nat} {bank : List Nat} {v a b : Nat}
    (h : recipeGate mask bank v a b = true) : GateWord mask bank v := by
  simp only [recipeGate, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, availableB_spec] at h
  rcases h with ⟨ha, first | ⟨hb, second⟩⟩
  · exact Or.inl ⟨a, ha, first⟩
  · exact Or.inr ⟨a, b, ha, hb, second⟩

theorem replayRecipesBuilds (mask : Nat) (needed : List Nat) (recipes : List (Nat × Nat × Nat))
    (bank : List Nat) : WordBuilds mask bank (replayRecipes mask needed recipes bank) := by
  induction recipes generalizing bank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuilds mask bank
      (if needed.contains (w &&& mask) && !availableB mask bank (w &&& mask) &&
          recipeGate mask bank (w &&& mask) (a &&& mask) (b &&& mask) then
        (w &&& mask) :: replayRecipes mask needed recipes ((w &&& mask) :: bank)
      else replayRecipes mask needed recipes bank)
    split
    · rename_i yes
      exact ⟨recipeGate_spec (Bool.and_eq_true_iff.mp yes).2, ih _⟩
    · exact ih _

theorem flatCountCard (mask : Nat) {words : List Nat} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat, maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons, flIns fresh, ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h, bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h, no]

theorem buildsAppend {mask : Nat} {roots first second : List Nat}
    (left : WordBuilds mask roots first)
    (right : WordBuilds mask (first ++ roots) second) :
    WordBuilds mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact right
  | cons w ws ih =>
    refine ⟨left.1, ih left.2 ?_⟩
    have same (bank other vals : List Nat) (perm : bank.Perm other)
        (h : WordBuilds mask bank vals) : WordBuilds mask other vals := by
      induction vals generalizing bank other with
      | nil => trivial
      | cons v vs ih =>
        exact ⟨gateWeaken (fun x hx => Or.inr (Or.inr (perm.mem_iff.mp hx))) h.1,
          ih _ _ (perm.cons v) h.2⟩
    exact same _ _ _ (List.perm_middle (a := w) (l₁ := ws) (l₂ := roots)).symm right

theorem buildableWords {mask goal n : Nat} {pool : Finset Nat} {bank : List Nat}
    (h : buildable mask goal n pool) (supply : ∀ w ∈ pool, AvailableWord mask bank w) :
    ∃ values, values.length ≤ n ∧ WordBuilds mask bank values ∧
      AvailableWord mask (values ++ bank) goal := by
  induction n generalizing pool bank with
  | zero => exact ⟨[], Nat.le_refl _, trivial, supply _ h⟩
  | succ n ih =>
    have add {w : Nat} (g : GateWord mask bank w)
        (tail : buildable mask goal n (insert w pool)) :
        ∃ values, values.length ≤ n+1 ∧ WordBuilds mask bank values ∧
          AvailableWord mask (values ++ bank) goal := by
      have growing : ∀ v ∈ insert w pool, AvailableWord mask (w :: bank) v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun _ hh => Or.inr (Or.inr (List.mem_cons_of_mem _ hh))) (supply _ hv)
      obtain ⟨values, budget, build, hit⟩ := ih tail growing
      refine ⟨w :: values, by simp only [List.length_cons]; omega, ⟨g, build⟩, ?_⟩
      rcases hit with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by simp only [List.mem_append, List.mem_cons] at *; tauto))
    rcases h with h | ⟨a, ha, h⟩ | ⟨a, ha, b, hb, d, h⟩
    · obtain ⟨values, cap, build, hit⟩ := ih h supply
      exact ⟨values, by omega, build, hit⟩
    · exact add (Or.inl ⟨a, supply a ha, rfl⟩) h
    · apply add (w := binWord d a b) ?_ h
      exact Or.inr ⟨a, b, supply a ha, supply b hb, by cases d <;> simp [binWord]⟩

theorem boundClosesSound {state : (Nat × List Nat × List (Nat × Nat × Nat))} {bound : (Nat × List Nat × Nat × Nat)}
    (known : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : WordViable mask target state) :
    boundCloses target state bound = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, t, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveWord mask target k t ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let replay := replayRecipes cut (recipeNeeded cut stock ws history) history.reverse stock
  change ((target &&& cut) == goal && goal != 0 && goal != cut &&
    (if fuel - flatCount cut ws < minimum then
      if (recipeStart cut stock ws).length + (fuel - flatCount cut ws) < minimum then
        if (recipeNeeded cut stock ws history).length + (fuel - flatCount cut ws) < minimum then
          (replay.length + (fuel - flatCount cut ws) < minimum) &&
            ws.all (fun w => availableB cut (replay ++ stock) (w &&& cut))
        else false
      else false
    else false)) = true at hc
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  simp only [decide_eq_true_eq] at length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuild live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvailableWord cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableB_spec.mp (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableWords build supply
  have both := buildsAppend (replayRecipesBuilds cut _ history.reverse stock) built
  have hit : AvailableWord cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact availableWeaken (fun v hv => Or.inr (Or.inr (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega

theorem knownClosesSound {bounds : List (Nat × List Nat × Nat × Nat)} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (known : Known bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (viable : WordViable mask target state) :
    knownCloses target bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (boundCloses target state bound || knownCloses target bounds state) = false
    rw [boundClosesSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))

def encodePoint (f : (Fin rows → Bool)) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem encodeBit (f : (Fin rows → Bool)) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

theorem encodeNot (f : (Fin rows → Bool)) : encodePoint (fun j => !f j) = ~~~encodePoint f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_not, encodeBit f ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
  simp [hi]

theorem encodeAnd (a b : (Fin rows → Bool)) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

theorem encodeOr (a b : (Fin rows → Bool)) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

def pointWord (f : (Fin rows → Bool)) : Nat := (encodePoint f).toNat

def relabel (sourceIndex : Fin rows → Fin rows) (word : Nat) : Nat :=
  pointWord fun i => word.testBit (sourceIndex i).val

theorem maskBit {i : Nat} (hi : i < rows) : (fullMask rows).testBit i = true := by
  simp [fullMask, Nat.testBit_two_pow_sub_one, hi]

theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]

theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))

theorem relabelMask (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex (fullMask rows) = fullMask rows := by
  have all : (fun i => (fullMask rows).testBit (sourceIndex i).val) = fun _ => true := by
    funext i
    exact maskBit (sourceIndex i).isLt
  have bits : encodePoint (fun _ : Fin rows => true) = BitVec.allOnes rows := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp [hi]
  simp [relabel, all, pointWord, bits, fullMask]

theorem relabelNot (sourceIndex : Fin rows → Fin rows) (a : Nat) :
    relabel sourceIndex (fullMask rows ^^^ a) = fullMask rows ^^^ relabel sourceIndex a := by
  have eq : (fun i => (fullMask rows ^^^ a).testBit (sourceIndex i).val) =
      fun i => !a.testBit (sourceIndex i).val := by
    funext i
    simp [Nat.testBit_xor, maskBit (sourceIndex i).isLt]
  simp only [relabel, eq, pointWord, encodeNot, notNat]

theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]

theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]

theorem lowerRelabel (sourceIndex : Fin rows → Fin rows) {bank roots : List Nat}
    {src dst : Nat} {minimum : Nat}
    (old : Lower (fullMask rows) bank src minimum)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord (fullMask rows) bank (relabel sourceIndex w)) :
    Lower (fullMask rows) roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) (relabelMask sourceIndex)
    (relabelNot sourceIndex) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rw [goal]
  exact old

theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel, pointWord, BitVec.toNat_xor] using congrArg BitVec.toNat eq

theorem lowerRelabelMasked (sourceIndex : Fin rows → Fin rows)
    {oldMask newMask : Nat} {bank roots : List Nat} {src dst : Nat} {minimum : Nat}
    (old : Lower oldMask bank src minimum)
    (masks : relabel sourceIndex newMask = oldMask)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord oldMask bank (relabel sourceIndex w)) :
    Lower newMask roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) masks
    (fun w => by rw [relabelXor, masks]) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rwa [goal]

theorem extendKnownRelabel (sourceIndex : Fin rows → Fin rows) {bounds : List (Nat × List Nat × Nat × Nat)}
    {source destination : (Nat × List Nat × Nat × Nat)} (old : Known bounds) (mem : source ∈ bounds)
    (budget : destination.2.2.1 = source.2.2.1)
    (masks : relabel sourceIndex destination.1 = source.1)
    (goal : relabel sourceIndex destination.2.2.2 = source.2.2.2)
    (supply : ∀ w ∈ destination.2.1,
      AvailableWord source.1 source.2.1 (relabel sourceIndex w)) :
    Known (destination :: bounds) := by
  apply extendKnown old
  rw [budget]
  exact lowerRelabelMasked sourceIndex (old _ mem) masks goal supply

theorem relabelToNatBound (sourceIndex : Fin rows → Fin rows) (word : Nat) :
    Masked (fullMask rows) (relabel sourceIndex word) := toNatMasked _

theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Nat) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i

theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Nat) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)

theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Nat} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j, h⟩ := onto ⟨i, inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit, h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, inside, decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]

theorem kw_step (goal : Nat) (D D' : Finset Nat) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D', x ≠ w → x ∈ D)
    (hf : ∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i', c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i, goal.testBit e = true → goal.testBit i = false →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i, goal.testBit e = true → goal.testBit i = false → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_eq_left (h)]
    cases c e i
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun e i => if f e i = w then (cond (c e i) u v) else f e i, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2, h3⟩ := hf e i he hi
    show (if f e i = w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit e = true ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit i = false
    by_cases hw : f e i = w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx, hcc⟩ | ⟨hx, hcc⟩
      · rw [hx]; exact ⟨hu, hcu e i h2 h3 hcc⟩
      · rw [hx]; exact ⟨hv, hcv e i h2 h3 hcc⟩
    · rw [ite_eq_right (hw)]; exact ⟨hsub _ h1 hw, h2, h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i' = w then (cond (c e i') u v) else f e i') =
      (if f e i = w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i = w then (cond (c e i) u v) else f e i) =
      (if f e' i' = w then (cond (c e' i') u v) else f e' i') := heq
    by_cases h1 : f e i = w
    · by_cases h2 : f e' i' = w
      · have h3 : f e i' = w := (hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i = c e' i' := by
          rcases hg e i he hi h1 with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy, hy'⟩ | ⟨hy, hy'⟩
          · rw [hx', hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx', hy']
        rw [ite_eq_left (h3), ite_eq_left (h1), hc e i e' i' hcc]
      · exfalso
        rw [ite_eq_right (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, heq']; exact hm)
        · exact hvD (by rw [← hx, heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_eq_right (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, ← heq']; exact hm)
        · exact hvD (by rw [← hx, ← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_eq_right h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_eq_right h2
        rw [h1n, h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n, ite_eq_right (h3n)]
        exact h3

theorem and_cu (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (_h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem and_cv (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cu (u v e i : ℕ) (_h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cv (u v e i : ℕ) (h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

def KWPartition (goal : Nat) (ws : Finset Nat) : Prop :=
  ∃ f : Nat → Nat → Nat,
    (∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ ws ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
    (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true →
      goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)

theorem kwFromLive {mask goal : Nat} {k : Nat} {S : Finset Nat}
    (live : LiveWord mask goal k 0 S) (tight : S.card = k + 1) : KWPartition goal S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    subst S
    exact ⟨fun _ _ => goal, fun _ _ hp hn => ⟨by simp, hp, hn⟩, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, eq, _⟩ | ⟨U, a, b, op, rfl, pa, pb, ab, fresh, tail⟩
    · omega
    let w := binWord op a b
    have wU : w ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have wA : w ≠ a := fun eq => fresh (Finset.mem_insert.mpr (Or.inl eq))
    have wB : w ≠ b := fun eq => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq)))
    have tailSize := (liveWordSize tail).2
    change (insert w U).card + 0 ≤ k + 1 at tailSize
    rw [Finset.card_insert_of_notMem wU] at tailSize
    have paCard := Finset.card_insert_le a (insert b U)
    have pbCard := Finset.card_insert_le b U
    have aU : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
      omega
    have bU : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      have := Finset.card_insert_le a U
      omega
    obtain ⟨f, hf, hr⟩ := ih tail (by
      change (insert w U).card = k + 1
      rw [Finset.card_insert_of_notMem wU]
      omega)
    have keepA : a ∉ insert w U := by simp [wA.symm, aU]
    have keepB : b ∉ insert w U := by simp [wB.symm, bU]
    have other : ∀ x ∈ insert w U, x ≠ w → x ∈ insert a (insert b U) := by
      intro x hx hn
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left hn))
    have ha : a ∈ insert a (insert b U) := Finset.mem_insert_self ..
    have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    cases op
    · exact kw_step goal _ _ a b w (fun _ i => !(a.testBit i)) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => and_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => and_cv a b e i h1 h2 h3)
        (fun _ _ _ _ h => h.symm)
    · exact kw_step goal _ _ a b w (fun e _ => a.testBit e) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => or_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => or_cv a b e i h1 h2 h3)
        (fun _ _ _ _ _ => rfl)

theorem liveDirected {mask goal : Nat} {k : Nat} {S : Finset Nat}
    (live : LiveWord mask goal k 0 S) {p n : Nat}
    (hp : goal.testBit p = true) (hn : goal.testBit n = false) :
    ∃ w ∈ S, w.testBit p = true ∧ w.testBit n = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,_⟩ := live
    exact ⟨goal, by simp, hp, hn⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, ueq, _⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
    · omega
    obtain ⟨w, hw, wp, wn⟩ := ih tail
    rcases Finset.mem_insert.mp hw with eq | hU
    · subst w
      cases op
      · by_cases ha : a.testBit n = false
        · exact ⟨a, Finset.mem_insert_self .., and_cu a b p n wp wn (by simp [ha])⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            and_cv a b p n wp wn (by cases h : a.testBit n <;> simp_all)⟩
      · by_cases ha : a.testBit p = true
        · exact ⟨a, Finset.mem_insert_self .., or_cu a b p n wp wn ha⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            or_cv a b p n wp wn (by cases h : a.testBit p <;> simp_all)⟩
    · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),wp,wn⟩

namespace PackedRect

theorem tb4095 (i : ℕ) : (4095 : ℕ).testBit i = decide (i < 12) := by
  have e : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
  rw [e, Nat.testBit_two_pow_sub_one]

def tb (w e : ℕ) : Bool := !(Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)

theorem tb_eq (w e : ℕ) : tb w e = w.testBit e := by
  have h : Nat.land (Nat.shiftRight w e) 1 = 1 &&& (w >>> e) := Nat.and_comm _ _
  unfold tb Nat.testBit
  rw [h]
  generalize (1 &&& w >>> e) = X
  cases X <;> rfl

def rect (x J : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)

def rectW (x : ℕ) : ℕ := rect x (Nat.xor (Nat.shiftRight x 12) 4095) 12

theorem rect_tb (x J i : ℕ) (hJ : J.testBit i = true) : ∀ n e : ℕ, e < n → x.testBit e = true →
    (rect x J n).testBit (12 * e + i) = true := by
  intro n
  induction n with
  | zero => intro e he; omega
  | succ n ih =>
    intro e he hx
    show ((cond (tb x n) (J <<< (12 * n)) 0) ||| rect x J n).testBit (12 * e + i) = true
    rw [Nat.testBit_or]
    by_cases hen : e = n
    · subst hen
      rw [tb_eq, hx]
      simp [Nat.testBit_shiftLeft, hJ]
    · rw [ih e (by omega) hx]
      simp

theorem rectW_tb (x e i : ℕ) (he : e < 12) (hi : i < 12) (h1 : x.testBit e = true)
    (h2 : x.testBit (12 + i) = false) : (rectW x).testBit (12 * e + i) = true := by
  apply rect_tb _ _ _ _ 12 e he h1
  show ((x >>> 12) ^^^ 4095).testBit i = true
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, h2, tb4095]
  simp [hi]

def full : ℕ := 22300745198530623141535718272648361505980415

theorem full_eq : full = 2 ^ 144 - 1 := by norm_num [full]

theorem tb_land (a b q : ℕ) : (Nat.land a b).testBit q = (a.testBit q && b.testBit q) :=
  Nat.testBit_and a b q

theorem tb_lor (a b q : ℕ) : (Nat.lor a b).testBit q = (a.testBit q || b.testBit q) :=
  Nat.testBit_or a b q

theorem tb_xor (a b q : ℕ) : (Nat.xor a b).testBit q = Bool.xor (a.testBit q) (b.testBit q) :=
  Nat.testBit_xor a b q

theorem full_tb (q : ℕ) : full.testBit q = decide (q < 144) := by
  rw [full_eq, Nat.testBit_two_pow_sub_one]

theorem land_sub (h a : ℕ) (H : ∀ q, h.testBit q = true → a.testBit q = true) :
    Nat.land h a = h := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land]
  cases hh : h.testBit q
  · rfl
  · rw [H q hh]; rfl

theorem land_disj (a h : ℕ) (H : ∀ q, a.testBit q = true → h.testBit q = true → False) :
    Nat.land a h = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land, Nat.zero_testBit]
  cases ha : a.testBit q
  · rfl
  · cases hh : h.testBit q
    · rfl
    · exact (H q ha hh).elim

def orS (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x s)

def orSL (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x s)

theorem orS_tb (x s q : ℕ) : (orS x s).testBit q = (x.testBit q || x.testBit (s + q)) := by
  show (x ||| x >>> s).testBit q = _
  rw [Nat.testBit_or, Nat.testBit_shiftRight]

theorem orSL_tb (x s q : ℕ) :
    (orSL x s).testBit q = (x.testBit q || (decide (s ≤ q) && x.testBit (q - s))) := by
  show (x ||| x <<< s).testBit q = _
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]

theorem orS_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ p.testBit (k * j + q) = true) (q : ℕ)
    (h : (orS x (k * s)).testBit q = true) : ∃ j, j < n + s ∧ p.testBit (k * j + q) = true := by
  rw [orS_tb, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨j, hj, hp⟩ := hx q h
    exact ⟨j, by omega, hp⟩
  · obtain ⟨j, hj, hp⟩ := hx _ h
    refine ⟨j + s, by omega, ?_⟩
    rw [Nat.mul_add, Nat.add_assoc]; exact hp

theorem orSL_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true)
    (q : ℕ) (h : (orSL x (k * s)).testBit q = true) :
    ∃ j, j < n + s ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true := by
  rw [orSL_tb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨hs, h⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx q h
    exact ⟨j, by omega, hq, hp⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx _ h
    have e : q - k * (j + s) = q - k * s - k * j := by rw [Nat.mul_add]; omega
    refine ⟨j + s, by omega, ?_, ?_⟩
    · rw [Nat.mul_add]; omega
    · rw [e]; exact hp

def rowM : ℕ := 5445847423328601499764522166702896582657

theorem rowM_tb (q : ℕ) (h : rowM.testBit q = true) : q < 144 ∧ q % 12 = 0 := by
  have hlt : q < 144 := by
    by_contra hq
    have h0 : rowM.testBit q = false := by
      apply Nat.testBit_lt_two_pow
      have h1 : rowM < 2 ^ 144 := by norm_num [rowM]
      have h2 : (2 : ℕ) ^ 144 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [h0] at h
    exact Bool.noConfusion h
  have hall : ∀ q : ℕ, q < 144 → rowM.testBit q = true → q % 12 = 0 := by decide +kernel
  exact ⟨hlt, hall q hlt h⟩

def rowsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 6) 3) 1) 1) rowM

def colsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 96) 48) 24) 12) 4095

def hullC (p : ℕ) : ℕ :=
  Nat.land (orSL (orSL (orSL (orSL (rowsOf p) 6) 3) 1) 1)
    (orSL (orSL (orSL (orSL (colsOf p) 96) 48) 24) 12)

def hull (p : ℕ) : ℕ := hullC (Nat.land p full)

theorem rowsOf_tb (p q : ℕ) (h : (rowsOf p).testBit q = true) :
    (q < 144 ∧ q % 12 = 0) ∧ ∃ j, j < 12 ∧ p.testBit (j + q) = true := by
  unfold rowsOf at h
  rw [tb_land, Bool.and_eq_true] at h
  refine ⟨rowM_tb q h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (1 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 1 p _ 1 6 h0
  have h2 := orS_ex 1 p _ _ 3 h1
  have h3 := orS_ex 1 p _ _ 1 h2
  have h4 := orS_ex 1 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, by simpa using hp⟩

theorem colsOf_tb (p q : ℕ) (h : (colsOf p).testBit q = true) :
    q < 12 ∧ ∃ j, j < 16 ∧ p.testBit (12 * j + q) = true := by
  unfold colsOf at h
  rw [tb_land, Bool.and_eq_true, tb4095, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (12 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 12 p _ 1 8 h0
  have h2 := orS_ex 12 p _ _ 4 h1
  have h3 := orS_ex 12 p _ _ 2 h2
  have h4 := orS_ex 12 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, hp⟩

theorem hullC_spec (p : ℕ) (hp : ∀ q, p.testBit q = true → q < 144) (q : ℕ)
    (h : (hullC p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  unfold hullC at h
  rw [tb_land, Bool.and_eq_true] at h
  obtain ⟨hR, hC⟩ := h
  have r0 : ∀ q, (rowsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 1 * j ≤ q ∧ (rowsOf p).testBit (q - 1 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have r1 := orSL_ex 1 (rowsOf p) _ 1 6 r0
  have r2 := orSL_ex 1 (rowsOf p) _ _ 3 r1
  have r3 := orSL_ex 1 (rowsOf p) _ _ 1 r2
  have r4 := orSL_ex 1 (rowsOf p) _ _ 1 r3
  obtain ⟨j, hj, hjq, hr⟩ := r4 q hR
  obtain ⟨⟨hb, hm⟩, i, hi, hpi⟩ := rowsOf_tb p _ hr
  have c0 : ∀ q, (colsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 12 * j ≤ q ∧ (colsOf p).testBit (q - 12 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have c1 := orSL_ex 12 (colsOf p) _ 1 8 c0
  have c2 := orSL_ex 12 (colsOf p) _ _ 4 c1
  have c3 := orSL_ex 12 (colsOf p) _ _ 2 c2
  have c4 := orSL_ex 12 (colsOf p) _ _ 1 c3
  obtain ⟨j', hj', hjq', hc⟩ := c4 q hC
  obtain ⟨hlt, e', he', hpe⟩ := colsOf_tb p _ hc
  have e1 : i + (q - 1 * j) = 12 * (q / 12) + i := by omega
  have e2 : q - 12 * j' = q % 12 := by omega
  rw [e1] at hpi
  rw [e2] at hpe
  have hb' := hp _ hpe
  exact ⟨by omega, i, e', hi, by omega, hpi, hpe⟩

theorem hull_spec (p q : ℕ) (h : (hull p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  have hp : ∀ q, (Nat.land p full).testBit q = true → q < 144 := by
    intro q hq
    rw [tb_land, full_tb, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2
  obtain ⟨h1, i, e', hi, he, ha, hb⟩ := hullC_spec _ hp q h
  rw [tb_land, Bool.and_eq_true] at ha hb
  exact ⟨h1, i, e', hi, he, ha.1, hb.1⟩

def tw : List ℕ → ℕ → ℕ → ℕ
  | [], _, t => t
  | a :: l, o, t => tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))

def priv (t a : ℕ) : ℕ := hull (Nat.land a (Nat.xor t full))

def hullsOK (t : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, acc => Nat.beq (Nat.land (priv t a) a) (priv t a) &&
      (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a)))

def avOK1 (as : List ℕ) : Bool := hullsOK (tw as 0 0) as 0

def orL : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.lor a (orL l)

def rectOK1 (l : List ℕ) : Bool := avOK1 (l.map rectW)

def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')

def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
  (∀ z ∈ zs, IsRect z.1) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → q < 144) ∧
  (zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)) ∧
  (∀ q, q < 144 → ∃ z ∈ zs, z.1 q) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true)

theorem Part.rect {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, IsRect z.1 := h.1

theorem Part.bnd {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → q < 144 := h.2.1

theorem Part.disj {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) := h.2.2.1

theorem Part.cov {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ q, q < 144 → ∃ z ∈ zs, z.1 q := h.2.2.2.1

theorem Part.sub {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true := h.2.2.2.2

theorem pw_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ l : List α, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
    intro h a ha b hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha']; exact h.1 b hb'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb']; exact hs _ _ (h.1 a ha')
      · exact ih h.2 a ha' b hb' hab

theorem tw_spec (q : ℕ) : ∀ (as : List ℕ) (o t : ℕ), (tw as o t).testBit q = false →
    t.testBit q = false ∧ (o.testBit q = true → ∀ a ∈ as, a.testBit q = false) ∧
    as.Pairwise (fun a b => ¬ (a.testBit q = true ∧ b.testBit q = true)) := by
  intro as
  induction as with
  | nil => intro o t h; exact ⟨h, fun _ a ha => by simp at ha, List.Pairwise.nil⟩
  | cons a l ih =>
    intro o t h
    obtain ⟨h1, h2, h3⟩ := ih (Nat.lor o a) (Nat.lor t (Nat.land o a)) h
    rw [tb_lor, Bool.or_eq_false_iff, tb_land] at h1
    refine ⟨h1.1, ?_, ?_⟩
    · intro ho b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have h4 := h1.2
        rw [ho] at h4
        simpa using h4
      · exact h2 (by rw [tb_lor, ho]; rfl) b hb
    · refine List.pairwise_cons.mpr ⟨?_, h3⟩
      intro b hb hab
      have h4 := h2 (by rw [tb_lor, hab.1]; simp) b hb
      rw [h4] at hab
      exact Bool.noConfusion hab.2

theorem priv_in {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) : ∀ z ∈ zs, ∀ q,
    (priv (tw (zs.map Prod.snd) 0 0) z.2).testBit q = true → z.1 q := by
  intro z hz q hq
  obtain ⟨hq144, i, e', hi, he', ha, hb⟩ := hull_spec _ q hq
  have key : ∀ x, x < 144 →
      (Nat.land z.2 (Nat.xor (tw (zs.map Prod.snd) 0 0) full)).testBit x = true → z.1 x := by
    intro x hx hbit
    rw [tb_land, tb_xor, full_tb, Bool.and_eq_true] at hbit
    obtain ⟨hzx, ht⟩ := hbit
    have ht' : (tw (zs.map Prod.snd) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_, _, hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z', hz', hzq⟩ := hP.cov x hx
    by_cases hzz : z' = z
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2, h'.1⟩) zs hpw z' hz' z hz hzz
        ⟨hP.sub z' hz' x hzq, hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hP.rect z hz (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

theorem hullsOK_sound (t : ℕ) : ∀ (zs : List ((ℕ → Prop) × ℕ)) (acc : ℕ),
    (∀ z ∈ zs, ∀ q, (priv t z.2).testBit q = true → z.1 q) →
    (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true) →
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) →
    (∀ q, acc.testBit q = true → ∀ z ∈ zs, ¬ z.1 q) →
    hullsOK t (zs.map Prod.snd) acc = true := by
  intro zs
  induction zs with
  | nil => intros; rfl
  | cons z zs ih =>
    intro acc hh hs hd ha
    rw [List.pairwise_cons] at hd
    have hz := hh z List.mem_cons_self
    have e1 := land_sub _ _ (fun q hq => hs z List.mem_cons_self q (hz q hq))
    have e2 := land_disj acc (priv t z.2) (fun q h1 h2 => ha q h1 z List.mem_cons_self (hz q h2))
    have e3 := ih (Nat.lor acc (priv t z.2)) (fun z' hz' => hh z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' => hs z' (List.mem_cons_of_mem _ hz')) hd.2 (fun q hq z' hz' hz'q => by
        rw [tb_lor, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact ha q hq z' (List.mem_cons_of_mem _ hz') hz'q
        · exact hd.1 z' hz' q (hz q hq) hz'q)
    show (Nat.beq (Nat.land (priv t z.2) z.2) (priv t z.2) &&
      (Nat.beq (Nat.land acc (priv t z.2)) 0 &&
        hullsOK t (zs.map Prod.snd) (Nat.lor acc (priv t z.2)))) = true
    rw [e1, e2, e3, Nat.beq_refl]
    rfl

theorem avOK1_sound {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    avOK1 (zs.map Prod.snd) = true :=
  hullsOK_sound _ zs 0 (priv_in hP) hP.sub hP.disj (fun q hq => by simp at hq)

end PackedRect

def witnessWord (w : (Nat × Nat × Nat)) : Nat := w.1

def essentialB (mask target : Nat) (stock : List Nat) (entry : (Nat × Nat × Nat)) : Bool :=
  let (w,p,n) := entry
  mask.testBit p && mask.testBit n && target.testBit p && !target.testBit n &&
    (w.testBit p != w.testBit n) &&
    stock.all (fun x => x == w || x.testBit p == x.testBit n)

theorem essentialRequired {stock : List Nat} {entry : (Nat × Nat × Nat)} {S : Finset Nat} {k t : Nat}
    (ok : essentialB mask target stock entry = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    witnessWord entry ∈ S := by
  obtain ⟨w,p,n⟩ := entry
  simp only [essentialB, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp,mn⟩,tp⟩,tn⟩,unequal⟩,rest⟩ := ok
  by_contra no
  have all : ∀ x ∈ S, AgreesAt p n x := by
    intro x hx
    have h := List.all_eq_true.mp rest x (sub x hx)
    have hw : x ≠ w := fun e => no (by simpa [witnessWord, e] using hx)
    simpa [hw, AgreesAt] using h
  have agree := liveAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n = false := by simpa using tn
  simp [AgreesAt, tp, falseBit] at agree

theorem essentialWordsIn {stock : List Nat} {witnesses : List (Nat × Nat × Nat)} {S : Finset Nat} {k t : Nat}
    (ok : witnesses.all (essentialB mask target stock) = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    (witnesses.map witnessWord).toFinset ⊆ S := by
  intro w hw
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  exact essentialRequired (List.all_eq_true.mp ok entry mem) sub live

theorem essentialLower {stock : List Nat} {witnesses : List (Nat × Nat × Nat)} {minimum : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (bound : minimum ≤ (witnesses.map witnessWord).toFinset.card - 1) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have card := Finset.card_le_card (essentialWordsIn ok sub live)
  have size := (liveWordSize live).2
  omega

theorem essentialLift {stock cutStock : List Nat} {witnesses : List (Nat × Nat × Nat)} {minimum cut prior : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (submask : mask &&& cut = cut)
    (cutProper : properWord cut (target &&& cut))
    (supplies : ∀ w ∈ stock, AvailableWord cut cutStock (w &&& cut))
    (known : Lower cut cutStock (target &&& cut) prior)
    (bound : minimum ≤ prior + (flatSet cut (witnesses.map witnessWord).toFinset).card) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have subW := essentialWordsIn ok sub live
  have subFlat : flatSet cut (witnesses.map witnessWord).toFinset ⊆ flatSet cut S :=
    Finset.filter_subset_filter _ subW
  have card := Finset.card_le_card subFlat
  have pf : ¬maskedFlat cut target := by simpa [maskedFlat, properWord] using cutProper
  obtain ⟨n, budget, built⟩ := maskedBuild live cut submask pf
  have starts : ∀ w ∈ projectedStock cut S, AvailableWord cut cutStock w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | rfl | ⟨x,hx,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact supplies _ (sub _ hx)
  obtain ⟨ys,len,built',out⟩ := buildableWords built starts
  have lower := known ys built' out
  omega

def unpackWitnesses (stock : List Nat) (codes : List Nat) : List (Nat × Nat × Nat) :=
  List.rec [] (fun code _ rest =>
    (stock.getD (code >>> 18) 0, (code >>> 9) &&& 511, code &&& 511) :: rest) codes

def DagAuto (mask goal : Nat) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal

def mixStep (m : (List (Nat × Nat) × List (Nat × Nat))) (w : Nat) : Nat :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right

def BitLinear (f : Nat → Nat) : Prop :=
  ∀ w i, (f w).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (2 ^ j)).testBit i = true

theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]

theorem bitLinearOr {f g : Nat → Nat} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  rw [hf w i, hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩

theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩

theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩

theorem mixStepLinear (move : (List (Nat × Nat) × List (Nat × Nat))) : BitLinear (mixStep move) := by
  obtain ⟨left, right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih

def mixMove (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (w : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) id
    (fun step _ next w => next (mixStep step w)) move) w

theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j, w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]

theorem bitLinearComp {f g : Nat → Nat} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩ := (hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩ := (hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩

theorem mixMoveLinear (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : BitLinear (mixMove move) := by
  induction move with
  | nil => exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w => mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)

def permuteAxes (axes : List Nat) (offset row : Nat) : Nat :=
  offset ^^^ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun j _ next i => (if row.testBit i then 1 <<< j else 0) ||| next (i + 1)) axes) 0

theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select) := by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows := ⟨i,inside⟩
    change (relabel select w).testBit ii.val = true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val = true
      rw [relabelBit, Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit, Nat.testBit_two_pow, decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]

theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Nat} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear, relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and, bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩

theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i, inverse (select i) = i) :
    ∀ j : Fin rows, select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp, right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside), Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]

theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))}
    (left : ∀ i, inverse (select i) = i)
    (right : ∀ i, select (inverse i) = i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w, Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Nat} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩

theorem maskedBelow {mask w : Nat} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]

theorem maskedTransfer {mask w : Nat} {select : Fin rows → Fin rows}
    (same : relabel select mask = mask) (hw : Masked mask w) :
    Masked mask (relabel select w) := by
  unfold Masked at *
  rw [← same, ← relabelAnd, hw]

theorem liveMaskedImage {mask goal : Nat} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k t : Nat} {S : Finset Nat} (live : LiveWord mask goal k t S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveWord mask goal k t (S.image (relabel select)) := by
  let f := relabel select
  have hmask : f mask = mask := auto.2.1
  have inj {a b : Nat} (ma : Masked mask a) (mb : Masked mask b) :
      f a = f b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have proper {a : Nat} (ma : Masked mask a) (ha : properWord mask a) :
      properWord mask (f a) := by
    exact ⟨fun eq => ha.1 (inj ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (inj ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {S : Finset Nat} {v : Nat} (hv : v ∉ S) (mv : Masked mask v)
      (ms : ∀ w ∈ S, Masked mask w) : f v ∉ S.image f := by
    intro hw
    obtain ⟨w,hs,eq⟩ := Finset.mem_image.mp hw
    exact hv (inj (ms w hs) mv eq ▸ hs)
  induction live using LiveWord.ind with
  | stop hp =>
    rw [Finset.image_singleton, auto.2.2]
    exact LiveWord.stop hp
  | @unary k t U a ha fresh tail ih =>
    let v := mask ^^^ a
    have ma := masked a (Finset.mem_insert_self ..)
    have mv : Masked mask v := by
      apply maskedGate (bank := [a]) (by simpa using ma)
      exact Or.inl ⟨a, Or.inr (Or.inr (by simp)), rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem hU)
    have fve : f v = mask ^^^ f a := by
      change relabel select (mask ^^^ a) = _
      rw [relabelXor, auto.2.1]
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) (t+1) ((insert a U).image f)
    rw [Finset.image_insert] at ht hf
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht hf
    rw [Finset.image_insert]
    exact LiveWord.unary (proper ma ha) hf ht
  | @binary k t U a b op pa pb ab fresh tail ih =>
    let v := binWord op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply maskedGate (bank := [a,b]) (by simpa using And.intro ma mb)
      exact Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by
        cases op <;> simp [v, binWord]⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have fve : f v = binWord op (f a) (f b) := by
      cases op
      · exact relabelAnd ..
      · exact relabelOr ..
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) t ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveWord.binary (proper ma pa) (proper mb pb) (fun h => ab (inj ma mb h)) hf ht

def dagMoveWords (m : (List (List (Nat × Nat) × List (Nat × Nat)))) (ws : List Nat) : List Nat :=
  List.rec [] (fun w _ next => insertWord (mixMove m w) next) ws

theorem dagMoveSet {m : (List (List (Nat × Nat) × List (Nat × Nat)))} {ws : List Nat} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWords m ws).toFinset = ws.toFinset.image (relabel select) := by
  induction ws with
  | nil => simp [dagMoveWords]
  | cons w ws ih =>
    change (insertWord (mixMove m w) (dagMoveWords m ws)).toFinset = _
    rw [insertWordSet, ih (fun w hw => agree _ (List.mem_cons_of_mem _ hw)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]

def chartRow (chart : ({ rows : List Nat // rows.length = 24 })) (i : Nat) : Nat :=
  chart.val.getD i 0

def chartBits (w : Nat) (rows : List Nat) : Nat :=
  List.rec 0 (fun r _ packed => ((w >>> r) &&& 1) ||| (packed <<< 1)) rows

theorem chartBitsBit (w : Nat) (rows : List Nat) (i : Nat) (hi : i < rows.length) :
    (chartBits w rows).testBit i = w.testBit (rows.getD i 0) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
    change (((w >>> row) &&& 1) ||| (chartBits w rows <<< 1)).testBit i = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have lt : i < rows.length := by simpa using hi
      simp [ih i lt, Nat.testBit_succ]

def chartWord (chart : ({ rows : List Nat // rows.length = 24 })) (w : Nat) : Nat := chartBits w chart.val

def ChartOK (goal : Nat) (chart : ({ rows : List Nat // rows.length = 24 })) : Prop :=
  (∀ i : Fin 12, goal.testBit (chartRow chart i.val) = true) ∧
  (∀ i : Fin 12, goal.testBit (chartRow chart (12+i.val)) = false)

def chartCheck (goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) : Bool :=
  chart.all fun c => @decide (ChartOK goal c) (by unfold ChartOK; infer_instance)

theorem chartOfCheck {goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    (ok : chartCheck goal chart = true) (c : ({ rows : List Nat // rows.length = 24 })) (eq : chart = some c) :
    ChartOK goal c := by
  subst chart
  unfold ChartOK
  exact of_decide_eq_true ok

theorem chartWordBit (chart : ({ rows : List Nat // rows.length = 24 })) (w : Nat) {i : Nat} (hi : i < 24) :
    (chartWord chart w).testBit i = w.testBit (chartRow chart i) := by
  exact chartBitsBit w chart.val i (by rw [chart.property]; exact hi)

theorem chartPos {goal : Nat} {chart : ({ rows : List Nat // rows.length = 24 })} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart i) = true := ok.1 ⟨i,hi⟩

theorem chartNeg {goal : Nat} {chart : ({ rows : List Nat // rows.length = 24 })} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart (12+i)) = false := ok.2 ⟨i,hi⟩

theorem chartRectangles {goal : Nat} {chart : ({ rows : List Nat // rows.length = 24 })} {ws : List Nat}
    (ok : ChartOK goal chart) (nd : ws.Nodup) (kw : KWPartition goal ws.toFinset) :
    PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨f, good, rectangle⟩ := kw
  let label := fun p n => f (chartRow chart p) (chartRow chart (12+n))
  let part := fun w => ((fun q : Nat => q < 144 ∧ label (q/12) (q % 12) = w),
    PackedRect.rectW (chartWord chart w))
  have partition : PackedRect.Part (ws.map part) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro z hz
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      intro p n p' n' hp hn hp' hn' h h'
      have divmod (a b : Nat) (lt : b < 12) :
          (12*a+b)/12 = a ∧ (12*a+b)%12 = b := by omega
      have h1 := h.2
      have h2 := h'.2
      rw [(divmod p n hn).1, (divmod p n hn).2] at h1
      rw [(divmod p' n' hn').1, (divmod p' n' hn').2] at h2
      refine ⟨by omega,?_⟩
      rw [(divmod p n' hn').1, (divmod p n' hn').2]
      exact (rectangle _ _ _ _ (chartPos ok hp) (chartPos ok hp') (chartNeg ok hn)
        (chartNeg ok hn') (h1.trans h2.symm)).trans h1
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      exact hq.1
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun hne q h1 h2 => hne (h1.2.symm.trans h2.2)) nd
    · intro q hq
      have member := (good _ _ (chartPos ok (show q/12 < 12 by omega))
        (chartNeg ok (Nat.mod_lt q (by decide : 0 < 12)))).1
      exact ⟨_, List.mem_map.mpr ⟨_,List.mem_toFinset.mp member,rfl⟩,hq,rfl⟩
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      obtain ⟨bound, same⟩ := hq
      have hp : q/12 < 12 := by omega
      have hn : q % 12 < 12 := Nat.mod_lt _ (by decide)
      have h := (good _ _ (chartPos ok hp) (chartNeg ok hn)).2
      change (label (q/12) (q % 12)).testBit (chartRow chart (q/12)) = true ∧
        (label (q/12) (q % 12)).testBit (chartRow chart (12+q % 12)) = false at h
      rw [same] at h
      have bit := PackedRect.rectW_tb (chartWord chart w) (q/12) (q % 12) hp hn
        ((chartWordBit chart w (by omega)).trans h.1)
        ((chartWordBit chart w (by omega)).trans h.2)
      rwa [Nat.div_add_mod] at bit
  have hw := PackedRect.avOK1_sound partition
  simpa only [PackedRect.rectOK1, List.map_map, Function.comp_def, part] using hw

theorem tightChart {goal mask : Nat} {chart : ({ rows : List Nat // rows.length = 24 })} {ws : List Nat} {fuel : Nat}
    (ok : ChartOK goal chart) (tight : ws.length = fuel + 1)
    (viable : WordViable mask goal (fuel,ws,[])) : PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change (ws : List Nat).length + t ≤ k + 1 at card
  have ht : t = 0 := by omega
  have hk : ws.toFinset.card = k + 1 := by
    have q : ws.toFinset.card = ws.length := List.toFinset_card_of_nodup nd
    omega
  subst t
  exact chartRectangles ok nd (kwFromLive live hk)

def dagForceWord {α : Type} (word : Nat) (cont : Nat → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word

theorem dagForceWordEq {α : Type} (word : Nat) (cont : Nat → α) :
    dagForceWord word cont = cont word := by cases word <;> rfl

def dagForceWords (words : List Nat) (cont : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => dagForceWord w (fun v => next (fun rest => k (v :: rest)))) words) cont

theorem dagForceWordsEq (words : List Nat) (cont : List Nat → Bool) :
    dagForceWords words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change dagForceWord w (fun v => dagForceWords ws (fun rest => cont (v :: rest))) = _
    rw [dagForceWordEq, ih]

def dagBoundCloses (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStart mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosure mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipes mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)

theorem dagBoundClosesEq (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) :
    dagBoundCloses target state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨mask, stock, lower, goal⟩ := bound
  simp [dagBoundCloses, boundCloses, dagForceWordsEq, dagForceWordEq, Nat.blt_eq]

def dagKnownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  List.rec false (fun bound _ later => dagBoundCloses target state bound || later) bounds

theorem dagKnownClosesEq (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) :
    dagKnownCloses target bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundCloses target state bound || dagKnownCloses target bounds state) =
      (boundCloses target state bound || knownCloses target bounds state)
    rw [dagBoundClosesEq, ih]

def dagAllowedRoot (witnesses : List (Nat × Nat × Nat)) (ws : List Nat) : Bool :=
  witnesses.all (fun entry => ws.contains (witnessWord entry))

def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : (Nat → Nat × Nat))
    (i : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ previous j =>
      let (parent, token) := forest j
      if parent == 0 then
        if token < 2 ^ stock.length then some (rootState stock fuel token) else none
      else (previous (parent - 1)).bind (childState mask token)) (fuel + 1)) i

def dagRef (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) (links : (Nat → Nat → Option (Nat × Nat))) (parent token : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  match links parent token with
  | none => false
  | some (destination, auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto-1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWords m state.2.1

def dagPartition (directed : Bool) (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      dagForceWord (p &&& w) (fun up =>
        dagForceWord (n &&& w) (fun down =>
          rest up down &&
            dagForceWord (p ^^^ up) (fun offP =>
              dagForceWord (if directed then n else n ^^^ down) (rest offP))))) ws

theorem dagOffBits {v w : Nat} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at bit ⊢

theorem dagPartitionSound {directed : Bool} {ws : List Nat} {positive negative : Nat}
    (fail : dagPartition directed ws positive negative = false) :
    ∃ p n, positive.testBit p = true ∧ negative.testBit n = true ∧
      ∀ w ∈ ws, if directed then w.testBit p = true → w.testBit n = true
                  else w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all
    apply hn
    apply Nat.eq_of_testBit_eq
    intro i
    simp [all i]
  induction ws generalizing positive negative with
  | nil =>
    change (Nat.beq positive 0 || Nat.beq negative 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p,hp⟩ := nonempty (w := positive) (fun eq => by simp [eq] at fail)
    obtain ⟨n,hn⟩ := nonempty (w := negative) (fun eq => by simp [eq] at fail)
    exact ⟨p,n,hp,hn,by simp⟩
  | cons w ws ih =>
    change (Nat.beq positive 0 || Nat.beq negative 0 ||
      dagForceWord (positive &&& w) (fun up =>
        dagForceWord (negative &&& w) (fun down =>
          dagPartition directed ws up down &&
            dagForceWord (positive ^^^ up) (fun offP =>
              dagForceWord (if directed then negative else negative ^^^ down)
                (dagPartition directed ws offP))))) = false at fail
    simp only [dagForceWordEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2, hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := dagOffBits hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply dagOffBits
          simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2, hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n = true := by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn',?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail

theorem dagPartitionLive {mask goal : Nat} {ws : List Nat} {k t : Nat} {directed : Bool}
    (goalMask : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) :
    dagPartition directed ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : dagPartition directed ws goal (mask ^^^ goal) = false := by
    cases h : dagPartition directed ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p,n,hp,hn,agree⟩ := dagPartitionSound openPair
  have pm := positiveInMask goalMask hp
  have nm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have implied := fun ht : goal.testBit n = true => positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  cases mode : directed with
  | false =>
    have same := liveAgrees live (pm.trans nm.1.symm) (fun w hw => by
      simpa [mode,AgreesAt] using agree w (List.mem_toFinset.mp hw))
    simp [AgreesAt, hp, nm.2] at same
  | true =>
    have ht := noNot mode
    subst t
    obtain ⟨w,hw,a,b⟩ := liveDirected live hp nm.2
    have same := agree w (List.mem_toFinset.mp hw)
    simp [mode, a, b] at same

def dagForceCache (tags : List (Nat × Nat)) (use : List (Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => (List (Nat × Nat) → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      dagForceWord tag.1 (fun up => dagForceWord tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use

theorem dagForceCacheEq (tags : List (Nat × Nat)) (use : List (Nat × Nat) → Bool) :
    dagForceCache tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change dagForceWord a (fun up => dagForceWord b (fun down =>
      dagForceCache rest (fun tail => use ((up,down)::tail)))) = _
    simp only [dagForceWordEq, ih]

def dagSignalContrast (directed : Bool) (full : Nat) (tag : (Nat × Nat)) : Nat :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2

def dagCountStep (acc : (Nat × Nat × Nat)) (column : Nat) : (Nat × Nat × Nat) :=
  (acc.1 ||| column, acc.2.1 ||| (acc.1 &&& column), acc.2.2 ||| (acc.2.1 &&& column))

def dagCountSigns (directed : Bool) (full : Nat) (tags : List (Nat × Nat))
    (use : (Nat × Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => ((Nat × Nat × Nat) → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      dagForceWord (dagSignalContrast directed full tag) (fun column =>
        more (fun acc =>
          dagForceWord (acc.1 ||| column) (fun once =>
            dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use

theorem dagCountSignsEq (directed : Bool) (full : Nat) (tags : List (Nat × Nat))
    (use : (Nat × Nat × Nat) → Bool) : dagCountSigns directed full tags use =
    use (tags.foldr (fun tag acc => dagCountStep acc (dagSignalContrast directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change dagForceWord (dagSignalContrast directed full tag) (fun column =>
      dagCountSigns directed full tags (fun acc =>
        dagForceWord (acc.1 ||| column) (fun once =>
          dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [dagForceWordEq, ih]
    rfl

def dagHighest (value : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      dagForceWord (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset+shift))) 8) value 0

def dagSampleMiss (sample : (Nat × Nat)) (full : Nat) (normal tight : (Nat × Nat × Nat))
    (x y out : (Nat × Nat)) (directed : Bool) (op keep : Nat) : List Nat :=
  let counts := if directed then tight else normal
  let dx := if keep.testBit 0 then 0 else dagSignalContrast directed full x
  let dy := if op == 2 || keep.testBit 1 then 0 else dagSignalContrast directed full y
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  dagForceWord ((rest ||| dagSignalContrast directed full out) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then [] else [unpack sample.1 18 (dagHighest missing)])

def dagPairReject (mask goal : Nat) (directed : Bool) (ws : List Nat) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)

theorem dagPairsOpen {mask goal : Nat} {ws : List Nat} {pairs : List Nat} {k t : Nat} {directed : Bool}
    (masked : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) : dagPairReject mask goal directed ws pairs = false := by
  apply Bool.eq_false_iff.mpr
  intro close
  obtain ⟨code,_,check⟩ := List.any_eq_true.mp close
  simp only [Bool.and_eq_true, Bool.not_eq_true, List.all_eq_true] at check
  obtain ⟨⟨⟨hp, mn⟩, hn⟩, bank⟩ := check
  have neg : goal.testBit (code >>> 9) = false := by simpa using hn
  cases mode : directed
  · have h := liveAgrees live ((positiveInMask masked hp).trans mn.symm) (fun w hw => by
      have pair := bank _ (List.mem_toFinset.mp hw)
      simpa [mode, AgreesAt] using pair)
    simp [AgreesAt, hp, neg] at h
  · have ht := noNot mode
    subst t
    obtain ⟨word,mem,on,off⟩ := liveDirected live hp neg
    have pair := bank _ (List.mem_toFinset.mp mem)
    simp [mode,on,off] at pair

def dagLocal (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 }))
    (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  let (fuel,ws,_) := state
  ws.length > fuel + 1 ||
    (!ws.contains goal &&
      (fuel == 0 ||
        (if ws.length == fuel + 1 then
           chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c)))
         else false) ||
        cut state ||
        (if ws.length == fuel + 1 then !dagPartition true ws goal (mask ^^^ goal)
         else !dagPartition false ws goal (mask ^^^ goal))))

def dagSizeFloor (n op keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) -
    (if op == 2 || keep.testBit 1 then 0 else 1)) + 1

def dagTooWide (n fuel token : Nat) : Bool :=
  dagSizeFloor n (token / 4 % 3) (token % 4) > (fuel-1) + 1

def dagKept (ws : List Nat) (op keep x y : Nat) : List Nat :=
  keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)

def dagGateWord (mask op x y : Nat) : Nat :=
  if Nat.beq op 0 then x &&& y else if Nat.beq op 1 then x ||| y else mask ^^^ x

def dagDirectChild (mask : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (a b op keep x y out : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, history) := state
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    some (fuel-1, insertWord out (dagKept ws op keep x y), (out,x,y) :: history)

theorem dagDirectChildEq {mask a b op keep : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (hb : b < 64) (hop : op < 3) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    dagDirectChild mask state a b op keep x y (dagGateWord mask op x y) =
      childState mask (gateToken a b op keep) state := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨keepEq,opEq,aEq,bEq⟩ := gateTokenFields (a := a) hb hop hk
  simp only [childState, keepEq, opEq, aEq, bEq]
  rfl

def dagTagBases (stock : List Nat) (positive negative width : Nat) : List (Nat × (Nat × Nat)) :=
  (List.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun w _ next i => (w, unpack positive width i, unpack negative width i) :: next (i+1)) stock) 0

def dagTagRoot (bank : List (Nat × (Nat × Nat))) (token : Nat) : List (Nat × (Nat × Nat)) :=
  (List.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token

def dagTagKeep (keep : Bool) (w : Nat) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank

def dagTagInsert (tag : (Nat × (Nat × Nat))) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank

def dagTagStep (mask full token : Nat) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  let keep := token % 4
  let op := token / 4 % 3
  let x := bank.getD (token / (4*3*64)) (0,0,0)
  let y := bank.getD (token / (4*3) % 64) (0,0,0)
  let tag := (dagGateWord mask op x.1 y.1, dagGateWord full op x.2.1 y.2.1, dagGateWord full op x.2.2 y.2.2)
  dagTagInsert tag (dagTagKeep (op == 2 || keep.testBit 1) y.1 (dagTagKeep (keep.testBit 0) x.1 bank))

def dagTraceTags (mask width : Nat) (root : List (Nat × (Nat × Nat))) (fuel : Nat) (forest : (Nat → Nat × Nat))
    (i : Nat) : List (Nat × Nat) :=
  let tags := (Nat.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun _ previous j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then dagTagRoot root token
      else dagTagStep mask (fullMask width) token (previous (parent-1))) (fuel+1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags

def dagPackWords (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ tail => (w &&& fullMask 512) ||| (tail <<< 512)) ws

def dagLaneMarks (n : Nat) : Nat :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 512)) n

def dagOmitted (a b : Nat) (left right : Bool) : Nat :=
  (if left then 0 else 1 <<< (512*a)) ||| (if right then 0 else 1 <<< (512*b))

def dagPackedPair (mask goal packed marks erased out : Nat) (directed : Bool) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    dagForceWord code (fun code =>
      dagForceWord (code &&& 511) (fun p =>
        dagForceWord (code >>> 9) (fun n =>
          let up := (packed >>> p) &&& marks
          let down := (packed >>> n) &&& marks
          let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
          let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
          goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 512 && Nat.blt n 512 &&
            gateOK && Nat.beq (contrast &&& (marks ^^^ erased)) 0)))

theorem dagPackBits {ws : List Nat} {i row : Nat} (inside : i < ws.length) (width : row < 512) :
    (dagPackWords ws).testBit (512*i+row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fullMask 512) ||| (dagPackWords ws <<< 512)).testBit (512*i+row) = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp [fullMask, Nat.testBit_two_pow_sub_one, width, Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 512 ≤ 512*i.succ+row := by omega
      have offset : 512*i.succ+row-512 = 512*i+row := by omega
      have past : ¬ 512*i.succ+row < 512 := by omega
      simp [crossed, offset, fullMask, Nat.testBit_two_pow_sub_one, past, ih hi]

theorem dagMarkBits {length i : Nat} (inside : i < length) :
    (dagLaneMarks length).testBit (512*i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (dagLaneMarks length <<< 512)).testBit (512*i) = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 512 ≤ 512*i.succ := by omega
      have offset : 512*i.succ-512 = 512*i := by omega
      simp [crossed, offset, ih hi]

def dagCheckChildren (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (reference : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (sample : (Nat × Nat)) (tags : List (Nat × Nat)) : Bool :=
  let n := state.2.1.length
  (n ≤ 64) && !state.2.1.contains goal &&
  dagForceWord (dagPackWords state.2.1) (fun packed =>
    dagForceWord (dagLaneMarks n) (fun marks =>
      dagForceCache tags (fun tags =>
    dagForceWord (fullMask sample.2) (fun full =>
      dagCountSigns false full tags (fun normal =>
        dagCountSigns true full tags (fun tight =>
          let visit := fun a b op retains =>
            dagForceWord (state.2.1.getD a 0) (fun x =>
              dagForceWord (state.2.1.getD b 0) (fun y =>
                dagForceWord (dagGateWord mask op x y) (fun out =>
                  let xs := tags.getD a (0,0)
                  let ys := tags.getD b (0,0)
                  dagForceWord (dagGateWord full op xs.1 ys.1) (fun up =>
                    dagForceWord (dagGateWord full op xs.2 ys.2) (fun down =>
                      treeBlock 0 retains (fun keep =>
                        let token := gateToken a b op keep
                        if dagTooWide n state.1 token then true else
                          let directed := dagSizeFloor n op keep == (state.1-1)+1
                          let pairs := dagSampleMiss sample full normal tight xs ys (up,down) directed op keep
                          let erased := dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)
                          if dagPackedPair mask goal packed marks erased out directed pairs then true
                          else match dagDirectChild mask state a b op keep x y out with
                          | none => true
                          | some (fuel, ws, history) => dagForceWords ws (fun forced =>
                            let child := (fuel, forced, history)
                            reference token child || dagLocal mask goal chart cut child)))))))
          treeBlock 0 n (fun a =>
            visit a a 2 2 && treeBlock (a+1) (n-(a+1)) (fun b =>
              treeBlock 0 2 (fun op => visit a b op 4)))))))))

def dagStateOK (mask : Nat) (ws : List Nat) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)

theorem dagStateOKSpec {mask : Nat} {ws : List Nat} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩

def dagCheckNode (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) (links : (Nat → Nat → Option (Nat × Nat)))
    (sample : (Nat × Nat)) (tags : Nat → List (Nat × Nat)) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) => dagForceWords ws (fun forced =>
      dagStateOK mask forced && dagCheckChildren mask goal chart cut
        (dagRef count states moves links (i+1)) (fuel, forced, history) sample (tags i))

def dagCheckRoots (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (witnesses : List (Nat × Nat × Nat)) (reference : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool) (stock : List Nat)
    (fuel : Nat) : Bool :=
  treeBlock 0 (2^stock.length) fun token =>
    let state := rootState stock fuel token
    !dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart cut state || reference token state

theorem dagLocalOpen {mask goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (masked : Masked mask goal) (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (viable : WordViable mask goal state) (noCut : cut state = false) :
    dagLocal mask goal chart cut state = false := by
  obtain ⟨fuel,ws,history⟩ := state
  have ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change ws.length + t ≤ k + 1 at card
  have fit : ¬ ws.length > fuel + 1 := by omega
  by_cases hz : fuel = 0
  · have kz : k = 0 := by omega
    subst k
    obtain ⟨_,eq,_⟩ := live
    have hm : goal ∈ ws := List.mem_toFinset.mp (by rw [eq]; simp)
    simp [dagLocal, fit, hm]
  by_cases tight : ws.length = fuel + 1
  · have ht : t = 0 := by omega
    subst t
    have dir := dagPartitionLive (directed := true) masked live (fun _ => rfl)
    have noChart : chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c))) = false := by
      cases opt : chart with
      | none => rfl
      | some c =>
        have vt : WordViable mask goal (fuel,ws,[]) := viable
        have ok := tightChart (chartOK c opt) tight vt
        simp [ok]
    simp [dagLocal, fit, hz, tight, dir, noCut, noChart]
  · have sep := dagPartitionLive (directed := false) masked live (by simp)
    simp [dagLocal, fit, hz, tight, sep, noCut]

theorem dagInsertLength (w : Nat) (ws : List Nat) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]

theorem dagKeepLength (keep : Bool) (w : Nat) (ws : List Nat) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]

theorem dagWideChild {mask token : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (eval : childState mask token state = some child)
    (wide : dagTooWide state.2.1.length state.1 token = true) :
    child.2.1.length > child.1 + 1 := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let i := token / (4 * 3 * 64)
  let j := token / (4 * 3) % 64
  let x := ws.getD i 0
  let y := ws.getD j 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let a := keep.testBit 0
  let b := op == 2 || keep.testBit 1
  let rest := keepWord b y (keepWord a x ws)
  let bad : Bool := fuel == 0 || j ≥ ws.length || (if op == 2 then i != j || keep ≥ 2 else i ≥ j)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  rw [← eq]
  change (insertWord z rest).length > fuel - 1 + 1
  rw [dagInsertLength]
  have h1 := dagKeepLength a x ws
  have h2 := dagKeepLength b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega

theorem dagKeepMem {ws : List Nat} {x w : Nat} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord, nd.mem_erase_iff, and_comm] using h
  · simpa [keepWord] using h

theorem dagKeepNodup {ws : List Nat} (nd : ws.Nodup) (keep : Bool) (x : Nat) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd

theorem dagPackedPairSound {mask goal out : Nat} {ws : List Nat} {directed : Bool}
    {pairs : List Nat} {a b : Nat} {left right : Bool}
    (nd : ws.Nodup)
    (checked : dagPackedPair mask goal (dagPackWords ws) (dagLaneMarks ws.length)
      (dagOmitted a b left right) out directed pairs = true) :
    dagPairReject mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) pairs = true := by
  obtain ⟨code,mem,verdict⟩ := List.any_eq_true.mp checked
  apply List.any_eq_true.mpr
  refine ⟨code,mem,?_⟩
  simp only [dagForceWordEq, Bool.and_eq_true, Nat.blt_eq] at verdict
  obtain ⟨⟨⟨⟨⟨⟨hp, hn⟩, neg⟩, wp⟩, wn⟩, output⟩, closure⟩ := verdict
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp,hn⟩,neg⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := dagKeepMem (dagKeepNodup nd left (ws.getD a 0)) later
  have leftMem := dagKeepMem nd rightMem.1
  obtain ⟨i,inside,eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside] using eq
  have omitted : (dagOmitted a b left right).testBit (512*i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (512*j)).testBit (512*i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, show 512*j ≠ 512*i by omega]
    simp [dagOmitted, Nat.testBit_or, cleared a left leftMem.2, cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := dagLaneMarks ws.length
  let signal := dagPackWords ws
  have mark : marks.testBit (512*i) = true := dagMarkBits inside
  have test {j : Nat} (within : j < 512) :
      ((signal >>> j) &&& marks).testBit (512*i) = w.testBit j := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, mark, Bool.and_true,
      Nat.add_comm j, dagPackBits inside within, atIndex]
  have h := congrArg (fun word => Nat.testBit word (512*i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ dagOmitted a b left right)).testBit (512*i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px,nx,pt,nt,Nat.testBit_and,Nat.testBit_xor,mark,omitted,p,n] at h ⊢

theorem dagEarlyOpen {mask goal a b op keep out : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (masked : Masked mask goal) (viable : WordViable mask goal child)
    (parent : state.2.1.Nodup) (eval : dagDirectChild mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) (pairs : List Nat) :
    dagPackedPair mask goal (dagPackWords state.2.1) (dagLaneMarks state.2.1.length)
      (dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)) out
      (dagSizeFloor state.2.1.length op keep == (state.1-1)+1) pairs = false := by
  obtain ⟨fuel,ws,history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  have closed := dagPackedPairSound parent closed
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := out == 0 || out == mask || ws.contains out
  let bank := dagKept ws op keep x y
  change (if bad then none else if stale then none else
    some (fuel-1, insertWord out bank, (out,x,y)::history)) = some child at eval
  by_cases h : bad = true
  · simp [h] at eval
  by_cases h' : stale = true
  · simp [h,h'] at eval
  have eq : (fuel-1,insertWord out bank,(out,x,y)::history) = child := by simpa [h,h'] using eval
  subst child
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel-1 at cap
  have size := (liveWordSize live).2
  change (insertWord out bank : List Nat).toFinset.card + t ≤ k+1 at size
  rw [List.toFinset_card_of_nodup nd, dagInsertLength] at size
  have same : (out::bank).toFinset = (insertWord out bank).toFinset := by
    ext w
    simp only [List.mem_toFinset, List.mem_cons, insertWordMem]
  have openBank := dagPairsOpen (pairs := pairs)
    (directed := dagSizeFloor ws.length op keep == (fuel-1)+1) masked (show LiveWord mask goal k t (out::bank).toFinset by rwa [same])
  have available : (dagSizeFloor ws.length op keep == (fuel-1)+1) = true → t = 0 := by
    intro directed
    have exactBudget := beq_iff_eq.mp directed
    have first := dagKeepLength (keep.testBit 0) x ws
    have second := dagKeepLength (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    change dagSizeFloor ws.length op keep = (fuel-1)+1 at exactBudget
    unfold dagSizeFloor at exactBudget
    dsimp only [bank, dagKept] at size
    omega
  have refuses := openBank available
  exact Bool.noConfusion (closed.symm.trans refuses)

theorem dagChildAt {mask goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool} {state child : (Nat × List Nat × List (Nat × Nat × Nat))} {sample : (Nat × Nat)} {tags : List (Nat × Nat)} {a b op keep : Nat}
    (checked : dagCheckChildren mask goal chart cut ref state sample tags = true)
    (ha : a < state.2.1.length)
    (legal : (a = b ∧ op = 2 ∧ keep < 2) ∨ (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4))
    (eval : childState mask (gateToken a b op keep) state = some child)
    (masked : Masked mask goal) (viable : WordViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : dagLocal mask goal chart cut child = false) :
    ref (gateToken a b op keep) child = true := by
  have narrow : dagTooWide state.2.1.length state.1 (gateToken a b op keep) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have tooMany := dagWideChild eval h
    obtain ⟨f,w,path⟩ := child
    simp [dagLocal, tooMany] at openChild
  simp only [dagCheckChildren, dagForceCacheEq, dagForceWordEq, dagCountSignsEq,
    Bool.and_eq_true, decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  rcases Bool.and_eq_true_iff.mp atA with ⟨unary,binary⟩
  rcases legal with ⟨rfl,rfl,hk⟩ | ⟨ab,hb,hop,hk⟩
  · have atKeep := treeBlock_at unary (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := a) (op := 2)
      (keep := keep) (by omega) (by decide) (by omega)
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep
  · have atB := treeBlock_at binary (i := b) (by omega) (by omega)
    have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
    have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := b) (op := op)
      (keep := keep) (by omega) (by omega) hk
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep

theorem readWordMasked {mask : Nat} {ws : List Nat}
    (all : ∀ w ∈ ws, Masked mask w) (i : Nat) : Masked mask (ws.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp [Masked]
  | some w => exact all w (List.mem_of_getElem? h)

theorem childStateData {mask token : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (eval : childState mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let a := token / (4 * 3 * 64)
  let b := token / (4 * 3) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let rest := keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega,?_⟩
  have read (i : Nat) : AvailableWord mask ws (ws.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : ws[i]? with
    | none => exact Or.inl rfl
    | some a => exact Or.inr (Or.inr (List.mem_of_getElem? h))
  have hm : Masked mask z := by
    apply maskedGate masked
    unfold z
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inl rfl⟩
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inr rfl⟩
    · exact Or.inl ⟨x,read _,rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (op == 2 || keep.testBit 1) y _ w other

def DagMovesOK (mask goal : Nat) (width : Nat) (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) : Prop :=
  ∀ (i : Nat) (m : (List (List (Nat × Nat) × List (Nat × Nat)))), moves[i]? = some m →
    ∃ select : Fin width → Fin width, DagAuto mask goal select ∧
      ∀ w, Masked mask w → mixMove m w = relabel select w

def dagMoves (cert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width)))) : Array (List (List (Nat × Nat) × List (Nat × Nat))) := (cert.map Prod.fst).toArray

def dagMoveRecordProps {width : Nat} (mask goal : Nat) (entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))) : Prop :=
  let (move, select, inverse) := entry
  (∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal

def dagMoveRecordOK {width : Nat} (mask goal : Nat) (entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))) : Bool :=
  let (move, select, inverse) := entry
  decide ((∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)

theorem dagMoveRecordSpec {width : Nat} {mask goal : Nat} {entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))}
    (ok : dagMoveRecordOK mask goal entry = true) : dagMoveRecordProps mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold dagMoveRecordProps
  exact of_decide_eq_true ok

theorem dagMovesOfCheck {width : Nat} {mask goal : Nat} {cert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width)))}
    (ok : cert.all (dagMoveRecordOK mask goal) = true) :
    DagMovesOK mask goal width (dagMoves cert) := by
  intro i m get
  simp only [dagMoves, List.getElem?_toArray, List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      dagMoveRecordSpec (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select, dagAutoFromMove left right bm gm basis mm mg⟩

theorem dagLinked {mask goal : Nat} {width count : Nat} {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {parent token : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRef count states moves links parent token state = true)
    {k t : Nat} (live : LiveWord mask goal k t state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveWord mask goal k t saved.2.1.toFinset := by
  unfold dagRef at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination,saved,hd,eq,finish.1,?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select,auto,agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWords m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSet (fun w hw => agree w (masked w hw))]
          exact liveMaskedImage auto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))

theorem dagAllNodes {mask goal : Nat} {width fuel count : Nat}
    {stock : List Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {forest : (Nat → Nat × Nat)} {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {sample : (Nat × Nat)}
    {tags : Nat → List (Nat × Nat)}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (cutSound : ∀ s, WordViable mask goal s → cut s = false)
    (autos : DagMovesOK mask goal width moves)
    (verified : treeBlock 0 count (dagCheckNode mask goal chart cut count
      (dagTrace mask stock fuel forest) moves links sample tags) = true):
    ∀ cap i saved, i < count → dagTrace mask stock fuel forest i = some saved →
      saved.1 = cap → ∀ k t, k ≤ cap → ¬LiveWord mask goal k t saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k t kBound live
    rcases s with ⟨remaining, words, history⟩
    let s : (Nat × List Nat × List (Nat × Nat × Nat)) := (remaining, words, history)
    let states := dagTrace mask stock fuel forest
    change states i = some s at stateEq
    have checked := treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change dagCheckNode mask goal chart cut count states moves links sample tags i = true at checked
    simp only [dagCheckNode, stateEq, dagForceWordsEq, Bool.and_eq_true] at checked
    obtain ⟨nd,masked⟩ := dagStateOKSpec checked.1
    have ok := checked.2
    have viable : WordViable mask goal s := ⟨nd,k,t,sFuel ▸ kBound,live⟩
    have scanned := ok
    simp only [dagCheckChildren, Bool.and_eq_true, decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgress wide viable with hit | ⟨child, possible, cv⟩
    · simpa [hit] using absent
    obtain ⟨a,b,op,keep,ha,legal,eval⟩ := possible
    have r := dagChildAt ok ha legal eval goalMask cv nd (dagLocalOpen goalMask chartOK cv (cutSound _ cv))
    have ⟨less,cm⟩ := childStateData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_,k',t',fits,clive⟩ := cv
    obtain ⟨j,dest,bound,restore,fuelEq,tail⟩ :=
      dagLinked maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' t' fits tail

theorem lowerDag {mask goal : Nat} {width fuel count : Nat}
    {stock : List Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {forest : (Nat → Nat × Nat)} {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {sample : (Nat × Nat)}
    {tags : Nat → List (Nat × Nat)}
    {bounds : List (Nat × List Nat × Nat × Nat)} {witnesses : List (Nat × Nat × Nat)}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal) (proper : properWord mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (autos : DagMovesOK mask goal width moves)
    (stockMasked : ∀ w ∈ stock, Masked mask w) (stockNd : stock.Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : Known bounds) (submasks : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (rootCheck : dagCheckRoots mask goal chart (dagKnownCloses goal bounds) witnesses
      (dagRef count (dagTrace mask stock fuel forest) moves links 0)
      stock fuel = true)
    (nodeCheck : treeBlock 0 count (dagCheckNode mask goal chart (dagKnownCloses goal bounds)
      count (dagTrace mask stock fuel forest) moves links sample tags) = true) :
    Lower mask stock goal (fuel+1) := by
  intro values build hit
  by_contra! small
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive stockMasked build hit proper
  have included : S ⊆ stock.toFinset := fun w hw => List.mem_toFinset.mpr (sub w hw)
  obtain ⟨token,tokenBound,eq⟩ := rootToken stock S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state := rootState stock fuel token
  have eq' : state.2.1.toFinset = S := eq
  have v : WordViable mask goal state := by
    refine ⟨(rootWordSublist stock token).nodup stockNd,k,t,?_,?_⟩
    · change k ≤ fuel
      omega
    · rwa [eq']
  have cutOpen (s : (Nat × List Nat × List (Nat × Nat × Nat))) (h : WordViable mask goal s) : dagKnownCloses goal bounds s = false := by
    rw [dagKnownClosesEq]
    exact knownClosesSound known submasks h
  have openRoot := dagLocalOpen goalMask chartOK v (cutOpen _ v)
  have allowed : dagAllowedRoot witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset, eq']
    exact essentialRequired (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart (dagKnownCloses goal bounds) state ||
    dagRef count (dagTrace mask stock fuel forest) moves links 0 token state) = true at checked
  simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
  have finish := dagAllNodes maskBounds goalMask chartOK cutOpen autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveWord mask goal k t state.2.1.toFinset := by rwa [eq']
  have stateMask : ∀ w ∈ state.2.1, Masked mask w := by
    intro w hw
    exact stockMasked _ ((rootWordSublist stock token).subset hw)
  obtain ⟨i,s,hi,restore,cap,plan⟩ := dagLinked maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k t fits plan

def dagLookupLinks (index data indexWidth sizeBits tokenBits destinationBits autoBits trials : Nat) :
    (Nat → Nat → Option (Nat × Nat)) := fun parent token =>
  let entry := unpack index indexWidth parent
  let size := entry &&& ((1 <<< sizeBits) - 1)
  let offset := entry >>> sizeBits
  let width := tokenBits + destinationBits + autoBits
  (Nat.rec (motive := fun _ => Nat → Nat → Option (Nat × Nat)) (fun _ _ => none)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo+hi)/2
        let code := unpack data width mid
        let key := code &&& ((1 <<< tokenBits) - 1)
        if Nat.beq token key then
          some ((code >>> tokenBits) &&& ((1 <<< destinationBits) - 1),
            code >>> (tokenBits + destinationBits))
        else if Nat.blt token key then next lo mid else next (mid+1) hi
      else none) trials) offset (offset+size)

def projectDAGStock (mask : Nat) (source : List Nat) (indices : List Nat) : List Nat :=
  List.rec [] (fun i _ rest => (mask &&& source.getD i 0) :: rest) indices

theorem stockMaskedOfCheck {mask : Nat} {stock : List Nat}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)

theorem suppliesOfCheck {oldMask : Nat} {old new : List Nat} {rename : Nat → Nat}
    (h : new.all (fun w => availableB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvailableWord oldMask old (rename w) := by
  intro w hw
  exact availableB_spec.mp (List.all_eq_true.mp h w hw)

def dagShift (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (word : Nat) : Nat :=
  mixMove move (word &&& mask)

def dagShiftUnique (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : Nat → Nat → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      dagForceWord (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && dagForceWord (occupied ||| col) next)
    else next occupied)

theorem dagShiftLinear (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : BitLinear (dagShift mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0

theorem dagShiftBasis (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (i : Nat) :
    dagShift mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and, Nat.testBit_two_pow, same, h]
  rw [dagShift, select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp

theorem dagShiftUniqueSpec {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))} {n : Nat} {occupied : Nat}
    (ok : dagShiftUnique mask move n occupied = true) :
    (∀ j < n, ∀ b, (dagShift mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n, ∀ k < n, ∀ b, (dagShift mask move (2^j)).testBit b = true →
      (dagShift mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then dagForceWord col (fun w =>
      Nat.beq (w &&& occupied) 0 && dagForceWord (occupied ||| w) (dagShiftUnique mask move n))
      else dagShiftUnique mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,dagForceWordEq] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : dagShift mask move (2^n) = 0 := by simp [dagShiftBasis,active]
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · simp [same,dead] at h
        · exact existing j (by omega) b h
      · intro j hj k hk b a c
        by_cases e : j = n
        · simp [e,dead] at a
        by_cases e' : k = n
        · simp [e',dead] at c
        exact unique j (by omega) k (by omega) b a c
    · simp only [active,ite_true,dagForceWordEq,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : dagShift mask move (2^n) = col := by simp [dagShiftBasis,active,col]
      have old {j b : Nat} (hj : j < n) (h : (dagShift mask move (2^j)).testBit b = true) :
          occupied.testBit b = false ∧ col.testBit b = false := by
        simpa [Nat.testBit_or, Bool.or_eq_false_iff] using existing j hj b h
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · rw [same,colEq] at h
          have bit := congrArg (fun w => Nat.testBit w b) disjoint
          simpa [Nat.testBit_and,h] using bit
        · exact (old (by omega) h).1
      · intro j hj k hk b a c
        by_cases e : j = n
        · by_cases e' : k = n
          · exact e.trans e'.symm
          · rw [e,colEq,(old (by omega) c).2] at a
            contradiction
        by_cases e' : k = n
        · rw [e',colEq,(old (by omega) a).2] at c
          contradiction
        exact unique j (by omega) k (by omega) b a c

theorem dagShiftGates {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))} {width : Nat}
    (bounded : Masked (fullMask width) mask) (checked : dagShiftUnique mask move width 0 = true) :
    (∀ a b, dagShift mask move (a &&& b) = dagShift mask move a &&& dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ||| b) = dagShift mask move a ||| dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ^^^ b) = dagShift mask move a ^^^ dagShift mask move b) := by
  let f := dagShift mask move
  have lin := dagShiftLinear mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fullMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,dagShiftBasis,zero] at a
    exact (dagShiftUniqueSpec checked).2 j (within hj) k (within hk) i hj hk
  refine ⟨?_,?_,?_⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_and, Bool.and_eq_true, lin, lin, lin]
    constructor
    · rintro ⟨j,hj,h⟩
      rw [Nat.testBit_and, Bool.and_eq_true] at hj
      exact ⟨⟨j,hj.1,h⟩,⟨j,hj.2,h⟩⟩
    · rintro ⟨⟨j,hj,q⟩,⟨k,hk,r⟩⟩
      have same := uniq q r
      subst k
      exact ⟨j,by simp [Nat.testBit_and,hj,hk],q⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [lin (a ||| b) i, Nat.testBit_or, Bool.or_eq_true, lin a i, lin b i]
    simp only [Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro ⟨j,(left | right),same⟩
      · exact Or.inl ⟨j,left,same⟩
      · exact Or.inr ⟨j,right,same⟩
    · rintro (⟨j,left,same⟩ | ⟨j,right,same⟩)
      · exact ⟨j,Or.inl left,same⟩
      · exact ⟨j,Or.inr right,same⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    have l := lin a i
    have r := lin b i
    have v := lin (a ^^^ b) i
    cases pa : (f a).testBit i <;> cases pb : (f b).testBit i
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      have disj : a.testBit j = true ∨ b.testBit j = true := by
        rw [Nat.testBit_xor] at hj
        cases aj : a.testBit j <;> cases bj : b.testBit j <;> simp [aj,bj] at hj ⊢
      rcases disj with da | db
      · have := l.mpr ⟨j,da,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this
      · have := r.mpr ⟨j,db,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := r.mp pb
      have notA : a.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := l.mpr ⟨j,yes,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this)
      exact ⟨j,by simp [Nat.testBit_xor,notA,hj],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := l.mp pa
      have notB : b.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := r.mpr ⟨j,yes,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this)
      exact ⟨j,by simp [Nat.testBit_xor,hj,notB],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      obtain ⟨a',ha,q⟩ := l.mp pa
      obtain ⟨b',hb,r⟩ := r.mp pb
      have ea := uniq h q
      have eb := uniq h r
      rw [← ea] at ha
      rw [← eb] at hb
      simp [Nat.testBit_xor,ha,hb] at hj

def dagShiftCheck (width mask goal oldMask oldGoal : Nat) (stock old : List Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : Bool :=
  Nat.beq (mask &&& fullMask width) mask && dagShiftUnique mask move width 0 &&
    Nat.beq (dagShift mask move mask) oldMask && Nat.beq (dagShift mask move goal) oldGoal &&
    stock.all (fun w => availableB oldMask old (dagShift mask move w))

theorem dagShiftLower {width mask goal oldMask oldGoal : Nat} {stock old : List Nat} {min : Nat}
    (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (origin : Lower oldMask old oldGoal min)
    (ok : dagShiftCheck width mask goal oldMask oldGoal stock old move = true) :
    Lower mask stock goal min := by
  simp only [dagShiftCheck,Bool.and_eq_true,Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded,unique⟩,masks⟩,goals⟩,supply⟩ := ok
  obtain ⟨andG,orG,xorG⟩ := dagShiftGates bounded unique
  have zero : dagShift mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [dagShiftLinear]
    simp
  apply lowerMap (dagShift mask move) zero masks (fun w => by rw [xorG,masks]) andG orG (suppliesOfCheck supply)
  rwa [goals]

def moveSchedule (stages : Array (List (Nat × Nat) × List (Nat × Nat))) (indices : List Nat) : (List (List (Nat × Nat) × List (Nat × Nat))) :=
  List.rec [] (fun i _ rest => stages[i]?.getD ([],[]) :: rest) indices

def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

theorem hcsGateWord {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    GateWord (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl | rfl
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact Or.inl ⟨0, zeroAv, by simpa [hcsGateVal] using notNat (0 : BitVec rows)⟩
    | cons a _ => exact Or.inl ⟨_, toNatAvailable bank a, by simpa [hcsGateVal] using notNat (bank.getD a 0)⟩

theorem hcsBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length = gs.length ∧ WordBuilds (fullMask rows) (bank.map BitVec.toNat) vs ∧
      ∀ v ∈ gs.foldl hcsStep bank, v.toNat ∈ vs ++ bank.map BitVec.toNat := by
  induction gs generalizing bank with
  | nil => exact ⟨[], rfl, trivial, fun _ h => List.mem_map_of_mem h⟩
  | cons g gs ih =>
    let v := hcsGateVal bank g
    have hg := hfan g List.mem_cons_self
    obtain ⟨xs, len, build, sub⟩ := ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    have eq : (hcsStep bank g).map BitVec.toNat = bank.map BitVec.toNat ++ [v.toNat] := by
      simp [hcsStep, v]
    rw [eq] at build
    refine ⟨v.toNat :: xs, by simp [len], ⟨hcsGateWord bank g hg.1 hg.2, buildsWeaken ?_ build⟩, ?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using m

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

theorem hcsLowerEq {m1 m2 g1 g2 min : Nat} {b1 b2 : List Nat}
    (hm : m1 = m2) (hb : b1 = b2) (hg : g1 = g2)
    (h : Lower m1 b1 g1 min) : Lower m2 b2 g2 min := by
  subst hm; subst hb; subst hg; exact h

theorem hcsEvalWord {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hev : ∀ x, C.eval (List.ofFn x) = f x) :
    (C.gates.foldl hcsStep raw).getD C.output 0 = goal := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let y : Fin n → Bool := fun k => j.testBit k.val
  have hbank : raw.map (fun v => v.getLsbD j) = List.ofFn y :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
  have hfg : goal.getLsbD j = f y :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
  have hbits := hcsFoldBits raw ⟨j, hj⟩ C.gates hfan
  have hevj : (C.wires (List.ofFn y)).getD C.output false = f y := hev y
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn y)).getD C.output false = f y at hevj
  rw [← hbank, ← hbits] at hevj
  rw [hfg, ← hevj, ← hcsGetDBit]

theorem hcsLower {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n)) (min : Nat)
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (claim : Lower (fullMask (2 ^ n)) (raw.map BitVec.toNat) goal.toNat min)
    (t : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize n f t) : min ≤ t := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  obtain ⟨vs, len, built, sub⟩ := hcsBuilds raw C.gates hfan
  let eb := C.gates.foldl hcsStep raw
  have same : eb.getD C.output 0 = goal := hcsEvalWord raw goal f hRaw hGoal C hfan hev
  have av : AvailableWord (fullMask (2 ^ n)) (vs ++ raw.map BitVec.toNat) goal.toNat := by
    rw [← same, List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some v => exact Or.inr (Or.inr (sub v (List.mem_of_getElem? h)))
  have lb := claim vs built av
  have hs : C.gates.length ≤ t := hsz
  omega

def moveStage0 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff0000ffff, 16)], [(0xffff0000ffff0000, 16)])
def moveStage1 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])
def moveStage2 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])
def moveStage3 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])
def moveStage4 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffff, 32)], [(0xffffffff00000000, 32)])
def moveStage5 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f0f0f00f0f0f0f, 0), (0xf0f0f0f0, 28)], [(0xf0f0f0f00000000, 28)])
def moveStage6 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])
def moveStage7 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])
def moveStage8 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])
def moveStage9 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])
def moveStage10 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])
def moveStage11 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcccccccc33333333, 0), (0xcccccccc, 30)], [(0x3333333300000000, 30)])
def moveStage12 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])
def moveStage13 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcc33cc33cc33cc33, 0), (0xcc00cc00cc00cc, 6)], [(0x3300330033003300, 6)])
def moveStages : Array (List (Nat × Nat) × List (Nat × Nat)) := #[moveStage0, moveStage1, moveStage2, moveStage3, moveStage4, moveStage5, moveStage6, moveStage7, moveStage8, moveStage9, moveStage10, moveStage11, moveStage12, moveStage13]
def sBase : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000, 0x5555555555555555, 0x3333333333333333, 0xf0f0f0f0f0f0f0f, 0xff00ff00ff00ff, 0xffff0000ffff, 0xffffffff]
def sGoal : Nat := 0xfeeefae8feaae8a0
def s0Mask : Nat := 0xff00000000
abbrev s0Goal : Nat := sGoal &&& s0Mask
abbrev s0StockWords : List Nat := projectDAGStock s0Mask sBase [0, 1, 2]
def s0Fact : (Nat × List Nat × Nat × Nat) := (s0Mask, s0StockWords, 4, s0Goal)
def s0Cuts : List (Nat × List Nat × Nat × Nat) := []
def s0Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[35, 37, 38, 35, 35, 35, 35, 35, 35, 35, 35, 35, 33, 34, 36, 33, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s0Sample : (Nat × Nat) := (0x1209842251108c4426120944223, 6)
def s0Witnesses := unpackWitnesses s0StockWords [17954, 280097, 543265]
def s0Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s0Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s0Tags := dagTraceTags s0Mask 6 (dagTagBases s0StockWords 0x36b5b 0x22311 6) 3 s0Data
def s0States := dagTrace s0Mask s0StockWords 3 s0Data
def s0MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 64 s0Moves := dagMovesOfCheck (by decide +kernel)
def s0Check := dagCheckNode s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) 1 s0States s0Moves s0Links s0Sample s0Tags
def s0RootAt (token : Nat) : Bool :=
  let s := rootState s0StockWords 3 token
  !dagAllowedRoot s0Witnesses s.2.1 || dagLocal s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s ||
  dagRef 1 s0States s0Moves s0Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0RootBlock0 : treeBlock 0 8 s0RootAt = true := by decide +kernel
theorem s0Roots : dagCheckRoots s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s0Witnesses (dagRef 1 s0States s0Moves s0Links 0) s0StockWords 3 = true := s0RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block0 : treeBlock 0 1 s0Check = true := by decide +kernel
theorem s0Blocks : treeBlock 0 1 s0Check = true := s0Block0
theorem s0Known : Known s0Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Stock : Lower s0Mask s0StockWords s0Goal 4 := by
  apply lowerDag _ _ _ _ s0Autos _ _ _ s0Known _ s0Roots s0Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s0StockWords; decide +kernel
  · decide +kernel
  · simp only [s0Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s1Mask : Nat := 0xff00
abbrev s1Goal : Nat := sGoal &&& s1Mask
abbrev s1StockWords : List Nat := projectDAGStock s1Mask sBase [0, 1, 2]
def s1Fact : (Nat × List Nat × Nat × Nat) := (s1Mask, s1StockWords, 4, s1Goal)
def s1Cuts : List (Nat × List Nat × Nat × Nat) := []
def s1Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 13, 14, 11, 11, 11, 11, 11, 11, 11, 11, 11, 9, 10, 12, 9, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s1Sample : (Nat × Nat) := (0x6038120d0502c140e06034120b, 6)
def s1Witnesses := unpackWitnesses s1StockWords [5642, 267785, 530953]
def s1Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s1Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s1Tags := dagTraceTags s1Mask 6 (dagTagBases s1StockWords 0x36b5b 0x22311 6) 3 s1Data
def s1States := dagTrace s1Mask s1StockWords 3 s1Data
def s1MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s1Moves := dagMoves s1MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Autos : DagMovesOK s1Mask s1Goal 64 s1Moves := dagMovesOfCheck (by decide +kernel)
def s1Check := dagCheckNode s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) 1 s1States s1Moves s1Links s1Sample s1Tags
def s1RootAt (token : Nat) : Bool :=
  let s := rootState s1StockWords 3 token
  !dagAllowedRoot s1Witnesses s.2.1 || dagLocal s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) s ||
  dagRef 1 s1States s1Moves s1Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1RootBlock0 : treeBlock 0 8 s1RootAt = true := by decide +kernel
theorem s1Roots : dagCheckRoots s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) s1Witnesses (dagRef 1 s1States s1Moves s1Links 0) s1StockWords 3 = true := s1RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Block0 : treeBlock 0 1 s1Check = true := by decide +kernel
theorem s1Blocks : treeBlock 0 1 s1Check = true := s1Block0
theorem s1Known : Known s1Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Stock : Lower s1Mask s1StockWords s1Goal 4 := by
  apply lowerDag _ _ _ _ s1Autos _ _ _ s1Known _ s1Roots s1Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s1StockWords; decide +kernel
  · decide +kernel
  · simp only [s1Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s2Mask : Nat := 0xf000f00000000
abbrev s2Goal : Nat := sGoal &&& s2Mask
abbrev s2StockWords : List Nat := projectDAGStock s2Mask sBase [0, 1, 4]
def s2Fact : (Nat × List Nat × Nat × Nat) := (s2Mask, s2StockWords, 4, s2Goal)
def s2Cuts : List (Nat × List Nat × Nat × Nat) := []
def s2Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[35, 49, 50, 35, 35, 35, 35, 35, 35, 35, 35, 35, 33, 34, 48, 33, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s2Sample : (Nat × Nat) := (0x180c842311108c4432180c44223, 6)
def s2Witnesses := unpackWitnesses s2StockWords [17954, 280097, 549409]
def s2Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s2Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s2Tags := dagTraceTags s2Mask 6 (dagTagBases s2StockWords 0x36b5b 0x22311 6) 3 s2Data
def s2States := dagTrace s2Mask s2StockWords 3 s2Data
def s2MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s2Moves := dagMoves s2MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Autos : DagMovesOK s2Mask s2Goal 64 s2Moves := dagMovesOfCheck (by decide +kernel)
def s2Check := dagCheckNode s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) 1 s2States s2Moves s2Links s2Sample s2Tags
def s2RootAt (token : Nat) : Bool :=
  let s := rootState s2StockWords 3 token
  !dagAllowedRoot s2Witnesses s.2.1 || dagLocal s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) s ||
  dagRef 1 s2States s2Moves s2Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2RootBlock0 : treeBlock 0 8 s2RootAt = true := by decide +kernel
theorem s2Roots : dagCheckRoots s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) s2Witnesses (dagRef 1 s2States s2Moves s2Links 0) s2StockWords 3 = true := s2RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block0 : treeBlock 0 1 s2Check = true := by decide +kernel
theorem s2Blocks : treeBlock 0 1 s2Check = true := s2Block0
theorem s2Known : Known s2Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Stock : Lower s2Mask s2StockWords s2Goal 4 := by
  apply lowerDag _ _ _ _ s2Autos _ _ _ s2Known _ s2Roots s2Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s2StockWords; decide +kernel
  · decide +kernel
  · simp only [s2Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s3Mask : Nat := 0xf000f00
abbrev s3Goal : Nat := sGoal &&& s3Mask
abbrev s3StockWords : List Nat := projectDAGStock s3Mask sBase [0, 1, 4]
def s3Fact : (Nat × List Nat × Nat × Nat) := (s3Mask, s3StockWords, 4, s3Goal)
def s3Cuts : List (Nat × List Nat × Nat × Nat) := []
def s3Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 25, 26, 11, 11, 11, 11, 11, 11, 11, 11, 11, 9, 10, 24, 9, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s3Sample : (Nat × Nat) := (0xc06812190502c141a0c064120b, 6)
def s3Witnesses := unpackWitnesses s3StockWords [5642, 267785, 537097]
def s3Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s3Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s3Tags := dagTraceTags s3Mask 6 (dagTagBases s3StockWords 0x36b5b 0x22311 6) 3 s3Data
def s3States := dagTrace s3Mask s3StockWords 3 s3Data
def s3MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s3Moves := dagMoves s3MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Autos : DagMovesOK s3Mask s3Goal 64 s3Moves := dagMovesOfCheck (by decide +kernel)
def s3Check := dagCheckNode s3Mask s3Goal s3Chart (dagKnownCloses s3Goal s3Cuts) 1 s3States s3Moves s3Links s3Sample s3Tags
def s3RootAt (token : Nat) : Bool :=
  let s := rootState s3StockWords 3 token
  !dagAllowedRoot s3Witnesses s.2.1 || dagLocal s3Mask s3Goal s3Chart (dagKnownCloses s3Goal s3Cuts) s ||
  dagRef 1 s3States s3Moves s3Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3RootBlock0 : treeBlock 0 8 s3RootAt = true := by decide +kernel
theorem s3Roots : dagCheckRoots s3Mask s3Goal s3Chart (dagKnownCloses s3Goal s3Cuts) s3Witnesses (dagRef 1 s3States s3Moves s3Links 0) s3StockWords 3 = true := s3RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Block0 : treeBlock 0 1 s3Check = true := by decide +kernel
theorem s3Blocks : treeBlock 0 1 s3Check = true := s3Block0
theorem s3Known : Known s3Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Stock : Lower s3Mask s3StockWords s3Goal 4 := by
  apply lowerDag _ _ _ _ s3Autos _ _ _ s3Known _ s3Roots s3Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s3StockWords; decide +kernel
  · decide +kernel
  · simp only [s3Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s4Mask : Nat := 0x333300000000
abbrev s4Goal : Nat := sGoal &&& s4Mask
abbrev s4StockWords : List Nat := projectDAGStock s4Mask sBase [0, 2, 3]
def s4Fact : (Nat × List Nat × Nat × Nat) := (s4Mask, s4StockWords, 4, s4Goal)
def s4Cuts : List (Nat × List Nat × Nat × Nat) := []
def s4Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[37, 41, 44, 37, 37, 37, 37, 37, 37, 37, 37, 37, 33, 36, 40, 33, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s4Sample : (Nat × Nat) := (0x140b0422912094482c140a44225, 6)
def s4Witnesses := unpackWitnesses s4StockWords [18980, 281121, 545313]
def s4Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s4Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s4Tags := dagTraceTags s4Mask 6 (dagTagBases s4StockWords 0x36b5b 0x22311 6) 3 s4Data
def s4States := dagTrace s4Mask s4StockWords 3 s4Data
def s4MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s4Moves := dagMoves s4MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Autos : DagMovesOK s4Mask s4Goal 64 s4Moves := dagMovesOfCheck (by decide +kernel)
def s4Check := dagCheckNode s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) 1 s4States s4Moves s4Links s4Sample s4Tags
def s4RootAt (token : Nat) : Bool :=
  let s := rootState s4StockWords 3 token
  !dagAllowedRoot s4Witnesses s.2.1 || dagLocal s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) s ||
  dagRef 1 s4States s4Moves s4Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4RootBlock0 : treeBlock 0 8 s4RootAt = true := by decide +kernel
theorem s4Roots : dagCheckRoots s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) s4Witnesses (dagRef 1 s4States s4Moves s4Links 0) s4StockWords 3 = true := s4RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Block0 : treeBlock 0 1 s4Check = true := by decide +kernel
theorem s4Blocks : treeBlock 0 1 s4Check = true := s4Block0
theorem s4Known : Known s4Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Stock : Lower s4Mask s4StockWords s4Goal 4 := by
  apply lowerDag _ _ _ _ s4Autos _ _ _ s4Known _ s4Roots s4Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s4StockWords; decide +kernel
  · decide +kernel
  · simp only [s4Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s5Mask : Nat := 0xcccc
abbrev s5Goal : Nat := sGoal &&& s5Mask
abbrev s5StockWords : List Nat := projectDAGStock s5Mask sBase [0, 2, 3]
def s5Fact : (Nat × List Nat × Nat × Nat) := (s5Mask, s5StockWords, 4, s5Goal)
def s5Cuts : List (Nat × List Nat × Nat × Nat) := []
def s5Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[7, 11, 14, 7, 7, 7, 7, 7, 7, 7, 7, 7, 3, 6, 10, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s5Sample : (Nat × Nat) := (0x5038060b0301c0c0e0502c0607, 6)
def s5Witnesses := unpackWitnesses s5StockWords [3590, 265731, 529923]
def s5Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s5Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s5Tags := dagTraceTags s5Mask 6 (dagTagBases s5StockWords 0x36b5b 0x22311 6) 3 s5Data
def s5States := dagTrace s5Mask s5StockWords 3 s5Data
def s5MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s5Moves := dagMoves s5MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Autos : DagMovesOK s5Mask s5Goal 64 s5Moves := dagMovesOfCheck (by decide +kernel)
def s5Check := dagCheckNode s5Mask s5Goal s5Chart (dagKnownCloses s5Goal s5Cuts) 1 s5States s5Moves s5Links s5Sample s5Tags
def s5RootAt (token : Nat) : Bool :=
  let s := rootState s5StockWords 3 token
  !dagAllowedRoot s5Witnesses s.2.1 || dagLocal s5Mask s5Goal s5Chart (dagKnownCloses s5Goal s5Cuts) s ||
  dagRef 1 s5States s5Moves s5Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5RootBlock0 : treeBlock 0 8 s5RootAt = true := by decide +kernel
theorem s5Roots : dagCheckRoots s5Mask s5Goal s5Chart (dagKnownCloses s5Goal s5Cuts) s5Witnesses (dagRef 1 s5States s5Moves s5Links 0) s5StockWords 3 = true := s5RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Block0 : treeBlock 0 1 s5Check = true := by decide +kernel
theorem s5Blocks : treeBlock 0 1 s5Check = true := s5Block0
theorem s5Known : Known s5Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Stock : Lower s5Mask s5StockWords s5Goal 4 := by
  apply lowerDag _ _ _ _ s5Autos _ _ _ s5Known _ s5Roots s5Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s5StockWords; decide +kernel
  · decide +kernel
  · simp only [s5Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s6Mask : Nat := 0x33003300
abbrev s6Goal : Nat := sGoal &&& s6Mask
abbrev s6StockWords : List Nat := projectDAGStock s6Mask sBase [0, 2, 4]
def s6Fact : (Nat × List Nat × Nat × Nat) := (s6Mask, s6StockWords, 4, s6Goal)
def s6Cuts : List (Nat × List Nat × Nat × Nat) := []
def s6Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[13, 25, 28, 13, 13, 13, 13, 13, 13, 13, 13, 13, 9, 12, 24, 9, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s6Sample : (Nat × Nat) := (0xc070121906034181c0c064120d, 6)
def s6Witnesses := unpackWitnesses s6StockWords [6668, 268809, 537097]
def s6Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s6Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s6Tags := dagTraceTags s6Mask 6 (dagTagBases s6StockWords 0x36b5b 0x22311 6) 3 s6Data
def s6States := dagTrace s6Mask s6StockWords 3 s6Data
def s6MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s6Moves := dagMoves s6MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Autos : DagMovesOK s6Mask s6Goal 64 s6Moves := dagMovesOfCheck (by decide +kernel)
def s6Check := dagCheckNode s6Mask s6Goal s6Chart (dagKnownCloses s6Goal s6Cuts) 1 s6States s6Moves s6Links s6Sample s6Tags
def s6RootAt (token : Nat) : Bool :=
  let s := rootState s6StockWords 3 token
  !dagAllowedRoot s6Witnesses s.2.1 || dagLocal s6Mask s6Goal s6Chart (dagKnownCloses s6Goal s6Cuts) s ||
  dagRef 1 s6States s6Moves s6Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6RootBlock0 : treeBlock 0 8 s6RootAt = true := by decide +kernel
theorem s6Roots : dagCheckRoots s6Mask s6Goal s6Chart (dagKnownCloses s6Goal s6Cuts) s6Witnesses (dagRef 1 s6States s6Moves s6Links 0) s6StockWords 3 = true := s6RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Block0 : treeBlock 0 1 s6Check = true := by decide +kernel
theorem s6Blocks : treeBlock 0 1 s6Check = true := s6Block0
theorem s6Known : Known s6Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Stock : Lower s6Mask s6StockWords s6Goal 4 := by
  apply lowerDag _ _ _ _ s6Autos _ _ _ s6Known _ s6Roots s6Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s6StockWords; decide +kernel
  · decide +kernel
  · simp only [s6Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s7Mask : Nat := 0x330000003300
abbrev s7Goal : Nat := sGoal &&& s7Mask
abbrev s7StockWords : List Nat := projectDAGStock s7Mask sBase [0, 2, 5]
def s7Fact : (Nat × List Nat × Nat × Nat) := (s7Mask, s7StockWords, 4, s7Goal)
def s7Cuts : List (Nat × List Nat × Nat × Nat) := []
def s7Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[13, 41, 44, 13, 13, 13, 13, 13, 13, 13, 13, 13, 9, 12, 40, 9, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s7Sample : (Nat × Nat) := (0x140b0122906034182c140a4120d, 6)
def s7Witnesses := unpackWitnesses s7StockWords [6668, 268809, 545289]
def s7Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s7Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s7Tags := dagTraceTags s7Mask 6 (dagTagBases s7StockWords 0x36b5b 0x22311 6) 3 s7Data
def s7States := dagTrace s7Mask s7StockWords 3 s7Data
def s7MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s7Moves := dagMoves s7MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Autos : DagMovesOK s7Mask s7Goal 64 s7Moves := dagMovesOfCheck (by decide +kernel)
def s7Check := dagCheckNode s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) 1 s7States s7Moves s7Links s7Sample s7Tags
def s7RootAt (token : Nat) : Bool :=
  let s := rootState s7StockWords 3 token
  !dagAllowedRoot s7Witnesses s.2.1 || dagLocal s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) s ||
  dagRef 1 s7States s7Moves s7Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7RootBlock0 : treeBlock 0 8 s7RootAt = true := by decide +kernel
theorem s7Roots : dagCheckRoots s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) s7Witnesses (dagRef 1 s7States s7Moves s7Links 0) s7StockWords 3 = true := s7RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Block0 : treeBlock 0 1 s7Check = true := by decide +kernel
theorem s7Blocks : treeBlock 0 1 s7Check = true := s7Block0
theorem s7Known : Known s7Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Stock : Lower s7Mask s7StockWords s7Goal 4 := by
  apply lowerDag _ _ _ _ s7Autos _ _ _ s7Known _ s7Roots s7Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s7StockWords; decide +kernel
  · decide +kernel
  · simp only [s7Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s8Mask : Nat := 0xcc000000cc
abbrev s8Goal : Nat := sGoal &&& s8Mask
abbrev s8StockWords : List Nat := projectDAGStock s8Mask sBase [0, 2, 5]
def s8Fact : (Nat × List Nat × Nat × Nat) := (s8Mask, s8StockWords, 4, s8Goal)
def s8Cuts : List (Nat × List Nat × Nat × Nat) := []
def s8Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[7, 35, 38, 7, 7, 7, 7, 7, 7, 7, 7, 7, 3, 6, 34, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s8Sample : (Nat × Nat) := (0x1109806230301c0c261108c0607, 6)
def s8Witnesses := unpackWitnesses s8StockWords [3590, 265731, 542211]
def s8Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s8Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s8Tags := dagTraceTags s8Mask 6 (dagTagBases s8StockWords 0x36b5b 0x22311 6) 3 s8Data
def s8States := dagTrace s8Mask s8StockWords 3 s8Data
def s8MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s8Moves := dagMoves s8MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Autos : DagMovesOK s8Mask s8Goal 64 s8Moves := dagMovesOfCheck (by decide +kernel)
def s8Check := dagCheckNode s8Mask s8Goal s8Chart (dagKnownCloses s8Goal s8Cuts) 1 s8States s8Moves s8Links s8Sample s8Tags
def s8RootAt (token : Nat) : Bool :=
  let s := rootState s8StockWords 3 token
  !dagAllowedRoot s8Witnesses s.2.1 || dagLocal s8Mask s8Goal s8Chart (dagKnownCloses s8Goal s8Cuts) s ||
  dagRef 1 s8States s8Moves s8Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8RootBlock0 : treeBlock 0 8 s8RootAt = true := by decide +kernel
theorem s8Roots : dagCheckRoots s8Mask s8Goal s8Chart (dagKnownCloses s8Goal s8Cuts) s8Witnesses (dagRef 1 s8States s8Moves s8Links 0) s8StockWords 3 = true := s8RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Block0 : treeBlock 0 1 s8Check = true := by decide +kernel
theorem s8Blocks : treeBlock 0 1 s8Check = true := s8Block0
theorem s8Known : Known s8Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Stock : Lower s8Mask s8StockWords s8Goal 4 := by
  apply lowerDag _ _ _ _ s8Autos _ _ _ s8Known _ s8Roots s8Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s8StockWords; decide +kernel
  · decide +kernel
  · simp only [s8Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s9Mask : Nat := 0xc0c0c0c
abbrev s9Goal : Nat := sGoal &&& s9Mask
abbrev s9StockWords : List Nat := projectDAGStock s9Mask sBase [0, 3, 4]
def s9Fact : (Nat × List Nat × Nat × Nat) := (s9Mask, s9StockWords, 4, s9Goal)
def s9Cuts : List (Nat × List Nat × Nat × Nat) := []
def s9Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 19, 26, 11, 11, 11, 11, 11, 11, 11, 11, 11, 3, 10, 18, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s9Sample : (Nat × Nat) := (0x906806130502c141a0904c060b, 6)
def s9Witnesses := unpackWitnesses s9StockWords [5642, 267779, 534019]
def s9Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s9Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s9Tags := dagTraceTags s9Mask 6 (dagTagBases s9StockWords 0x36b5b 0x22311 6) 3 s9Data
def s9States := dagTrace s9Mask s9StockWords 3 s9Data
def s9MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s9Moves := dagMoves s9MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Autos : DagMovesOK s9Mask s9Goal 64 s9Moves := dagMovesOfCheck (by decide +kernel)
def s9Check := dagCheckNode s9Mask s9Goal s9Chart (dagKnownCloses s9Goal s9Cuts) 1 s9States s9Moves s9Links s9Sample s9Tags
def s9RootAt (token : Nat) : Bool :=
  let s := rootState s9StockWords 3 token
  !dagAllowedRoot s9Witnesses s.2.1 || dagLocal s9Mask s9Goal s9Chart (dagKnownCloses s9Goal s9Cuts) s ||
  dagRef 1 s9States s9Moves s9Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9RootBlock0 : treeBlock 0 8 s9RootAt = true := by decide +kernel
theorem s9Roots : dagCheckRoots s9Mask s9Goal s9Chart (dagKnownCloses s9Goal s9Cuts) s9Witnesses (dagRef 1 s9States s9Moves s9Links 0) s9StockWords 3 = true := s9RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Block0 : treeBlock 0 1 s9Check = true := by decide +kernel
theorem s9Blocks : treeBlock 0 1 s9Check = true := s9Block0
theorem s9Known : Known s9Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Stock : Lower s9Mask s9StockWords s9Goal 4 := by
  apply lowerDag _ _ _ _ s9Autos _ _ _ s9Known _ s9Roots s9Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s9StockWords; decide +kernel
  · decide +kernel
  · simp only [s9Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s10Mask : Nat := 0xc000c000c000c
abbrev s10Goal : Nat := sGoal &&& s10Mask
abbrev s10StockWords : List Nat := projectDAGStock s10Mask sBase [0, 4, 5]
def s10Fact : (Nat × List Nat × Nat × Nat) := (s10Mask, s10StockWords, 4, s10Goal)
def s10Cuts : List (Nat × List Nat × Nat × Nat) := []
def s10Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[19, 35, 50, 19, 19, 19, 19, 19, 19, 19, 19, 19, 3, 18, 34, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s10Sample : (Nat × Nat) := (0x110c806230904c24321108c0613, 6)
def s10Witnesses := unpackWitnesses s10StockWords [9746, 271875, 542211]
def s10Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s10Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s10Tags := dagTraceTags s10Mask 6 (dagTagBases s10StockWords 0x36b5b 0x22311 6) 3 s10Data
def s10States := dagTrace s10Mask s10StockWords 3 s10Data
def s10MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s10Moves := dagMoves s10MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Autos : DagMovesOK s10Mask s10Goal 64 s10Moves := dagMovesOfCheck (by decide +kernel)
def s10Check := dagCheckNode s10Mask s10Goal s10Chart (dagKnownCloses s10Goal s10Cuts) 1 s10States s10Moves s10Links s10Sample s10Tags
def s10RootAt (token : Nat) : Bool :=
  let s := rootState s10StockWords 3 token
  !dagAllowedRoot s10Witnesses s.2.1 || dagLocal s10Mask s10Goal s10Chart (dagKnownCloses s10Goal s10Cuts) s ||
  dagRef 1 s10States s10Moves s10Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10RootBlock0 : treeBlock 0 8 s10RootAt = true := by decide +kernel
theorem s10Roots : dagCheckRoots s10Mask s10Goal s10Chart (dagKnownCloses s10Goal s10Cuts) s10Witnesses (dagRef 1 s10States s10Moves s10Links 0) s10StockWords 3 = true := s10RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Block0 : treeBlock 0 1 s10Check = true := by decide +kernel
theorem s10Blocks : treeBlock 0 1 s10Check = true := s10Block0
theorem s10Known : Known s10Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Stock : Lower s10Mask s10StockWords s10Goal 4 := by
  apply lowerDag _ _ _ _ s10Autos _ _ _ s10Known _ s10Roots s10Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s10StockWords; decide +kernel
  · decide +kernel
  · simp only [s10Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s11Mask : Nat := 0x55005500
abbrev s11Goal : Nat := sGoal &&& s11Mask
abbrev s11StockWords : List Nat := projectDAGStock s11Mask sBase [1, 2, 4]
def s11Fact : (Nat × List Nat × Nat × Nat) := (s11Mask, s11StockWords, 4, s11Goal)
def s11Cuts : List (Nat × List Nat × Nat × Nat) := []
def s11Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[14, 26, 28, 14, 14, 14, 14, 14, 14, 14, 14, 14, 10, 12, 24, 10, 10, 10, 10, 10, 10, 10, 10, 10], rfl⟩
def s11Sample : (Nat × Nat) := (0xc070141a06038181c0c068140e, 6)
def s11Witnesses := unpackWitnesses s11StockWords [7180, 269322, 537610]
def s11Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s11Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s11Tags := dagTraceTags s11Mask 6 (dagTagBases s11StockWords 0x36b5b 0x22311 6) 3 s11Data
def s11States := dagTrace s11Mask s11StockWords 3 s11Data
def s11MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s11Moves := dagMoves s11MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Autos : DagMovesOK s11Mask s11Goal 64 s11Moves := dagMovesOfCheck (by decide +kernel)
def s11Check := dagCheckNode s11Mask s11Goal s11Chart (dagKnownCloses s11Goal s11Cuts) 1 s11States s11Moves s11Links s11Sample s11Tags
def s11RootAt (token : Nat) : Bool :=
  let s := rootState s11StockWords 3 token
  !dagAllowedRoot s11Witnesses s.2.1 || dagLocal s11Mask s11Goal s11Chart (dagKnownCloses s11Goal s11Cuts) s ||
  dagRef 1 s11States s11Moves s11Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11RootBlock0 : treeBlock 0 8 s11RootAt = true := by decide +kernel
theorem s11Roots : dagCheckRoots s11Mask s11Goal s11Chart (dagKnownCloses s11Goal s11Cuts) s11Witnesses (dagRef 1 s11States s11Moves s11Links 0) s11StockWords 3 = true := s11RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Block0 : treeBlock 0 1 s11Check = true := by decide +kernel
theorem s11Blocks : treeBlock 0 1 s11Check = true := s11Block0
theorem s11Known : Known s11Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Stock : Lower s11Mask s11StockWords s11Goal 4 := by
  apply lowerDag _ _ _ _ s11Autos _ _ _ s11Known _ s11Roots s11Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s11StockWords; decide +kernel
  · decide +kernel
  · simp only [s11Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s12Mask : Nat := 0x505000005050
abbrev s12Goal : Nat := sGoal &&& s12Mask
abbrev s12StockWords : List Nat := projectDAGStock s12Mask sBase [1, 3, 5]
def s12Fact : (Nat × List Nat × Nat × Nat) := (s12Mask, s12StockWords, 4, s12Goal)
def s12Cuts : List (Nat × List Nat × Nat × Nat) := []
def s12Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[14, 38, 44, 14, 14, 14, 14, 14, 14, 14, 14, 14, 6, 12, 36, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩
def s12Sample : (Nat × Nat) := (0x120b00c2606038182c120980c0e, 6)
def s12Witnesses := unpackWitnesses s12StockWords [7180, 269318, 543750]
def s12Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s12Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s12Tags := dagTraceTags s12Mask 6 (dagTagBases s12StockWords 0x36b5b 0x22311 6) 3 s12Data
def s12States := dagTrace s12Mask s12StockWords 3 s12Data
def s12MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s12Moves := dagMoves s12MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Autos : DagMovesOK s12Mask s12Goal 64 s12Moves := dagMovesOfCheck (by decide +kernel)
def s12Check := dagCheckNode s12Mask s12Goal s12Chart (dagKnownCloses s12Goal s12Cuts) 1 s12States s12Moves s12Links s12Sample s12Tags
def s12RootAt (token : Nat) : Bool :=
  let s := rootState s12StockWords 3 token
  !dagAllowedRoot s12Witnesses s.2.1 || dagLocal s12Mask s12Goal s12Chart (dagKnownCloses s12Goal s12Cuts) s ||
  dagRef 1 s12States s12Moves s12Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12RootBlock0 : treeBlock 0 8 s12RootAt = true := by decide +kernel
theorem s12Roots : dagCheckRoots s12Mask s12Goal s12Chart (dagKnownCloses s12Goal s12Cuts) s12Witnesses (dagRef 1 s12States s12Moves s12Links 0) s12StockWords 3 = true := s12RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block0 : treeBlock 0 1 s12Check = true := by decide +kernel
theorem s12Blocks : treeBlock 0 1 s12Check = true := s12Block0
theorem s12Known : Known s12Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Stock : Lower s12Mask s12StockWords s12Goal 4 := by
  apply lowerDag _ _ _ _ s12Autos _ _ _ s12Known _ s12Roots s12Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s12StockWords; decide +kernel
  · decide +kernel
  · simp only [s12Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s13Mask : Nat := 0xa0a00000a0a
abbrev s13Goal : Nat := sGoal &&& s13Mask
abbrev s13StockWords : List Nat := projectDAGStock s13Mask sBase [1, 3, 5]
def s13Fact : (Nat × List Nat × Nat × Nat) := (s13Mask, s13StockWords, 4, s13Goal)
def s13Cuts : List (Nat × List Nat × Nat × Nat) := []
def s13Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 35, 41, 11, 11, 11, 11, 11, 11, 11, 11, 11, 3, 9, 33, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s13Sample : (Nat × Nat) := (0x108a406230482c12291088c060b, 6)
def s13Witnesses := unpackWitnesses s13StockWords [5641, 267779, 542211]
def s13Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 1 1
def s13Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s13Tags := dagTraceTags s13Mask 6 (dagTagBases s13StockWords 0x36b5b 0x22311 6) 3 s13Data
def s13States := dagTrace s13Mask s13StockWords 3 s13Data
def s13MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s13Moves := dagMoves s13MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Autos : DagMovesOK s13Mask s13Goal 64 s13Moves := dagMovesOfCheck (by decide +kernel)
def s13Check := dagCheckNode s13Mask s13Goal s13Chart (dagKnownCloses s13Goal s13Cuts) 1 s13States s13Moves s13Links s13Sample s13Tags
def s13RootAt (token : Nat) : Bool :=
  let s := rootState s13StockWords 3 token
  !dagAllowedRoot s13Witnesses s.2.1 || dagLocal s13Mask s13Goal s13Chart (dagKnownCloses s13Goal s13Cuts) s ||
  dagRef 1 s13States s13Moves s13Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13RootBlock0 : treeBlock 0 8 s13RootAt = true := by decide +kernel
theorem s13Roots : dagCheckRoots s13Mask s13Goal s13Chart (dagKnownCloses s13Goal s13Cuts) s13Witnesses (dagRef 1 s13States s13Moves s13Links 0) s13StockWords 3 = true := s13RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Block0 : treeBlock 0 1 s13Check = true := by decide +kernel
theorem s13Blocks : treeBlock 0 1 s13Check = true := s13Block0
theorem s13Known : Known s13Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Stock : Lower s13Mask s13StockWords s13Goal 4 := by
  apply lowerDag _ _ _ _ s13Autos _ _ _ s13Known _ s13Roots s13Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s13StockWords; decide +kernel
  · decide +kernel
  · simp only [s13Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s14Mask : Nat := 0xa0a00000a0a
abbrev s14Goal : Nat := sGoal &&& s14Mask
abbrev s14StockWords : List Nat := projectDAGStock s14Mask sBase [1, 3, 5, 7]
def s14Fact : (Nat × List Nat × Nat × Nat) := (s14Mask, s14StockWords, 4, s14Goal)
def s14Cuts : List (Nat × List Nat × Nat × Nat) := [s13Fact]
def s14Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 35, 41, 11, 11, 11, 11, 11, 11, 11, 11, 11, 3, 9, 33, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s14Sample : (Nat × Nat) := (0x12290182c120b, 3)
def s14Witnesses := unpackWitnesses s14StockWords [267779, 542211]
def s14Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0xe 2 1 4 1 1 1
def s14Data : (Nat → Nat × Nat) := fun i => decodeNode 1 5 0x1c i
def s14Tags := dagTraceTags s14Mask 3 (dagTagBases s14StockWords 0x93b 0xa2a 3) 3 s14Data
def s14States := dagTrace s14Mask s14StockWords 3 s14Data
def s14MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s14Moves := dagMoves s14MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Autos : DagMovesOK s14Mask s14Goal 64 s14Moves := dagMovesOfCheck (by decide +kernel)
def s14Check := dagCheckNode s14Mask s14Goal s14Chart (dagKnownCloses s14Goal s14Cuts) 1 s14States s14Moves s14Links s14Sample s14Tags
def s14RootAt (token : Nat) : Bool :=
  let s := rootState s14StockWords 3 token
  !dagAllowedRoot s14Witnesses s.2.1 || dagLocal s14Mask s14Goal s14Chart (dagKnownCloses s14Goal s14Cuts) s ||
  dagRef 1 s14States s14Moves s14Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14RootBlock0 : treeBlock 0 16 s14RootAt = true := by decide +kernel
theorem s14Roots : dagCheckRoots s14Mask s14Goal s14Chart (dagKnownCloses s14Goal s14Cuts) s14Witnesses (dagRef 1 s14States s14Moves s14Links 0) s14StockWords 3 = true := s14RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Block0 : treeBlock 0 1 s14Check = true := by decide +kernel
theorem s14Blocks : treeBlock 0 1 s14Check = true := s14Block0
theorem s14Known : Known s14Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s13Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Stock : Lower s14Mask s14StockWords s14Goal 4 := by
  apply lowerDag _ _ _ _ s14Autos _ _ _ s14Known _ s14Roots s14Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s14StockWords; decide +kernel
  · decide +kernel
  · simp only [s14Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s15Mask : Nat := 0xff00ff00
abbrev s15Goal : Nat := sGoal &&& s15Mask
abbrev s15StockWords : List Nat := projectDAGStock s15Mask sBase [0, 1, 2, 4]
def s15Fact : (Nat × List Nat × Nat × Nat) := (s15Mask, s15StockWords, 7, s15Goal)
def s15Cuts : List (Nat × List Nat × Nat × Nat) := [s1Fact, s11Fact, s3Fact, s6Fact]
def s15Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 13, 14, 25, 26, 28, 11, 11, 11, 11, 11, 11, 9, 10, 12, 24, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s15Sample : (Nat × Nat) := (0x603812190c070180d0482c301a0c064140e06070120d0502c141a, 12)
def s15Witnesses := unpackWitnesses s15StockWords [5642, 267785, 530953, 799241]
def s15Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x1c0c9e4303719a4c242e4702cc3401 0x572582d881918a093282a020e18a4418f07029a802214072a19b4432a2806c100a9949622620046282a4b13315e16200c6578cc7e098a3302b4603e0c04c08040000f 9 4 12 4 3 4
def s15Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x620b92c1328931e7029732b101c502a401313142008100f0 i
def s15Tags := dagTraceTags s15Mask 12 (dagTagBases s15StockWords 0x669b1c8d35a6 0x260908013484 12) 6 s15Data
def s15States := dagTrace s15Mask s15StockWords 6 s15Data
def s15Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])]
def s15Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s15Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s15Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])]
def s15Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s15Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s15Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc0c00303c0c00303, 0), (0xc0c00000c0c, 2), (0x303000003030, 12), (0xc0c00000c0c0, 14)], [(0x3030000030300000, 2), (0xc0c00000c0c0000, 12), (0x303000003030000, 14)])]
def s15Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 1, 3, 2, 5] 0 i.val)
def s15Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 4, 3, 1, 5] 0 i.val)
def s15Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])]
def s15Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s15Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s15Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9090090990900909, 0), (0x2020020220200202, 1), (0x404000004040, 11), (0x909000009090, 12), (0x202000002020, 13)], [(0x4040040440400404, 1), (0x202000002020000, 11), (0x909000009090000, 12), (0x404000004040000, 13)])]
def s15Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 4, 3, 2, 5] 0 i.val)
def s15Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 4, 3, 2, 5] 0 i.val)
def s15Move5Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s15Move5Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s15Move5Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s15MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s15Move0Stages, s15Move0Map, s15Move0Inverse), (s15Move1Stages, s15Move1Map, s15Move1Inverse), (s15Move2Stages, s15Move2Map, s15Move2Inverse), (s15Move3Stages, s15Move3Map, s15Move3Inverse), (s15Move4Stages, s15Move4Map, s15Move4Inverse), (s15Move5Stages, s15Move5Map, s15Move5Inverse)]
def s15Moves := dagMoves s15MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Autos : DagMovesOK s15Mask s15Goal 64 s15Moves := dagMovesOfCheck (by decide +kernel)
def s15Check := dagCheckNode s15Mask s15Goal s15Chart (dagKnownCloses s15Goal s15Cuts) 12 s15States s15Moves s15Links s15Sample s15Tags
def s15RootAt (token : Nat) : Bool :=
  let s := rootState s15StockWords 6 token
  !dagAllowedRoot s15Witnesses s.2.1 || dagLocal s15Mask s15Goal s15Chart (dagKnownCloses s15Goal s15Cuts) s ||
  dagRef 12 s15States s15Moves s15Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15RootBlock0 : treeBlock 0 16 s15RootAt = true := by decide +kernel
theorem s15Roots : dagCheckRoots s15Mask s15Goal s15Chart (dagKnownCloses s15Goal s15Cuts) s15Witnesses (dagRef 12 s15States s15Moves s15Links 0) s15StockWords 6 = true := s15RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Block0 : treeBlock 0 12 s15Check = true := by decide +kernel
theorem s15Blocks : treeBlock 0 12 s15Check = true := s15Block0
theorem s15Known : Known s15Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s6Stock) s3Stock) s11Stock) s1Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Stock : Lower s15Mask s15StockWords s15Goal 7 := by
  apply lowerDag _ _ _ _ s15Autos _ _ _ s15Known _ s15Roots s15Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s15StockWords; decide +kernel
  · decide +kernel
  · simp only [s15Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s16Mask : Nat := 0xffff
abbrev s16Goal : Nat := sGoal &&& s16Mask
abbrev s16StockWords : List Nat := projectDAGStock s16Mask sBase [0, 1, 2, 3]
def s16Fact : (Nat × List Nat × Nat × Nat) := (s16Mask, s16StockWords, 5, s16Goal)
def s16Witnesses := unpackWitnesses s16StockWords [2564, 267785, 526849, 792067]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Stock : Lower s16Mask s16StockWords s16Goal 5 := by
  apply essentialLift (witnesses := s16Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
def s17Mask : Nat := 0xffff00000000
abbrev s17Goal : Nat := sGoal &&& s17Mask
abbrev s17StockWords : List Nat := projectDAGStock s17Mask sBase [0, 1, 2, 3]
def s17Fact : (Nat × List Nat × Nat × Nat) := (s17Mask, s17StockWords, 5, s17Goal)
def s17Witnesses := unpackWitnesses s17StockWords [17954, 280097, 543265, 807457]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Stock : Lower s17Mask s17StockWords s17Goal 5 := by
  apply essentialLift (witnesses := s17Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s18Mask : Nat := 0xff00ff00000000
abbrev s18Goal : Nat := sGoal &&& s18Mask
abbrev s18StockWords : List Nat := projectDAGStock s18Mask sBase [0, 1, 2, 4]
def s18Fact : (Nat × List Nat × Nat × Nat) := (s18Mask, s18StockWords, 5, s18Goal)
def s18Witnesses := unpackWitnesses s18StockWords [17954, 280097, 543265, 811553]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Stock : Lower s18Mask s18StockWords s18Goal 5 := by
  apply essentialLift (witnesses := s18Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s19Mask : Nat := 0xff000000ff
abbrev s19Goal : Nat := sGoal &&& s19Mask
abbrev s19StockWords : List Nat := projectDAGStock s19Mask sBase [0, 1, 2, 5]
def s19Fact : (Nat × List Nat × Nat × Nat) := (s19Mask, s19StockWords, 5, s19Goal)
def s19Witnesses := unpackWitnesses s19StockWords [2564, 280097, 526849, 804355]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Stock : Lower s19Mask s19StockWords s19Goal 5 := by
  apply essentialLift (witnesses := s19Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s20Mask : Nat := 0xff000000ff00
abbrev s20Goal : Nat := sGoal &&& s20Mask
abbrev s20StockWords : List Nat := projectDAGStock s20Mask sBase [0, 1, 2, 5]
def s20Fact : (Nat × List Nat × Nat × Nat) := (s20Mask, s20StockWords, 5, s20Goal)
def s20Witnesses := unpackWitnesses s20StockWords [5642, 267785, 530953, 807433]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Stock : Lower s20Mask s20StockWords s20Goal 5 := by
  apply essentialLift (witnesses := s20Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
def s21Mask : Nat := 0xf0f0f0f
abbrev s21Goal : Nat := sGoal &&& s21Mask
abbrev s21StockWords : List Nat := projectDAGStock s21Mask sBase [0, 1, 3, 4]
def s21Fact : (Nat × List Nat × Nat × Nat) := (s21Mask, s21StockWords, 5, s21Goal)
def s21Witnesses := unpackWitnesses s21StockWords [5642, 267785, 529923, 795137]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Stock : Lower s21Mask s21StockWords s21Goal 5 := by
  apply essentialLift (witnesses := s21Witnesses) (cut := s3Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s3StockWords) (by decide +kernel)
  · exact s3Stock
  · decide +kernel
def s22Mask : Nat := 0xf0f0f0f00000000
abbrev s22Goal : Nat := sGoal &&& s22Mask
abbrev s22StockWords : List Nat := projectDAGStock s22Mask sBase [0, 1, 3, 4]
def s22Fact : (Nat × List Nat × Nat × Nat) := (s22Mask, s22StockWords, 5, s22Goal)
def s22Witnesses := unpackWitnesses s22StockWords [17954, 280097, 545313, 811553]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Stock : Lower s22Mask s22StockWords s22Goal 5 := by
  apply essentialLift (witnesses := s22Witnesses) (cut := s2Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s2StockWords) (by decide +kernel)
  · exact s2Stock
  · decide +kernel
def s23Mask : Nat := 0xf0f00000f0f
abbrev s23Goal : Nat := sGoal &&& s23Mask
abbrev s23StockWords : List Nat := projectDAGStock s23Mask sBase [0, 1, 3, 5]
def s23Fact : (Nat × List Nat × Nat × Nat) := (s23Mask, s23StockWords, 5, s23Goal)
def s23Witnesses := unpackWitnesses s23StockWords [5642, 267785, 529923, 804355]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Stock : Lower s23Mask s23StockWords s23Goal 5 := by
  apply essentialLift (witnesses := s23Witnesses) (cut := s13Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s13StockWords) (by decide +kernel)
  · exact s13Stock
  · decide +kernel
def s24Mask : Nat := 0xf0f00000f0f0
abbrev s24Goal : Nat := sGoal &&& s24Mask
abbrev s24StockWords : List Nat := projectDAGStock s24Mask sBase [0, 1, 3, 5]
def s24Fact : (Nat × List Nat × Nat × Nat) := (s24Mask, s24StockWords, 5, s24Goal)
def s24Witnesses := unpackWitnesses s24StockWords [2564, 269324, 531462, 805894]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Stock : Lower s24Mask s24StockWords s24Goal 5 := by
  apply essentialLift (witnesses := s24Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s25Mask : Nat := 0xf000f000f000f
abbrev s25Goal : Nat := sGoal &&& s25Mask
abbrev s25StockWords : List Nat := projectDAGStock s25Mask sBase [0, 1, 4, 5]
def s25Fact : (Nat × List Nat × Nat × Nat) := (s25Mask, s25StockWords, 5, s25Goal)
def s25Witnesses := unpackWitnesses s25StockWords [8720, 280097, 532993, 804355]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Stock : Lower s25Mask s25StockWords s25Goal 5 := by
  apply essentialLift (witnesses := s25Witnesses) (cut := s2Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s2StockWords) (by decide +kernel)
  · exact s2Stock
  · decide +kernel
def s26Mask : Nat := 0xf000f000f000f00
abbrev s26Goal : Nat := sGoal &&& s26Mask
abbrev s26StockWords : List Nat := projectDAGStock s26Mask sBase [0, 1, 4, 5]
def s26Fact : (Nat × List Nat × Nat × Nat) := (s26Mask, s26StockWords, 5, s26Goal)
def s26Witnesses := unpackWitnesses s26StockWords [5642, 267785, 537097, 807433]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Stock : Lower s26Mask s26StockWords s26Goal 5 := by
  apply essentialLift (witnesses := s26Witnesses) (cut := s3Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s3StockWords) (by decide +kernel)
  · exact s3Stock
  · decide +kernel
def s27Mask : Nat := 0x33333333
abbrev s27Goal : Nat := sGoal &&& s27Mask
abbrev s27StockWords : List Nat := projectDAGStock s27Mask sBase [0, 2, 3, 4]
def s27Fact : (Nat × List Nat × Nat × Nat) := (s27Mask, s27StockWords, 5, s27Goal)
def s27Witnesses := unpackWitnesses s27StockWords [2564, 264705, 538644, 795137]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Stock : Lower s27Mask s27StockWords s27Goal 5 := by
  apply essentialLift (witnesses := s27Witnesses) (cut := s6Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s6StockWords) (by decide +kernel)
  · exact s6Stock
  · decide +kernel
def s28Mask : Nat := 0x3333333300000000
abbrev s28Goal : Nat := sGoal &&& s28Mask
abbrev s28StockWords : List Nat := projectDAGStock s28Mask sBase [0, 2, 3, 4]
def s28Fact : (Nat × List Nat × Nat × Nat) := (s28Mask, s28StockWords, 5, s28Goal)
def s28Witnesses := unpackWitnesses s28StockWords [18980, 281121, 545313, 811553]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Stock : Lower s28Mask s28StockWords s28Goal 5 := by
  apply essentialLift (witnesses := s28Witnesses) (cut := s4Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s4StockWords) (by decide +kernel)
  · exact s4Stock
  · decide +kernel
def s29Mask : Nat := 0xcccccccc
abbrev s29Goal : Nat := sGoal &&& s29Mask
abbrev s29StockWords : List Nat := projectDAGStock s29Mask sBase [0, 2, 3, 4]
def s29Fact : (Nat × List Nat × Nat × Nat) := (s29Mask, s29StockWords, 5, s29Goal)
def s29Witnesses := unpackWitnesses s29StockWords [3590, 265731, 529923, 796163]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Stock : Lower s29Mask s29StockWords s29Goal 5 := by
  apply essentialLift (witnesses := s29Witnesses) (cut := s5Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s5StockWords) (by decide +kernel)
  · exact s5Stock
  · decide +kernel
def s30Mask : Nat := 0x333300003333
abbrev s30Goal : Nat := sGoal &&& s30Mask
abbrev s30StockWords : List Nat := projectDAGStock s30Mask sBase [0, 2, 3, 5]
def s30Fact : (Nat × List Nat × Nat × Nat) := (s30Mask, s30StockWords, 5, s30Goal)
def s30Witnesses := unpackWitnesses s30StockWords [2564, 264705, 545313, 807433]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Stock : Lower s30Mask s30StockWords s30Goal 5 := by
  apply essentialLift (witnesses := s30Witnesses) (cut := s4Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s4StockWords) (by decide +kernel)
  · exact s4Stock
  · decide +kernel
def s31Mask : Nat := 0xcccc0000cccc
abbrev s31Goal : Nat := sGoal &&& s31Mask
abbrev s31StockWords : List Nat := projectDAGStock s31Mask sBase [0, 2, 3, 5]
def s31Fact : (Nat × List Nat × Nat × Nat) := (s31Mask, s31StockWords, 5, s31Goal)
def s31Witnesses := unpackWitnesses s31StockWords [3590, 265731, 529923, 804355]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Stock : Lower s31Mask s31StockWords s31Goal 5 := by
  apply essentialLift (witnesses := s31Witnesses) (cut := s5Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s5StockWords) (by decide +kernel)
  · exact s5Stock
  · decide +kernel
def s32Mask : Nat := 0x3300330033003300
abbrev s32Goal : Nat := sGoal &&& s32Mask
abbrev s32StockWords : List Nat := projectDAGStock s32Mask sBase [0, 2, 4, 5]
def s32Fact : (Nat × List Nat × Nat × Nat) := (s32Mask, s32StockWords, 5, s32Goal)
def s32Witnesses := unpackWitnesses s32StockWords [6668, 268809, 537097, 807433]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Stock : Lower s32Mask s32StockWords s32Goal 5 := by
  apply essentialLift (witnesses := s32Witnesses) (cut := s6Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s6StockWords) (by decide +kernel)
  · exact s6Stock
  · decide +kernel
def s33Mask : Nat := 0xcc00cc00cc00cc
abbrev s33Goal : Nat := sGoal &&& s33Mask
abbrev s33StockWords : List Nat := projectDAGStock s33Mask sBase [0, 2, 4, 5]
def s33Fact : (Nat × List Nat × Nat × Nat) := (s33Mask, s33StockWords, 5, s33Goal)
def s33Witnesses := unpackWitnesses s33StockWords [3590, 265731, 534019, 804355]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Stock : Lower s33Mask s33StockWords s33Goal 5 := by
  apply essentialLift (witnesses := s33Witnesses) (cut := s8Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s8StockWords) (by decide +kernel)
  · exact s8Stock
  · decide +kernel
def s34Mask : Nat := 0xc0c0c0c0c0c0c0c
abbrev s34Goal : Nat := sGoal &&& s34Mask
abbrev s34StockWords : List Nat := projectDAGStock s34Mask sBase [0, 3, 4, 5]
def s34Fact : (Nat × List Nat × Nat × Nat) := (s34Mask, s34StockWords, 5, s34Goal)
def s34Witnesses := unpackWitnesses s34StockWords [5642, 267779, 534019, 804355]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Stock : Lower s34Mask s34StockWords s34Goal 5 := by
  apply essentialLift (witnesses := s34Witnesses) (cut := s9Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s9StockWords) (by decide +kernel)
  · exact s9Stock
  · decide +kernel
def s35Mask : Nat := 0x55555555
abbrev s35Goal : Nat := sGoal &&& s35Mask
abbrev s35StockWords : List Nat := projectDAGStock s35Mask sBase [1, 2, 3, 4]
def s35Fact : (Nat × List Nat × Nat × Nat) := (s35Mask, s35StockWords, 5, s35Goal)
def s35Witnesses := unpackWitnesses s35StockWords [7180, 269322, 531462, 799754]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Stock : Lower s35Mask s35StockWords s35Goal 5 := by
  apply essentialLift (witnesses := s35Witnesses) (cut := s11Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s11StockWords) (by decide +kernel)
  · exact s11Stock
  · decide +kernel
def s36Mask : Nat := 0x555500005555
abbrev s36Goal : Nat := sGoal &&& s36Mask
abbrev s36StockWords : List Nat := projectDAGStock s36Mask sBase [1, 2, 3, 5]
def s36Fact : (Nat × List Nat × Nat × Nat) := (s36Mask, s36StockWords, 5, s36Goal)
def s36Witnesses := unpackWitnesses s36StockWords [7180, 269322, 531462, 805894]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Stock : Lower s36Mask s36StockWords s36Goal 5 := by
  apply essentialLift (witnesses := s36Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s37Mask : Nat := 0xaaaa0000aaaa
abbrev s37Goal : Nat := sGoal &&& s37Mask
abbrev s37StockWords : List Nat := projectDAGStock s37Mask sBase [1, 2, 3, 5]
def s37Fact : (Nat × List Nat × Nat × Nat) := (s37Mask, s37StockWords, 5, s37Goal)
def s37Witnesses := unpackWitnesses s37StockWords [5641, 264705, 529923, 804355]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Stock : Lower s37Mask s37StockWords s37Goal 5 := by
  apply essentialLift (witnesses := s37Witnesses) (cut := s13Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s13StockWords) (by decide +kernel)
  · exact s13Stock
  · decide +kernel
def s38Mask : Nat := 0x5500550055005500
abbrev s38Goal : Nat := sGoal &&& s38Mask
abbrev s38StockWords : List Nat := projectDAGStock s38Mask sBase [1, 2, 4, 5]
def s38Fact : (Nat × List Nat × Nat × Nat) := (s38Mask, s38StockWords, 5, s38Goal)
def s38Witnesses := unpackWitnesses s38StockWords [7180, 269322, 537610, 808972]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Stock : Lower s38Mask s38StockWords s38Goal 5 := by
  apply essentialLift (witnesses := s38Witnesses) (cut := s11Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s11StockWords) (by decide +kernel)
  · exact s11Stock
  · decide +kernel
def s39Mask : Nat := 0x5050505050505050
abbrev s39Goal : Nat := sGoal &&& s39Mask
abbrev s39StockWords : List Nat := projectDAGStock s39Mask sBase [1, 3, 4, 5]
def s39Fact : (Nat × List Nat × Nat × Nat) := (s39Mask, s39StockWords, 5, s39Goal)
def s39Witnesses := unpackWitnesses s39StockWords [7180, 269318, 538636, 805894]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Stock : Lower s39Mask s39StockWords s39Goal 5 := by
  apply essentialLift (witnesses := s39Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s40Mask : Nat := 0xa0a0a0a0a0a0a0a
abbrev s40Goal : Nat := sGoal &&& s40Mask
abbrev s40StockWords : List Nat := projectDAGStock s40Mask sBase [1, 3, 4, 5]
def s40Fact : (Nat × List Nat × Nat × Nat) := (s40Mask, s40StockWords, 5, s40Goal)
def s40Witnesses := unpackWitnesses s40StockWords [5641, 267779, 532993, 804355]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Stock : Lower s40Mask s40StockWords s40Goal 5 := by
  apply essentialLift (witnesses := s40Witnesses) (cut := s13Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s13StockWords) (by decide +kernel)
  · exact s13Stock
  · decide +kernel
def s41Mask : Nat := 0xffff
abbrev s41Goal : Nat := sGoal &&& s41Mask
abbrev s41StockWords : List Nat := projectDAGStock s41Mask sBase [0, 1, 2, 3, 6]
def s41Fact : (Nat × List Nat × Nat × Nat) := (s41Mask, s41StockWords, 5, s41Goal)
def s41Cuts : List (Nat × List Nat × Nat × Nat) := [s16Fact]
def s41Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 6, 9, 10, 12, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s41Sample : (Nat × Nat) := (0x60380c0e008140805, 4)
def s41Witnesses := unpackWitnesses s41StockWords [267785, 526849, 792067]
def s41Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x1c1e 3 1 5 1 1 1
def s41Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0xc7c i
def s41Tags := dagTraceTags s41Mask 4 (dagTagBases s41StockWords 0xccfc3 0xd8d42 4) 4 s41Data
def s41States := dagTrace s41Mask s41StockWords 4 s41Data
def s41MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s41Moves := dagMoves s41MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Autos : DagMovesOK s41Mask s41Goal 64 s41Moves := dagMovesOfCheck (by decide +kernel)
def s41Check := dagCheckNode s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) 2 s41States s41Moves s41Links s41Sample s41Tags
def s41RootAt (token : Nat) : Bool :=
  let s := rootState s41StockWords 4 token
  !dagAllowedRoot s41Witnesses s.2.1 || dagLocal s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) s ||
  dagRef 2 s41States s41Moves s41Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41RootBlock0 : treeBlock 0 32 s41RootAt = true := by decide +kernel
theorem s41Roots : dagCheckRoots s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) s41Witnesses (dagRef 2 s41States s41Moves s41Links 0) s41StockWords 4 = true := s41RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block0 : treeBlock 0 2 s41Check = true := by decide +kernel
theorem s41Blocks : treeBlock 0 2 s41Check = true := s41Block0
theorem s41Known : Known s41Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s16Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Stock : Lower s41Mask s41StockWords s41Goal 5 := by
  apply lowerDag _ _ _ _ s41Autos _ _ _ s41Known _ s41Roots s41Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s41StockWords; decide +kernel
  · decide +kernel
  · simp only [s41Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s42Mask : Nat := 0xffff00000000
abbrev s42Goal : Nat := sGoal &&& s42Mask
abbrev s42StockWords : List Nat := projectDAGStock s42Mask sBase [0, 1, 2, 3, 6]
def s42Fact : (Nat × List Nat × Nat × Nat) := (s42Mask, s42StockWords, 5, s42Goal)
def s42Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact]
def s42Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[35, 37, 38, 41, 44, 35, 35, 35, 35, 35, 35, 35, 33, 36, 42, 33, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s42Sample : (Nat × Nat) := (0x120b044261088c4423, 4)
def s42Witnesses := unpackWitnesses s42StockWords [280097, 543265, 807457]
def s42Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x1e1e 3 1 5 1 1 1
def s42Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0xe7c i
def s42Tags := dagTraceTags s42Mask 4 (dagTagBases s42StockWords 0xc8c73 0xd0852 4) 4 s42Data
def s42States := dagTrace s42Mask s42StockWords 4 s42Data
def s42MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s42Moves := dagMoves s42MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Autos : DagMovesOK s42Mask s42Goal 64 s42Moves := dagMovesOfCheck (by decide +kernel)
def s42Check := dagCheckNode s42Mask s42Goal s42Chart (dagKnownCloses s42Goal s42Cuts) 2 s42States s42Moves s42Links s42Sample s42Tags
def s42RootAt (token : Nat) : Bool :=
  let s := rootState s42StockWords 4 token
  !dagAllowedRoot s42Witnesses s.2.1 || dagLocal s42Mask s42Goal s42Chart (dagKnownCloses s42Goal s42Cuts) s ||
  dagRef 2 s42States s42Moves s42Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42RootBlock0 : treeBlock 0 32 s42RootAt = true := by decide +kernel
theorem s42Roots : dagCheckRoots s42Mask s42Goal s42Chart (dagKnownCloses s42Goal s42Cuts) s42Witnesses (dagRef 2 s42States s42Moves s42Links 0) s42StockWords 4 = true := s42RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Block0 : treeBlock 0 2 s42Check = true := by decide +kernel
theorem s42Blocks : treeBlock 0 2 s42Check = true := s42Block0
theorem s42Known : Known s42Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s17Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Stock : Lower s42Mask s42StockWords s42Goal 5 := by
  apply lowerDag _ _ _ _ s42Autos _ _ _ s42Known _ s42Roots s42Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s42StockWords; decide +kernel
  · decide +kernel
  · simp only [s42Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s43Mask : Nat := 0xffff
abbrev s43Goal : Nat := sGoal &&& s43Mask
abbrev s43StockWords : List Nat := projectDAGStock s43Mask sBase [0, 1, 2, 3, 7]
def s43Fact : (Nat × List Nat × Nat × Nat) := (s43Mask, s43StockWords, 5, s43Goal)
def s43Cuts : List (Nat × List Nat × Nat × Nat) := [s16Fact, s5Fact]
def s43Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 6, 9, 10, 12, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s43Sample : (Nat × Nat) := (0x0, 0)
def s43Witnesses := unpackWitnesses s43StockWords [2564, 526849, 792067]
def s43Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s43Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s43Tags := dagTraceTags s43Mask 0 (dagTagBases s43StockWords 0x0 0x0 0) 4 s43Data
def s43States := dagTrace s43Mask s43StockWords 4 s43Data
def s43MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s43Moves := dagMoves s43MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Autos : DagMovesOK s43Mask s43Goal 64 s43Moves := dagMovesOfCheck (by decide +kernel)
def s43Check := dagCheckNode s43Mask s43Goal s43Chart (dagKnownCloses s43Goal s43Cuts) 0 s43States s43Moves s43Links s43Sample s43Tags
def s43RootAt (token : Nat) : Bool :=
  let s := rootState s43StockWords 4 token
  !dagAllowedRoot s43Witnesses s.2.1 || dagLocal s43Mask s43Goal s43Chart (dagKnownCloses s43Goal s43Cuts) s ||
  dagRef 0 s43States s43Moves s43Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43RootBlock0 : treeBlock 0 32 s43RootAt = true := by decide +kernel
theorem s43Roots : dagCheckRoots s43Mask s43Goal s43Chart (dagKnownCloses s43Goal s43Cuts) s43Witnesses (dagRef 0 s43States s43Moves s43Links 0) s43StockWords 4 = true := s43RootBlock0
theorem s43Blocks : treeBlock 0 0 s43Check = true := by decide +kernel
theorem s43Known : Known s43Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s5Stock) s16Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Stock : Lower s43Mask s43StockWords s43Goal 5 := by
  apply lowerDag _ _ _ _ s43Autos _ _ _ s43Known _ s43Roots s43Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s43StockWords; decide +kernel
  · decide +kernel
  · simp only [s43Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s44Mask : Nat := 0xffff00000000
abbrev s44Goal : Nat := sGoal &&& s44Mask
abbrev s44StockWords : List Nat := projectDAGStock s44Mask sBase [0, 1, 2, 3, 7]
def s44Fact : (Nat × List Nat × Nat × Nat) := (s44Mask, s44StockWords, 5, s44Goal)
def s44Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact, s4Fact]
def s44Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[35, 37, 38, 41, 44, 35, 35, 35, 35, 35, 35, 35, 33, 36, 42, 33, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s44Sample : (Nat × Nat) := (0x0, 0)
def s44Witnesses := unpackWitnesses s44StockWords [17954, 543265, 807457]
def s44Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s44Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s44Tags := dagTraceTags s44Mask 0 (dagTagBases s44StockWords 0x0 0x0 0) 4 s44Data
def s44States := dagTrace s44Mask s44StockWords 4 s44Data
def s44MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s44Moves := dagMoves s44MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Autos : DagMovesOK s44Mask s44Goal 64 s44Moves := dagMovesOfCheck (by decide +kernel)
def s44Check := dagCheckNode s44Mask s44Goal s44Chart (dagKnownCloses s44Goal s44Cuts) 0 s44States s44Moves s44Links s44Sample s44Tags
def s44RootAt (token : Nat) : Bool :=
  let s := rootState s44StockWords 4 token
  !dagAllowedRoot s44Witnesses s.2.1 || dagLocal s44Mask s44Goal s44Chart (dagKnownCloses s44Goal s44Cuts) s ||
  dagRef 0 s44States s44Moves s44Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44RootBlock0 : treeBlock 0 32 s44RootAt = true := by decide +kernel
theorem s44Roots : dagCheckRoots s44Mask s44Goal s44Chart (dagKnownCloses s44Goal s44Cuts) s44Witnesses (dagRef 0 s44States s44Moves s44Links 0) s44StockWords 4 = true := s44RootBlock0
theorem s44Blocks : treeBlock 0 0 s44Check = true := by decide +kernel
theorem s44Known : Known s44Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s4Stock) s17Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Stock : Lower s44Mask s44StockWords s44Goal 5 := by
  apply lowerDag _ _ _ _ s44Autos _ _ _ s44Known _ s44Roots s44Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s44StockWords; decide +kernel
  · decide +kernel
  · simp only [s44Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s45Mask : Nat := 0xffff
abbrev s45Goal : Nat := sGoal &&& s45Mask
abbrev s45StockWords : List Nat := projectDAGStock s45Mask sBase [0, 1, 2, 3, 8]
def s45Fact : (Nat × List Nat × Nat × Nat) := (s45Mask, s45StockWords, 5, s45Goal)
def s45Cuts : List (Nat × List Nat × Nat × Nat) := [s16Fact]
def s45Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 6, 9, 10, 12, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s45Sample : (Nat × Nat) := (0x482c060b020140205, 4)
def s45Witnesses := unpackWitnesses s45StockWords [2564, 267785, 792067]
def s45Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x71801b 3 1 10 1 1 1
def s45Data : (Nat → Nat × Nat) := fun i => decodeNode 1 11 0x318836 i
def s45Tags := dagTraceTags s45Mask 4 (dagTagBases s45StockWords 0xcc3cf 0xd824d 4) 4 s45Data
def s45States := dagTrace s45Mask s45StockWords 4 s45Data
def s45MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s45Moves := dagMoves s45MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Autos : DagMovesOK s45Mask s45Goal 64 s45Moves := dagMovesOfCheck (by decide +kernel)
def s45Check := dagCheckNode s45Mask s45Goal s45Chart (dagKnownCloses s45Goal s45Cuts) 2 s45States s45Moves s45Links s45Sample s45Tags
def s45RootAt (token : Nat) : Bool :=
  let s := rootState s45StockWords 4 token
  !dagAllowedRoot s45Witnesses s.2.1 || dagLocal s45Mask s45Goal s45Chart (dagKnownCloses s45Goal s45Cuts) s ||
  dagRef 2 s45States s45Moves s45Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45RootBlock0 : treeBlock 0 32 s45RootAt = true := by decide +kernel
theorem s45Roots : dagCheckRoots s45Mask s45Goal s45Chart (dagKnownCloses s45Goal s45Cuts) s45Witnesses (dagRef 2 s45States s45Moves s45Links 0) s45StockWords 4 = true := s45RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Block0 : treeBlock 0 2 s45Check = true := by decide +kernel
theorem s45Blocks : treeBlock 0 2 s45Check = true := s45Block0
theorem s45Known : Known s45Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s16Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Stock : Lower s45Mask s45StockWords s45Goal 5 := by
  apply lowerDag _ _ _ _ s45Autos _ _ _ s45Known _ s45Roots s45Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s45StockWords; decide +kernel
  · decide +kernel
  · simp only [s45Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s46Mask : Nat := 0xffff00000000
abbrev s46Goal : Nat := sGoal &&& s46Mask
abbrev s46StockWords : List Nat := projectDAGStock s46Mask sBase [0, 1, 2, 3, 8]
def s46Fact : (Nat × List Nat × Nat × Nat) := (s46Mask, s46StockWords, 5, s46Goal)
def s46Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact]
def s46Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[35, 37, 38, 41, 44, 35, 35, 35, 35, 35, 35, 35, 33, 36, 42, 33, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s46Sample : (Nat × Nat) := (0x108a448251088c4225, 4)
def s46Witnesses := unpackWitnesses s46StockWords [17954, 280097, 807457]
def s46Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x71c01b 3 1 10 1 1 1
def s46Data : (Nat → Nat × Nat) := fun i => decodeNode 1 11 0x31c836 i
def s46Tags := dagTraceTags s46Mask 4 (dagTagBases s46StockWords 0xa852f 0xb040b 4) 4 s46Data
def s46States := dagTrace s46Mask s46StockWords 4 s46Data
def s46MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s46Moves := dagMoves s46MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Autos : DagMovesOK s46Mask s46Goal 64 s46Moves := dagMovesOfCheck (by decide +kernel)
def s46Check := dagCheckNode s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) 2 s46States s46Moves s46Links s46Sample s46Tags
def s46RootAt (token : Nat) : Bool :=
  let s := rootState s46StockWords 4 token
  !dagAllowedRoot s46Witnesses s.2.1 || dagLocal s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) s ||
  dagRef 2 s46States s46Moves s46Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46RootBlock0 : treeBlock 0 32 s46RootAt = true := by decide +kernel
theorem s46Roots : dagCheckRoots s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) s46Witnesses (dagRef 2 s46States s46Moves s46Links 0) s46StockWords 4 = true := s46RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block0 : treeBlock 0 2 s46Check = true := by decide +kernel
theorem s46Blocks : treeBlock 0 2 s46Check = true := s46Block0
theorem s46Known : Known s46Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s17Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Stock : Lower s46Mask s46StockWords s46Goal 5 := by
  apply lowerDag _ _ _ _ s46Autos _ _ _ s46Known _ s46Roots s46Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s46StockWords; decide +kernel
  · decide +kernel
  · simp only [s46Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s47Mask : Nat := 0xffff
abbrev s47Goal : Nat := sGoal &&& s47Mask
abbrev s47StockWords : List Nat := projectDAGStock s47Mask sBase [0, 1, 2, 3, 9]
def s47Fact : (Nat × List Nat × Nat × Nat) := (s47Mask, s47StockWords, 5, s47Goal)
def s47Cuts : List (Nat × List Nat × Nat × Nat) := [s16Fact, s1Fact]
def s47Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 6, 9, 10, 12, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s47Sample : (Nat × Nat) := (0x0, 0)
def s47Witnesses := unpackWitnesses s47StockWords [2564, 267785, 526849]
def s47Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s47Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s47Tags := dagTraceTags s47Mask 0 (dagTagBases s47StockWords 0x0 0x0 0) 4 s47Data
def s47States := dagTrace s47Mask s47StockWords 4 s47Data
def s47MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s47Moves := dagMoves s47MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Autos : DagMovesOK s47Mask s47Goal 64 s47Moves := dagMovesOfCheck (by decide +kernel)
def s47Check := dagCheckNode s47Mask s47Goal s47Chart (dagKnownCloses s47Goal s47Cuts) 0 s47States s47Moves s47Links s47Sample s47Tags
def s47RootAt (token : Nat) : Bool :=
  let s := rootState s47StockWords 4 token
  !dagAllowedRoot s47Witnesses s.2.1 || dagLocal s47Mask s47Goal s47Chart (dagKnownCloses s47Goal s47Cuts) s ||
  dagRef 0 s47States s47Moves s47Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47RootBlock0 : treeBlock 0 32 s47RootAt = true := by decide +kernel
theorem s47Roots : dagCheckRoots s47Mask s47Goal s47Chart (dagKnownCloses s47Goal s47Cuts) s47Witnesses (dagRef 0 s47States s47Moves s47Links 0) s47StockWords 4 = true := s47RootBlock0
theorem s47Blocks : treeBlock 0 0 s47Check = true := by decide +kernel
theorem s47Known : Known s47Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s1Stock) s16Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Stock : Lower s47Mask s47StockWords s47Goal 5 := by
  apply lowerDag _ _ _ _ s47Autos _ _ _ s47Known _ s47Roots s47Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s47StockWords; decide +kernel
  · decide +kernel
  · simp only [s47Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s48Mask : Nat := 0xffff00000000
abbrev s48Goal : Nat := sGoal &&& s48Mask
abbrev s48StockWords : List Nat := projectDAGStock s48Mask sBase [0, 1, 2, 3, 9]
def s48Fact : (Nat × List Nat × Nat × Nat) := (s48Mask, s48StockWords, 5, s48Goal)
def s48Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact, s0Fact]
def s48Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[35, 37, 38, 41, 44, 35, 35, 35, 35, 35, 35, 35, 33, 36, 42, 33, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s48Sample : (Nat × Nat) := (0x0, 0)
def s48Witnesses := unpackWitnesses s48StockWords [17954, 280097, 543265]
def s48Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s48Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s48Tags := dagTraceTags s48Mask 0 (dagTagBases s48StockWords 0x0 0x0 0) 4 s48Data
def s48States := dagTrace s48Mask s48StockWords 4 s48Data
def s48MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s48Moves := dagMoves s48MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Autos : DagMovesOK s48Mask s48Goal 64 s48Moves := dagMovesOfCheck (by decide +kernel)
def s48Check := dagCheckNode s48Mask s48Goal s48Chart (dagKnownCloses s48Goal s48Cuts) 0 s48States s48Moves s48Links s48Sample s48Tags
def s48RootAt (token : Nat) : Bool :=
  let s := rootState s48StockWords 4 token
  !dagAllowedRoot s48Witnesses s.2.1 || dagLocal s48Mask s48Goal s48Chart (dagKnownCloses s48Goal s48Cuts) s ||
  dagRef 0 s48States s48Moves s48Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48RootBlock0 : treeBlock 0 32 s48RootAt = true := by decide +kernel
theorem s48Roots : dagCheckRoots s48Mask s48Goal s48Chart (dagKnownCloses s48Goal s48Cuts) s48Witnesses (dagRef 0 s48States s48Moves s48Links 0) s48StockWords 4 = true := s48RootBlock0
theorem s48Blocks : treeBlock 0 0 s48Check = true := by decide +kernel
theorem s48Known : Known s48Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s0Stock) s17Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Stock : Lower s48Mask s48StockWords s48Goal 5 := by
  apply lowerDag _ _ _ _ s48Autos _ _ _ s48Known _ s48Roots s48Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s48StockWords; decide +kernel
  · decide +kernel
  · simp only [s48Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s49Mask : Nat := 0xff000000ff
abbrev s49Goal : Nat := sGoal &&& s49Mask
abbrev s49StockWords : List Nat := projectDAGStock s49Mask sBase [0, 1, 2, 5, 6]
def s49Fact : (Nat × List Nat × Nat × Nat) := (s49Mask, s49StockWords, 5, s49Goal)
def s49Cuts : List (Nat × List Nat × Nat × Nat) := [s19Fact]
def s49Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 35, 38, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 6, 33, 34, 36, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s49Sample : (Nat × Nat) := (0x120980c26008140805, 4)
def s49Witnesses := unpackWitnesses s49StockWords [280097, 526849, 804355]
def s49Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x1c1e 3 1 5 1 1 1
def s49Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0xc7c i
def s49Tags := dagTraceTags s49Mask 4 (dagTagBases s49StockWords 0xccfc3 0xd8d42 4) 4 s49Data
def s49States := dagTrace s49Mask s49StockWords 4 s49Data
def s49MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s49Moves := dagMoves s49MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Autos : DagMovesOK s49Mask s49Goal 64 s49Moves := dagMovesOfCheck (by decide +kernel)
def s49Check := dagCheckNode s49Mask s49Goal s49Chart (dagKnownCloses s49Goal s49Cuts) 2 s49States s49Moves s49Links s49Sample s49Tags
def s49RootAt (token : Nat) : Bool :=
  let s := rootState s49StockWords 4 token
  !dagAllowedRoot s49Witnesses s.2.1 || dagLocal s49Mask s49Goal s49Chart (dagKnownCloses s49Goal s49Cuts) s ||
  dagRef 2 s49States s49Moves s49Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49RootBlock0 : treeBlock 0 32 s49RootAt = true := by decide +kernel
theorem s49Roots : dagCheckRoots s49Mask s49Goal s49Chart (dagKnownCloses s49Goal s49Cuts) s49Witnesses (dagRef 2 s49States s49Moves s49Links 0) s49StockWords 4 = true := s49RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block0 : treeBlock 0 2 s49Check = true := by decide +kernel
theorem s49Blocks : treeBlock 0 2 s49Check = true := s49Block0
theorem s49Known : Known s49Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s19Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Stock : Lower s49Mask s49StockWords s49Goal 5 := by
  apply lowerDag _ _ _ _ s49Autos _ _ _ s49Known _ s49Roots s49Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s49StockWords; decide +kernel
  · decide +kernel
  · simp only [s49Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s50Mask : Nat := 0xff000000ff00
abbrev s50Goal : Nat := sGoal &&& s50Mask
abbrev s50StockWords : List Nat := projectDAGStock s50Mask sBase [0, 1, 2, 5, 6]
def s50Fact : (Nat × List Nat × Nat × Nat) := (s50Mask, s50StockWords, 5, s50Goal)
def s50Cuts : List (Nat × List Nat × Nat × Nat) := [s20Fact]
def s50Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 13, 14, 41, 44, 11, 11, 11, 11, 11, 11, 11, 9, 12, 42, 9, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s50Sample : (Nat × Nat) := (0x60b0140e0482c140b, 4)
def s50Witnesses := unpackWitnesses s50StockWords [267785, 530953, 807433]
def s50Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x1e1e 3 1 5 1 1 1
def s50Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0xe7c i
def s50Tags := dagTraceTags s50Mask 4 (dagTagBases s50StockWords 0xc8c73 0xd0852 4) 4 s50Data
def s50States := dagTrace s50Mask s50StockWords 4 s50Data
def s50MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s50Moves := dagMoves s50MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Autos : DagMovesOK s50Mask s50Goal 64 s50Moves := dagMovesOfCheck (by decide +kernel)
def s50Check := dagCheckNode s50Mask s50Goal s50Chart (dagKnownCloses s50Goal s50Cuts) 2 s50States s50Moves s50Links s50Sample s50Tags
def s50RootAt (token : Nat) : Bool :=
  let s := rootState s50StockWords 4 token
  !dagAllowedRoot s50Witnesses s.2.1 || dagLocal s50Mask s50Goal s50Chart (dagKnownCloses s50Goal s50Cuts) s ||
  dagRef 2 s50States s50Moves s50Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50RootBlock0 : treeBlock 0 32 s50RootAt = true := by decide +kernel
theorem s50Roots : dagCheckRoots s50Mask s50Goal s50Chart (dagKnownCloses s50Goal s50Cuts) s50Witnesses (dagRef 2 s50States s50Moves s50Links 0) s50StockWords 4 = true := s50RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block0 : treeBlock 0 2 s50Check = true := by decide +kernel
theorem s50Blocks : treeBlock 0 2 s50Check = true := s50Block0
theorem s50Known : Known s50Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s20Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Stock : Lower s50Mask s50StockWords s50Goal 5 := by
  apply lowerDag _ _ _ _ s50Autos _ _ _ s50Known _ s50Roots s50Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s50StockWords; decide +kernel
  · decide +kernel
  · simp only [s50Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s51Mask : Nat := 0xff000000ff
abbrev s51Goal : Nat := sGoal &&& s51Mask
abbrev s51StockWords : List Nat := projectDAGStock s51Mask sBase [0, 1, 2, 5, 7]
def s51Fact : (Nat × List Nat × Nat × Nat) := (s51Mask, s51StockWords, 5, s51Goal)
def s51Cuts : List (Nat × List Nat × Nat × Nat) := [s19Fact, s8Fact]
def s51Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 35, 38, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 6, 33, 34, 36, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s51Sample : (Nat × Nat) := (0x0, 0)
def s51Witnesses := unpackWitnesses s51StockWords [2564, 526849, 804355]
def s51Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s51Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s51Tags := dagTraceTags s51Mask 0 (dagTagBases s51StockWords 0x0 0x0 0) 4 s51Data
def s51States := dagTrace s51Mask s51StockWords 4 s51Data
def s51MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s51Moves := dagMoves s51MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Autos : DagMovesOK s51Mask s51Goal 64 s51Moves := dagMovesOfCheck (by decide +kernel)
def s51Check := dagCheckNode s51Mask s51Goal s51Chart (dagKnownCloses s51Goal s51Cuts) 0 s51States s51Moves s51Links s51Sample s51Tags
def s51RootAt (token : Nat) : Bool :=
  let s := rootState s51StockWords 4 token
  !dagAllowedRoot s51Witnesses s.2.1 || dagLocal s51Mask s51Goal s51Chart (dagKnownCloses s51Goal s51Cuts) s ||
  dagRef 0 s51States s51Moves s51Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51RootBlock0 : treeBlock 0 32 s51RootAt = true := by decide +kernel
theorem s51Roots : dagCheckRoots s51Mask s51Goal s51Chart (dagKnownCloses s51Goal s51Cuts) s51Witnesses (dagRef 0 s51States s51Moves s51Links 0) s51StockWords 4 = true := s51RootBlock0
theorem s51Blocks : treeBlock 0 0 s51Check = true := by decide +kernel
theorem s51Known : Known s51Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s8Stock) s19Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Stock : Lower s51Mask s51StockWords s51Goal 5 := by
  apply lowerDag _ _ _ _ s51Autos _ _ _ s51Known _ s51Roots s51Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s51StockWords; decide +kernel
  · decide +kernel
  · simp only [s51Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s52Mask : Nat := 0xff000000ff00
abbrev s52Goal : Nat := sGoal &&& s52Mask
abbrev s52StockWords : List Nat := projectDAGStock s52Mask sBase [0, 1, 2, 5, 7]
def s52Fact : (Nat × List Nat × Nat × Nat) := (s52Mask, s52StockWords, 5, s52Goal)
def s52Cuts : List (Nat × List Nat × Nat × Nat) := [s20Fact, s7Fact]
def s52Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 13, 14, 41, 44, 11, 11, 11, 11, 11, 11, 11, 9, 12, 42, 9, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s52Sample : (Nat × Nat) := (0x0, 0)
def s52Witnesses := unpackWitnesses s52StockWords [5642, 530953, 807433]
def s52Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s52Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s52Tags := dagTraceTags s52Mask 0 (dagTagBases s52StockWords 0x0 0x0 0) 4 s52Data
def s52States := dagTrace s52Mask s52StockWords 4 s52Data
def s52MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s52Moves := dagMoves s52MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52Autos : DagMovesOK s52Mask s52Goal 64 s52Moves := dagMovesOfCheck (by decide +kernel)
def s52Check := dagCheckNode s52Mask s52Goal s52Chart (dagKnownCloses s52Goal s52Cuts) 0 s52States s52Moves s52Links s52Sample s52Tags
def s52RootAt (token : Nat) : Bool :=
  let s := rootState s52StockWords 4 token
  !dagAllowedRoot s52Witnesses s.2.1 || dagLocal s52Mask s52Goal s52Chart (dagKnownCloses s52Goal s52Cuts) s ||
  dagRef 0 s52States s52Moves s52Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52RootBlock0 : treeBlock 0 32 s52RootAt = true := by decide +kernel
theorem s52Roots : dagCheckRoots s52Mask s52Goal s52Chart (dagKnownCloses s52Goal s52Cuts) s52Witnesses (dagRef 0 s52States s52Moves s52Links 0) s52StockWords 4 = true := s52RootBlock0
theorem s52Blocks : treeBlock 0 0 s52Check = true := by decide +kernel
theorem s52Known : Known s52Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s7Stock) s20Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52Stock : Lower s52Mask s52StockWords s52Goal 5 := by
  apply lowerDag _ _ _ _ s52Autos _ _ _ s52Known _ s52Roots s52Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s52StockWords; decide +kernel
  · decide +kernel
  · simp only [s52Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s53Mask : Nat := 0xff000000ff
abbrev s53Goal : Nat := sGoal &&& s53Mask
abbrev s53StockWords : List Nat := projectDAGStock s53Mask sBase [0, 1, 2, 5, 8]
def s53Fact : (Nat × List Nat × Nat × Nat) := (s53Mask, s53StockWords, 5, s53Goal)
def s53Cuts : List (Nat × List Nat × Nat × Nat) := [s19Fact]
def s53Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 35, 38, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 6, 33, 34, 36, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s53Sample : (Nat × Nat) := (0x1088c0623020140205, 4)
def s53Witnesses := unpackWitnesses s53StockWords [2564, 280097, 804355]
def s53Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x71801b 3 1 10 1 1 1
def s53Data : (Nat → Nat × Nat) := fun i => decodeNode 1 11 0x318836 i
def s53Tags := dagTraceTags s53Mask 4 (dagTagBases s53StockWords 0xcc3cf 0xd824d 4) 4 s53Data
def s53States := dagTrace s53Mask s53StockWords 4 s53Data
def s53MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s53Moves := dagMoves s53MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Autos : DagMovesOK s53Mask s53Goal 64 s53Moves := dagMovesOfCheck (by decide +kernel)
def s53Check := dagCheckNode s53Mask s53Goal s53Chart (dagKnownCloses s53Goal s53Cuts) 2 s53States s53Moves s53Links s53Sample s53Tags
def s53RootAt (token : Nat) : Bool :=
  let s := rootState s53StockWords 4 token
  !dagAllowedRoot s53Witnesses s.2.1 || dagLocal s53Mask s53Goal s53Chart (dagKnownCloses s53Goal s53Cuts) s ||
  dagRef 2 s53States s53Moves s53Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53RootBlock0 : treeBlock 0 32 s53RootAt = true := by decide +kernel
theorem s53Roots : dagCheckRoots s53Mask s53Goal s53Chart (dagKnownCloses s53Goal s53Cuts) s53Witnesses (dagRef 2 s53States s53Moves s53Links 0) s53StockWords 4 = true := s53RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Block0 : treeBlock 0 2 s53Check = true := by decide +kernel
theorem s53Blocks : treeBlock 0 2 s53Check = true := s53Block0
theorem s53Known : Known s53Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s19Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Stock : Lower s53Mask s53StockWords s53Goal 5 := by
  apply lowerDag _ _ _ _ s53Autos _ _ _ s53Known _ s53Roots s53Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s53StockWords; decide +kernel
  · decide +kernel
  · simp only [s53Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s54Mask : Nat := 0xff000000ff00
abbrev s54Goal : Nat := sGoal &&& s54Mask
abbrev s54StockWords : List Nat := projectDAGStock s54Mask sBase [0, 1, 2, 5, 8]
def s54Fact : (Nat × List Nat × Nat × Nat) := (s54Mask, s54StockWords, 5, s54Goal)
def s54Cuts : List (Nat × List Nat × Nat × Nat) := [s20Fact]
def s54Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 13, 14, 41, 44, 11, 11, 11, 11, 11, 11, 11, 9, 12, 42, 9, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s54Sample : (Nat × Nat) := (0x48a4180d0482c120d, 4)
def s54Witnesses := unpackWitnesses s54StockWords [5642, 267785, 807433]
def s54Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x71c01b 3 1 10 1 1 1
def s54Data : (Nat → Nat × Nat) := fun i => decodeNode 1 11 0x31c836 i
def s54Tags := dagTraceTags s54Mask 4 (dagTagBases s54StockWords 0xa852f 0xb040b 4) 4 s54Data
def s54States := dagTrace s54Mask s54StockWords 4 s54Data
def s54MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s54Moves := dagMoves s54MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Autos : DagMovesOK s54Mask s54Goal 64 s54Moves := dagMovesOfCheck (by decide +kernel)
def s54Check := dagCheckNode s54Mask s54Goal s54Chart (dagKnownCloses s54Goal s54Cuts) 2 s54States s54Moves s54Links s54Sample s54Tags
def s54RootAt (token : Nat) : Bool :=
  let s := rootState s54StockWords 4 token
  !dagAllowedRoot s54Witnesses s.2.1 || dagLocal s54Mask s54Goal s54Chart (dagKnownCloses s54Goal s54Cuts) s ||
  dagRef 2 s54States s54Moves s54Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54RootBlock0 : treeBlock 0 32 s54RootAt = true := by decide +kernel
theorem s54Roots : dagCheckRoots s54Mask s54Goal s54Chart (dagKnownCloses s54Goal s54Cuts) s54Witnesses (dagRef 2 s54States s54Moves s54Links 0) s54StockWords 4 = true := s54RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Block0 : treeBlock 0 2 s54Check = true := by decide +kernel
theorem s54Blocks : treeBlock 0 2 s54Check = true := s54Block0
theorem s54Known : Known s54Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s20Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Stock : Lower s54Mask s54StockWords s54Goal 5 := by
  apply lowerDag _ _ _ _ s54Autos _ _ _ s54Known _ s54Roots s54Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s54StockWords; decide +kernel
  · decide +kernel
  · simp only [s54Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s55Mask : Nat := 0xff000000ff
abbrev s55Goal : Nat := sGoal &&& s55Mask
abbrev s55StockWords : List Nat := projectDAGStock s55Mask sBase [0, 1, 2, 5, 11]
def s55Fact : (Nat × List Nat × Nat × Nat) := (s55Mask, s55StockWords, 5, s55Goal)
def s55Cuts : List (Nat × List Nat × Nat × Nat) := [s19Fact, s0Fact]
def s55Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 35, 38, 5, 5, 5, 5, 5, 5, 5, 5, 5, 3, 6, 33, 34, 36, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s55Sample : (Nat × Nat) := (0x0, 0)
def s55Witnesses := unpackWitnesses s55StockWords [2564, 280097, 526849]
def s55Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s55Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s55Tags := dagTraceTags s55Mask 0 (dagTagBases s55StockWords 0x0 0x0 0) 4 s55Data
def s55States := dagTrace s55Mask s55StockWords 4 s55Data
def s55MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s55Moves := dagMoves s55MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Autos : DagMovesOK s55Mask s55Goal 64 s55Moves := dagMovesOfCheck (by decide +kernel)
def s55Check := dagCheckNode s55Mask s55Goal s55Chart (dagKnownCloses s55Goal s55Cuts) 0 s55States s55Moves s55Links s55Sample s55Tags
def s55RootAt (token : Nat) : Bool :=
  let s := rootState s55StockWords 4 token
  !dagAllowedRoot s55Witnesses s.2.1 || dagLocal s55Mask s55Goal s55Chart (dagKnownCloses s55Goal s55Cuts) s ||
  dagRef 0 s55States s55Moves s55Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55RootBlock0 : treeBlock 0 32 s55RootAt = true := by decide +kernel
theorem s55Roots : dagCheckRoots s55Mask s55Goal s55Chart (dagKnownCloses s55Goal s55Cuts) s55Witnesses (dagRef 0 s55States s55Moves s55Links 0) s55StockWords 4 = true := s55RootBlock0
theorem s55Blocks : treeBlock 0 0 s55Check = true := by decide +kernel
theorem s55Known : Known s55Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s0Stock) s19Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Stock : Lower s55Mask s55StockWords s55Goal 5 := by
  apply lowerDag _ _ _ _ s55Autos _ _ _ s55Known _ s55Roots s55Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s55StockWords; decide +kernel
  · decide +kernel
  · simp only [s55Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s56Mask : Nat := 0xff000000ff00
abbrev s56Goal : Nat := sGoal &&& s56Mask
abbrev s56StockWords : List Nat := projectDAGStock s56Mask sBase [0, 1, 2, 5, 11]
def s56Fact : (Nat × List Nat × Nat × Nat) := (s56Mask, s56StockWords, 5, s56Goal)
def s56Cuts : List (Nat × List Nat × Nat × Nat) := [s20Fact, s1Fact]
def s56Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 13, 14, 41, 44, 11, 11, 11, 11, 11, 11, 11, 9, 12, 42, 9, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s56Sample : (Nat × Nat) := (0x0, 0)
def s56Witnesses := unpackWitnesses s56StockWords [5642, 267785, 530953]
def s56Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s56Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s56Tags := dagTraceTags s56Mask 0 (dagTagBases s56StockWords 0x0 0x0 0) 4 s56Data
def s56States := dagTrace s56Mask s56StockWords 4 s56Data
def s56MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s56Moves := dagMoves s56MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Autos : DagMovesOK s56Mask s56Goal 64 s56Moves := dagMovesOfCheck (by decide +kernel)
def s56Check := dagCheckNode s56Mask s56Goal s56Chart (dagKnownCloses s56Goal s56Cuts) 0 s56States s56Moves s56Links s56Sample s56Tags
def s56RootAt (token : Nat) : Bool :=
  let s := rootState s56StockWords 4 token
  !dagAllowedRoot s56Witnesses s.2.1 || dagLocal s56Mask s56Goal s56Chart (dagKnownCloses s56Goal s56Cuts) s ||
  dagRef 0 s56States s56Moves s56Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56RootBlock0 : treeBlock 0 32 s56RootAt = true := by decide +kernel
theorem s56Roots : dagCheckRoots s56Mask s56Goal s56Chart (dagKnownCloses s56Goal s56Cuts) s56Witnesses (dagRef 0 s56States s56Moves s56Links 0) s56StockWords 4 = true := s56RootBlock0
theorem s56Blocks : treeBlock 0 0 s56Check = true := by decide +kernel
theorem s56Known : Known s56Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s1Stock) s20Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Stock : Lower s56Mask s56StockWords s56Goal 5 := by
  apply lowerDag _ _ _ _ s56Autos _ _ _ s56Known _ s56Roots s56Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s56StockWords; decide +kernel
  · decide +kernel
  · simp only [s56Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s57Mask : Nat := 0xf0f0f0f
abbrev s57Goal : Nat := sGoal &&& s57Mask
abbrev s57StockWords : List Nat := projectDAGStock s57Mask sBase [0, 1, 3, 4, 7]
def s57Fact : (Nat × List Nat × Nat × Nat) := (s57Mask, s57StockWords, 5, s57Goal)
def s57Cuts : List (Nat × List Nat × Nat × Nat) := [s21Fact, s9Fact]
def s57Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 17, 26, 11, 11, 11, 11, 11, 11, 11, 11, 11, 3, 9, 10, 18, 24, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s57Sample : (Nat × Nat) := (0x0, 0)
def s57Witnesses := unpackWitnesses s57StockWords [5642, 529923, 795137]
def s57Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s57Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s57Tags := dagTraceTags s57Mask 0 (dagTagBases s57StockWords 0x0 0x0 0) 4 s57Data
def s57States := dagTrace s57Mask s57StockWords 4 s57Data
def s57MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s57Moves := dagMoves s57MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s57Autos : DagMovesOK s57Mask s57Goal 64 s57Moves := dagMovesOfCheck (by decide +kernel)
def s57Check := dagCheckNode s57Mask s57Goal s57Chart (dagKnownCloses s57Goal s57Cuts) 0 s57States s57Moves s57Links s57Sample s57Tags
def s57RootAt (token : Nat) : Bool :=
  let s := rootState s57StockWords 4 token
  !dagAllowedRoot s57Witnesses s.2.1 || dagLocal s57Mask s57Goal s57Chart (dagKnownCloses s57Goal s57Cuts) s ||
  dagRef 0 s57States s57Moves s57Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s57RootBlock0 : treeBlock 0 32 s57RootAt = true := by decide +kernel
theorem s57Roots : dagCheckRoots s57Mask s57Goal s57Chart (dagKnownCloses s57Goal s57Cuts) s57Witnesses (dagRef 0 s57States s57Moves s57Links 0) s57StockWords 4 = true := s57RootBlock0
theorem s57Blocks : treeBlock 0 0 s57Check = true := by decide +kernel
theorem s57Known : Known s57Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s9Stock) s21Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s57Stock : Lower s57Mask s57StockWords s57Goal 5 := by
  apply lowerDag _ _ _ _ s57Autos _ _ _ s57Known _ s57Roots s57Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s57StockWords; decide +kernel
  · decide +kernel
  · simp only [s57Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s58Mask : Nat := 0xf0f0f0f00000000
abbrev s58Goal : Nat := sGoal &&& s58Mask
abbrev s58StockWords : List Nat := projectDAGStock s58Mask sBase [0, 1, 3, 4, 7]
def s58Fact : (Nat × List Nat × Nat × Nat) := (s58Mask, s58StockWords, 5, s58Goal)
def s58Cuts : List (Nat × List Nat × Nat × Nat) := [s22Fact]
def s58Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[35, 41, 49, 50, 35, 35, 35, 35, 35, 35, 35, 35, 33, 42, 56, 33, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s58Sample : (Nat × Nat) := (0x5432108c442291108c4223, 5)
def s58Witnesses := unpackWitnesses s58StockWords [17954, 545313, 811553]
def s58Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x1d 2 1 5 1 1 1
def s58Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x3a i
def s58Tags := dagTraceTags s58Mask 5 (dagTagBases s58StockWords 0xcc126f 0xd0424d 5) 4 s58Data
def s58States := dagTrace s58Mask s58StockWords 4 s58Data
def s58MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s58Moves := dagMoves s58MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Autos : DagMovesOK s58Mask s58Goal 64 s58Moves := dagMovesOfCheck (by decide +kernel)
def s58Check := dagCheckNode s58Mask s58Goal s58Chart (dagKnownCloses s58Goal s58Cuts) 1 s58States s58Moves s58Links s58Sample s58Tags
def s58RootAt (token : Nat) : Bool :=
  let s := rootState s58StockWords 4 token
  !dagAllowedRoot s58Witnesses s.2.1 || dagLocal s58Mask s58Goal s58Chart (dagKnownCloses s58Goal s58Cuts) s ||
  dagRef 1 s58States s58Moves s58Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58RootBlock0 : treeBlock 0 32 s58RootAt = true := by decide +kernel
theorem s58Roots : dagCheckRoots s58Mask s58Goal s58Chart (dagKnownCloses s58Goal s58Cuts) s58Witnesses (dagRef 1 s58States s58Moves s58Links 0) s58StockWords 4 = true := s58RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Block0 : treeBlock 0 1 s58Check = true := by decide +kernel
theorem s58Blocks : treeBlock 0 1 s58Check = true := s58Block0
theorem s58Known : Known s58Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s22Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Stock : Lower s58Mask s58StockWords s58Goal 5 := by
  apply lowerDag _ _ _ _ s58Autos _ _ _ s58Known _ s58Roots s58Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s58StockWords; decide +kernel
  · decide +kernel
  · simp only [s58Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s59Mask : Nat := 0xf0f00000f0f
abbrev s59Goal : Nat := sGoal &&& s59Mask
abbrev s59StockWords : List Nat := projectDAGStock s59Mask sBase [0, 1, 3, 5, 6]
def s59Fact : (Nat × List Nat × Nat × Nat) := (s59Mask, s59StockWords, 5, s59Goal)
def s59Cuts : List (Nat × List Nat × Nat × Nat) := [s23Fact, s13Fact]
def s59Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 35, 41, 11, 11, 11, 11, 11, 11, 11, 11, 11, 3, 9, 33, 42, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s59Sample : (Nat × Nat) := (0x0, 0)
def s59Witnesses := unpackWitnesses s59StockWords [267785, 529923, 804355]
def s59Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s59Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s59Tags := dagTraceTags s59Mask 0 (dagTagBases s59StockWords 0x0 0x0 0) 4 s59Data
def s59States := dagTrace s59Mask s59StockWords 4 s59Data
def s59MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s59Moves := dagMoves s59MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59Autos : DagMovesOK s59Mask s59Goal 64 s59Moves := dagMovesOfCheck (by decide +kernel)
def s59Check := dagCheckNode s59Mask s59Goal s59Chart (dagKnownCloses s59Goal s59Cuts) 0 s59States s59Moves s59Links s59Sample s59Tags
def s59RootAt (token : Nat) : Bool :=
  let s := rootState s59StockWords 4 token
  !dagAllowedRoot s59Witnesses s.2.1 || dagLocal s59Mask s59Goal s59Chart (dagKnownCloses s59Goal s59Cuts) s ||
  dagRef 0 s59States s59Moves s59Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59RootBlock0 : treeBlock 0 32 s59RootAt = true := by decide +kernel
theorem s59Roots : dagCheckRoots s59Mask s59Goal s59Chart (dagKnownCloses s59Goal s59Cuts) s59Witnesses (dagRef 0 s59States s59Moves s59Links 0) s59StockWords 4 = true := s59RootBlock0
theorem s59Blocks : treeBlock 0 0 s59Check = true := by decide +kernel
theorem s59Known : Known s59Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s13Stock) s23Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59Stock : Lower s59Mask s59StockWords s59Goal 5 := by
  apply lowerDag _ _ _ _ s59Autos _ _ _ s59Known _ s59Roots s59Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s59StockWords; decide +kernel
  · decide +kernel
  · simp only [s59Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s60Mask : Nat := 0xf0f00000f0f
abbrev s60Goal : Nat := sGoal &&& s60Mask
abbrev s60StockWords : List Nat := projectDAGStock s60Mask sBase [0, 1, 3, 5, 7]
def s60Fact : (Nat × List Nat × Nat × Nat) := (s60Mask, s60StockWords, 5, s60Goal)
def s60Cuts : List (Nat × List Nat × Nat × Nat) := [s23Fact]
def s60Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 35, 41, 11, 11, 11, 11, 11, 11, 11, 11, 11, 3, 9, 33, 42, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s60Sample : (Nat × Nat) := (0x140b048a444230182c120b, 5)
def s60Witnesses := unpackWitnesses s60StockWords [5642, 529923, 804355]
def s60Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x1d 2 1 5 1 1 1
def s60Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x3a i
def s60Tags := dagTraceTags s60Mask 5 (dagTagBases s60StockWords 0x866eff 0x9266cb 5) 4 s60Data
def s60States := dagTrace s60Mask s60StockWords 4 s60Data
def s60MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s60Moves := dagMoves s60MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Autos : DagMovesOK s60Mask s60Goal 64 s60Moves := dagMovesOfCheck (by decide +kernel)
def s60Check := dagCheckNode s60Mask s60Goal s60Chart (dagKnownCloses s60Goal s60Cuts) 1 s60States s60Moves s60Links s60Sample s60Tags
def s60RootAt (token : Nat) : Bool :=
  let s := rootState s60StockWords 4 token
  !dagAllowedRoot s60Witnesses s.2.1 || dagLocal s60Mask s60Goal s60Chart (dagKnownCloses s60Goal s60Cuts) s ||
  dagRef 1 s60States s60Moves s60Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60RootBlock0 : treeBlock 0 32 s60RootAt = true := by decide +kernel
theorem s60Roots : dagCheckRoots s60Mask s60Goal s60Chart (dagKnownCloses s60Goal s60Cuts) s60Witnesses (dagRef 1 s60States s60Moves s60Links 0) s60StockWords 4 = true := s60RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Block0 : treeBlock 0 1 s60Check = true := by decide +kernel
theorem s60Blocks : treeBlock 0 1 s60Check = true := s60Block0
theorem s60Known : Known s60Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s23Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Stock : Lower s60Mask s60StockWords s60Goal 5 := by
  apply lowerDag _ _ _ _ s60Autos _ _ _ s60Known _ s60Roots s60Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s60StockWords; decide +kernel
  · decide +kernel
  · simp only [s60Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s61Mask : Nat := 0xf0f00000f0f0
abbrev s61Goal : Nat := sGoal &&& s61Mask
abbrev s61StockWords : List Nat := projectDAGStock s61Mask sBase [0, 1, 3, 5, 7]
def s61Fact : (Nat × List Nat × Nat × Nat) := (s61Mask, s61StockWords, 5, s61Goal)
def s61Cuts : List (Nat × List Nat × Nat × Nat) := [s24Fact]
def s61Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 14, 38, 44, 5, 5, 5, 5, 5, 5, 5, 5, 6, 12, 36, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩
def s61Sample : (Nat × Nat) := (0x120141805060b00c0e02014180e, 6)
def s61Witnesses := unpackWitnesses s61StockWords [2564, 531462, 805894]
def s61Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x1d 2 1 5 1 1 1
def s61Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x3a i
def s61Tags := dagTraceTags s61Mask 6 (dagTagBases s61StockWords 0x3a20d172 0x3b819100 6) 4 s61Data
def s61States := dagTrace s61Mask s61StockWords 4 s61Data
def s61MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s61Moves := dagMoves s61MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61Autos : DagMovesOK s61Mask s61Goal 64 s61Moves := dagMovesOfCheck (by decide +kernel)
def s61Check := dagCheckNode s61Mask s61Goal s61Chart (dagKnownCloses s61Goal s61Cuts) 1 s61States s61Moves s61Links s61Sample s61Tags
def s61RootAt (token : Nat) : Bool :=
  let s := rootState s61StockWords 4 token
  !dagAllowedRoot s61Witnesses s.2.1 || dagLocal s61Mask s61Goal s61Chart (dagKnownCloses s61Goal s61Cuts) s ||
  dagRef 1 s61States s61Moves s61Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61RootBlock0 : treeBlock 0 32 s61RootAt = true := by decide +kernel
theorem s61Roots : dagCheckRoots s61Mask s61Goal s61Chart (dagKnownCloses s61Goal s61Cuts) s61Witnesses (dagRef 1 s61States s61Moves s61Links 0) s61StockWords 4 = true := s61RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61Block0 : treeBlock 0 1 s61Check = true := by decide +kernel
theorem s61Blocks : treeBlock 0 1 s61Check = true := s61Block0
theorem s61Known : Known s61Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s24Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61Stock : Lower s61Mask s61StockWords s61Goal 5 := by
  apply lowerDag _ _ _ _ s61Autos _ _ _ s61Known _ s61Roots s61Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s61StockWords; decide +kernel
  · decide +kernel
  · simp only [s61Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s62Mask : Nat := 0xf0f00000f0f
abbrev s62Goal : Nat := sGoal &&& s62Mask
abbrev s62StockWords : List Nat := projectDAGStock s62Mask sBase [0, 1, 3, 5, 9]
def s62Fact : (Nat × List Nat × Nat × Nat) := (s62Mask, s62StockWords, 5, s62Goal)
def s62Cuts : List (Nat × List Nat × Nat × Nat) := [s23Fact]
def s62Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 35, 41, 11, 11, 11, 11, 11, 11, 11, 11, 11, 3, 9, 33, 42, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s62Sample : (Nat × Nat) := (0x50290502c06230482c060b, 5)
def s62Witnesses := unpackWitnesses s62StockWords [5642, 267785, 804355]
def s62Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x1b 2 1 5 1 1 1
def s62Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x36 i
def s62Tags := dagTraceTags s62Mask 5 (dagTagBases s62StockWords 0x4a6dff 0x5869a7 5) 4 s62Data
def s62States := dagTrace s62Mask s62StockWords 4 s62Data
def s62MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s62Moves := dagMoves s62MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62Autos : DagMovesOK s62Mask s62Goal 64 s62Moves := dagMovesOfCheck (by decide +kernel)
def s62Check := dagCheckNode s62Mask s62Goal s62Chart (dagKnownCloses s62Goal s62Cuts) 1 s62States s62Moves s62Links s62Sample s62Tags
def s62RootAt (token : Nat) : Bool :=
  let s := rootState s62StockWords 4 token
  !dagAllowedRoot s62Witnesses s.2.1 || dagLocal s62Mask s62Goal s62Chart (dagKnownCloses s62Goal s62Cuts) s ||
  dagRef 1 s62States s62Moves s62Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62RootBlock0 : treeBlock 0 32 s62RootAt = true := by decide +kernel
theorem s62Roots : dagCheckRoots s62Mask s62Goal s62Chart (dagKnownCloses s62Goal s62Cuts) s62Witnesses (dagRef 1 s62States s62Moves s62Links 0) s62StockWords 4 = true := s62RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62Block0 : treeBlock 0 1 s62Check = true := by decide +kernel
theorem s62Blocks : treeBlock 0 1 s62Check = true := s62Block0
theorem s62Known : Known s62Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s23Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62Stock : Lower s62Mask s62StockWords s62Goal 5 := by
  apply lowerDag _ _ _ _ s62Autos _ _ _ s62Known _ s62Roots s62Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s62StockWords; decide +kernel
  · decide +kernel
  · simp only [s62Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s63Mask : Nat := 0xf0f00000f0f0
abbrev s63Goal : Nat := sGoal &&& s63Mask
abbrev s63StockWords : List Nat := projectDAGStock s63Mask sBase [0, 1, 3, 5, 9]
def s63Fact : (Nat × List Nat × Nat × Nat) := (s63Mask, s63StockWords, 5, s63Goal)
def s63Cuts : List (Nat × List Nat × Nat × Nat) := [s24Fact]
def s63Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 14, 38, 44, 5, 5, 5, 5, 5, 5, 5, 5, 6, 12, 36, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩
def s63Sample : (Nat × Nat) := (0x120140c0503098180e020140c0e, 6)
def s63Witnesses := unpackWitnesses s63StockWords [2564, 269324, 805894]
def s63Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x1b 2 1 5 1 1 1
def s63Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x36 i
def s63Tags := dagTraceTags s63Mask 6 (dagTagBases s63StockWords 0x3a205372 0x3b804640 6) 4 s63Data
def s63States := dagTrace s63Mask s63StockWords 4 s63Data
def s63MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s63Moves := dagMoves s63MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Autos : DagMovesOK s63Mask s63Goal 64 s63Moves := dagMovesOfCheck (by decide +kernel)
def s63Check := dagCheckNode s63Mask s63Goal s63Chart (dagKnownCloses s63Goal s63Cuts) 1 s63States s63Moves s63Links s63Sample s63Tags
def s63RootAt (token : Nat) : Bool :=
  let s := rootState s63StockWords 4 token
  !dagAllowedRoot s63Witnesses s.2.1 || dagLocal s63Mask s63Goal s63Chart (dagKnownCloses s63Goal s63Cuts) s ||
  dagRef 1 s63States s63Moves s63Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63RootBlock0 : treeBlock 0 32 s63RootAt = true := by decide +kernel
theorem s63Roots : dagCheckRoots s63Mask s63Goal s63Chart (dagKnownCloses s63Goal s63Cuts) s63Witnesses (dagRef 1 s63States s63Moves s63Links 0) s63StockWords 4 = true := s63RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Block0 : treeBlock 0 1 s63Check = true := by decide +kernel
theorem s63Blocks : treeBlock 0 1 s63Check = true := s63Block0
theorem s63Known : Known s63Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s24Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Stock : Lower s63Mask s63StockWords s63Goal 5 := by
  apply lowerDag _ _ _ _ s63Autos _ _ _ s63Known _ s63Roots s63Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s63StockWords; decide +kernel
  · decide +kernel
  · simp only [s63Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s64Mask : Nat := 0xf0f00000f0f
abbrev s64Goal : Nat := sGoal &&& s64Mask
abbrev s64StockWords : List Nat := projectDAGStock s64Mask sBase [0, 1, 3, 5, 11]
def s64Fact : (Nat × List Nat × Nat × Nat) := (s64Mask, s64StockWords, 5, s64Goal)
def s64Cuts : List (Nat × List Nat × Nat × Nat) := [s23Fact]
def s64Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 35, 41, 11, 11, 11, 11, 11, 11, 11, 11, 11, 3, 9, 33, 42, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s64Sample : (Nat × Nat) := (0x50291108c42230182c0623, 5)
def s64Witnesses := unpackWitnesses s64StockWords [5642, 267785, 529923]
def s64Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x17 2 1 5 1 1 1
def s64Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x2e i
def s64Tags := dagTraceTags s64Mask 5 (dagTagBases s64StockWords 0x2ec9ff 0x3e4167 5) 4 s64Data
def s64States := dagTrace s64Mask s64StockWords 4 s64Data
def s64MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s64Moves := dagMoves s64MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Autos : DagMovesOK s64Mask s64Goal 64 s64Moves := dagMovesOfCheck (by decide +kernel)
def s64Check := dagCheckNode s64Mask s64Goal s64Chart (dagKnownCloses s64Goal s64Cuts) 1 s64States s64Moves s64Links s64Sample s64Tags
def s64RootAt (token : Nat) : Bool :=
  let s := rootState s64StockWords 4 token
  !dagAllowedRoot s64Witnesses s.2.1 || dagLocal s64Mask s64Goal s64Chart (dagKnownCloses s64Goal s64Cuts) s ||
  dagRef 1 s64States s64Moves s64Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64RootBlock0 : treeBlock 0 32 s64RootAt = true := by decide +kernel
theorem s64Roots : dagCheckRoots s64Mask s64Goal s64Chart (dagKnownCloses s64Goal s64Cuts) s64Witnesses (dagRef 1 s64States s64Moves s64Links 0) s64StockWords 4 = true := s64RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Block0 : treeBlock 0 1 s64Check = true := by decide +kernel
theorem s64Blocks : treeBlock 0 1 s64Check = true := s64Block0
theorem s64Known : Known s64Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s23Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Stock : Lower s64Mask s64StockWords s64Goal 5 := by
  apply lowerDag _ _ _ _ s64Autos _ _ _ s64Known _ s64Roots s64Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s64StockWords; decide +kernel
  · decide +kernel
  · simp only [s64Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s65Mask : Nat := 0xf0f00000f0f0
abbrev s65Goal : Nat := sGoal &&& s65Mask
abbrev s65StockWords : List Nat := projectDAGStock s65Mask sBase [0, 1, 3, 5, 11]
def s65Fact : (Nat × List Nat × Nat × Nat) := (s65Mask, s65StockWords, 5, s65Goal)
def s65Cuts : List (Nat × List Nat × Nat × Nat) := [s24Fact]
def s65Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 14, 38, 44, 5, 5, 5, 5, 5, 5, 5, 5, 6, 12, 36, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩
def s65Sample : (Nat × Nat) := (0x60140c05120980c0e020140c26, 6)
def s65Witnesses := unpackWitnesses s65StockWords [2564, 269324, 531462]
def s65Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x17 2 1 5 1 1 1
def s65Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x2e i
def s65Tags := dagTraceTags s65Mask 6 (dagTagBases s65StockWords 0x36244372 0x37220540 6) 4 s65Data
def s65States := dagTrace s65Mask s65StockWords 4 s65Data
def s65MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s65Moves := dagMoves s65MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Autos : DagMovesOK s65Mask s65Goal 64 s65Moves := dagMovesOfCheck (by decide +kernel)
def s65Check := dagCheckNode s65Mask s65Goal s65Chart (dagKnownCloses s65Goal s65Cuts) 1 s65States s65Moves s65Links s65Sample s65Tags
def s65RootAt (token : Nat) : Bool :=
  let s := rootState s65StockWords 4 token
  !dagAllowedRoot s65Witnesses s.2.1 || dagLocal s65Mask s65Goal s65Chart (dagKnownCloses s65Goal s65Cuts) s ||
  dagRef 1 s65States s65Moves s65Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65RootBlock0 : treeBlock 0 32 s65RootAt = true := by decide +kernel
theorem s65Roots : dagCheckRoots s65Mask s65Goal s65Chart (dagKnownCloses s65Goal s65Cuts) s65Witnesses (dagRef 1 s65States s65Moves s65Links 0) s65StockWords 4 = true := s65RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Block0 : treeBlock 0 1 s65Check = true := by decide +kernel
theorem s65Blocks : treeBlock 0 1 s65Check = true := s65Block0
theorem s65Known : Known s65Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s24Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Stock : Lower s65Mask s65StockWords s65Goal 5 := by
  apply lowerDag _ _ _ _ s65Autos _ _ _ s65Known _ s65Roots s65Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s65StockWords; decide +kernel
  · decide +kernel
  · simp only [s65Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s66Mask : Nat := 0xf000f000f000f
abbrev s66Goal : Nat := sGoal &&& s66Mask
abbrev s66StockWords : List Nat := projectDAGStock s66Mask sBase [0, 1, 4, 5, 7]
def s66Fact : (Nat × List Nat × Nat × Nat) := (s66Mask, s66StockWords, 5, s66Goal)
def s66Cuts : List (Nat × List Nat × Nat × Nat) := [s25Fact, s10Fact]
def s66Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[17, 35, 50, 17, 17, 17, 17, 17, 17, 17, 17, 17, 3, 18, 33, 34, 48, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s66Sample : (Nat × Nat) := (0x0, 0)
def s66Witnesses := unpackWitnesses s66StockWords [8720, 532993, 804355]
def s66Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s66Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s66Tags := dagTraceTags s66Mask 0 (dagTagBases s66StockWords 0x0 0x0 0) 4 s66Data
def s66States := dagTrace s66Mask s66StockWords 4 s66Data
def s66MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s66Moves := dagMoves s66MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Autos : DagMovesOK s66Mask s66Goal 64 s66Moves := dagMovesOfCheck (by decide +kernel)
def s66Check := dagCheckNode s66Mask s66Goal s66Chart (dagKnownCloses s66Goal s66Cuts) 0 s66States s66Moves s66Links s66Sample s66Tags
def s66RootAt (token : Nat) : Bool :=
  let s := rootState s66StockWords 4 token
  !dagAllowedRoot s66Witnesses s.2.1 || dagLocal s66Mask s66Goal s66Chart (dagKnownCloses s66Goal s66Cuts) s ||
  dagRef 0 s66States s66Moves s66Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66RootBlock0 : treeBlock 0 32 s66RootAt = true := by decide +kernel
theorem s66Roots : dagCheckRoots s66Mask s66Goal s66Chart (dagKnownCloses s66Goal s66Cuts) s66Witnesses (dagRef 0 s66States s66Moves s66Links 0) s66StockWords 4 = true := s66RootBlock0
theorem s66Blocks : treeBlock 0 0 s66Check = true := by decide +kernel
theorem s66Known : Known s66Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s10Stock) s25Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Stock : Lower s66Mask s66StockWords s66Goal 5 := by
  apply lowerDag _ _ _ _ s66Autos _ _ _ s66Known _ s66Roots s66Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s66StockWords; decide +kernel
  · decide +kernel
  · simp only [s66Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s67Mask : Nat := 0xf000f000f000f00
abbrev s67Goal : Nat := sGoal &&& s67Mask
abbrev s67StockWords : List Nat := projectDAGStock s67Mask sBase [0, 1, 4, 5, 7]
def s67Fact : (Nat × List Nat × Nat × Nat) := (s67Mask, s67StockWords, 5, s67Goal)
def s67Cuts : List (Nat × List Nat × Nat × Nat) := [s26Fact]
def s67Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 25, 26, 41, 11, 11, 11, 11, 11, 11, 11, 11, 9, 42, 56, 9, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s67Sample : (Nat × Nat) := (0x541a048a412190502c120b, 5)
def s67Witnesses := unpackWitnesses s67StockWords [5642, 537097, 807433]
def s67Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x1d 2 1 5 1 1 1
def s67Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x3a i
def s67Tags := dagTraceTags s67Mask 5 (dagTagBases s67StockWords 0xc4526f 0xd8024d 5) 4 s67Data
def s67States := dagTrace s67Mask s67StockWords 4 s67Data
def s67MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s67Moves := dagMoves s67MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Autos : DagMovesOK s67Mask s67Goal 64 s67Moves := dagMovesOfCheck (by decide +kernel)
def s67Check := dagCheckNode s67Mask s67Goal s67Chart (dagKnownCloses s67Goal s67Cuts) 1 s67States s67Moves s67Links s67Sample s67Tags
def s67RootAt (token : Nat) : Bool :=
  let s := rootState s67StockWords 4 token
  !dagAllowedRoot s67Witnesses s.2.1 || dagLocal s67Mask s67Goal s67Chart (dagKnownCloses s67Goal s67Cuts) s ||
  dagRef 1 s67States s67Moves s67Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67RootBlock0 : treeBlock 0 32 s67RootAt = true := by decide +kernel
theorem s67Roots : dagCheckRoots s67Mask s67Goal s67Chart (dagKnownCloses s67Goal s67Cuts) s67Witnesses (dagRef 1 s67States s67Moves s67Links 0) s67StockWords 4 = true := s67RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Block0 : treeBlock 0 1 s67Check = true := by decide +kernel
theorem s67Blocks : treeBlock 0 1 s67Check = true := s67Block0
theorem s67Known : Known s67Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s26Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Stock : Lower s67Mask s67StockWords s67Goal 5 := by
  apply lowerDag _ _ _ _ s67Autos _ _ _ s67Known _ s67Roots s67Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s67StockWords; decide +kernel
  · decide +kernel
  · simp only [s67Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s68Mask : Nat := 0x333300003333
abbrev s68Goal : Nat := sGoal &&& s68Mask
abbrev s68StockWords : List Nat := projectDAGStock s68Mask sBase [0, 2, 3, 5, 6]
def s68Fact : (Nat × List Nat × Nat × Nat) := (s68Mask, s68StockWords, 5, s68Goal)
def s68Cuts : List (Nat × List Nat × Nat × Nat) := [s30Fact]
def s68Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 41, 44, 5, 5, 5, 5, 5, 5, 5, 5, 5, 9, 12, 33, 36, 40, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s68Sample : (Nat × Nat) := (0x120b0182c008140805, 4)
def s68Witnesses := unpackWitnesses s68StockWords [264705, 545313, 807433]
def s68Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x71801e 3 1 10 1 1 1
def s68Data : (Nat → Nat × Nat) := fun i => decodeNode 1 11 0x31883c i
def s68Tags := dagTraceTags s68Mask 4 (dagTagBases s68StockWords 0xcccf3 0xd84d2 4) 4 s68Data
def s68States := dagTrace s68Mask s68StockWords 4 s68Data
def s68MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s68Moves := dagMoves s68MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Autos : DagMovesOK s68Mask s68Goal 64 s68Moves := dagMovesOfCheck (by decide +kernel)
def s68Check := dagCheckNode s68Mask s68Goal s68Chart (dagKnownCloses s68Goal s68Cuts) 2 s68States s68Moves s68Links s68Sample s68Tags
def s68RootAt (token : Nat) : Bool :=
  let s := rootState s68StockWords 4 token
  !dagAllowedRoot s68Witnesses s.2.1 || dagLocal s68Mask s68Goal s68Chart (dagKnownCloses s68Goal s68Cuts) s ||
  dagRef 2 s68States s68Moves s68Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68RootBlock0 : treeBlock 0 32 s68RootAt = true := by decide +kernel
theorem s68Roots : dagCheckRoots s68Mask s68Goal s68Chart (dagKnownCloses s68Goal s68Cuts) s68Witnesses (dagRef 2 s68States s68Moves s68Links 0) s68StockWords 4 = true := s68RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Block0 : treeBlock 0 2 s68Check = true := by decide +kernel
theorem s68Blocks : treeBlock 0 2 s68Check = true := s68Block0
theorem s68Known : Known s68Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s30Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Stock : Lower s68Mask s68StockWords s68Goal 5 := by
  apply lowerDag _ _ _ _ s68Autos _ _ _ s68Known _ s68Roots s68Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s68StockWords; decide +kernel
  · decide +kernel
  · simp only [s68Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s69Mask : Nat := 0xcccc0000cccc
abbrev s69Goal : Nat := sGoal &&& s69Mask
abbrev s69StockWords : List Nat := projectDAGStock s69Mask sBase [0, 2, 3, 5, 6]
def s69Fact : (Nat × List Nat × Nat × Nat) := (s69Mask, s69StockWords, 5, s69Goal)
def s69Cuts : List (Nat × List Nat × Nat × Nat) := [s31Fact]
def s69Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[7, 11, 14, 35, 38, 7, 7, 7, 7, 7, 7, 7, 3, 6, 42, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s69Sample : (Nat × Nat) := (0x30980c0e0181c0c07, 4)
def s69Witnesses := unpackWitnesses s69StockWords [265731, 529923, 804355]
def s69Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x71c01e 3 1 10 1 1 1
def s69Data : (Nat → Nat × Nat) := fun i => decodeNode 1 11 0x31c83c i
def s69Tags := dagTraceTags s69Mask 4 (dagTagBases s69StockWords 0xc84f3 0xd00d2 4) 4 s69Data
def s69States := dagTrace s69Mask s69StockWords 4 s69Data
def s69MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s69Moves := dagMoves s69MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Autos : DagMovesOK s69Mask s69Goal 64 s69Moves := dagMovesOfCheck (by decide +kernel)
def s69Check := dagCheckNode s69Mask s69Goal s69Chart (dagKnownCloses s69Goal s69Cuts) 2 s69States s69Moves s69Links s69Sample s69Tags
def s69RootAt (token : Nat) : Bool :=
  let s := rootState s69StockWords 4 token
  !dagAllowedRoot s69Witnesses s.2.1 || dagLocal s69Mask s69Goal s69Chart (dagKnownCloses s69Goal s69Cuts) s ||
  dagRef 2 s69States s69Moves s69Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69RootBlock0 : treeBlock 0 32 s69RootAt = true := by decide +kernel
theorem s69Roots : dagCheckRoots s69Mask s69Goal s69Chart (dagKnownCloses s69Goal s69Cuts) s69Witnesses (dagRef 2 s69States s69Moves s69Links 0) s69StockWords 4 = true := s69RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Block0 : treeBlock 0 2 s69Check = true := by decide +kernel
theorem s69Blocks : treeBlock 0 2 s69Check = true := s69Block0
theorem s69Known : Known s69Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s31Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Stock : Lower s69Mask s69StockWords s69Goal 5 := by
  apply lowerDag _ _ _ _ s69Autos _ _ _ s69Known _ s69Roots s69Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s69StockWords; decide +kernel
  · decide +kernel
  · simp only [s69Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s70Mask : Nat := 0x333300003333
abbrev s70Goal : Nat := sGoal &&& s70Mask
abbrev s70StockWords : List Nat := projectDAGStock s70Mask sBase [0, 2, 3, 5, 8]
def s70Fact : (Nat × List Nat × Nat × Nat) := (s70Mask, s70StockWords, 5, s70Goal)
def s70Cuts : List (Nat × List Nat × Nat × Nat) := [s30Fact]
def s70Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 41, 44, 5, 5, 5, 5, 5, 5, 5, 5, 5, 9, 12, 33, 36, 40, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s70Sample : (Nat × Nat) := (0x108a41229020140205, 4)
def s70Witnesses := unpackWitnesses s70StockWords [2564, 545313, 807433]
def s70Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x71801d 3 1 10 1 1 1
def s70Data : (Nat → Nat × Nat) := fun i => decodeNode 1 11 0x31883a i
def s70Tags := dagTraceTags s70Mask 4 (dagTagBases s70StockWords 0xccc3f 0xd842d 4) 4 s70Data
def s70States := dagTrace s70Mask s70StockWords 4 s70Data
def s70MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s70Moves := dagMoves s70MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s70Autos : DagMovesOK s70Mask s70Goal 64 s70Moves := dagMovesOfCheck (by decide +kernel)
def s70Check := dagCheckNode s70Mask s70Goal s70Chart (dagKnownCloses s70Goal s70Cuts) 2 s70States s70Moves s70Links s70Sample s70Tags
def s70RootAt (token : Nat) : Bool :=
  let s := rootState s70StockWords 4 token
  !dagAllowedRoot s70Witnesses s.2.1 || dagLocal s70Mask s70Goal s70Chart (dagKnownCloses s70Goal s70Cuts) s ||
  dagRef 2 s70States s70Moves s70Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s70RootBlock0 : treeBlock 0 32 s70RootAt = true := by decide +kernel
theorem s70Roots : dagCheckRoots s70Mask s70Goal s70Chart (dagKnownCloses s70Goal s70Cuts) s70Witnesses (dagRef 2 s70States s70Moves s70Links 0) s70StockWords 4 = true := s70RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s70Block0 : treeBlock 0 2 s70Check = true := by decide +kernel
theorem s70Blocks : treeBlock 0 2 s70Check = true := s70Block0
theorem s70Known : Known s70Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s30Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s70Stock : Lower s70Mask s70StockWords s70Goal 5 := by
  apply lowerDag _ _ _ _ s70Autos _ _ _ s70Known _ s70Roots s70Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s70StockWords; decide +kernel
  · decide +kernel
  · simp only [s70Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s71Mask : Nat := 0xcccc0000cccc
abbrev s71Goal : Nat := sGoal &&& s71Mask
abbrev s71StockWords : List Nat := projectDAGStock s71Mask sBase [0, 2, 3, 5, 8]
def s71Fact : (Nat × List Nat × Nat × Nat) := (s71Mask, s71StockWords, 5, s71Goal)
def s71Cuts : List (Nat × List Nat × Nat × Nat) := [s31Fact]
def s71Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[7, 11, 14, 35, 38, 7, 7, 7, 7, 7, 7, 7, 3, 6, 42, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s71Sample : (Nat × Nat) := (0x188c060b0301c0607, 4)
def s71Witnesses := unpackWitnesses s71StockWords [3590, 529923, 804355]
def s71Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x71c01d 3 1 10 1 1 1
def s71Data : (Nat → Nat × Nat) := fun i => decodeNode 1 11 0x31c83a i
def s71Tags := dagTraceTags s71Mask 4 (dagTagBases s71StockWords 0xc843f 0xd002d 4) 4 s71Data
def s71States := dagTrace s71Mask s71StockWords 4 s71Data
def s71MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s71Moves := dagMoves s71MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Autos : DagMovesOK s71Mask s71Goal 64 s71Moves := dagMovesOfCheck (by decide +kernel)
def s71Check := dagCheckNode s71Mask s71Goal s71Chart (dagKnownCloses s71Goal s71Cuts) 2 s71States s71Moves s71Links s71Sample s71Tags
def s71RootAt (token : Nat) : Bool :=
  let s := rootState s71StockWords 4 token
  !dagAllowedRoot s71Witnesses s.2.1 || dagLocal s71Mask s71Goal s71Chart (dagKnownCloses s71Goal s71Cuts) s ||
  dagRef 2 s71States s71Moves s71Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71RootBlock0 : treeBlock 0 32 s71RootAt = true := by decide +kernel
theorem s71Roots : dagCheckRoots s71Mask s71Goal s71Chart (dagKnownCloses s71Goal s71Cuts) s71Witnesses (dagRef 2 s71States s71Moves s71Links 0) s71StockWords 4 = true := s71RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Block0 : treeBlock 0 2 s71Check = true := by decide +kernel
theorem s71Blocks : treeBlock 0 2 s71Check = true := s71Block0
theorem s71Known : Known s71Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s31Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Stock : Lower s71Mask s71StockWords s71Goal 5 := by
  apply lowerDag _ _ _ _ s71Autos _ _ _ s71Known _ s71Roots s71Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s71StockWords; decide +kernel
  · decide +kernel
  · simp only [s71Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s72Mask : Nat := 0x333300003333
abbrev s72Goal : Nat := sGoal &&& s72Mask
abbrev s72StockWords : List Nat := projectDAGStock s72Mask sBase [0, 2, 3, 5, 9]
def s72Fact : (Nat × List Nat × Nat × Nat) := (s72Mask, s72StockWords, 5, s72Goal)
def s72Cuts : List (Nat × List Nat × Nat × Nat) := [s30Fact, s7Fact]
def s72Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 41, 44, 5, 5, 5, 5, 5, 5, 5, 5, 5, 9, 12, 33, 36, 40, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s72Sample : (Nat × Nat) := (0x0, 0)
def s72Witnesses := unpackWitnesses s72StockWords [2564, 264705, 807433]
def s72Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s72Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s72Tags := dagTraceTags s72Mask 0 (dagTagBases s72StockWords 0x0 0x0 0) 4 s72Data
def s72States := dagTrace s72Mask s72StockWords 4 s72Data
def s72MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s72Moves := dagMoves s72MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Autos : DagMovesOK s72Mask s72Goal 64 s72Moves := dagMovesOfCheck (by decide +kernel)
def s72Check := dagCheckNode s72Mask s72Goal s72Chart (dagKnownCloses s72Goal s72Cuts) 0 s72States s72Moves s72Links s72Sample s72Tags
def s72RootAt (token : Nat) : Bool :=
  let s := rootState s72StockWords 4 token
  !dagAllowedRoot s72Witnesses s.2.1 || dagLocal s72Mask s72Goal s72Chart (dagKnownCloses s72Goal s72Cuts) s ||
  dagRef 0 s72States s72Moves s72Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72RootBlock0 : treeBlock 0 32 s72RootAt = true := by decide +kernel
theorem s72Roots : dagCheckRoots s72Mask s72Goal s72Chart (dagKnownCloses s72Goal s72Cuts) s72Witnesses (dagRef 0 s72States s72Moves s72Links 0) s72StockWords 4 = true := s72RootBlock0
theorem s72Blocks : treeBlock 0 0 s72Check = true := by decide +kernel
theorem s72Known : Known s72Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s7Stock) s30Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Stock : Lower s72Mask s72StockWords s72Goal 5 := by
  apply lowerDag _ _ _ _ s72Autos _ _ _ s72Known _ s72Roots s72Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s72StockWords; decide +kernel
  · decide +kernel
  · simp only [s72Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s73Mask : Nat := 0xcccc0000cccc
abbrev s73Goal : Nat := sGoal &&& s73Mask
abbrev s73StockWords : List Nat := projectDAGStock s73Mask sBase [0, 2, 3, 5, 9]
def s73Fact : (Nat × List Nat × Nat × Nat) := (s73Mask, s73StockWords, 5, s73Goal)
def s73Cuts : List (Nat × List Nat × Nat × Nat) := [s31Fact, s8Fact]
def s73Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[7, 11, 14, 35, 38, 7, 7, 7, 7, 7, 7, 7, 3, 6, 42, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s73Sample : (Nat × Nat) := (0x0, 0)
def s73Witnesses := unpackWitnesses s73StockWords [3590, 265731, 804355]
def s73Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s73Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s73Tags := dagTraceTags s73Mask 0 (dagTagBases s73StockWords 0x0 0x0 0) 4 s73Data
def s73States := dagTrace s73Mask s73StockWords 4 s73Data
def s73MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s73Moves := dagMoves s73MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Autos : DagMovesOK s73Mask s73Goal 64 s73Moves := dagMovesOfCheck (by decide +kernel)
def s73Check := dagCheckNode s73Mask s73Goal s73Chart (dagKnownCloses s73Goal s73Cuts) 0 s73States s73Moves s73Links s73Sample s73Tags
def s73RootAt (token : Nat) : Bool :=
  let s := rootState s73StockWords 4 token
  !dagAllowedRoot s73Witnesses s.2.1 || dagLocal s73Mask s73Goal s73Chart (dagKnownCloses s73Goal s73Cuts) s ||
  dagRef 0 s73States s73Moves s73Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73RootBlock0 : treeBlock 0 32 s73RootAt = true := by decide +kernel
theorem s73Roots : dagCheckRoots s73Mask s73Goal s73Chart (dagKnownCloses s73Goal s73Cuts) s73Witnesses (dagRef 0 s73States s73Moves s73Links 0) s73StockWords 4 = true := s73RootBlock0
theorem s73Blocks : treeBlock 0 0 s73Check = true := by decide +kernel
theorem s73Known : Known s73Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s8Stock) s31Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Stock : Lower s73Mask s73StockWords s73Goal 5 := by
  apply lowerDag _ _ _ _ s73Autos _ _ _ s73Known _ s73Roots s73Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s73StockWords; decide +kernel
  · decide +kernel
  · simp only [s73Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s74Mask : Nat := 0x333300003333
abbrev s74Goal : Nat := sGoal &&& s74Mask
abbrev s74StockWords : List Nat := projectDAGStock s74Mask sBase [0, 2, 3, 5, 11]
def s74Fact : (Nat × List Nat × Nat × Nat) := (s74Mask, s74StockWords, 5, s74Goal)
def s74Cuts : List (Nat × List Nat × Nat × Nat) := [s30Fact, s4Fact]
def s74Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 41, 44, 5, 5, 5, 5, 5, 5, 5, 5, 5, 9, 12, 33, 36, 40, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s74Sample : (Nat × Nat) := (0x0, 0)
def s74Witnesses := unpackWitnesses s74StockWords [2564, 264705, 545313]
def s74Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s74Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s74Tags := dagTraceTags s74Mask 0 (dagTagBases s74StockWords 0x0 0x0 0) 4 s74Data
def s74States := dagTrace s74Mask s74StockWords 4 s74Data
def s74MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s74Moves := dagMoves s74MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Autos : DagMovesOK s74Mask s74Goal 64 s74Moves := dagMovesOfCheck (by decide +kernel)
def s74Check := dagCheckNode s74Mask s74Goal s74Chart (dagKnownCloses s74Goal s74Cuts) 0 s74States s74Moves s74Links s74Sample s74Tags
def s74RootAt (token : Nat) : Bool :=
  let s := rootState s74StockWords 4 token
  !dagAllowedRoot s74Witnesses s.2.1 || dagLocal s74Mask s74Goal s74Chart (dagKnownCloses s74Goal s74Cuts) s ||
  dagRef 0 s74States s74Moves s74Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74RootBlock0 : treeBlock 0 32 s74RootAt = true := by decide +kernel
theorem s74Roots : dagCheckRoots s74Mask s74Goal s74Chart (dagKnownCloses s74Goal s74Cuts) s74Witnesses (dagRef 0 s74States s74Moves s74Links 0) s74StockWords 4 = true := s74RootBlock0
theorem s74Blocks : treeBlock 0 0 s74Check = true := by decide +kernel
theorem s74Known : Known s74Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s4Stock) s30Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Stock : Lower s74Mask s74StockWords s74Goal 5 := by
  apply lowerDag _ _ _ _ s74Autos _ _ _ s74Known _ s74Roots s74Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s74StockWords; decide +kernel
  · decide +kernel
  · simp only [s74Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s75Mask : Nat := 0xcccc0000cccc
abbrev s75Goal : Nat := sGoal &&& s75Mask
abbrev s75StockWords : List Nat := projectDAGStock s75Mask sBase [0, 2, 3, 5, 11]
def s75Fact : (Nat × List Nat × Nat × Nat) := (s75Mask, s75StockWords, 5, s75Goal)
def s75Cuts : List (Nat × List Nat × Nat × Nat) := [s31Fact, s5Fact]
def s75Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[7, 11, 14, 35, 38, 7, 7, 7, 7, 7, 7, 7, 3, 6, 42, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s75Sample : (Nat × Nat) := (0x0, 0)
def s75Witnesses := unpackWitnesses s75StockWords [3590, 265731, 529923]
def s75Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s75Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s75Tags := dagTraceTags s75Mask 0 (dagTagBases s75StockWords 0x0 0x0 0) 4 s75Data
def s75States := dagTrace s75Mask s75StockWords 4 s75Data
def s75MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s75Moves := dagMoves s75MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Autos : DagMovesOK s75Mask s75Goal 64 s75Moves := dagMovesOfCheck (by decide +kernel)
def s75Check := dagCheckNode s75Mask s75Goal s75Chart (dagKnownCloses s75Goal s75Cuts) 0 s75States s75Moves s75Links s75Sample s75Tags
def s75RootAt (token : Nat) : Bool :=
  let s := rootState s75StockWords 4 token
  !dagAllowedRoot s75Witnesses s.2.1 || dagLocal s75Mask s75Goal s75Chart (dagKnownCloses s75Goal s75Cuts) s ||
  dagRef 0 s75States s75Moves s75Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75RootBlock0 : treeBlock 0 32 s75RootAt = true := by decide +kernel
theorem s75Roots : dagCheckRoots s75Mask s75Goal s75Chart (dagKnownCloses s75Goal s75Cuts) s75Witnesses (dagRef 0 s75States s75Moves s75Links 0) s75StockWords 4 = true := s75RootBlock0
theorem s75Blocks : treeBlock 0 0 s75Check = true := by decide +kernel
theorem s75Known : Known s75Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s5Stock) s31Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Stock : Lower s75Mask s75StockWords s75Goal 5 := by
  apply lowerDag _ _ _ _ s75Autos _ _ _ s75Known _ s75Roots s75Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s75StockWords; decide +kernel
  · decide +kernel
  · simp only [s75Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s76Mask : Nat := 0x55555555
abbrev s76Goal : Nat := sGoal &&& s76Mask
abbrev s76StockWords : List Nat := projectDAGStock s76Mask sBase [1, 2, 3, 4, 7]
def s76Fact : (Nat × List Nat × Nat × Nat) := (s76Mask, s76StockWords, 5, s76Goal)
def s76Cuts : List (Nat × List Nat × Nat × Nat) := [s35Fact]
def s76Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[14, 26, 28, 14, 14, 14, 14, 14, 14, 14, 14, 14, 10, 12, 22, 24, 10, 10, 10, 10, 10, 10, 10, 10], rfl⟩
def s76Sample : (Nat × Nat) := (0x241a05038181c03038180e, 5)
def s76Witnesses := unpackWitnesses s76StockWords [269322, 531462, 799754]
def s76Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x1e 2 1 5 1 1 1
def s76Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x3c i
def s76Tags := dagTraceTags s76Mask 5 (dagTagBases s76StockWords 0x4a7dfb 0x5834fa 5) 4 s76Data
def s76States := dagTrace s76Mask s76StockWords 4 s76Data
def s76MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s76Moves := dagMoves s76MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Autos : DagMovesOK s76Mask s76Goal 64 s76Moves := dagMovesOfCheck (by decide +kernel)
def s76Check := dagCheckNode s76Mask s76Goal s76Chart (dagKnownCloses s76Goal s76Cuts) 1 s76States s76Moves s76Links s76Sample s76Tags
def s76RootAt (token : Nat) : Bool :=
  let s := rootState s76StockWords 4 token
  !dagAllowedRoot s76Witnesses s.2.1 || dagLocal s76Mask s76Goal s76Chart (dagKnownCloses s76Goal s76Cuts) s ||
  dagRef 1 s76States s76Moves s76Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76RootBlock0 : treeBlock 0 32 s76RootAt = true := by decide +kernel
theorem s76Roots : dagCheckRoots s76Mask s76Goal s76Chart (dagKnownCloses s76Goal s76Cuts) s76Witnesses (dagRef 1 s76States s76Moves s76Links 0) s76StockWords 4 = true := s76RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Block0 : treeBlock 0 1 s76Check = true := by decide +kernel
theorem s76Blocks : treeBlock 0 1 s76Check = true := s76Block0
theorem s76Known : Known s76Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s35Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Stock : Lower s76Mask s76StockWords s76Goal 5 := by
  apply lowerDag _ _ _ _ s76Autos _ _ _ s76Known _ s76Roots s76Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s76StockWords; decide +kernel
  · decide +kernel
  · simp only [s76Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s77Mask : Nat := 0x555500005555
abbrev s77Goal : Nat := sGoal &&& s77Mask
abbrev s77StockWords : List Nat := projectDAGStock s77Mask sBase [1, 2, 3, 5, 7]
def s77Fact : (Nat × List Nat × Nat × Nat) := (s77Mask, s77StockWords, 5, s77Goal)
def s77Cuts : List (Nat × List Nat × Nat × Nat) := [s36Fact]
def s77Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[14, 38, 44, 14, 14, 14, 14, 14, 14, 14, 14, 14, 6, 12, 36, 42, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩
def s77Sample : (Nat × Nat) := (0x140e060b0442603038180e, 5)
def s77Witnesses := unpackWitnesses s77StockWords [269322, 531462, 805894]
def s77Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x1e 2 1 5 1 1 1
def s77Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x3c i
def s77Tags := dagTraceTags s77Mask 5 (dagTagBases s77StockWords 0x866ff7 0x926576 5) 4 s77Data
def s77States := dagTrace s77Mask s77StockWords 4 s77Data
def s77MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s77Moves := dagMoves s77MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s77Autos : DagMovesOK s77Mask s77Goal 64 s77Moves := dagMovesOfCheck (by decide +kernel)
def s77Check := dagCheckNode s77Mask s77Goal s77Chart (dagKnownCloses s77Goal s77Cuts) 1 s77States s77Moves s77Links s77Sample s77Tags
def s77RootAt (token : Nat) : Bool :=
  let s := rootState s77StockWords 4 token
  !dagAllowedRoot s77Witnesses s.2.1 || dagLocal s77Mask s77Goal s77Chart (dagKnownCloses s77Goal s77Cuts) s ||
  dagRef 1 s77States s77Moves s77Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s77RootBlock0 : treeBlock 0 32 s77RootAt = true := by decide +kernel
theorem s77Roots : dagCheckRoots s77Mask s77Goal s77Chart (dagKnownCloses s77Goal s77Cuts) s77Witnesses (dagRef 1 s77States s77Moves s77Links 0) s77StockWords 4 = true := s77RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s77Block0 : treeBlock 0 1 s77Check = true := by decide +kernel
theorem s77Blocks : treeBlock 0 1 s77Check = true := s77Block0
theorem s77Known : Known s77Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s36Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s77Stock : Lower s77Mask s77StockWords s77Goal 5 := by
  apply lowerDag _ _ _ _ s77Autos _ _ _ s77Known _ s77Roots s77Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s77StockWords; decide +kernel
  · decide +kernel
  · simp only [s77Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s78Mask : Nat := 0xaaaa0000aaaa
abbrev s78Goal : Nat := sGoal &&& s78Mask
abbrev s78StockWords : List Nat := projectDAGStock s78Mask sBase [1, 2, 3, 5, 7]
def s78Fact : (Nat × List Nat × Nat × Nat) := (s78Mask, s78StockWords, 5, s78Goal)
def s78Cuts : List (Nat × List Nat × Nat × Nat) := [s37Fact]
def s78Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 35, 41, 5, 5, 5, 5, 5, 5, 5, 5, 3, 9, 33, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s78Sample : (Nat × Nat) := (0x108141205048a4060b00814120b, 6)
def s78Witnesses := unpackWitnesses s78StockWords [264705, 529923, 804355]
def s78Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x1e 2 1 5 1 1 1
def s78Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x3c i
def s78Tags := dagTraceTags s78Mask 6 (dagTagBases s78StockWords 0x3a20dc85 0x3b819004 6) 4 s78Data
def s78States := dagTrace s78Mask s78StockWords 4 s78Data
def s78MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s78Moves := dagMoves s78MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s78Autos : DagMovesOK s78Mask s78Goal 64 s78Moves := dagMovesOfCheck (by decide +kernel)
def s78Check := dagCheckNode s78Mask s78Goal s78Chart (dagKnownCloses s78Goal s78Cuts) 1 s78States s78Moves s78Links s78Sample s78Tags
def s78RootAt (token : Nat) : Bool :=
  let s := rootState s78StockWords 4 token
  !dagAllowedRoot s78Witnesses s.2.1 || dagLocal s78Mask s78Goal s78Chart (dagKnownCloses s78Goal s78Cuts) s ||
  dagRef 1 s78States s78Moves s78Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s78RootBlock0 : treeBlock 0 32 s78RootAt = true := by decide +kernel
theorem s78Roots : dagCheckRoots s78Mask s78Goal s78Chart (dagKnownCloses s78Goal s78Cuts) s78Witnesses (dagRef 1 s78States s78Moves s78Links 0) s78StockWords 4 = true := s78RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s78Block0 : treeBlock 0 1 s78Check = true := by decide +kernel
theorem s78Blocks : treeBlock 0 1 s78Check = true := s78Block0
theorem s78Known : Known s78Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s37Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s78Stock : Lower s78Mask s78StockWords s78Goal 5 := by
  apply lowerDag _ _ _ _ s78Autos _ _ _ s78Known _ s78Roots s78Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s78StockWords; decide +kernel
  · decide +kernel
  · simp only [s78Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s79Mask : Nat := 0x555500005555
abbrev s79Goal : Nat := sGoal &&& s79Mask
abbrev s79StockWords : List Nat := projectDAGStock s79Mask sBase [1, 2, 3, 5, 8]
def s79Fact : (Nat × List Nat × Nat × Nat) := (s79Mask, s79StockWords, 5, s79Goal)
def s79Cuts : List (Nat × List Nat × Nat × Nat) := [s36Fact, s12Fact]
def s79Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[14, 38, 44, 14, 14, 14, 14, 14, 14, 14, 14, 14, 6, 12, 36, 42, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩
def s79Sample : (Nat × Nat) := (0x0, 0)
def s79Witnesses := unpackWitnesses s79StockWords [7180, 531462, 805894]
def s79Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x0 0x0 2 1 1 1 1 1
def s79Data : (Nat → Nat × Nat) := fun i => decodeNode 1 2 0x0 i
def s79Tags := dagTraceTags s79Mask 0 (dagTagBases s79StockWords 0x0 0x0 0) 4 s79Data
def s79States := dagTrace s79Mask s79StockWords 4 s79Data
def s79MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s79Moves := dagMoves s79MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Autos : DagMovesOK s79Mask s79Goal 64 s79Moves := dagMovesOfCheck (by decide +kernel)
def s79Check := dagCheckNode s79Mask s79Goal s79Chart (dagKnownCloses s79Goal s79Cuts) 0 s79States s79Moves s79Links s79Sample s79Tags
def s79RootAt (token : Nat) : Bool :=
  let s := rootState s79StockWords 4 token
  !dagAllowedRoot s79Witnesses s.2.1 || dagLocal s79Mask s79Goal s79Chart (dagKnownCloses s79Goal s79Cuts) s ||
  dagRef 0 s79States s79Moves s79Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79RootBlock0 : treeBlock 0 32 s79RootAt = true := by decide +kernel
theorem s79Roots : dagCheckRoots s79Mask s79Goal s79Chart (dagKnownCloses s79Goal s79Cuts) s79Witnesses (dagRef 0 s79States s79Moves s79Links 0) s79StockWords 4 = true := s79RootBlock0
theorem s79Blocks : treeBlock 0 0 s79Check = true := by decide +kernel
theorem s79Known : Known s79Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s12Stock) s36Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Stock : Lower s79Mask s79StockWords s79Goal 5 := by
  apply lowerDag _ _ _ _ s79Autos _ _ _ s79Known _ s79Roots s79Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s79StockWords; decide +kernel
  · decide +kernel
  · simp only [s79Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s80Mask : Nat := 0x555500005555
abbrev s80Goal : Nat := sGoal &&& s80Mask
abbrev s80StockWords : List Nat := projectDAGStock s80Mask sBase [1, 2, 3, 5, 9]
def s80Fact : (Nat × List Nat × Nat × Nat) := (s80Mask, s80StockWords, 5, s80Goal)
def s80Cuts : List (Nat × List Nat × Nat × Nat) := [s36Fact]
def s80Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[14, 38, 44, 14, 14, 14, 14, 14, 14, 14, 14, 14, 6, 12, 36, 42, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩
def s80Sample : (Nat × Nat) := (0x502c060380c26050380c0e, 5)
def s80Witnesses := unpackWitnesses s80StockWords [7180, 269322, 805894]
def s80Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x1b 2 1 5 1 1 1
def s80Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x36 i
def s80Tags := dagTraceTags s80Mask 5 (dagTagBases s80StockWords 0x4a6fef 0x5869a7 5) 4 s80Data
def s80States := dagTrace s80Mask s80StockWords 4 s80Data
def s80MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s80Moves := dagMoves s80MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Autos : DagMovesOK s80Mask s80Goal 64 s80Moves := dagMovesOfCheck (by decide +kernel)
def s80Check := dagCheckNode s80Mask s80Goal s80Chart (dagKnownCloses s80Goal s80Cuts) 1 s80States s80Moves s80Links s80Sample s80Tags
def s80RootAt (token : Nat) : Bool :=
  let s := rootState s80StockWords 4 token
  !dagAllowedRoot s80Witnesses s.2.1 || dagLocal s80Mask s80Goal s80Chart (dagKnownCloses s80Goal s80Cuts) s ||
  dagRef 1 s80States s80Moves s80Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80RootBlock0 : treeBlock 0 32 s80RootAt = true := by decide +kernel
theorem s80Roots : dagCheckRoots s80Mask s80Goal s80Chart (dagKnownCloses s80Goal s80Cuts) s80Witnesses (dagRef 1 s80States s80Moves s80Links 0) s80StockWords 4 = true := s80RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Block0 : treeBlock 0 1 s80Check = true := by decide +kernel
theorem s80Blocks : treeBlock 0 1 s80Check = true := s80Block0
theorem s80Known : Known s80Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s36Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Stock : Lower s80Mask s80StockWords s80Goal 5 := by
  apply lowerDag _ _ _ _ s80Autos _ _ _ s80Known _ s80Roots s80Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s80StockWords; decide +kernel
  · decide +kernel
  · simp only [s80Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s81Mask : Nat := 0xaaaa0000aaaa
abbrev s81Goal : Nat := sGoal &&& s81Mask
abbrev s81StockWords : List Nat := projectDAGStock s81Mask sBase [1, 2, 3, 5, 9]
def s81Fact : (Nat × List Nat × Nat × Nat) := (s81Mask, s81StockWords, 5, s81Goal)
def s81Cuts : List (Nat × List Nat × Nat × Nat) := [s37Fact]
def s81Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 35, 41, 5, 5, 5, 5, 5, 5, 5, 5, 3, 9, 33, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s81Sample : (Nat × Nat) := (0x1081406050188c120b00814060b, 6)
def s81Witnesses := unpackWitnesses s81StockWords [5641, 264705, 804355]
def s81Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x1b 2 1 5 1 1 1
def s81Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x36 i
def s81Tags := dagTraceTags s81Mask 6 (dagTagBases s81StockWords 0x3a205c8d 0x3b804019 6) 4 s81Data
def s81States := dagTrace s81Mask s81StockWords 4 s81Data
def s81MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s81Moves := dagMoves s81MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s81Autos : DagMovesOK s81Mask s81Goal 64 s81Moves := dagMovesOfCheck (by decide +kernel)
def s81Check := dagCheckNode s81Mask s81Goal s81Chart (dagKnownCloses s81Goal s81Cuts) 1 s81States s81Moves s81Links s81Sample s81Tags
def s81RootAt (token : Nat) : Bool :=
  let s := rootState s81StockWords 4 token
  !dagAllowedRoot s81Witnesses s.2.1 || dagLocal s81Mask s81Goal s81Chart (dagKnownCloses s81Goal s81Cuts) s ||
  dagRef 1 s81States s81Moves s81Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s81RootBlock0 : treeBlock 0 32 s81RootAt = true := by decide +kernel
theorem s81Roots : dagCheckRoots s81Mask s81Goal s81Chart (dagKnownCloses s81Goal s81Cuts) s81Witnesses (dagRef 1 s81States s81Moves s81Links 0) s81StockWords 4 = true := s81RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s81Block0 : treeBlock 0 1 s81Check = true := by decide +kernel
theorem s81Blocks : treeBlock 0 1 s81Check = true := s81Block0
theorem s81Known : Known s81Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s37Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s81Stock : Lower s81Mask s81StockWords s81Goal 5 := by
  apply lowerDag _ _ _ _ s81Autos _ _ _ s81Known _ s81Roots s81Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s81StockWords; decide +kernel
  · decide +kernel
  · simp only [s81Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s82Mask : Nat := 0x555500005555
abbrev s82Goal : Nat := sGoal &&& s82Mask
abbrev s82StockWords : List Nat := projectDAGStock s82Mask sBase [1, 2, 3, 5, 11]
def s82Fact : (Nat × List Nat × Nat × Nat) := (s82Mask, s82StockWords, 5, s82Goal)
def s82Cuts : List (Nat × List Nat × Nat × Nat) := [s36Fact]
def s82Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[14, 38, 44, 14, 14, 14, 14, 14, 14, 14, 14, 14, 6, 12, 36, 42, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩
def s82Sample : (Nat × Nat) := (0x502c120984426030380c26, 5)
def s82Witnesses := unpackWitnesses s82StockWords [7180, 269322, 531462]
def s82Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x17 2 1 5 1 1 1
def s82Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x2e i
def s82Tags := dagTraceTags s82Mask 5 (dagTagBases s82StockWords 0x2ecbef 0x3e4167 5) 4 s82Data
def s82States := dagTrace s82Mask s82StockWords 4 s82Data
def s82MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s82Moves := dagMoves s82MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82Autos : DagMovesOK s82Mask s82Goal 64 s82Moves := dagMovesOfCheck (by decide +kernel)
def s82Check := dagCheckNode s82Mask s82Goal s82Chart (dagKnownCloses s82Goal s82Cuts) 1 s82States s82Moves s82Links s82Sample s82Tags
def s82RootAt (token : Nat) : Bool :=
  let s := rootState s82StockWords 4 token
  !dagAllowedRoot s82Witnesses s.2.1 || dagLocal s82Mask s82Goal s82Chart (dagKnownCloses s82Goal s82Cuts) s ||
  dagRef 1 s82States s82Moves s82Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82RootBlock0 : treeBlock 0 32 s82RootAt = true := by decide +kernel
theorem s82Roots : dagCheckRoots s82Mask s82Goal s82Chart (dagKnownCloses s82Goal s82Cuts) s82Witnesses (dagRef 1 s82States s82Moves s82Links 0) s82StockWords 4 = true := s82RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82Block0 : treeBlock 0 1 s82Check = true := by decide +kernel
theorem s82Blocks : treeBlock 0 1 s82Check = true := s82Block0
theorem s82Known : Known s82Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s36Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82Stock : Lower s82Mask s82StockWords s82Goal 5 := by
  apply lowerDag _ _ _ _ s82Autos _ _ _ s82Known _ s82Roots s82Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s82StockWords; decide +kernel
  · decide +kernel
  · simp only [s82Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s83Mask : Nat := 0xaaaa0000aaaa
abbrev s83Goal : Nat := sGoal &&& s83Mask
abbrev s83StockWords : List Nat := projectDAGStock s83Mask sBase [1, 2, 3, 5, 11]
def s83Fact : (Nat × List Nat × Nat × Nat) := (s83Mask, s83StockWords, 5, s83Goal)
def s83Cuts : List (Nat × List Nat × Nat × Nat) := [s37Fact]
def s83Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 35, 41, 5, 5, 5, 5, 5, 5, 5, 5, 3, 9, 33, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s83Sample : (Nat × Nat) := (0x481406051088c060b008140623, 6)
def s83Witnesses := unpackWitnesses s83StockWords [5641, 264705, 529923]
def s83Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x17 2 1 5 1 1 1
def s83Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x2e i
def s83Tags := dagTraceTags s83Mask 6 (dagTagBases s83StockWords 0x36244c8d 0x37220015 6) 4 s83Data
def s83States := dagTrace s83Mask s83StockWords 4 s83Data
def s83MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s83Moves := dagMoves s83MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s83Autos : DagMovesOK s83Mask s83Goal 64 s83Moves := dagMovesOfCheck (by decide +kernel)
def s83Check := dagCheckNode s83Mask s83Goal s83Chart (dagKnownCloses s83Goal s83Cuts) 1 s83States s83Moves s83Links s83Sample s83Tags
def s83RootAt (token : Nat) : Bool :=
  let s := rootState s83StockWords 4 token
  !dagAllowedRoot s83Witnesses s.2.1 || dagLocal s83Mask s83Goal s83Chart (dagKnownCloses s83Goal s83Cuts) s ||
  dagRef 1 s83States s83Moves s83Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s83RootBlock0 : treeBlock 0 32 s83RootAt = true := by decide +kernel
theorem s83Roots : dagCheckRoots s83Mask s83Goal s83Chart (dagKnownCloses s83Goal s83Cuts) s83Witnesses (dagRef 1 s83States s83Moves s83Links 0) s83StockWords 4 = true := s83RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s83Block0 : treeBlock 0 1 s83Check = true := by decide +kernel
theorem s83Blocks : treeBlock 0 1 s83Check = true := s83Block0
theorem s83Known : Known s83Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s37Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s83Stock : Lower s83Mask s83StockWords s83Goal 5 := by
  apply lowerDag _ _ _ _ s83Autos _ _ _ s83Known _ s83Roots s83Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s83StockWords; decide +kernel
  · decide +kernel
  · simp only [s83Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s84Mask : Nat := 0xffffffff
abbrev s84Goal : Nat := sGoal &&& s84Mask
abbrev s84StockWords : List Nat := projectDAGStock s84Mask sBase [0, 1, 2, 3, 4]
def s84Fact : (Nat × List Nat × Nat × Nat) := (s84Mask, s84StockWords, 8, s84Goal)
def s84Witnesses := unpackWitnesses s84StockWords [2564, 267785, 526849, 792067, 1057281]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Stock : Lower s84Mask s84StockWords s84Goal 8 := by
  apply essentialLift (witnesses := s84Witnesses) (cut := s15Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s15StockWords) (by decide +kernel)
  · exact s15Stock
  · decide +kernel
def s85Mask : Nat := 0xffff0000ffff
abbrev s85Goal : Nat := sGoal &&& s85Mask
abbrev s85StockWords : List Nat := projectDAGStock s85Mask sBase [0, 1, 2, 3, 5]
def s85Fact : (Nat × List Nat × Nat × Nat) := (s85Mask, s85StockWords, 8, s85Goal)
def s85Cuts : List (Nat × List Nat × Nat × Nat) := [s30Fact, s36Fact, s16Fact, s19Fact, s17Fact, s23Fact, s20Fact, s24Fact, s31Fact, s37Fact]
def s85Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 35, 38, 41, 44, 5, 5, 5, 5, 5, 3, 6, 9, 12, 33, 36, 42, 3, 3, 3, 3, 3], rfl⟩
def s85Sample : (Nat × Nat) := (0x48a44225030384223150ac422903098140e060380805, 10)
def s85Witnesses := unpackWitnesses s85StockWords [2564, 267785, 526849, 792067, 1066499]
def s85Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x1c2a50a0d0681 0x370e0592c8988023146b0e1292c0d8802314730e1492c85880431404020001f 7 3 12 3 3 3
def s85Data : (Nat → Nat × Nat) := fun i => decodeNode 3 15 0x24b298a16204628802080f8 i
def s85Tags := dagTraceTags s85Mask 10 (dagTagBases s85StockWords 0x378ad98f3bb71 0x1708988b2b350 10) 7 s85Data
def s85States := dagTrace s85Mask s85StockWords 7 s85Data
def s85Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])]
def s85Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val)
def s85Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val)
def s85Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcc33cc33cc33cc33, 0), (0xcc00cc00cc00cc, 6)], [(0x3300330033003300, 6)])]
def s85Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)
def s85Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)
def s85Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcc00cc0000330033, 0), (0xcc00cc, 6), (0x33003300, 24), (0xcc00cc00, 30)], [(0x3300330000000000, 6), (0xcc00cc00000000, 24), (0x33003300000000, 30)])]
def s85Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 5, 2, 1, 4, 3] 0 i.val)
def s85Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 2, 5, 4, 1] 0 i.val)
def s85Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s85Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s85Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s85MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s85Move0Stages, s85Move0Map, s85Move0Inverse), (s85Move1Stages, s85Move1Map, s85Move1Inverse), (s85Move2Stages, s85Move2Map, s85Move2Inverse), (s85Move3Stages, s85Move3Map, s85Move3Inverse)]
def s85Moves := dagMoves s85MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Autos : DagMovesOK s85Mask s85Goal 64 s85Moves := dagMovesOfCheck (by decide +kernel)
def s85Check := dagCheckNode s85Mask s85Goal s85Chart (dagKnownCloses s85Goal s85Cuts) 6 s85States s85Moves s85Links s85Sample s85Tags
def s85RootAt (token : Nat) : Bool :=
  let s := rootState s85StockWords 7 token
  !dagAllowedRoot s85Witnesses s.2.1 || dagLocal s85Mask s85Goal s85Chart (dagKnownCloses s85Goal s85Cuts) s ||
  dagRef 6 s85States s85Moves s85Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85RootBlock0 : treeBlock 0 32 s85RootAt = true := by decide +kernel
theorem s85Roots : dagCheckRoots s85Mask s85Goal s85Chart (dagKnownCloses s85Goal s85Cuts) s85Witnesses (dagRef 6 s85States s85Moves s85Links 0) s85StockWords 7 = true := s85RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Block0 : treeBlock 0 6 s85Check = true := by decide +kernel
theorem s85Blocks : treeBlock 0 6 s85Check = true := s85Block0
theorem s85Known : Known s85Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s37Stock) s31Stock) s24Stock) s20Stock) s23Stock) s17Stock) s19Stock) s16Stock) s36Stock) s30Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Stock : Lower s85Mask s85StockWords s85Goal 8 := by
  apply lowerDag _ _ _ _ s85Autos _ _ _ s85Known _ s85Roots s85Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s85StockWords; decide +kernel
  · decide +kernel
  · simp only [s85Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s86Mask : Nat := 0xff00ff00ff00ff00
abbrev s86Goal : Nat := sGoal &&& s86Mask
abbrev s86StockWords : List Nat := projectDAGStock s86Mask sBase [0, 1, 2, 4, 5]
def s86Fact : (Nat × List Nat × Nat × Nat) := (s86Mask, s86StockWords, 8, s86Goal)
def s86Witnesses := unpackWitnesses s86StockWords [5642, 267785, 530953, 799241, 1069577]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s86Stock : Lower s86Mask s86StockWords s86Goal 8 := by
  apply essentialLift (witnesses := s86Witnesses) (cut := s15Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s15StockWords) (by decide +kernel)
  · exact s15Stock
  · decide +kernel
def s87Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev s87Goal : Nat := sGoal &&& s87Mask
abbrev s87StockWords : List Nat := projectDAGStock s87Mask sBase [0, 1, 3, 4, 5]
def s87Fact : (Nat × List Nat × Nat × Nat) := (s87Mask, s87StockWords, 8, s87Goal)
def s87Cuts : List (Nat × List Nat × Nat × Nat) := [s25Fact, s23Fact, s21Fact, s34Fact, s40Fact, s26Fact, s22Fact, s13Fact, s10Fact, s9Fact]
def s87Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 17, 26, 35, 41, 50, 11, 11, 11, 11, 11, 11, 3, 9, 18, 33, 42, 56, 3, 3, 3, 3, 3, 3], rfl⟩
def s87Sample : (Nat × Nat) := (0x60320188c0613150a4241a108a44223150ac4432090c812290804412190c068060b, 15)
def s87Witnesses := unpackWitnesses s87StockWords [5642, 267785, 529923, 795137, 1066499]
def s87Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x7b78786360525050503b0e01 0x31870892c3310270e112583314349608c5278703620118a5f0e152587620298a1003c2010001f 8 3 12 4 1 3
def s87Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x92c1c38892c8620192c6314100f162023142008101f0 i
def s87Tags := dagTraceTags s87Mask 15 (dagTagBases s87StockWords 0x6bf0a8dc3a5faf1bb9d 0x4bc088542259e70b315 15) 7 s87Data
def s87States := dagTrace s87Mask s87StockWords 7 s87Data
def s87Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])]
def s87Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val)
def s87Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val)
def s87MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s87Move0Stages, s87Move0Map, s87Move0Inverse)]
def s87Moves := dagMoves s87MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Autos : DagMovesOK s87Mask s87Goal 64 s87Moves := dagMovesOfCheck (by decide +kernel)
def s87Check := dagCheckNode s87Mask s87Goal s87Chart (dagKnownCloses s87Goal s87Cuts) 11 s87States s87Moves s87Links s87Sample s87Tags
def s87RootAt (token : Nat) : Bool :=
  let s := rootState s87StockWords 7 token
  !dagAllowedRoot s87Witnesses s.2.1 || dagLocal s87Mask s87Goal s87Chart (dagKnownCloses s87Goal s87Cuts) s ||
  dagRef 11 s87States s87Moves s87Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87RootBlock0 : treeBlock 0 32 s87RootAt = true := by decide +kernel
theorem s87Roots : dagCheckRoots s87Mask s87Goal s87Chart (dagKnownCloses s87Goal s87Cuts) s87Witnesses (dagRef 11 s87States s87Moves s87Links 0) s87StockWords 7 = true := s87RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block0 : treeBlock 0 11 s87Check = true := by decide +kernel
theorem s87Blocks : treeBlock 0 11 s87Check = true := s87Block0
theorem s87Known : Known s87Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s9Stock) s10Stock) s13Stock) s22Stock) s26Stock) s40Stock) s34Stock) s21Stock) s23Stock) s25Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Stock : Lower s87Mask s87StockWords s87Goal 8 := by
  apply lowerDag _ _ _ _ s87Autos _ _ _ s87Known _ s87Roots s87Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s87StockWords; decide +kernel
  · decide +kernel
  · simp only [s87Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s88Mask : Nat := 0x5555555555555555
abbrev s88Goal : Nat := sGoal &&& s88Mask
abbrev s88StockWords : List Nat := projectDAGStock s88Mask sBase [1, 2, 3, 4, 5]
def s88Fact : (Nat × List Nat × Nat × Nat) := (s88Mask, s88StockWords, 8, s88Goal)
def s88Cuts : List (Nat × List Nat × Nat × Nat) := [s36Fact, s39Fact, s12Fact, s35Fact, s38Fact, s76Fact, s11Fact, s77Fact]
def s88Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[14, 26, 28, 38, 44, 50, 14, 14, 14, 14, 14, 14, 12, 22, 42, 52, 56, 12, 12, 12, 12, 12, 12, 12], rfl⟩
def s88Sample : (Nat × Nat) := (0x140b054260309868260b068140e0b098180e03038541a150b0683212098442606070482c090c8182c09068301a110c8301c, 22)
def s88Witnesses := unpackWitnesses s88StockWords [7180, 269322, 531462, 799754, 1068038]
def s88Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x542a132984c2610380401e2f0783483801 0xcc38cc96270e10c402314281a498804629bc386c9bae4b2ec40a31b398a580dcc057401b20078c0242010001f 9 4 12 4 1 4
def s88Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x9371c38c92c131b1c3886208314102b1034500f100913142008101f0 i
def s88Tags := dagTraceTags s88Mask 22 (dagTagBases s88StockWords 0x3c8f720852be378ddf7af45ff72e 0x341f421a10b7158953b9b41bb92a 22) 7 s88Data
def s88States := dagTrace s88Mask s88StockWords 7 s88Data
def s88Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00f00000000f00f, 0), (0xf00000000000f0, 4), (0xf000000, 12), (0xf00f0000, 16), (0xf00000, 20)], [(0xf00000000000f00, 4), (0xf000000000, 12), (0xf00f00000000, 16), (0xf0000000000, 20)])]
def s88Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)
def s88Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)
def s88MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s88Move0Stages, s88Move0Map, s88Move0Inverse)]
def s88Moves := dagMoves s88MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Autos : DagMovesOK s88Mask s88Goal 64 s88Moves := dagMovesOfCheck (by decide +kernel)
def s88Check := dagCheckNode s88Mask s88Goal s88Chart (dagKnownCloses s88Goal s88Cuts) 14 s88States s88Moves s88Links s88Sample s88Tags
def s88RootAt (token : Nat) : Bool :=
  let s := rootState s88StockWords 7 token
  !dagAllowedRoot s88Witnesses s.2.1 || dagLocal s88Mask s88Goal s88Chart (dagKnownCloses s88Goal s88Cuts) s ||
  dagRef 14 s88States s88Moves s88Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88RootBlock0 : treeBlock 0 32 s88RootAt = true := by decide +kernel
theorem s88Roots : dagCheckRoots s88Mask s88Goal s88Chart (dagKnownCloses s88Goal s88Cuts) s88Witnesses (dagRef 14 s88States s88Moves s88Links 0) s88StockWords 7 = true := s88RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Block0 : treeBlock 0 14 s88Check = true := by decide +kernel
theorem s88Blocks : treeBlock 0 14 s88Check = true := s88Block0
theorem s88Known : Known s88Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s77Stock) s11Stock) s76Stock) s38Stock) s35Stock) s12Stock) s39Stock) s36Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Stock : Lower s88Mask s88StockWords s88Goal 8 := by
  apply lowerDag _ _ _ _ s88Autos _ _ _ s88Known _ s88Roots s88Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s88StockWords; decide +kernel
  · decide +kernel
  · simp only [s88Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s89Mask : Nat := 0xffffffff00000000
abbrev s89Goal : Nat := sGoal &&& s89Mask
abbrev s89StockWords : List Nat := projectDAGStock s89Mask sBase [0, 1, 2, 3, 4]
def s89Fact : (Nat × List Nat × Nat × Nat) := (s89Mask, s89StockWords, 7, s89Goal)
def s89Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact, s18Fact, s22Fact, s28Fact]
def s89Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[35, 37, 38, 41, 44, 49, 50, 35, 35, 35, 35, 35, 33, 42, 52, 56, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s89Sample : (Nat × Nat) := (0x1a0f05029120984225108c442291c0f0703a1a0d4543a120b044261088c4423, 14)
def s89Witnesses := unpackWitnesses s89StockWords [17954, 280097, 543265, 807457, 1073697]
def s89Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x141f 3 1 5 1 1 1
def s89Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x47e i
def s89Tags := dagTraceTags s89Mask 14 (dagTagBases s89StockWords 0x22f0c762cac215d723 0x20e043428280054702 14) 6 s89Data
def s89States := dagTrace s89Mask s89StockWords 6 s89Data
def s89MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s89Moves := dagMoves s89MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Autos : DagMovesOK s89Mask s89Goal 64 s89Moves := dagMovesOfCheck (by decide +kernel)
def s89Check := dagCheckNode s89Mask s89Goal s89Chart (dagKnownCloses s89Goal s89Cuts) 2 s89States s89Moves s89Links s89Sample s89Tags
def s89RootAt (token : Nat) : Bool :=
  let s := rootState s89StockWords 6 token
  !dagAllowedRoot s89Witnesses s.2.1 || dagLocal s89Mask s89Goal s89Chart (dagKnownCloses s89Goal s89Cuts) s ||
  dagRef 2 s89States s89Moves s89Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89RootBlock0 : treeBlock 0 32 s89RootAt = true := by decide +kernel
theorem s89Roots : dagCheckRoots s89Mask s89Goal s89Chart (dagKnownCloses s89Goal s89Cuts) s89Witnesses (dagRef 2 s89States s89Moves s89Links 0) s89StockWords 6 = true := s89RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Block0 : treeBlock 0 2 s89Check = true := by decide +kernel
theorem s89Blocks : treeBlock 0 2 s89Check = true := s89Block0
theorem s89Known : Known s89Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s28Stock) s22Stock) s18Stock) s17Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Stock : Lower s89Mask s89StockWords s89Goal 7 := by
  apply lowerDag _ _ _ _ s89Autos _ _ _ s89Known _ s89Roots s89Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s89StockWords; decide +kernel
  · decide +kernel
  · simp only [s89Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s90Mask : Nat := 0x3333333333333333
abbrev s90Goal : Nat := sGoal &&& s90Mask
abbrev s90StockWords : List Nat := projectDAGStock s90Mask sBase [0, 2, 3, 4, 5]
def s90Fact : (Nat × List Nat × Nat × Nat) := (s90Mask, s90StockWords, 7, s90Goal)
def s90Cuts : List (Nat × List Nat × Nat × Nat) := [s32Fact, s27Fact, s30Fact, s28Fact]
def s90Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 17, 28, 41, 44, 5, 5, 5, 5, 5, 5, 5, 9, 12, 33, 52, 56, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s90Sample : (Nat × Nat) := (0x182c060704231108a412290a07002111c0f07039020140205, 11)
def s90Witnesses := unpackWitnesses s90StockWords [2564, 264705, 538644, 795137, 1069577]
def s90Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xcc61 0x2c5081001f 4 2 10 2 1 2
def s90Data : (Nat → Nat × Nat) := fun i => decodeNode 1 11 0x18a40883e i
def s90Tags := dagTraceTags s90Mask 11 (dagTagBases s90StockWords 0x5cc679bb3159d7 0x18c059933111d1 11) 6 s90Data
def s90States := dagTrace s90Mask s90StockWords 6 s90Data
def s90MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s90Moves := dagMoves s90MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90Autos : DagMovesOK s90Mask s90Goal 64 s90Moves := dagMovesOfCheck (by decide +kernel)
def s90Check := dagCheckNode s90Mask s90Goal s90Chart (dagKnownCloses s90Goal s90Cuts) 3 s90States s90Moves s90Links s90Sample s90Tags
def s90RootAt (token : Nat) : Bool :=
  let s := rootState s90StockWords 6 token
  !dagAllowedRoot s90Witnesses s.2.1 || dagLocal s90Mask s90Goal s90Chart (dagKnownCloses s90Goal s90Cuts) s ||
  dagRef 3 s90States s90Moves s90Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90RootBlock0 : treeBlock 0 32 s90RootAt = true := by decide +kernel
theorem s90Roots : dagCheckRoots s90Mask s90Goal s90Chart (dagKnownCloses s90Goal s90Cuts) s90Witnesses (dagRef 3 s90States s90Moves s90Links 0) s90StockWords 6 = true := s90RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90Block0 : treeBlock 0 3 s90Check = true := by decide +kernel
theorem s90Blocks : treeBlock 0 3 s90Check = true := s90Block0
theorem s90Known : Known s90Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s28Stock) s30Stock) s27Stock) s32Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90Stock : Lower s90Mask s90StockWords s90Goal 7 := by
  apply lowerDag _ _ _ _ s90Autos _ _ _ s90Known _ s90Roots s90Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s90StockWords; decide +kernel
  · decide +kernel
  · simp only [s90Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s91Mask : Nat := 0xf0f0f0f0f0f0f0f0
abbrev s91Goal : Nat := sGoal &&& s91Mask
abbrev s91StockWords : List Nat := projectDAGStock s91Mask sBase [0, 1, 3, 4, 5]
def s91Fact : (Nat × List Nat × Nat × Nat) := (s91Mask, s91StockWords, 6, s91Goal)
def s91Witnesses := unpackWitnesses s91StockWords [2564, 269324, 531462, 800780, 1068038]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Stock : Lower s91Mask s91StockWords s91Goal 6 := by
  apply essentialLift (witnesses := s91Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s92Mask : Nat := 0xcccccccccccccccc
abbrev s92Goal : Nat := sGoal &&& s92Mask
abbrev s92StockWords : List Nat := projectDAGStock s92Mask sBase [0, 2, 3, 4, 5]
def s92Fact : (Nat × List Nat × Nat × Nat) := (s92Mask, s92StockWords, 6, s92Goal)
def s92Witnesses := unpackWitnesses s92StockWords [3590, 265731, 529923, 796163, 1066499]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Stock : Lower s92Mask s92StockWords s92Goal 6 := by
  apply essentialLift (witnesses := s92Witnesses) (cut := s5Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s5StockWords) (by decide +kernel)
  · exact s5Stock
  · decide +kernel
def s93Mask : Nat := 0xaaaaaaaaaaaaaaaa
abbrev s93Goal : Nat := sGoal &&& s93Mask
abbrev s93StockWords : List Nat := projectDAGStock s93Mask sBase [1, 2, 3, 4, 5]
def s93Fact : (Nat × List Nat × Nat × Nat) := (s93Mask, s93StockWords, 6, s93Goal)
def s93Witnesses := unpackWitnesses s93StockWords [5641, 264705, 529923, 795137, 1066499]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Stock : Lower s93Mask s93StockWords s93Goal 6 := by
  apply essentialLift (witnesses := s93Witnesses) (cut := s13Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s13StockWords) (by decide +kernel)
  · exact s13Stock
  · decide +kernel
def s94Mask : Nat := 0xffffffff
abbrev s94Goal : Nat := sGoal &&& s94Mask
abbrev s94StockWords : List Nat := projectDAGStock s94Mask sBase [0, 1, 2, 3, 4, 6]
def s94Fact : (Nat × List Nat × Nat × Nat) := (s94Mask, s94StockWords, 8, s94Goal)
def s94Cuts : List (Nat × List Nat × Nat × Nat) := [s84Fact]
def s94Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 17, 26, 28, 5, 5, 5, 5, 5, 5, 3, 9, 10, 12, 22, 24, 3, 3, 3, 3, 3, 3], rfl⟩
def s94Sample : (Nat × Nat) := (0x301904864061306034120d0b0702c170804400110b038040b0201c080500014061104814060509068020503038140e0c068181c0482c02110181c281c0182c180e0c070141a0a054140b, 33)
def s94Witnesses := unpackWitnesses s94StockWords [267785, 526849, 792067, 1057281]
def s94Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xf00f00ee1ec1ec0ec0ec0ec0ec0ea1ea0ea0e62e60e60e60e60e60e03de1dc1dc0dc0dc0d82d04d00d00d00d00d00ca3ca0ca0a15a00a00a00a00a009659609419219209018e18e08a28a08a08058008007e17c17a17a07817427027006e16c16c06c06c06256206016006005e15e05c15c05c05c05c05c05c05c05c05c04e74e04c14c04a14a04a04a04a04a04a040505e002 0x5f33055630586305593c48028510285001c4f0104a018490184a624493184d9304c3244b02448018440344302842010dbc41dac3d60c385e9415d93d5c92c5b6415a63d59620573415633d5432653314520364e0324702a460264501e4101a400123f00e2f92c1f62013326063143900837024123243403c1102410324310102f92c1e620053142e011020082932426010a701c2700c28318260282963425010230240f0241f92c1e6200e31a04314020081c3241963c1701c1392c1263211626106200f3190e3140d0080b624090340692c05620043140301a020083dc393c9373b9333a92d3892c36637356333362b32627306212d6202c3372b3332a32b243272231f2131b203151d3141b0371a0331802b160271501f1401b0c01a0a0130800f07009010083e03f0003e 12 5 12 7 1 5
def s94Data : (Nat → Nat × Nat) := fun i => decodeNode 7 19 0x61c3f330bf282fe4f5fc963f6417ec7afd881fb18583417e67afe4f2a9933f3147e06cfc0a2780e4f0109e064fe4c241924802490c4924c62480c4802a7e04cfc079f81a420288402108069f8093f00e7e07e030e40c9b819330325a04021cc96010246ec6e058cc081e3462b02c4e040418b108192c5c022b9880099b8133302656058d1298c2600c4e050980412993810244663e04c6c098a8192c3cc4078c5009921c03702066058f0c8158101c2e04e0407c080d8192c1ac64358986b100d3191a62834020680d0162416026040d04807810090325809880118a0201a0401008020081f00 i
def s94Tags := dagTraceTags s94Mask 33 (dagTagBases s94StockWords 0x110178b9cf048d4edc605f3e8f2edd36889c1756bf77f43a3 0x25ff178bf0e80884ad8010f0e8b2c09148998b614ad00743a0 33) 7 s94Data
def s94States := dagTrace s94Mask s94StockWords 7 s94Data
def s94Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])]
def s94Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s94Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s94MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s94Move0Stages, s94Move0Map, s94Move0Inverse)]
def s94Moves := dagMoves s94MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Autos : DagMovesOK s94Mask s94Goal 64 s94Moves := dagMovesOfCheck (by decide +kernel)
def s94Check := dagCheckNode s94Mask s94Goal s94Chart (dagKnownCloses s94Goal s94Cuts) 97 s94States s94Moves s94Links s94Sample s94Tags
def s94RootAt (token : Nat) : Bool :=
  let s := rootState s94StockWords 7 token
  !dagAllowedRoot s94Witnesses s.2.1 || dagLocal s94Mask s94Goal s94Chart (dagKnownCloses s94Goal s94Cuts) s ||
  dagRef 97 s94States s94Moves s94Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94RootBlock0 : treeBlock 0 64 s94RootAt = true := by decide +kernel
theorem s94Roots : dagCheckRoots s94Mask s94Goal s94Chart (dagKnownCloses s94Goal s94Cuts) s94Witnesses (dagRef 97 s94States s94Moves s94Links 0) s94StockWords 7 = true := s94RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Block0 : treeBlock 0 16 s94Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Block16 : treeBlock 16 16 s94Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Block32 : treeBlock 32 16 s94Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Block48 : treeBlock 48 16 s94Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Block64 : treeBlock 64 16 s94Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Block80 : treeBlock 80 16 s94Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Block96 : treeBlock 96 1 s94Check = true := by decide +kernel
theorem s94Verified : treeBlock 0 97 s94Check = true := (@treeBlock_merge 0 48 49 s94Check (@treeBlock_merge 0 16 32 s94Check s94Block0 (@treeBlock_merge 16 16 16 s94Check s94Block16 s94Block32)) (@treeBlock_merge 48 32 17 s94Check (@treeBlock_merge 48 16 16 s94Check s94Block48 s94Block64) (@treeBlock_merge 80 16 1 s94Check s94Block80 s94Block96)))
theorem s94Blocks : treeBlock 0 97 s94Check = true := s94Verified
theorem s94Known : Known s94Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s84Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Stock : Lower s94Mask s94StockWords s94Goal 8 := by
  apply lowerDag _ _ _ _ s94Autos _ _ _ s94Known _ s94Roots s94Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s94StockWords; decide +kernel
  · decide +kernel
  · simp only [s94Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s95Mask : Nat := 0xffffffff
abbrev s95Goal : Nat := sGoal &&& s95Mask
abbrev s95StockWords : List Nat := projectDAGStock s95Mask sBase [0, 1, 2, 3, 4, 7]
def s95Fact : (Nat × List Nat × Nat × Nat) := (s95Mask, s95StockWords, 8, s95Goal)
def s95Cuts : List (Nat × List Nat × Nat × Nat) := [s84Fact]
def s95Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 17, 26, 28, 5, 5, 5, 5, 5, 5, 3, 9, 10, 12, 22, 24, 3, 3, 3, 3, 3, 3], rfl⟩
def s95Sample : (Nat × Nat) := (0x906830190486428150303802050084c28110b038020b0201c0207060140c0704814201100844141a0502c28050b078301c0181c301a05038180e0a070180d0184c060b0904c120d06070120b, 34)
def s95Witnesses := unpackWitnesses s95StockWords [2564, 526849, 792067, 1057281]
def s95Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xce0ce0cc1ca1ca0ca0ca0ca0ca0c81c80c61c60c41c40c21c20c01c00be1be0be0bc1bc0bc0bc09549409409409409408a58a08a08a08057e17e07e07e07a27a07a07057007006e16e06e06a26a06816806806806806805e55e05e05c15c05c05c05635605605605035005005005005004a34a04a04a04a04a04a040505e002 0x52330456304b63c4931c4793c4593c43624413343e034cec41cdc3d53c38519415093d4f92c4e6414d63d4c6204a336483324632a443264231e4031a3f0413d03d3c0113b00d3a0089b9312992c1c62006314340089bc382c92c1b6200531430008a0c3c2c93c2b0402992c1a6200431428035020082332423634223402093c1c92c1b6311a6200331402008170288b040140281301c1193c109300f3240b0400a034090280692c0563104620033140200838c3937937369333592d3392c32637316332f6312e62b2d6272a6212762026337253332432b213271f31f1e31b1d3151931418037160331502b120270e01f0d01b0c0130800f07009010083903f0003d 12 5 12 7 1 5
def s95Data : (Nat → Nat × Nat) := fun i => decodeNode 7 19 0xc38746614a505d49eba92c74c82e98f5d3103a63c9666ce8c7249993a93c8e654ea4f229933a6248663ce8cd2098d3a04174068f80f5d008ba00d74010e80fc061c8193703266064b408043492c02c6e058cc08043063102c560589c0c9e2b04056c42064b1401aa86200266e04ccc0995816344468088c9c0c9e2031f0263604c540c961a63134c4068c50081b810282e066040ac08141301c2604e064f07c980f3241e03e0406c08098104012068240a048078100903258098c41310023140401008020081e80 i
def s95Tags := dagTraceTags s95Mask 34 (dagTagBases s95StockWords 0x750b9431bcc0734aae8c06df5c72f87bc68af46bce5ddfec87d 0x777b9571f46047488600a65d1c66b061c288846a8e0994a0835 34) 7 s95Data
def s95States := dagTrace s95Mask s95StockWords 7 s95Data
def s95Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])]
def s95Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s95Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s95MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s95Move0Stages, s95Move0Map, s95Move0Inverse)]
def s95Moves := dagMoves s95MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Autos : DagMovesOK s95Mask s95Goal 64 s95Moves := dagMovesOfCheck (by decide +kernel)
def s95Check := dagCheckNode s95Mask s95Goal s95Chart (dagKnownCloses s95Goal s95Cuts) 84 s95States s95Moves s95Links s95Sample s95Tags
def s95RootAt (token : Nat) : Bool :=
  let s := rootState s95StockWords 7 token
  !dagAllowedRoot s95Witnesses s.2.1 || dagLocal s95Mask s95Goal s95Chart (dagKnownCloses s95Goal s95Cuts) s ||
  dagRef 84 s95States s95Moves s95Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95RootBlock0 : treeBlock 0 64 s95RootAt = true := by decide +kernel
theorem s95Roots : dagCheckRoots s95Mask s95Goal s95Chart (dagKnownCloses s95Goal s95Cuts) s95Witnesses (dagRef 84 s95States s95Moves s95Links 0) s95StockWords 7 = true := s95RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Block0 : treeBlock 0 16 s95Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Block16 : treeBlock 16 16 s95Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Block32 : treeBlock 32 16 s95Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Block48 : treeBlock 48 16 s95Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Block64 : treeBlock 64 16 s95Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Block80 : treeBlock 80 4 s95Check = true := by decide +kernel
theorem s95Verified : treeBlock 0 84 s95Check = true := (@treeBlock_merge 0 48 36 s95Check (@treeBlock_merge 0 16 32 s95Check s95Block0 (@treeBlock_merge 16 16 16 s95Check s95Block16 s95Block32)) (@treeBlock_merge 48 16 20 s95Check s95Block48 (@treeBlock_merge 64 16 4 s95Check s95Block64 s95Block80)))
theorem s95Blocks : treeBlock 0 84 s95Check = true := s95Verified
theorem s95Known : Known s95Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s84Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Stock : Lower s95Mask s95StockWords s95Goal 8 := by
  apply lowerDag _ _ _ _ s95Autos _ _ _ s95Known _ s95Roots s95Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s95StockWords; decide +kernel
  · decide +kernel
  · simp only [s95Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s96Mask : Nat := 0xffffffff
abbrev s96Goal : Nat := sGoal &&& s96Mask
abbrev s96StockWords : List Nat := projectDAGStock s96Mask sBase [0, 1, 2, 3, 4, 8]
def s96Fact : (Nat × List Nat × Nat × Nat) := (s96Mask, s96StockWords, 8, s96Goal)
def s96Cuts : List (Nat × List Nat × Nat × Nat) := [s84Fact]
def s96Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 17, 26, 28, 5, 5, 5, 5, 5, 5, 3, 9, 10, 12, 22, 24, 3, 3, 3, 3, 3, 3], rfl⟩
def s96Sample : (Nat × Nat) := (0x12190184c120d0181c2c1c0c0640215018442c0e008340c070081c2805000140c050904c241a060340c0e0c044120b05068301c06038181c0182c281500814281c0c06802110502c140e, 33)
def s96Witnesses := unpackWitnesses s96StockWords [2564, 267785, 792067, 1057281]
def s96Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xe80e80e80e61e60e03e00e00e00e00de1dc1dc0da1d81d80d80d80d61d60d22d20d01d00ce1ce0ce0ce0ce0ce0ce0ce0c83c809f59e09e09e09e09e09459409219208c38c08c08a18818808428408407a57a07a07a07817807617607607607607417407407406676606606606605c55c05c05c05c05c05c05635605605415405405214a44a04a04a04a04a04a04a04a04a040505e002 0x513245fc3c5e33050324593185831c563244f32451930509404f6244d6244b33445034440284301c62c4161c3d60c385d9415c93d5b92c5a636576325562a54626533415233d4e3264c31d4a31949314480414703d4601d42019410082f92c246261c620063143b008393183893037324223183433c21324206243101c2f92c1b620053142e01d020082a63c28340236242492c2263621626206201f3140c01d040081c92c1b620033141a01a0200815040140281301c103180d6241193c0f9300e3240c3180692c056200431a03314020083fc393e9373d9333c92d3a92c36637356333362b32627306212d6202c3372b3332932b273272631f2531b1e31a1d3151931418037170331602b120270b01f0a01b090130800f07009010084003f0003b 12 5 12 7 1 5
def s96Data : (Nat → Nat × Nat) := fun i => decodeNode 7 19 0x1883070f60e1c41c3cbc6617a5060c9ec192c82c6d04c62c98e5863282649598aa0b13413418267b064c28ca04f6249e64d05892698ec13349663304c520820c103d8203b040d218144301c8603304022081f80c390326e064cc0c96810087725804c61cc98373246ec6e058cc099e3462b02c4e040718b108192c5c03ab9880099b8133302c78a8cac09a0283270263e04c6c0c961f62446c6c7d898fb101f3143e63404c540c961a6203403468c50081b81033020560410098141301c2604e064f0618c109301864831890698c0c01f020360404c0807810090325809880118d023140401008020081d80 i
def s96Tags := dagTraceTags s96Mask 33 (dagTagBases s96StockWords 0x31406711d9e032d5cacc0efcd9d7f31dc542c6b517eefeb0e6 0x3dd56795e19132458a4005f85845530d41668e9107e6a010a4 33) 7 s96Data
def s96States := dagTrace s96Mask s96StockWords 7 s96Data
def s96MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s96Moves := dagMoves s96MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Autos : DagMovesOK s96Mask s96Goal 64 s96Moves := dagMovesOfCheck (by decide +kernel)
def s96Check := dagCheckNode s96Mask s96Goal s96Chart (dagKnownCloses s96Goal s96Cuts) 99 s96States s96Moves s96Links s96Sample s96Tags
def s96RootAt (token : Nat) : Bool :=
  let s := rootState s96StockWords 7 token
  !dagAllowedRoot s96Witnesses s.2.1 || dagLocal s96Mask s96Goal s96Chart (dagKnownCloses s96Goal s96Cuts) s ||
  dagRef 99 s96States s96Moves s96Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96RootBlock0 : treeBlock 0 64 s96RootAt = true := by decide +kernel
theorem s96Roots : dagCheckRoots s96Mask s96Goal s96Chart (dagKnownCloses s96Goal s96Cuts) s96Witnesses (dagRef 99 s96States s96Moves s96Links 0) s96StockWords 7 = true := s96RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block0 : treeBlock 0 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block16 : treeBlock 16 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block32 : treeBlock 32 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block48 : treeBlock 48 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block64 : treeBlock 64 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block80 : treeBlock 80 16 s96Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Block96 : treeBlock 96 3 s96Check = true := by decide +kernel
theorem s96Verified : treeBlock 0 99 s96Check = true := (@treeBlock_merge 0 48 51 s96Check (@treeBlock_merge 0 16 32 s96Check s96Block0 (@treeBlock_merge 16 16 16 s96Check s96Block16 s96Block32)) (@treeBlock_merge 48 32 19 s96Check (@treeBlock_merge 48 16 16 s96Check s96Block48 s96Block64) (@treeBlock_merge 80 16 3 s96Check s96Block80 s96Block96)))
theorem s96Blocks : treeBlock 0 99 s96Check = true := s96Verified
theorem s96Known : Known s96Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s84Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Stock : Lower s96Mask s96StockWords s96Goal 8 := by
  apply lowerDag _ _ _ _ s96Autos _ _ _ s96Known _ s96Roots s96Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s96StockWords; decide +kernel
  · decide +kernel
  · simp only [s96Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s97Mask : Nat := 0xffffffff
abbrev s97Goal : Nat := sGoal &&& s97Mask
abbrev s97StockWords : List Nat := projectDAGStock s97Mask sBase [0, 1, 2, 3, 4, 10]
def s97Fact : (Nat × List Nat × Nat × Nat) := (s97Mask, s97StockWords, 8, s97Goal)
def s97Cuts : List (Nat × List Nat × Nat × Nat) := [s84Fact]
def s97Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 17, 26, 28, 5, 5, 5, 5, 5, 5, 3, 9, 10, 12, 22, 24, 3, 3, 3, 3, 3, 3], rfl⟩
def s97Sample : (Nat × Nat) := (0x12190184c120d0181c2c1c0086402150904c02130a04400110603412050181424110301c241a0c0640c0e06014120b05038181c0c068301c0182c281500844281c0603802050502c141a, 33)
def s97Witnesses := unpackWitnesses s97StockWords [2564, 267785, 526849, 792067]
def s97Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xe61e60e03e00e00de1de0dc1dc0dc0dc0dc0dc0da1d81d80d80d80d80d61d60d41d40d21d20ce2ce0ce0ce0ce0ce0ce0ce0c83c809f59e09e09c19c09639609609229209208858808808808618418408407a57a07a07a07a07a07817807807807806a76a06816806616606606606605c55c05c05c05c05a15a05a05815045005005005005004a34a04a04a04a04a04a04a04a040505e002 0x4d32463630623304c3245f33c5d330576245631c5193c4f3284d6244c9404b93045034440284301c619416093d5e9355c9315b92c5a6415963d586355563154620533415233d503354e3314a32649314480414703d4603542031410083e3243d63c3c33c27324266303901c2e92c1c620063143701d360083233c253302e92c246261b620053140200828630279362692c2562524620233141102904008219301f3401c92c1b620033141a02602008153241263016c3c1463c1333c113240d0400c0340b01c0692c056200432603314020083fc393b9373a9333892d3592c34637336333162b306272f6212d6202c3372b3332a32b29327223262031f1e31b1d3151931418037170331002b0f0270e01f0a01b090130800f07009010084003f0002f 12 5 12 7 1 5
def s97Data : (Nat → Nat × Nat) := fun i => decodeNode 7 19 0x630c46618a5060c9ec133cbf26b04cc2ec98c192c82c83058f60b1ac1624ae639598c60b10413418267b064f2899ac13289e663058926ca04b9309664d04c520820c103d8206b040d218144301c8606304022081f80c3902648f98f1e19e3c9370326604071cc968101d6c010da4b00b1b8163302678c98ac0b138162103258b9880099b813330265604c9c0b1828936472588d8951b10233144664c064c1098f813403e63604c540c961a6203404c68c50081b810330387844c90ab1e1133c22c6048c908815810270203e04100581a0b01c160360404c08078100903258098801193023140401008020081780 i
def s97Tags := dagTraceTags s97Mask 33 (dagTagBases s97StockWords 0xc074f11d9fc58771ac10efcd9d0e9b5714606b517effeb0e6 0x3daf4f95e12858350a0185f85842899161641e9107ed1810a4 33) 7 s97Data
def s97States := dagTrace s97Mask s97StockWords 7 s97Data
def s97MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s97Moves := dagMoves s97MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Autos : DagMovesOK s97Mask s97Goal 64 s97Moves := dagMovesOfCheck (by decide +kernel)
def s97Check := dagCheckNode s97Mask s97Goal s97Chart (dagKnownCloses s97Goal s97Cuts) 100 s97States s97Moves s97Links s97Sample s97Tags
def s97RootAt (token : Nat) : Bool :=
  let s := rootState s97StockWords 7 token
  !dagAllowedRoot s97Witnesses s.2.1 || dagLocal s97Mask s97Goal s97Chart (dagKnownCloses s97Goal s97Cuts) s ||
  dagRef 100 s97States s97Moves s97Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97RootBlock0 : treeBlock 0 64 s97RootAt = true := by decide +kernel
theorem s97Roots : dagCheckRoots s97Mask s97Goal s97Chart (dagKnownCloses s97Goal s97Cuts) s97Witnesses (dagRef 100 s97States s97Moves s97Links 0) s97StockWords 7 = true := s97RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Block0 : treeBlock 0 16 s97Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Block16 : treeBlock 16 16 s97Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Block32 : treeBlock 32 16 s97Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Block48 : treeBlock 48 16 s97Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Block64 : treeBlock 64 16 s97Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Block80 : treeBlock 80 16 s97Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Block96 : treeBlock 96 4 s97Check = true := by decide +kernel
theorem s97Verified : treeBlock 0 100 s97Check = true := (@treeBlock_merge 0 48 52 s97Check (@treeBlock_merge 0 16 32 s97Check s97Block0 (@treeBlock_merge 16 16 16 s97Check s97Block16 s97Block32)) (@treeBlock_merge 48 32 20 s97Check (@treeBlock_merge 48 16 16 s97Check s97Block48 s97Block64) (@treeBlock_merge 80 16 4 s97Check s97Block80 s97Block96)))
theorem s97Blocks : treeBlock 0 100 s97Check = true := s97Verified
theorem s97Known : Known s97Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s84Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Stock : Lower s97Mask s97StockWords s97Goal 8 := by
  apply lowerDag _ _ _ _ s97Autos _ _ _ s97Known _ s97Roots s97Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s97StockWords; decide +kernel
  · decide +kernel
  · simp only [s97Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s98Mask : Nat := 0xffff0000ffff
abbrev s98Goal : Nat := sGoal &&& s98Mask
abbrev s98StockWords : List Nat := projectDAGStock s98Mask sBase [0, 1, 2, 3, 5, 6]
def s98Fact : (Nat × List Nat × Nat × Nat) := (s98Mask, s98StockWords, 8, s98Goal)
def s98Cuts : List (Nat × List Nat × Nat × Nat) := [s36Fact, s37Fact, s41Fact, s49Fact, s68Fact, s59Fact, s12Fact, s42Fact, s13Fact, s50Fact, s69Fact, s85Fact]
def s98Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 35, 38, 41, 44, 5, 5, 5, 5, 5, 3, 6, 9, 12, 33, 36, 42, 3, 3, 3, 3, 3], rfl⟩
def s98Sample : (Nat × Nat) := (0x150ac542e008144229048a4422303098180e030380805, 10)
def s98Witnesses := unpackWitnesses s98StockWords [267785, 526849, 792067, 1066499]
def s98Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xa8a8a8937b786360604b484848331402 0xec386c9630c5132587620218a264b0cc4033143c96198804628492c1b1008c5152588620298a04021607e003e 8 3 12 4 1 3
def s98Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0xc38c92cc314c03f092c192c9620192c66206314192c262023142008103e0 i
def s98Tags := dagTraceTags s98Mask 10 (dagTagBases s98StockWords 0x43b78d998fc7af1 0xc3f50c900fc28f0 10) 7 s98Data
def s98States := dagTrace s98Mask s98StockWords 7 s98Data
def s98MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s98Moves := dagMoves s98MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Autos : DagMovesOK s98Mask s98Goal 64 s98Moves := dagMovesOfCheck (by decide +kernel)
def s98Check := dagCheckNode s98Mask s98Goal s98Chart (dagKnownCloses s98Goal s98Cuts) 15 s98States s98Moves s98Links s98Sample s98Tags
def s98RootAt (token : Nat) : Bool :=
  let s := rootState s98StockWords 7 token
  !dagAllowedRoot s98Witnesses s.2.1 || dagLocal s98Mask s98Goal s98Chart (dagKnownCloses s98Goal s98Cuts) s ||
  dagRef 15 s98States s98Moves s98Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98RootBlock0 : treeBlock 0 64 s98RootAt = true := by decide +kernel
theorem s98Roots : dagCheckRoots s98Mask s98Goal s98Chart (dagKnownCloses s98Goal s98Cuts) s98Witnesses (dagRef 15 s98States s98Moves s98Links 0) s98StockWords 7 = true := s98RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Block0 : treeBlock 0 15 s98Check = true := by decide +kernel
theorem s98Blocks : treeBlock 0 15 s98Check = true := s98Block0
theorem s98Known : Known s98Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s85Stock) s69Stock) s50Stock) s13Stock) s42Stock) s12Stock) s59Stock) s68Stock) s49Stock) s41Stock) s37Stock) s36Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Stock : Lower s98Mask s98StockWords s98Goal 8 := by
  apply lowerDag _ _ _ _ s98Autos _ _ _ s98Known _ s98Roots s98Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s98StockWords; decide +kernel
  · decide +kernel
  · simp only [s98Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s99Mask : Nat := 0xffff0000ffff
abbrev s99Goal : Nat := sGoal &&& s99Mask
abbrev s99StockWords : List Nat := projectDAGStock s99Mask sBase [0, 1, 2, 3, 5, 7]
def s99Fact : (Nat × List Nat × Nat × Nat) := (s99Mask, s99StockWords, 8, s99Goal)
def s99Cuts : List (Nat × List Nat × Nat × Nat) := [s30Fact, s31Fact, s43Fact, s51Fact, s60Fact, s77Fact, s44Fact, s4Fact, s52Fact, s61Fact, s5Fact, s78Fact, s7Fact, s8Fact, s85Fact]
def s99Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 35, 38, 41, 44, 5, 5, 5, 5, 5, 3, 6, 9, 12, 33, 36, 42, 3, 3, 3, 3, 3], rfl⟩
def s99Sample : (Nat × Nat) := (0x120980c26048a4482c0182c542e140a40c0700814120b, 10)
def s99Witnesses := unpackWitnesses s99StockWords [2564, 526849, 792067, 1066499]
def s99Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xa0a0927b786360604b484848331402 0x6b103002132587620218a264b0cc4033143c96198804628492c1b1008c5152588620298a04021607e003d 8 3 12 4 1 3
def s99Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x620c008c03f092c192c9620192c66206314192c262023142008103d0 i
def s99Tags := dagTraceTags s99Mask 10 (dagTagBases s99StockWords 0x32bd83e756cd4af 0xb2e58267444d0a3 10) 7 s99Data
def s99States := dagTrace s99Mask s99StockWords 7 s99Data
def s99MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s99Moves := dagMoves s99MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s99Autos : DagMovesOK s99Mask s99Goal 64 s99Moves := dagMovesOfCheck (by decide +kernel)
def s99Check := dagCheckNode s99Mask s99Goal s99Chart (dagKnownCloses s99Goal s99Cuts) 14 s99States s99Moves s99Links s99Sample s99Tags
def s99RootAt (token : Nat) : Bool :=
  let s := rootState s99StockWords 7 token
  !dagAllowedRoot s99Witnesses s.2.1 || dagLocal s99Mask s99Goal s99Chart (dagKnownCloses s99Goal s99Cuts) s ||
  dagRef 14 s99States s99Moves s99Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s99RootBlock0 : treeBlock 0 64 s99RootAt = true := by decide +kernel
theorem s99Roots : dagCheckRoots s99Mask s99Goal s99Chart (dagKnownCloses s99Goal s99Cuts) s99Witnesses (dagRef 14 s99States s99Moves s99Links 0) s99StockWords 7 = true := s99RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s99Block0 : treeBlock 0 14 s99Check = true := by decide +kernel
theorem s99Blocks : treeBlock 0 14 s99Check = true := s99Block0
theorem s99Known : Known s99Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s85Stock) s8Stock) s7Stock) s78Stock) s5Stock) s61Stock) s52Stock) s4Stock) s44Stock) s77Stock) s60Stock) s51Stock) s43Stock) s31Stock) s30Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s99Stock : Lower s99Mask s99StockWords s99Goal 8 := by
  apply lowerDag _ _ _ _ s99Autos _ _ _ s99Known _ s99Roots s99Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s99StockWords; decide +kernel
  · decide +kernel
  · simp only [s99Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s100Mask : Nat := 0xffff0000ffff
abbrev s100Goal : Nat := sGoal &&& s100Mask
abbrev s100StockWords : List Nat := projectDAGStock s100Mask sBase [0, 1, 2, 3, 5, 8]
def s100Fact : (Nat × List Nat × Nat × Nat) := (s100Mask, s100StockWords, 8, s100Goal)
def s100Cuts : List (Nat × List Nat × Nat × Nat) := [s23Fact, s24Fact, s45Fact, s53Fact, s70Fact, s79Fact, s13Fact, s46Fact, s12Fact, s54Fact, s71Fact, s85Fact]
def s100Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 35, 38, 41, 44, 5, 5, 5, 5, 5, 3, 6, 9, 12, 33, 36, 42, 3, 3, 3, 3, 3], rfl⟩
def s100Sample : (Nat × Nat) := (0x150b8542b02014482c060b048260188c120b0182c0205, 10)
def s100Witnesses := unpackWitnesses s100StockWords [2564, 267785, 792067, 1066499]
def s100Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xa8a8a8937b786360604b484848331402 0xec386c9630c5132587620218a264b0cc4033143c96198804628492c1b1008c5152588620298a04021607e003b 8 3 12 4 1 3
def s100Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0xc38c92cc314c03f092c192c9620192c66206314192c262023142008103b0 i
def s100Tags := dagTraceTags s100Mask 10 (dagTagBases s100StockWords 0x43b78d9af1c798f 0xc3f50c90f0c280f 10) 7 s100Data
def s100States := dagTrace s100Mask s100StockWords 7 s100Data
def s100MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s100Moves := dagMoves s100MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s100Autos : DagMovesOK s100Mask s100Goal 64 s100Moves := dagMovesOfCheck (by decide +kernel)
def s100Check := dagCheckNode s100Mask s100Goal s100Chart (dagKnownCloses s100Goal s100Cuts) 15 s100States s100Moves s100Links s100Sample s100Tags
def s100RootAt (token : Nat) : Bool :=
  let s := rootState s100StockWords 7 token
  !dagAllowedRoot s100Witnesses s.2.1 || dagLocal s100Mask s100Goal s100Chart (dagKnownCloses s100Goal s100Cuts) s ||
  dagRef 15 s100States s100Moves s100Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s100RootBlock0 : treeBlock 0 64 s100RootAt = true := by decide +kernel
theorem s100Roots : dagCheckRoots s100Mask s100Goal s100Chart (dagKnownCloses s100Goal s100Cuts) s100Witnesses (dagRef 15 s100States s100Moves s100Links 0) s100StockWords 7 = true := s100RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s100Block0 : treeBlock 0 15 s100Check = true := by decide +kernel
theorem s100Blocks : treeBlock 0 15 s100Check = true := s100Block0
theorem s100Known : Known s100Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s85Stock) s71Stock) s54Stock) s12Stock) s46Stock) s13Stock) s79Stock) s70Stock) s53Stock) s45Stock) s24Stock) s23Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s100Stock : Lower s100Mask s100StockWords s100Goal 8 := by
  apply lowerDag _ _ _ _ s100Autos _ _ _ s100Known _ s100Roots s100Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s100StockWords; decide +kernel
  · decide +kernel
  · simp only [s100Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s101Mask : Nat := 0xffff0000ffff
abbrev s101Goal : Nat := sGoal &&& s101Mask
abbrev s101StockWords : List Nat := projectDAGStock s101Mask sBase [0, 1, 2, 3, 5, 9]
def s101Fact : (Nat × List Nat × Nat × Nat) := (s101Mask, s101StockWords, 8, s101Goal)
def s101Cuts : List (Nat × List Nat × Nat × Nat) := [s19Fact, s20Fact, s47Fact, s62Fact, s72Fact, s80Fact, s48Fact, s0Fact, s63Fact, s73Fact, s1Fact, s81Fact, s7Fact, s8Fact, s85Fact]
def s101Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 35, 38, 41, 44, 5, 5, 5, 5, 5, 3, 6, 9, 12, 33, 36, 42, 3, 3, 3, 3, 3], rfl⟩
def s101Sample : (Nat × Nat) := (0x120b0182c0188c48260482c542e1108c180d00814060b, 10)
def s101Witnesses := unpackWitnesses s101StockWords [2564, 267785, 526849, 1066499]
def s101Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xa0a0927b786360604b484848331402 0x6b103002132587620218a264b0cc4033143c96198804628492c1b1008c5152588620298a04021607e0037 8 3 12 4 1 3
def s101Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x620c008c03f092c192c9620192c66206314192c26202314200810370 i
def s101Tags := dagTraceTags s101Mask 10 (dagTagBases s101StockWords 0x32bd8cd7563e4af 0xb2e584d344264a3 10) 7 s101Data
def s101States := dagTrace s101Mask s101StockWords 7 s101Data
def s101MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s101Moves := dagMoves s101MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s101Autos : DagMovesOK s101Mask s101Goal 64 s101Moves := dagMovesOfCheck (by decide +kernel)
def s101Check := dagCheckNode s101Mask s101Goal s101Chart (dagKnownCloses s101Goal s101Cuts) 14 s101States s101Moves s101Links s101Sample s101Tags
def s101RootAt (token : Nat) : Bool :=
  let s := rootState s101StockWords 7 token
  !dagAllowedRoot s101Witnesses s.2.1 || dagLocal s101Mask s101Goal s101Chart (dagKnownCloses s101Goal s101Cuts) s ||
  dagRef 14 s101States s101Moves s101Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s101RootBlock0 : treeBlock 0 64 s101RootAt = true := by decide +kernel
theorem s101Roots : dagCheckRoots s101Mask s101Goal s101Chart (dagKnownCloses s101Goal s101Cuts) s101Witnesses (dagRef 14 s101States s101Moves s101Links 0) s101StockWords 7 = true := s101RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s101Block0 : treeBlock 0 14 s101Check = true := by decide +kernel
theorem s101Blocks : treeBlock 0 14 s101Check = true := s101Block0
theorem s101Known : Known s101Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s85Stock) s8Stock) s7Stock) s81Stock) s1Stock) s73Stock) s63Stock) s0Stock) s48Stock) s80Stock) s72Stock) s62Stock) s47Stock) s20Stock) s19Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s101Stock : Lower s101Mask s101StockWords s101Goal 8 := by
  apply lowerDag _ _ _ _ s101Autos _ _ _ s101Known _ s101Roots s101Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s101StockWords; decide +kernel
  · decide +kernel
  · simp only [s101Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s102Mask : Nat := 0xffff0000ffff
abbrev s102Goal : Nat := sGoal &&& s102Mask
abbrev s102StockWords : List Nat := projectDAGStock s102Mask sBase [0, 1, 2, 3, 5, 11]
def s102Fact : (Nat × List Nat × Nat × Nat) := (s102Mask, s102StockWords, 8, s102Goal)
def s102Cuts : List (Nat × List Nat × Nat × Nat) := [s16Fact, s17Fact, s55Fact, s64Fact, s74Fact, s82Fact, s56Fact, s65Fact, s75Fact, s0Fact, s83Fact, s1Fact, s4Fact, s5Fact, s85Fact]
def s102Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 35, 38, 41, 44, 5, 5, 5, 5, 5, 3, 6, 9, 12, 33, 36, 42, 3, 3, 3, 3, 3], rfl⟩
def s102Sample : (Nat × Nat) := (0x60b0180e1088c482c0182c542e0502c4825008140623, 10)
def s102Witnesses := unpackWitnesses s102StockWords [2564, 267785, 526849, 792067]
def s102Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xa0a0927b786360604b484848331402 0x6b103002132587620218a264b0cc4033143c96198804628492c1b1008c5152588620298a04021607e002f 8 3 12 4 1 3
def s102Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x620c008c03f092c192c9620192c66206314192c262023142008102f0 i
def s102Tags := dagTraceTags s102Mask 10 (dagTagBases s102StockWords 0x4aad5de3566e4af 0xcacd4c63440e4a3 10) 7 s102Data
def s102States := dagTrace s102Mask s102StockWords 7 s102Data
def s102MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s102Moves := dagMoves s102MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s102Autos : DagMovesOK s102Mask s102Goal 64 s102Moves := dagMovesOfCheck (by decide +kernel)
def s102Check := dagCheckNode s102Mask s102Goal s102Chart (dagKnownCloses s102Goal s102Cuts) 14 s102States s102Moves s102Links s102Sample s102Tags
def s102RootAt (token : Nat) : Bool :=
  let s := rootState s102StockWords 7 token
  !dagAllowedRoot s102Witnesses s.2.1 || dagLocal s102Mask s102Goal s102Chart (dagKnownCloses s102Goal s102Cuts) s ||
  dagRef 14 s102States s102Moves s102Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s102RootBlock0 : treeBlock 0 64 s102RootAt = true := by decide +kernel
theorem s102Roots : dagCheckRoots s102Mask s102Goal s102Chart (dagKnownCloses s102Goal s102Cuts) s102Witnesses (dagRef 14 s102States s102Moves s102Links 0) s102StockWords 7 = true := s102RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s102Block0 : treeBlock 0 14 s102Check = true := by decide +kernel
theorem s102Blocks : treeBlock 0 14 s102Check = true := s102Block0
theorem s102Known : Known s102Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s85Stock) s5Stock) s4Stock) s1Stock) s83Stock) s0Stock) s75Stock) s65Stock) s56Stock) s82Stock) s74Stock) s64Stock) s55Stock) s17Stock) s16Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s102Stock : Lower s102Mask s102StockWords s102Goal 8 := by
  apply lowerDag _ _ _ _ s102Autos _ _ _ s102Known _ s102Roots s102Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s102StockWords; decide +kernel
  · decide +kernel
  · simp only [s102Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s103Mask : Nat := 0xff00ff00ff00ff00
abbrev s103Goal : Nat := sGoal &&& s103Mask
abbrev s103StockWords : List Nat := projectDAGStock s103Mask sBase [0, 1, 2, 4, 5, 6]
def s103Fact : (Nat × List Nat × Nat × Nat) := (s103Mask, s103StockWords, 8, s103Goal)
def s103Cuts : List (Nat × List Nat × Nat × Nat) := [s86Fact]
def s103Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 13, 14, 25, 26, 28, 41, 44, 11, 11, 11, 11, 9, 12, 42, 56, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s103Sample : (Nat × Nat) := (0x703c1c0e410291c068541a04064540e04034100b150b0702c06070180d0482c120d150b8122904864703a06038182c150e8542b0c0703019, 25)
def s103Witnesses := unpackWitnesses s103StockWords [267785, 530953, 799241, 1069577]
def s103Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x1480a405202901442a205102881440a2051028054009e14f027813c09e04f026c73609a0cd02681340971cb825c12a2940ca02501280911c8824032009004802346ef67703b81dc0ee07703b81dc0e267103881bc4de06f03781bc0ce867033819c0cc16413201900c615d32e81740ba05d02e81740b435a02c85640b20561ab01580ac05602819400a004e127013809c04e027011908c0450a1890828023e11f00f427623b01d80e827213901c04d465e62f01704b805c02e0158cac05602a09408a005002801400a004e127010980be002 0xf39307c0287364075040733305d0106f0286e01c6d0106b634690346801c67010656286401c6363061034600285f0105d0345b0345a0285901c7fc417ec3d7dc38f6941f493d7b9357a92c796417863d77620763417433d7233571314700366c0326a02a660266201e5e01a5c0125800e4192c30620083145202a5101250008499344d0344ac3849626456204831d2f314220351f019070084401045934430304001c4192c2e62027329063143f025020083a3403932838010366349034034334330103092c2f6292e620263290531402008253342b03428c38226352762026314250261e01a120120c0081c018229341b0181d0281c3342001c1c634170101d0101c6281501016028163281631c18628170281501c1f9341e3341b3281a040190341401c12034100400f0340e0280b0280c3340a030040280892c076290662005314030250200856c3955937549335392d4f92c4e6374c6334b62b4762946627426213e6203d3373c3333b32b373273531f3231b313152d3142c0372a0332902b24029230272101f1301b110130d00f09009010085703f0003e 13 5 12 7 1 5
def s103Data : (Nat → Nat × Nat) := fun i => decodeNode 7 19 0xc41b187b630e2c0147c935b125961906c31ed8620b068360103a99ed8330e666b60c52c01b58028da039b4043681958634d6055600d3380e67010ce04d618a3200e64630c603d600d2f8145f010be035600d2e80958034b205164072c8075803f01872064dc0c998192d020554004a80045092c02c6e040d26b198162b038712189a418ec862902c4e064d218084403086c42064b1f80e400257ec4004cdc09998132b02680e0ca1c0083832702c68d8c7c099a330106663604c540c962e6295cc40b8c50081b8103456066040ac0e1c256204a62894099281481027032688807c080e209342866850040eb141c32828080500d0a314150282a63858070a80e1401b020684804c08200e0341c0503803c099a0a02816060280240c960262904c4008c501014040250401008020081f00 i
def s103Tags := dagTraceTags s103Mask 25 (dagTagBases s103StockWords 0x269c4f5c0c35cdc1065c1bd8c86a14d8cb1d85 0x3ffe4ffb4c24cd02021800c0c0290418000d80 25) 7 s103Data
def s103States := dagTrace s103Mask s103StockWords 7 s103Data
def s103Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])]
def s103Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s103Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s103MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s103Move0Stages, s103Move0Map, s103Move0Inverse)]
def s103Moves := dagMoves s103MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Autos : DagMovesOK s103Mask s103Goal 64 s103Moves := dagMovesOfCheck (by decide +kernel)
def s103Check := dagCheckNode s103Mask s103Goal s103Chart (dagKnownCloses s103Goal s103Cuts) 128 s103States s103Moves s103Links s103Sample s103Tags
def s103RootAt (token : Nat) : Bool :=
  let s := rootState s103StockWords 7 token
  !dagAllowedRoot s103Witnesses s.2.1 || dagLocal s103Mask s103Goal s103Chart (dagKnownCloses s103Goal s103Cuts) s ||
  dagRef 128 s103States s103Moves s103Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103RootBlock0 : treeBlock 0 64 s103RootAt = true := by decide +kernel
theorem s103Roots : dagCheckRoots s103Mask s103Goal s103Chart (dagKnownCloses s103Goal s103Cuts) s103Witnesses (dagRef 128 s103States s103Moves s103Links 0) s103StockWords 7 = true := s103RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block0 : treeBlock 0 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block16 : treeBlock 16 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block32 : treeBlock 32 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block48 : treeBlock 48 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block64 : treeBlock 64 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block80 : treeBlock 80 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block96 : treeBlock 96 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block112 : treeBlock 112 16 s103Check = true := by decide +kernel
theorem s103Verified : treeBlock 0 128 s103Check = true := (@treeBlock_merge 0 64 64 s103Check (@treeBlock_merge 0 32 32 s103Check (@treeBlock_merge 0 16 16 s103Check s103Block0 s103Block16) (@treeBlock_merge 32 16 16 s103Check s103Block32 s103Block48)) (@treeBlock_merge 64 32 32 s103Check (@treeBlock_merge 64 16 16 s103Check s103Block64 s103Block80) (@treeBlock_merge 96 16 16 s103Check s103Block96 s103Block112)))
theorem s103Blocks : treeBlock 0 128 s103Check = true := s103Verified
theorem s103Known : Known s103Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s86Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Stock : Lower s103Mask s103StockWords s103Goal 8 := by
  apply lowerDag _ _ _ _ s103Autos _ _ _ s103Known _ s103Roots s103Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s103StockWords; decide +kernel
  · decide +kernel
  · simp only [s103Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s104Mask : Nat := 0xff00ff00ff00ff00
abbrev s104Goal : Nat := sGoal &&& s104Mask
abbrev s104StockWords : List Nat := projectDAGStock s104Mask sBase [0, 1, 2, 4, 5, 7]
def s104Fact : (Nat × List Nat × Nat × Nat) := (s104Mask, s104StockWords, 8, s104Goal)
def s104Cuts : List (Nat × List Nat × Nat × Nat) := [s86Fact]
def s104Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 13, 14, 25, 26, 28, 41, 44, 11, 11, 11, 11, 9, 12, 42, 56, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s104Sample : (Nat × Nat) := (0x541a04038140b0402c702c1c0a4540e05038101a0c0e8141a1502c703904864180d0482c703c048a4542e150ac543a060b0180e06070120d0c064703a, 27)
def s104Witnesses := unpackWitnesses s104StockWords [5642, 530953, 799241, 1069577]
def s104Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x1b20d906b8b5c1aa2d40ea03501a80d406813401a00c656303105861c116082fc57c1bd0dc92e416e2b515a06cc3660b20d902c81640a855402a014e1a70528a9414a0a40d2028c33e49f04f827c13e09c1ce027013619914c826413209904c825872c0950ca824c4f597a03c09e00f00770bb05d80ec07603b01c88e406a43501a80d40690b4818ccc41610af897c0bc15e02f01742ba05c0ae01700a885402a01500a4252029014809864c025852829404a025012808e347023051808c0431a1810c084142021010807863c01d84e827403a01d00e807403719b80d826c03601b00cc66603209808b845c02e01684b405812821400a004e127013809c04e027010980be002 0x9e0342f00e20d90138068960344bc9658d8812c628630084461c58a4b134c40623144c81b2600d52a0689401e4180ea4c021220785301c2ac9a23f0f11528081640468201540d0ab2608bc3c4549a1f0d00f264888c3c4031a58b0f0fec68839302ce1e10c0a0a187083932414989f18d502c4a80620b69949fcc50da052610083e49a1e8c70ea020776283ab141e64d0f06687631c3a0081c4cd0e06506f0103619a1b5900d66786703433014194070c606862c3c3099a27f1053b87c9bc3d4961e2430e11d2828c93d44c9aa1e4b2d4c836963d43310214cd90866a7e3343e9991ecca8e664c7231e3718d1a8104d207a6801132006980020b38785e3342d8141540d0ad258556201418a020020b38703a92c13b1001cc50b0054570292a01414c0209f2603992c13310018c50a00644e02a2680410d8d086c604b9302531a1200d0860504393022e1c1124c484c543d6202098e894c508003a050081ec9a0f00c0752643992c12310010c507004a020081b3140d58c23a68031328180080b98d22e6802c334158080a0ca04f2642692c12b14891880066280200811194084cc03a0801c0280d80e0658d02e080160340a80e04d8a024c601000c070140300701c0200c0100818e03c1001a0680b0280401401e4c80d258056290231000cc50040105dc392e49b96a4cca52645192d264961258dc8ec664662b1fb148f989c76c42376201a19b8ccccc646562f3271698f8a8c6c5262a233141001b87c0cc3c0561a0270c00f85006c220260a00f04804804020be07e0003d 13 5 12 8 1 5
def s104Data : (Nat → Nat × Nat) := fun i => decodeNode 8 20 0xc41600349ec3e600349cc3d6062093036930359392c96314960349301e9300893c3c6003c91c3860c3c8f941600408d93d60c3c8a9348a93560c3c8892c606206033660335609327f9317f6257f6207f3147f33460332609347c32a6031c7a93474334746287731c7462875010743266031e603346f3286f0106f31a606406b3346c33c6b0416003d6001160034650286501c6500d6003463c3c61334610086003f003345ec3901937010285b93301c385302a530295392c556205502853008539320192d010324d9304f02a4d0084d92c019304a6344a63701034486330162b01c3840931409304362a4031d4001d4062901627019343c0303c621019323892c3802538620016283663035337013330132b013283001030327016342e31f013342b0102b31b0131501328289322492c246292462024314013282233021037010330102b010401b0281b01c1b027016341901f01040150341501c1501b0162813630120130131c0b0400b0100e0340b0100c0280b00f0100901028089320292c02629026200231402008020080103d00 i
def s104Tags := dagTraceTags s104Mask 27 (dagTagBases s104StockWords 0x303b1706247e180ec89696054f3cfc4e89a0fa86 0x1733f1fc70c5c10c4880600040e28cc0e00002a04 27) 7 s104Data
def s104States := dagTrace s104Mask s104StockWords 7 s104Data
def s104Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s104Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s104Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s104MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s104Move0Stages, s104Move0Map, s104Move0Inverse)]
def s104Moves := dagMoves s104MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Autos : DagMovesOK s104Mask s104Goal 64 s104Moves := dagMovesOfCheck (by decide +kernel)
def s104Check := dagCheckNode s104Mask s104Goal s104Chart (dagKnownCloses s104Goal s104Cuts) 160 s104States s104Moves s104Links s104Sample s104Tags
def s104RootAt (token : Nat) : Bool :=
  let s := rootState s104StockWords 7 token
  !dagAllowedRoot s104Witnesses s.2.1 || dagLocal s104Mask s104Goal s104Chart (dagKnownCloses s104Goal s104Cuts) s ||
  dagRef 160 s104States s104Moves s104Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104RootBlock0 : treeBlock 0 64 s104RootAt = true := by decide +kernel
theorem s104Roots : dagCheckRoots s104Mask s104Goal s104Chart (dagKnownCloses s104Goal s104Cuts) s104Witnesses (dagRef 160 s104States s104Moves s104Links 0) s104StockWords 7 = true := s104RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Block0 : treeBlock 0 16 s104Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Block16 : treeBlock 16 16 s104Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Block32 : treeBlock 32 16 s104Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Block48 : treeBlock 48 16 s104Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Block64 : treeBlock 64 16 s104Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Block80 : treeBlock 80 16 s104Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Block96 : treeBlock 96 16 s104Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Block112 : treeBlock 112 16 s104Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Block128 : treeBlock 128 16 s104Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Block144 : treeBlock 144 16 s104Check = true := by decide +kernel
theorem s104Verified : treeBlock 0 160 s104Check = true := (@treeBlock_merge 0 80 80 s104Check (@treeBlock_merge 0 32 48 s104Check (@treeBlock_merge 0 16 16 s104Check s104Block0 s104Block16) (@treeBlock_merge 32 16 32 s104Check s104Block32 (@treeBlock_merge 48 16 16 s104Check s104Block48 s104Block64))) (@treeBlock_merge 80 32 48 s104Check (@treeBlock_merge 80 16 16 s104Check s104Block80 s104Block96) (@treeBlock_merge 112 16 32 s104Check s104Block112 (@treeBlock_merge 128 16 16 s104Check s104Block128 s104Block144))))
theorem s104Blocks : treeBlock 0 160 s104Check = true := s104Verified
theorem s104Known : Known s104Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s86Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Stock : Lower s104Mask s104StockWords s104Goal 8 := by
  apply lowerDag _ _ _ _ s104Autos _ _ _ s104Known _ s104Roots s104Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s104StockWords; decide +kernel
  · decide +kernel
  · simp only [s104Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s105Mask : Nat := 0xff00ff00ff00ff00
abbrev s105Goal : Nat := sGoal &&& s105Mask
abbrev s105StockWords : List Nat := projectDAGStock s105Mask sBase [0, 1, 2, 4, 5, 8]
def s105Fact : (Nat × List Nat × Nat × Nat) := (s105Mask, s105StockWords, 8, s105Goal)
def s105Cuts : List (Nat × List Nat × Nat × Nat) := [s86Fact]
def s105Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 13, 14, 25, 26, 28, 41, 44, 11, 11, 11, 11, 9, 12, 42, 56, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s105Sample : (Nat × Nat) := (0x703c1c0e4102c04070701a15068100e04034540b150a4702904864120d06038180d150ac182c06070703a0482c1229150e8542e0c064301c, 25)
def s105Witnesses := unpackWitnesses s105StockWords [5642, 267785, 799241, 1069577]
def s105Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x29414a0a5052828c5460a3051828c1460a01d0027c33e09f04f827073809c04d0a6813029804b865c12e09704a0e5012809404a02501242910c8824412208e1c701e2cf007803c01e00f007803c01c8ce407203809c00e007003801a10d0068034019c2ca26503281902bc65e02f01704b805c02e01700a885402985482a024f0a6892c49604a0a409200900470a3051808a14219e18f007803b09c88e407203901c80e026463201900c806403201900bc65e02e09700b805632b01504a805402a0138c9c04e027013809c04e027010980be002 0x16c9303eb141e58a0f06387701c3ab1a1cd8d0e46387101c363201b8100d86606a31c3519a1a0cd0ce6506601030b14180c70bec605d0342e01416c071018827fc3d3f61c5be506db27a7c9353dc961e98d8ecc647462a383131bcd04da67a6b3353498e994c64c8628630413101e978074b403259008214960818800e6285302a2900f144020952684e03425e1c1298988cc40343351898c87cc509203a060082280e11a4d08806041028214960e58a43cc40053142001280802070c683d0341d61c0d18d472c40383261818d090c501c022040081780e0d4c60692682d318178140b98d0640202e634148080bc0405cc5027010140140a0ca0506382a6281481409c070632683063416b140b0d005666826010118140918d0440601d0281049607d8a43cc40033140e0128080202e080160280a80e04d8d218080110340800e038cd0180800b0340501401e4b00cc52056200219480cc500401057c392b49b9564cca925a5092c27b1b9358cc98c564862923b1390d8847ec403e3371e1998eccac6e652363271998f894c6c4262a1b3140d01b8640cc30056140270900f83c06c1a0260900f04004804020b007e0003b 13 5 12 8 1 5
def s105Data : (Nat → Nat × Nat) := fun i => decodeNode 7 19 0x620d9c3db3871658a3ec9ad992cb2c6d658a3b98e7701ceec65658d3ab1559634e2639c40738b1359341b2081b8cf6c9986c335b2669a8c76c99a66328cc02198c66c98a59041b207b658a3018e60630be03b640d2d8145b01cb603364022c81f80c390326e064cc0c968102aa203d440228c960163702069398cc0b1581c3892c4d240764b1481627032691007228184462103259000a20812c06200266e040d1e9998132b03870e1881c193383290264e04c61ac9a3431f02020ca4d1331a260105ec50b98a131a0263344cc509c0a1398e2801c4e02098c6c0b1a220284606088c540c961c62938c40700a0e8129c3140206e040cc0815810402a05054070a813816342603e040d0800e1001b026683804c08200a034140502803c08048192c04c52098801194823140401008020081d80 i
def s105Tags := dagTraceTags s105Mask 25 (dagTagBases s105StockWords 0x133c4f5c0c35cdc1065d9876143a14d883f632 0x3ffe4ff99c24cc820218003600130418003030 25) 7 s105Data
def s105States := dagTrace s105Mask s105StockWords 7 s105Data
def s105Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])]
def s105Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s105Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s105MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s105Move0Stages, s105Move0Map, s105Move0Inverse)]
def s105Moves := dagMoves s105MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Autos : DagMovesOK s105Mask s105Goal 64 s105Moves := dagMovesOfCheck (by decide +kernel)
def s105Check := dagCheckNode s105Mask s105Goal s105Chart (dagKnownCloses s105Goal s105Cuts) 129 s105States s105Moves s105Links s105Sample s105Tags
def s105RootAt (token : Nat) : Bool :=
  let s := rootState s105StockWords 7 token
  !dagAllowedRoot s105Witnesses s.2.1 || dagLocal s105Mask s105Goal s105Chart (dagKnownCloses s105Goal s105Cuts) s ||
  dagRef 129 s105States s105Moves s105Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105RootBlock0 : treeBlock 0 64 s105RootAt = true := by decide +kernel
theorem s105Roots : dagCheckRoots s105Mask s105Goal s105Chart (dagKnownCloses s105Goal s105Cuts) s105Witnesses (dagRef 129 s105States s105Moves s105Links 0) s105StockWords 7 = true := s105RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Block0 : treeBlock 0 16 s105Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Block16 : treeBlock 16 16 s105Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Block32 : treeBlock 32 16 s105Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Block48 : treeBlock 48 16 s105Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Block64 : treeBlock 64 16 s105Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Block80 : treeBlock 80 16 s105Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Block96 : treeBlock 96 16 s105Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Block112 : treeBlock 112 16 s105Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Block128 : treeBlock 128 1 s105Check = true := by decide +kernel
theorem s105Verified : treeBlock 0 129 s105Check = true := (@treeBlock_merge 0 64 65 s105Check (@treeBlock_merge 0 32 32 s105Check (@treeBlock_merge 0 16 16 s105Check s105Block0 s105Block16) (@treeBlock_merge 32 16 16 s105Check s105Block32 s105Block48)) (@treeBlock_merge 64 32 33 s105Check (@treeBlock_merge 64 16 16 s105Check s105Block64 s105Block80) (@treeBlock_merge 96 16 17 s105Check s105Block96 (@treeBlock_merge 112 16 1 s105Check s105Block112 s105Block128))))
theorem s105Blocks : treeBlock 0 129 s105Check = true := s105Verified
theorem s105Known : Known s105Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s86Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Stock : Lower s105Mask s105StockWords s105Goal 8 := by
  apply lowerDag _ _ _ _ s105Autos _ _ _ s105Known _ s105Roots s105Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s105StockWords; decide +kernel
  · decide +kernel
  · simp only [s105Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s106Mask : Nat := 0xff00ff00ff00ff00
abbrev s106Goal : Nat := sGoal &&& s106Mask
abbrev s106StockWords : List Nat := projectDAGStock s106Mask sBase [0, 1, 2, 4, 5, 10]
def s106Fact : (Nat × List Nat × Nat × Nat) := (s106Mask, s106StockWords, 8, s106Goal)
def s106Cuts : List (Nat × List Nat × Nat × Nat) := [s86Fact]
def s106Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 13, 14, 25, 26, 28, 41, 44, 11, 11, 11, 11, 9, 12, 42, 56, 9, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s106Sample : (Nat × Nat) := (0x101c1c068301904064542c150a4540e0c070101a050e8301a1c064542b0482c180d04864182c1c0f07039150b8703a048a4181c06038120d0502c543a, 27)
def s106Witnesses := unpackWitnesses s106StockWords [5642, 267785, 530953, 1069577]
def s106Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x1b00d806b0b581a82d30e9834c1a60d3069833c99e0c5562830c5841c10e0830036cab605b02d816c0b60598ecc1622b00d70ab815c0ac15586a834c4a605286941462a305182883440a10ce927413a09b14d826c13419814c026013009804c025472a0940ca02484f397903b89dc0ee0760ba85d40ea07503a81d40e2471034a1a40d206903405a00c466203085802c006003001800ba35d02e81702b805632a854c4a60520a901480a215102881402a0048424012008e1470238110688044021090808404202100f0c7803b09d04e807403a01d00e806e33701b04d046803211900c806213101804b085802b09580ac05602819400a004e127013809c04e027010980be002 0x2f01a2780711b8809c01c4b01425a4b2c6c40953143180426b0e2c5258706203118a2640d91a06a9801e4b80ea50071260109103c2901a2364c0b38783501c27e1c2364c9192636d629423101e8cd50064a6f3143681498402110c688731c4300e58b0f1092685631c4131e1f0d01018807f0402b00e158cc0fb8787a9403e19a1dcc90f52687831c398081d4ca0e6050776343b19a1d0ca0e402070c3c37c9a1b0c70db8806b33c3381a1980a0ca0386301c3161e1864d13f8829dc3e4de1ea4b0f1218708f9364749aa2e4d1152656a641b4b1ea258a50ac4a83620409a09f8cf4f666a79329389929b8c50d40826903d34014990094c001059c3c2f49a16c070ac0385692c2ab10150c501001059c38204960a18800e6285801e2b80e94c070a40104e6301fc9609d8800c6284f0322680f13002094668499308f320114c708803841028204990fe4b06cc52266200298a0080206a6383d6301a19a0ec0d06a038353301c61c0de4c46cc403432a1998f0acc501e022040081819a434d005c6682d01015b1a0a80c0512642792c1331000cc504a04a020081198e088cc03c0801d0280e00e068cd033260160180b814048040280381201c0b194054100260681101c0799a034100180680b0280400e01e4c80d258056200219480cc50040105dc392e49b96a4cca32645092d25c961218dc8ec664662b21b139098847cc403c3371d1998e4cac64652313271798f8b0c6c5262a243141081b8800cc3e0561b0270c00f84006c1c0260a00f04804804020be07e00037 13 5 12 8 1 5
def s106Data : (Nat → Nat × Nat) := fun i => decodeNode 8 20 0xc416001c9ec3e6001c9cc3d60c38930369301e9301d9392c953149501c9300893c3c6003c91c386093660935609328c9318c9346093260629606348631c8601c8662560934846206063c8234160c407f0407f33d60c3c7c3347c335609347a3296031c7863472334723287532872028730107232560c3c6f9346f31460c406b31c6c33c6b0416003d6002960034650286501c650256001c63c3c61934610086003f009345ec39019370101c5b93301c385201e5201d5292c54620543145401c52008529320192d010324c6304e01e4c0084c92c013344a93049637016330162b0131c4401c446270162101028419323f92c3f620016303d337010343b3330132b01c383393133620333303532a3331e3332901327013343031f013342d0102d31b016342a0302a315019322592c2562025025253140131c2333022037010330102b010401c0281c01c1c027013341a9301901f0102817328110401101c140341101c1201c1101b013340f013010400b0340b0280b00f010090101c089320292c02620023290231402008020080103700 i
def s106Tags := dagTraceTags s106Mask 27 (dagTagBases s106StockWords 0x383a5706247e1f1f16a31605a710bb0659a0f926 0x27b3e5fa70c3c1613068000050603920418002824 27) 7 s106Data
def s106States := dagTrace s106Mask s106StockWords 7 s106Data
def s106Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s106Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s106Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s106MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s106Move0Stages, s106Move0Map, s106Move0Inverse)]
def s106Moves := dagMoves s106MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Autos : DagMovesOK s106Mask s106Goal 64 s106Moves := dagMovesOfCheck (by decide +kernel)
def s106Check := dagCheckNode s106Mask s106Goal s106Chart (dagKnownCloses s106Goal s106Cuts) 160 s106States s106Moves s106Links s106Sample s106Tags
def s106RootAt (token : Nat) : Bool :=
  let s := rootState s106StockWords 7 token
  !dagAllowedRoot s106Witnesses s.2.1 || dagLocal s106Mask s106Goal s106Chart (dagKnownCloses s106Goal s106Cuts) s ||
  dagRef 160 s106States s106Moves s106Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106RootBlock0 : treeBlock 0 64 s106RootAt = true := by decide +kernel
theorem s106Roots : dagCheckRoots s106Mask s106Goal s106Chart (dagKnownCloses s106Goal s106Cuts) s106Witnesses (dagRef 160 s106States s106Moves s106Links 0) s106StockWords 7 = true := s106RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Block0 : treeBlock 0 16 s106Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Block16 : treeBlock 16 16 s106Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Block32 : treeBlock 32 16 s106Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Block48 : treeBlock 48 16 s106Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Block64 : treeBlock 64 16 s106Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Block80 : treeBlock 80 16 s106Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Block96 : treeBlock 96 16 s106Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Block112 : treeBlock 112 16 s106Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Block128 : treeBlock 128 16 s106Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Block144 : treeBlock 144 16 s106Check = true := by decide +kernel
theorem s106Verified : treeBlock 0 160 s106Check = true := (@treeBlock_merge 0 80 80 s106Check (@treeBlock_merge 0 32 48 s106Check (@treeBlock_merge 0 16 16 s106Check s106Block0 s106Block16) (@treeBlock_merge 32 16 32 s106Check s106Block32 (@treeBlock_merge 48 16 16 s106Check s106Block48 s106Block64))) (@treeBlock_merge 80 32 48 s106Check (@treeBlock_merge 80 16 16 s106Check s106Block80 s106Block96) (@treeBlock_merge 112 16 32 s106Check s106Block112 (@treeBlock_merge 128 16 16 s106Check s106Block128 s106Block144))))
theorem s106Blocks : treeBlock 0 160 s106Check = true := s106Verified
theorem s106Known : Known s106Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s86Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Stock : Lower s106Mask s106StockWords s106Goal 8 := by
  apply lowerDag _ _ _ _ s106Autos _ _ _ s106Known _ s106Roots s106Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s106StockWords; decide +kernel
  · decide +kernel
  · simp only [s106Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s107Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev s107Goal : Nat := sGoal &&& s107Mask
abbrev s107StockWords : List Nat := projectDAGStock s107Mask sBase [0, 1, 3, 4, 5, 7]
def s107Fact : (Nat × List Nat × Nat × Nat) := (s107Mask, s107StockWords, 8, s107Goal)
def s107Cuts : List (Nat × List Nat × Nat × Nat) := [s34Fact, s57Fact, s14Fact, s60Fact, s66Fact, s58Fact, s67Fact, s9Fact, s10Fact, s87Fact]
def s107Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 17, 26, 35, 41, 50, 11, 11, 11, 11, 11, 11, 3, 9, 18, 33, 42, 56, 3, 3, 3, 3, 3, 3], rfl⟩
def s107Sample : (Nat × Nat) := (0x184c02131084412110188c241a108a44223150e8542b090c812290182c021108044301a, 16)
def s107Witnesses := unpackWitnesses s107StockWords [5642, 529923, 795137, 1066499]
def s107Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xa8a8a8a88c7370706260604b48483a1502 0xf9417496340358010892c33100cc51125856203496158804628392c118a2a4b12c6e7620218a04021607e003d 8 3 12 4 1 3
def s107Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x941c92cc00dc008c03f092c1637192c8620192c56205314192c23142008103d0 i
def s107Tags := dagTraceTags s107Mask 16 (dagTagBases s107StockWords 0x32160bf0f4a706d9cde9fb5e 0x731723c0042310d18ce8fb1c 16) 7 s107Data
def s107States := dagTrace s107Mask s107StockWords 7 s107Data
def s107MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s107Moves := dagMoves s107MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Autos : DagMovesOK s107Mask s107Goal 64 s107Moves := dagMovesOfCheck (by decide +kernel)
def s107Check := dagCheckNode s107Mask s107Goal s107Chart (dagKnownCloses s107Goal s107Cuts) 16 s107States s107Moves s107Links s107Sample s107Tags
def s107RootAt (token : Nat) : Bool :=
  let s := rootState s107StockWords 7 token
  !dagAllowedRoot s107Witnesses s.2.1 || dagLocal s107Mask s107Goal s107Chart (dagKnownCloses s107Goal s107Cuts) s ||
  dagRef 16 s107States s107Moves s107Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107RootBlock0 : treeBlock 0 64 s107RootAt = true := by decide +kernel
theorem s107Roots : dagCheckRoots s107Mask s107Goal s107Chart (dagKnownCloses s107Goal s107Cuts) s107Witnesses (dagRef 16 s107States s107Moves s107Links 0) s107StockWords 7 = true := s107RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Block0 : treeBlock 0 16 s107Check = true := by decide +kernel
theorem s107Blocks : treeBlock 0 16 s107Check = true := s107Block0
theorem s107Known : Known s107Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s87Stock) s10Stock) s9Stock) s67Stock) s58Stock) s66Stock) s60Stock) s14Stock) s57Stock) s34Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Stock : Lower s107Mask s107StockWords s107Goal 8 := by
  apply lowerDag _ _ _ _ s107Autos _ _ _ s107Known _ s107Roots s107Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s107StockWords; decide +kernel
  · decide +kernel
  · simp only [s107Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s108Mask : Nat := 0xffffffffffffffff
abbrev s108Goal : Nat := sGoal &&& s108Mask
abbrev s108StockWords : List Nat := projectDAGStock s108Mask sBase [0, 1, 2, 3, 4, 5]
def s108Cuts : List (Nat × List Nat × Nat × Nat) := [s87Fact, s88Fact, s85Fact, s86Fact, s33Fact, s84Fact, s90Fact, s15Fact, s13Fact, s89Fact, s91Fact, s99Fact, s29Fact, s107Fact, s8Fact, s19Fact, s4Fact, s95Fact, s101Fact, s102Fact, s10Fact, s39Fact, s100Fact, s104Fact, s18Fact, s97Fact, s98Fact, s94Fact, s103Fact, s92Fact, s34Fact, s106Fact, s96Fact, s12Fact, s24Fact, s93Fact, s105Fact, s5Fact, s2Fact, s9Fact, s25Fact, s37Fact, s28Fact, s23Fact, s40Fact, s27Fact, s30Fact, s36Fact, s35Fact]
def s108Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 11, 14, 17, 26, 28, 35, 38, 41, 44, 50, 5, 3, 9, 12, 22, 33, 42, 52, 56, 3, 3, 3, 3], rfl⟩
def s108Sample : (Nat × Nat) := (0x60321c0a444260b098140b108145432140b050291a0980c260b0680c0e01814543a1c0c8140e12014201101844301a150685429120982c1c0a01448250182c68321c06812191c0b0301c0188c4225120b00613060b0683109068243205068180e048347039150b8703a0a0704223108c4180d150ac120b110c8703c0b07812291a0d806070b05c181c108a42c36, 63)
def s108Witnesses := unpackWitnesses s108StockWords [2564, 267785, 526849, 792067, 1057281, 1328643]
def s108Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x7e1be09e46ec37603a85d40d6a6913481986cc0650af99744ba05a1ad01604b00580289d440a205102881440a204752289102880430a1810c086043021810447663a09c84e407013801b84dc06e03701b80d446a03311980cc06413201884c4046e23011808c046023011808c044122011008804401758b805c02e01700990064001 0x7062b26195890c7d24c6a4a01f37315920cac4463e6c62b23195880c7c6c03a92c4e4849ea28d3cd46828433540193998c7484082580351a00e878c7c146288a6372b01b8c807c6003a8693d35320a118d4380822e01f090089f8d60f46807e6372a01b8b007cf4c6a52035404a19f0d30f06847632a280218a80ace802271250377a21b30e0d5284689323332117813c2c0521001104004038c740c628043142f18f950d60a46805a93d213209618d4ac69e1c341281938f30e06cc803ac382249e0f49407587036c4e1819a8c1900586b04d250257a7923d108d87042942204998fa4c87125834642191a78b8d0c5466616329141938624c04a4a022f441061c07a4b038c841a6320b315051880246841032a0718a0298801063e063150218a273d113588698c384b49625190d1cc6e8c620441a1a08cdce464e6431f3118a980c50b80864e0371300f83004c040100003f 13 5 13 7 1 5
def s108Data : (Nat → Nat × Nat) := fun i => decodeNode 7 20 0x7a2016218161c0149601321816274849ec831b813100131bc51a18149ec231ac219b814a1ba31bbf1a63a31abd1a13a1953a008ba19381928337a23361c334a133499333213318f8118a8118a0118faf0218149ea831aa81a7a81ac291a029193a801b81928147a7947a21461c1449e224a11449994499149281d61c1d496146271b321141a794320181a1941ac16199941939400f81928077a20761c074960732107319074980c31507310071a1071950718a07009813100218f8218a8218a020040101f80 i
def s108Tags := dagTraceTags s108Mask 63 (dagTagBases s108StockWords 0x3cf8c0ca5da3b5b1c1099e4745e5a3ad499a8e97957f3b8c6ad983c3686a46f6e9ee3471279a75ca6423939350c7c5a 0x39f0d1cb4c83b59168289466c1c581a94b838e07847e3a8820f083d02c4242b4e8fa5a41271054c8202080934086452 63) 10 s108Data
def s108States := dagTrace s108Mask s108StockWords 10 s108Data
def s108MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s108Moves := dagMoves s108MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s108Autos : DagMovesOK s108Mask s108Goal 64 s108Moves := dagMovesOfCheck (by decide +kernel)
def s108Check := dagCheckNode s108Mask s108Goal s108Chart (dagKnownCloses s108Goal s108Cuts) 79 s108States s108Moves s108Links s108Sample s108Tags
def s108RootAt (token : Nat) : Bool :=
  let s := rootState s108StockWords 10 token
  !dagAllowedRoot s108Witnesses s.2.1 || dagLocal s108Mask s108Goal s108Chart (dagKnownCloses s108Goal s108Cuts) s ||
  dagRef 79 s108States s108Moves s108Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s108RootBlock0 : treeBlock 0 64 s108RootAt = true := by decide +kernel
theorem s108Roots : dagCheckRoots s108Mask s108Goal s108Chart (dagKnownCloses s108Goal s108Cuts) s108Witnesses (dagRef 79 s108States s108Moves s108Links 0) s108StockWords 10 = true := s108RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s108Block0 : treeBlock 0 16 s108Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s108Block16 : treeBlock 16 16 s108Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s108Block32 : treeBlock 32 16 s108Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s108Block48 : treeBlock 48 16 s108Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s108Block64 : treeBlock 64 15 s108Check = true := by decide +kernel
theorem s108Verified : treeBlock 0 79 s108Check = true := (@treeBlock_merge 0 32 47 s108Check (@treeBlock_merge 0 16 16 s108Check s108Block0 s108Block16) (@treeBlock_merge 32 16 31 s108Check s108Block32 (@treeBlock_merge 48 16 15 s108Check s108Block48 s108Block64)))
theorem s108Blocks : treeBlock 0 79 s108Check = true := s108Verified
theorem s108Known : Known s108Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s35Stock) s36Stock) s30Stock) s27Stock) s40Stock) s23Stock) s28Stock) s37Stock) s25Stock) s9Stock) s2Stock) s5Stock) s105Stock) s93Stock) s24Stock) s12Stock) s96Stock) s106Stock) s34Stock) s92Stock) s103Stock) s94Stock) s98Stock) s97Stock) s18Stock) s104Stock) s100Stock) s39Stock) s10Stock) s102Stock) s101Stock) s95Stock) s4Stock) s19Stock) s8Stock) s107Stock) s29Stock) s99Stock) s91Stock) s89Stock) s13Stock) s15Stock) s90Stock) s84Stock) s33Stock) s86Stock) s85Stock) s88Stock) s87Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s108Stock : Lower s108Mask s108StockWords s108Goal 11 := by
  apply lowerDag _ _ _ _ s108Autos _ _ _ s108Known _ s108Roots s108Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s108StockWords; decide +kernel
  · decide +kernel
  · simp only [s108Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
end PEqualNP.Outside.L_meta_46566

open PEqualNP.Outside.L_meta_46566 in
theorem PEqualNP.Outside.L_meta_46566 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4272613536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4272613536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro t h
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
  let goal : BitVec 64 := 0xfeeefae8feaae8a0
  have root : Lower (fullMask 64) (raw.map BitVec.toNat) goal.toNat 11 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s108Stock
  have size : 11 ≤ t :=
    hcsLower (n := 6) raw goal 11 _ (by decide +kernel) (by decide +kernel) root t h
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [9, 13]⟩, ⟨.and, [6, 14]⟩, ⟨.or, [11, 15]⟩], 16⟩
  refine ⟨circuit, ?_, ?_, by decide +kernel⟩
  · intro gate member
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : circuit.size ≤ 11) size
