import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_28348

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

def hcsBitsNat : {k : Nat} → (Fin k → Bool) → Nat
  | 0, _ => 0
  | k + 1, x => (if x 0 then 1 else 0) + 2 * hcsBitsNat (fun i : Fin k => x i.succ)

theorem hcsBitsNat_lt : ∀ {k : Nat} (x : Fin k → Bool), hcsBitsNat x < 2 ^ k
  | 0, _ => by simp [hcsBitsNat]
  | k + 1, x => by
    have ih := hcsBitsNat_lt (fun i : Fin k => x i.succ)
    simp only [hcsBitsNat, Nat.pow_succ]
    cases x 0
    · simp; omega
    · simp; omega

theorem hcsBitsNat_testBit : ∀ {k : Nat} (x : Fin k → Bool) (i : Fin k),
    (hcsBitsNat x).testBit i.val = x i
  | 0, _, i => Fin.elim0 i
  | k + 1, x, i => by
    refine Fin.cases ?_ ?_ i
    · simp only [hcsBitsNat, Fin.val_zero]
      cases x 0
      · simp [Nat.testBit_zero]
      · have hmod : (1 + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) % 2 = 1 := by omega
        simp [Nat.testBit_zero, hmod]
    · intro j
      have ih := hcsBitsNat_testBit (fun m : Fin k => x m.succ) j
      have hdiv : ((if x 0 then 1 else 0) + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) / 2 =
          hcsBitsNat (fun m : Fin k => x m.succ) := by
        cases x 0
        · simp
        · simp; omega
      simpa only [hcsBitsNat, Fin.val_succ, Nat.testBit_succ, hdiv] using ih

theorem hcsWitnessEval {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (hEval : (C.gates.foldl hcsStep raw).getD C.output 0 = goal) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  let r := hcsBitsNat x
  have hr : r < 2 ^ n := hcsBitsNat_lt x
  have hx : x = fun j : Fin n => r.testBit j.val := by
    funext j
    exact (hcsBitsNat_testBit x j).symm
  rw [hx]
  have hbank : raw.map (fun v => v.getLsbD r) = List.ofFn fun j : Fin n => r.testBit j.val :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
  have hfg : goal.getLsbD r = f (fun j : Fin n => r.testBit j.val) :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
  have hbits := hcsFoldBits raw ⟨r, hr⟩ C.gates hfan
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn fun j : Fin n => r.testBit j.val)).getD C.output false =
      f (fun j : Fin n => r.testBit j.val)
  rw [← hbank, ← hbits, ← hcsGetDBit, hEval, hfg]


def moveStage0 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0x3333333333333333333333333333333333333333333333333333333333333333, 2)], [(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 2)])
def moveStage1 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])
def moveStage2 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])
def moveStage3 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0x9999999999999999999999999999999999999999999999999999999999999999, 0), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x4444444444444444444444444444444444444444444444444444444444444444, 1)])
def moveStage4 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffffffffffff0000000000000000ffffffffffffffff, 64)], [(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 64)])
def moveStage5 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff, 0), (0xffffffff00000000ffffffff00000000, 96)], [(0xffffffff00000000ffffffff00000000000000000000000000000000, 96)])
def moveStage6 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])
def moveStage7 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff, 0), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 24)])
def moveStage8 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff, 0), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000, 16)])
def moveStage9 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55, 0), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x5500550055005500550055005500550055005500550055005500550055005500, 7)])
def moveStage10 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)])
def moveStage11 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])
def moveStage12 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])
def moveStage13 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])
def moveStage14 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333, 0), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x3333000033330000333300003333000033330000333300003333000033330000, 14)])
def moveStage15 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8)], [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8)])
def moveStage16 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555, 0), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x5555555500000000555555550000000055555555000000005555555500000000, 31)])
def moveStage17 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcccccccccccccccc3333333333333333cccccccccccccccc3333333333333333, 0), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0x3333333333333333000000000000000033333333333333330000000000000000, 62)])
def moveStage18 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0ff0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f, 0), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60)], [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000, 60)])
def moveStage19 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff00ff00ff0000ff00ff00ff00ffff00ff00ff00ff0000ff00ff00ff00ff, 0), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000, 56)])
def moveStage20 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff, 0), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000, 48)])
def moveStage21 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555, 0), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0x5555000055550000555500005555000055550000555500005555000055550000, 15)])
def moveStage22 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0f, 0), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 28)])
def moveStage23 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 4)], [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 4)])
def moveStage24 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaaaaaaaaaaaaaaaa5555555555555555aaaaaaaaaaaaaaaa5555555555555555, 0), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0x5555555555555555000000000000000055555555555555550000000000000000, 63)])
def moveStage25 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcccccccccccccccccccccccccccccccc33333333333333333333333333333333, 0), (0xcccccccccccccccccccccccccccccccc, 126)], [(0x3333333333333333333333333333333300000000000000000000000000000000, 126)])
def moveStage26 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124)], [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000, 124)])
def moveStage27 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff, 0), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000, 120)])
def moveStage28 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff0000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff, 0), (0xffff0000ffff0000ffff0000ffff0000, 112)], [(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000, 112)])
def moveStage29 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)])
def moveStage30 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 32)], [(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 32)])
def moveStage31 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x5050505050505050505050505050505050505050505050505050505050505050, 3)])
def moveStage32 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 16)], [(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 16)])
def moveStage33 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffffffffffffffffffffffffffff, 128)], [(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000, 128)])
def moveStage34 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa55555555555555555555555555555555, 0), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0x5555555555555555555555555555555500000000000000000000000000000000, 127)])
def moveStages : Array (List (Nat × Nat) × List (Nat × Nat)) := #[moveStage0, moveStage1, moveStage2, moveStage3, moveStage4, moveStage5, moveStage6, moveStage7, moveStage8, moveStage9, moveStage10, moveStage11, moveStage12, moveStage13, moveStage14, moveStage15, moveStage16, moveStage17, moveStage18, moveStage19, moveStage20, moveStage21, moveStage22, moveStage23, moveStage24, moveStage25, moveStage26, moveStage27, moveStage28, moveStage29, moveStage30, moveStage31, moveStage32, moveStage33, moveStage34]
def sBase : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def sGoal : Nat := 0xffffffffffffffeeffffffffffffffeefffffffeffffffeefffefffaeeeeaa00
def s0Mask : Nat := 0x30300000303
abbrev s0Goal : Nat := sGoal &&& s0Mask
abbrev s0StockWords : List Nat := projectDAGStock s0Mask sBase [0, 3, 5]
def s0Fact : (Nat × List Nat × Nat × Nat) := (s0Mask, s0StockWords, 4, s0Goal)
def s0Cuts : List (Nat × List Nat × Nat × Nat) := []
def s0Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 33, 40, 9, 9, 9, 9, 9, 9, 9, 9, 9, 1, 8, 32, 1, 1, 1, 1, 1, 1, 1, 1, 1], rfl⟩
def s0Sample : (Nat × Nat) := (0x100a01028100840221040240209, 6)
def s0Witnesses := unpackWitnesses s0StockWords [16928, 282656, 544776]
def s0Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x1 0x7 2 1 3 1 1 1
def s0Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s0Tags := dagTraceTags s0Mask 6 (dagTagBases s0StockWords 0x3cccf 0x28485 6) 3 s0Data
def s0States := dagTrace s0Mask s0StockWords 3 s0Data
def s0MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := []
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 256 s0Moves := dagMovesOfCheck (by decide +kernel)
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
def s1Mask : Nat := 0xc0c00000c0c
abbrev s1Goal : Nat := sGoal &&& s1Mask
abbrev s1StockWords : List Nat := projectDAGStock s1Mask sBase [0, 3, 5]
def s1Fact : (Nat × List Nat × Nat × Nat) := (s1Mask, s1StockWords, 4, s1Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Stock : Lower s1Mask s1StockWords s1Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [0]) s0Stock (by decide +kernel)
def s2Mask : Nat := 0x3030000000000000303
abbrev s2Goal : Nat := sGoal &&& s2Mask
abbrev s2StockWords : List Nat := projectDAGStock s2Mask sBase [0, 3, 6]
def s2Fact : (Nat × List Nat × Nat × Nat) := (s2Mask, s2StockWords, 4, s2Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Stock : Lower s2Mask s2StockWords s2Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [1]) s0Stock (by decide +kernel)
def s3Mask : Nat := 0x300030000000000030003
abbrev s3Goal : Nat := sGoal &&& s3Mask
abbrev s3StockWords : List Nat := projectDAGStock s3Mask sBase [0, 4, 6]
def s3Fact : (Nat × List Nat × Nat × Nat) := (s3Mask, s3StockWords, 4, s3Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Stock : Lower s3Mask s3StockWords s3Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [2, 1]) s0Stock (by decide +kernel)
def s4Mask : Nat := 0x500050000000000050005
abbrev s4Goal : Nat := sGoal &&& s4Mask
abbrev s4StockWords : List Nat := projectDAGStock s4Mask sBase [1, 4, 6]
def s4Fact : (Nat × List Nat × Nat × Nat) := (s4Mask, s4StockWords, 4, s4Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Stock : Lower s4Mask s4StockWords s4Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 2, 1]) s0Stock (by decide +kernel)
def s5Mask : Nat := 0x50005000000000005000500000000
abbrev s5Goal : Nat := sGoal &&& s5Mask
abbrev s5StockWords : List Nat := projectDAGStock s5Mask sBase [1, 4, 6]
def s5Fact : (Nat × List Nat × Nat × Nat) := (s5Mask, s5StockWords, 4, s5Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Stock : Lower s5Mask s5StockWords s5Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 2, 1, 4]) s0Stock (by decide +kernel)
def s6Mask : Nat := 0x30300000000000000000000000000000303
abbrev s6Goal : Nat := sGoal &&& s6Mask
abbrev s6StockWords : List Nat := projectDAGStock s6Mask sBase [0, 3, 7]
def s6Fact : (Nat × List Nat × Nat × Nat) := (s6Mask, s6StockWords, 4, s6Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Stock : Lower s6Mask s6StockWords s6Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [5, 6]) s0Stock (by decide +kernel)
def s7Mask : Nat := 0x5000500000000000000000000000000050005
abbrev s7Goal : Nat := sGoal &&& s7Mask
abbrev s7StockWords : List Nat := projectDAGStock s7Mask sBase [1, 4, 7]
def s7Fact : (Nat × List Nat × Nat × Nat) := (s7Mask, s7StockWords, 4, s7Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Stock : Lower s7Mask s7StockWords s7Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 2, 5, 6]) s0Stock (by decide +kernel)
def s8Mask : Nat := 0x30000000300000000000000000000000300000003
abbrev s8Goal : Nat := sGoal &&& s8Mask
abbrev s8StockWords : List Nat := projectDAGStock s8Mask sBase [0, 5, 7]
def s8Fact : (Nat × List Nat × Nat × Nat) := (s8Mask, s8StockWords, 4, s8Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Stock : Lower s8Mask s8StockWords s8Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [7, 8, 5, 6]) s0Stock (by decide +kernel)
def s9Mask : Nat := 0x1010000010100000000000000000000010100000101
abbrev s9Goal : Nat := sGoal &&& s9Mask
abbrev s9StockWords : List Nat := projectDAGStock s9Mask sBase [3, 5, 7]
def s9Fact : (Nat × List Nat × Nat × Nat) := (s9Mask, s9StockWords, 4, s9Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Stock : Lower s9Mask s9StockWords s9Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [9, 10, 11, 7, 8, 5, 6]) s0Stock (by decide +kernel)
def s10Mask : Nat := 0x333300003333
abbrev s10Goal : Nat := sGoal &&& s10Mask
abbrev s10StockWords : List Nat := projectDAGStock s10Mask sBase [0, 2, 3, 5]
def s10Witnesses := unpackWitnesses s10StockWords [16928, 544800, 808972, 280608]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Stock : Lower s10Mask s10StockWords s10Goal 5 := by
  apply essentialLift (witnesses := s10Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s11Mask : Nat := 0x303030303030303
abbrev s11Goal : Nat := sGoal &&& s11Mask
abbrev s11StockWords : List Nat := projectDAGStock s11Mask sBase [0, 3, 4, 5]
def s11Fact : (Nat × List Nat × Nat × Nat) := (s11Mask, s11StockWords, 5, s11Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Stock : Lower s11Mask s11StockWords s11Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [9, 12, 7]) s10Stock (by decide +kernel)
def s12Mask : Nat := 0xc0c0c0c0c0c0c0c
abbrev s12Goal : Nat := sGoal &&& s12Mask
abbrev s12StockWords : List Nat := projectDAGStock s12Mask sBase [0, 3, 4, 5]
def s12Fact : (Nat × List Nat × Nat × Nat) := (s12Mask, s12StockWords, 5, s12Goal)
def s12Witnesses := unpackWitnesses s12StockWords [17954, 283682, 549922, 807946]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Stock : Lower s12Mask s12StockWords s12Goal 5 := by
  apply essentialLift (witnesses := s12Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
def s13Mask : Nat := 0xf0f0000000000000f0f
abbrev s13Goal : Nat := sGoal &&& s13Mask
abbrev s13StockWords : List Nat := projectDAGStock s13Mask sBase [0, 1, 3, 6]
def s13Fact : (Nat × List Nat × Nat × Nat) := (s13Mask, s13StockWords, 5, s13Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Stock : Lower s13Mask s13StockWords s13Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [13, 1]) s10Stock (by decide +kernel)
def s14Mask : Nat := 0xf000f00000000000f000f
abbrev s14Goal : Nat := sGoal &&& s14Mask
abbrev s14StockWords : List Nat := projectDAGStock s14Mask sBase [0, 1, 4, 6]
def s14Fact : (Nat × List Nat × Nat × Nat) := (s14Mask, s14StockWords, 5, s14Goal)
def s14Witnesses := unpackWitnesses s14StockWords [33344, 565312, 296000, 827408]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Stock : Lower s14Mask s14StockWords s14Goal 5 := by
  apply essentialLift (witnesses := s14Witnesses) (cut := s4Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s4StockWords) (by decide +kernel)
  · exact s4Stock
  · decide +kernel
def s15Mask : Nat := 0x30303030000000003030303
abbrev s15Goal : Nat := sGoal &&& s15Mask
abbrev s15StockWords : List Nat := projectDAGStock s15Mask sBase [0, 3, 4, 6]
def s15Fact : (Nat × List Nat × Nat × Nat) := (s15Mask, s15StockWords, 5, s15Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Stock : Lower s15Mask s15StockWords s15Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [9, 14, 12, 2]) s14Stock (by decide +kernel)
def s16Mask : Nat := 0x50505050000000005050505
abbrev s16Goal : Nat := sGoal &&& s16Mask
abbrev s16StockWords : List Nat := projectDAGStock s16Mask sBase [1, 3, 4, 6]
def s16Fact : (Nat × List Nat × Nat × Nat) := (s16Mask, s16StockWords, 5, s16Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Stock : Lower s16Mask s16StockWords s16Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 11, 2, 1]) s10Stock (by decide +kernel)
def s17Mask : Nat := 0x303030300000000030303030
abbrev s17Goal : Nat := sGoal &&& s17Mask
abbrev s17StockWords : List Nat := projectDAGStock s17Mask sBase [0, 3, 4, 6]
def s17Fact : (Nat × List Nat × Nat × Nat) := (s17Mask, s17StockWords, 5, s17Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Stock : Lower s17Mask s17StockWords s17Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [9, 14, 12, 2, 15]) s14Stock (by decide +kernel)
def s18Mask : Nat := 0x303000003030000030300000303
abbrev s18Goal : Nat := sGoal &&& s18Mask
abbrev s18StockWords : List Nat := projectDAGStock s18Mask sBase [0, 3, 5, 6]
def s18Fact : (Nat × List Nat × Nat × Nat) := (s18Mask, s18StockWords, 5, s18Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Stock : Lower s18Mask s18StockWords s18Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [16, 17, 18, 19, 8]) s14Stock (by decide +kernel)
def s19Mask : Nat := 0xc0c00000c0c00000c0c00000c0c
abbrev s19Goal : Nat := sGoal &&& s19Mask
abbrev s19StockWords : List Nat := projectDAGStock s19Mask sBase [0, 3, 5, 6]
def s19Fact : (Nat × List Nat × Nat × Nat) := (s19Mask, s19StockWords, 5, s19Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Stock : Lower s19Mask s19StockWords s19Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [20]) s12Stock (by decide +kernel)
def s20Mask : Nat := 0x30003000300030003000300030003
abbrev s20Goal : Nat := sGoal &&& s20Mask
abbrev s20StockWords : List Nat := projectDAGStock s20Mask sBase [0, 4, 5, 6]
def s20Fact : (Nat × List Nat × Nat × Nat) := (s20Mask, s20StockWords, 5, s20Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Stock : Lower s20Mask s20StockWords s20Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [21, 22, 19, 8]) s10Stock (by decide +kernel)
def s21Mask : Nat := 0xf000f00000000000f000f00000000
abbrev s21Goal : Nat := sGoal &&& s21Mask
abbrev s21StockWords : List Nat := projectDAGStock s21Mask sBase [0, 1, 4, 6]
def s21Fact : (Nat × List Nat × Nat × Nat) := (s21Mask, s21StockWords, 5, s21Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Stock : Lower s21Mask s21StockWords s21Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 13, 11, 2, 1, 0, 4]) s12Stock (by decide +kernel)
def s22Mask : Nat := 0x500050005000500050005000500050
abbrev s22Goal : Nat := sGoal &&& s22Mask
abbrev s22StockWords : List Nat := projectDAGStock s22Mask sBase [1, 4, 5, 6]
def s22Fact : (Nat × List Nat × Nat × Nat) := (s22Mask, s22StockWords, 5, s22Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Stock : Lower s22Mask s22StockWords s22Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 2, 8, 1, 0, 23]) s12Stock (by decide +kernel)
def s23Mask : Nat := 0x550055000000000055005500000000
abbrev s23Goal : Nat := sGoal &&& s23Mask
abbrev s23StockWords : List Nat := projectDAGStock s23Mask sBase [1, 2, 4, 6]
def s23Fact : (Nat × List Nat × Nat × Nat) := (s23Mask, s23StockWords, 5, s23Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Stock : Lower s23Mask s23StockWords s23Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 11, 2, 1, 0, 4]) s12Stock (by decide +kernel)
def s24Mask : Nat := 0x5050505000000000505050500000000
abbrev s24Goal : Nat := sGoal &&& s24Mask
abbrev s24StockWords : List Nat := projectDAGStock s24Mask sBase [1, 3, 4, 6]
def s24Fact : (Nat × List Nat × Nat × Nat) := (s24Mask, s24StockWords, 5, s24Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Stock : Lower s24Mask s24StockWords s24Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 2, 1, 0, 4]) s12Stock (by decide +kernel)
def s25Mask : Nat := 0xf000f000000000000000000000000000f000f
abbrev s25Goal : Nat := sGoal &&& s25Mask
abbrev s25StockWords : List Nat := projectDAGStock s25Mask sBase [0, 1, 4, 7]
def s25Fact : (Nat × List Nat × Nat × Nat) := (s25Mask, s25StockWords, 5, s25Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Stock : Lower s25Mask s25StockWords s25Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [6]) s14Stock (by decide +kernel)
def s26Mask : Nat := 0x505050500000000000000000000000005050505
abbrev s26Goal : Nat := sGoal &&& s26Mask
abbrev s26StockWords : List Nat := projectDAGStock s26Mask sBase [1, 3, 4, 7]
def s26Fact : (Nat × List Nat × Nat × Nat) := (s26Mask, s26StockWords, 5, s26Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Stock : Lower s26Mask s26StockWords s26Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 11, 2, 5, 6]) s10Stock (by decide +kernel)
def s27Mask : Nat := 0x3030000030300000000000000000000030300000303
abbrev s27Goal : Nat := sGoal &&& s27Mask
abbrev s27StockWords : List Nat := projectDAGStock s27Mask sBase [0, 3, 5, 7]
def s27Fact : (Nat × List Nat × Nat × Nat) := (s27Mask, s27StockWords, 7, s27Goal)
def s27Cuts : List (Nat × List Nat × Nat × Nat) := [s0Fact, s6Fact, s8Fact, s9Fact]
def s27Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 33, 40, 129, 136, 160, 9, 9, 9, 9, 9, 9, 1, 8, 32, 128, 1, 1, 1, 1, 1, 1, 1, 1], rfl⟩
def s27Sample : (Nat × Nat) := (0x4028040a0402201088402040281100a01028100840221040240209, 12)
def s27Witnesses := unpackWitnesses s27StockWords [66176, 331904, 606336, 868384]
def s27Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xe0f4400313c06c4ac400a8664000008ce21845d4705b1001a159151504004c400484e400000000b306801 0x7a4b0b310043143865268c7498149001d3d25855880198a1931c38c5260c7890148b0113265064ca0d31b183361e03a28044b496156200462838070480813629246523407840090e0280e02038ca0831b0f31d1a06c1804848140701c120501c070599b0a32a1006c180a824960362004628824b0fb159d620366565cc7ca18a1102b1803e1404c08040000f 10 4 12 6 1 4
def s27Data : (Nat → Nat × Nat) := fun i => decodeNode 6 18 0x24b0162b064b1e620058a5c32b058d9832864cd9831f064b1562054c50162948ca5202b058d8d31d34ca0e0363407c133618ca86028240d8601c1c0a86013064b0262008c5020080403c0 i
def s27Tags := dagTraceTags s27Mask 12 (dagTagBases s27StockWords 0xfc0c3c3330cf 0xa80428112045 12) 6 s27Data
def s27States := dagTrace s27Mask s27StockWords 6 s27Data
def s27MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := []
def s27Moves := dagMoves s27MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Autos : DagMovesOK s27Mask s27Goal 256 s27Moves := dagMovesOfCheck (by decide +kernel)
def s27Check := dagCheckNode s27Mask s27Goal s27Chart (dagKnownCloses s27Goal s27Cuts) 33 s27States s27Moves s27Links s27Sample s27Tags
def s27RootAt (token : Nat) : Bool :=
  let s := rootState s27StockWords 6 token
  !dagAllowedRoot s27Witnesses s.2.1 || dagLocal s27Mask s27Goal s27Chart (dagKnownCloses s27Goal s27Cuts) s ||
  dagRef 33 s27States s27Moves s27Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27RootBlock0 : treeBlock 0 16 s27RootAt = true := by decide +kernel
theorem s27Roots : dagCheckRoots s27Mask s27Goal s27Chart (dagKnownCloses s27Goal s27Cuts) s27Witnesses (dagRef 33 s27States s27Moves s27Links 0) s27StockWords 6 = true := s27RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Block0 : treeBlock 0 16 s27Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Block16 : treeBlock 16 16 s27Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Block32 : treeBlock 32 1 s27Check = true := by decide +kernel
theorem s27Verified : treeBlock 0 33 s27Check = true := (@treeBlock_merge 0 16 17 s27Check s27Block0 (@treeBlock_merge 16 16 1 s27Check s27Block16 s27Block32))
theorem s27Blocks : treeBlock 0 33 s27Check = true := s27Verified
theorem s27Known : Known s27Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s9Stock) s8Stock) s6Stock) s0Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Stock : Lower s27Mask s27StockWords s27Goal 7 := by
  apply lowerDag _ _ _ _ s27Autos _ _ _ s27Known _ s27Roots s27Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s27StockWords; decide +kernel
  · decide +kernel
  · simp only [s27Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s28Mask : Nat := 0x5050000050500000000000000000000050500000505
abbrev s28Goal : Nat := sGoal &&& s28Mask
abbrev s28StockWords : List Nat := projectDAGStock s28Mask sBase [1, 3, 5, 7]
def s28Fact : (Nat × List Nat × Nat × Nat) := (s28Mask, s28StockWords, 5, s28Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Stock : Lower s28Mask s28StockWords s28Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [9, 10, 11, 7, 8, 5, 6]) s10Stock (by decide +kernel)
def s29Mask : Nat := 0x500050005000500000000000000000005000500050005
abbrev s29Goal : Nat := sGoal &&& s29Mask
abbrev s29StockWords : List Nat := projectDAGStock s29Mask sBase [1, 4, 5, 7]
def s29Fact : (Nat × List Nat × Nat × Nat) := (s29Mask, s29StockWords, 5, s29Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Stock : Lower s29Mask s29StockWords s29Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 22, 2, 8, 5, 6]) s10Stock (by decide +kernel)
def s30Mask : Nat := 0x10101010101010100000000000000000101010101010101
abbrev s30Goal : Nat := sGoal &&& s30Mask
abbrev s30StockWords : List Nat := projectDAGStock s30Mask sBase [3, 4, 5, 7]
def s30Fact : (Nat × List Nat × Nat × Nat) := (s30Mask, s30StockWords, 5, s30Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Stock : Lower s30Mask s30StockWords s30Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [9, 10, 12, 7, 8, 5, 6]) s10Stock (by decide +kernel)
def s31Mask : Nat := 0x303000000000000030300000000000003030000000000000303
abbrev s31Goal : Nat := sGoal &&& s31Mask
abbrev s31StockWords : List Nat := projectDAGStock s31Mask sBase [0, 3, 6, 7]
def s31Fact : (Nat × List Nat × Nat × Nat) := (s31Mask, s31StockWords, 5, s31Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Stock : Lower s31Mask s31StockWords s31Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [24, 25, 26, 27, 20, 1, 6]) s14Stock (by decide +kernel)
def s32Mask : Nat := 0x30003000000000003000300000000000300030000000000030003
abbrev s32Goal : Nat := sGoal &&& s32Mask
abbrev s32StockWords : List Nat := projectDAGStock s32Mask sBase [0, 4, 6, 7]
def s32Fact : (Nat × List Nat × Nat × Nat) := (s32Mask, s32StockWords, 5, s32Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Stock : Lower s32Mask s32StockWords s32Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [24, 25, 26, 27, 20, 5]) s14Stock (by decide +kernel)
def s33Mask : Nat := 0x50005000000000005000500000000000500050000000000050005
abbrev s33Goal : Nat := sGoal &&& s33Mask
abbrev s33StockWords : List Nat := projectDAGStock s33Mask sBase [1, 4, 6, 7]
def s33Fact : (Nat × List Nat × Nat × Nat) := (s33Mask, s33StockWords, 5, s33Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Stock : Lower s33Mask s33StockWords s33Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [24, 25, 18, 19, 28, 1, 6]) s14Stock (by decide +kernel)
def s34Mask : Nat := 0x500050000000000050005000000000005000500000000000500050
abbrev s34Goal : Nat := sGoal &&& s34Mask
abbrev s34StockWords : List Nat := projectDAGStock s34Mask sBase [1, 4, 6, 7]
def s34Fact : (Nat × List Nat × Nat × Nat) := (s34Mask, s34StockWords, 5, s34Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Stock : Lower s34Mask s34StockWords s34Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [24, 25, 18, 19, 28, 1, 6, 15]) s14Stock (by decide +kernel)
def s35Mask : Nat := 0x300000003000000030000000300000003000000030000000300000003
abbrev s35Goal : Nat := sGoal &&& s35Mask
abbrev s35StockWords : List Nat := projectDAGStock s35Mask sBase [0, 5, 6, 7]
def s35Fact : (Nat × List Nat × Nat × Nat) := (s35Mask, s35StockWords, 5, s35Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Stock : Lower s35Mask s35StockWords s35Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [16, 18, 27, 20, 6]) s10Stock (by decide +kernel)
def s36Mask : Nat := 0x10100000101000001010000010100000101000001010000010100000101
abbrev s36Goal : Nat := sGoal &&& s36Mask
abbrev s36StockWords : List Nat := projectDAGStock s36Mask sBase [3, 5, 6, 7]
def s36Fact : (Nat × List Nat × Nat × Nat) := (s36Mask, s36StockWords, 5, s36Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Stock : Lower s36Mask s36StockWords s36Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [16, 29, 18, 27, 8, 5]) s10Stock (by decide +kernel)
def s37Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev s37Goal : Nat := sGoal &&& s37Mask
abbrev s37StockWords : List Nat := projectDAGStock s37Mask sBase [0, 1, 3, 4, 5]
def s37Fact : (Nat × List Nat × Nat × Nat) := (s37Mask, s37StockWords, 7, s37Goal)
def s37Cuts : List (Nat × List Nat × Nat × Nat) := [s11Fact, s12Fact, s1Fact]
def s37Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 17, 18, 33, 40, 9, 9, 9, 9, 9, 9, 9, 3, 10, 24, 34, 48, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s37Sample : (Nat × Nat) := (0x60380c0e06032110c86031110a844230188c301a050683019008440209, 13)
def s37Witnesses := unpackWitnesses s37StockWords [25136, 553008, 812066, 287792, 1077272]
def s37Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xe1 0xd8709880804001f 5 2 12 2 1 2
def s37Data : (Nat → Nat × Nat) := fun i => decodeNode 2 13 0x620404207c i
def s37Tags := dagTraceTags s37Mask 13 (dagTagBases s37StockWords 0x1fe0f8f6274df0167 0x17c0e8a20705d0023 13) 6 s37Data
def s37States := dagTrace s37Mask s37StockWords 6 s37Data
def s37Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def s37Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def s37MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [7]), s37Move0Map, s37Move0Inverse)]
def s37Moves := dagMoves s37MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Autos : DagMovesOK s37Mask s37Goal 256 s37Moves := dagMovesOfCheck (by decide +kernel)
def s37Check := dagCheckNode s37Mask s37Goal s37Chart (dagKnownCloses s37Goal s37Cuts) 3 s37States s37Moves s37Links s37Sample s37Tags
def s37RootAt (token : Nat) : Bool :=
  let s := rootState s37StockWords 6 token
  !dagAllowedRoot s37Witnesses s.2.1 || dagLocal s37Mask s37Goal s37Chart (dagKnownCloses s37Goal s37Cuts) s ||
  dagRef 3 s37States s37Moves s37Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37RootBlock0 : treeBlock 0 32 s37RootAt = true := by decide +kernel
theorem s37Roots : dagCheckRoots s37Mask s37Goal s37Chart (dagKnownCloses s37Goal s37Cuts) s37Witnesses (dagRef 3 s37States s37Moves s37Links 0) s37StockWords 6 = true := s37RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block0 : treeBlock 0 3 s37Check = true := by decide +kernel
theorem s37Blocks : treeBlock 0 3 s37Check = true := s37Block0
theorem s37Known : Known s37Cuts := extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s1Stock) s12Stock) s11Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Stock : Lower s37Mask s37StockWords s37Goal 7 := by
  apply lowerDag _ _ _ _ s37Autos _ _ _ s37Known _ s37Roots s37Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s37StockWords; decide +kernel
  · decide +kernel
  · simp only [s37Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl <;> decide +kernel
def s38Mask : Nat := 0x3333333333333333
abbrev s38Goal : Nat := sGoal &&& s38Mask
abbrev s38StockWords : List Nat := projectDAGStock s38Mask sBase [0, 2, 3, 4, 5]
def s38Fact : (Nat × List Nat × Nat × Nat) := (s38Mask, s38StockWords, 6, s38Goal)
def s38Witnesses := unpackWitnesses s38StockWords [25136, 553008, 797189, 1079324, 288816]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Stock : Lower s38Mask s38StockWords s38Goal 6 := by
  apply essentialLift (witnesses := s38Witnesses) (cut := s11Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s11StockWords) (by decide +kernel)
  · exact s11Stock
  · decide +kernel
def s39Mask : Nat := 0xf0f0f0f000000000f0f0f0f
abbrev s39Goal : Nat := sGoal &&& s39Mask
abbrev s39StockWords : List Nat := projectDAGStock s39Mask sBase [0, 1, 3, 4, 6]
def s39Fact : (Nat × List Nat × Nat × Nat) := (s39Mask, s39StockWords, 7, s39Goal)
def s39Cuts : List (Nat × List Nat × Nat × Nat) := [s13Fact, s14Fact, s15Fact, s16Fact]
def s39Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 17, 18, 65, 66, 72, 80, 9, 9, 9, 9, 9, 3, 10, 24, 64, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s39Sample : (Nat × Nat) := (0x305820140144a2012080422010402410c068141a0c06406130502c060b, 13)
def s39Witnesses := unpackWitnesses s39StockWords [33344, 561216, 827456, 296000, 1093656]
def s39Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x19 0x70e001f 3 1 12 1 1 1
def s39Data : (Nat → Nat × Nat) := fun i => decodeNode 2 14 0xc38407c i
def s39Tags := dagTraceTags s39Mask 13 (dagTagBases s39StockWords 0x1fc0c1e58eca6e0cf 0xb8081450e882e045 13) 6 s39Data
def s39States := dagTrace s39Mask s39StockWords 6 s39Data
def s39MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := []
def s39Moves := dagMoves s39MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Autos : DagMovesOK s39Mask s39Goal 256 s39Moves := dagMovesOfCheck (by decide +kernel)
def s39Check := dagCheckNode s39Mask s39Goal s39Chart (dagKnownCloses s39Goal s39Cuts) 2 s39States s39Moves s39Links s39Sample s39Tags
def s39RootAt (token : Nat) : Bool :=
  let s := rootState s39StockWords 6 token
  !dagAllowedRoot s39Witnesses s.2.1 || dagLocal s39Mask s39Goal s39Chart (dagKnownCloses s39Goal s39Cuts) s ||
  dagRef 2 s39States s39Moves s39Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39RootBlock0 : treeBlock 0 32 s39RootAt = true := by decide +kernel
theorem s39Roots : dagCheckRoots s39Mask s39Goal s39Chart (dagKnownCloses s39Goal s39Cuts) s39Witnesses (dagRef 2 s39States s39Moves s39Links 0) s39StockWords 6 = true := s39RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Block0 : treeBlock 0 2 s39Check = true := by decide +kernel
theorem s39Blocks : treeBlock 0 2 s39Check = true := s39Block0
theorem s39Known : Known s39Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s16Stock) s15Stock) s14Stock) s13Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Stock : Lower s39Mask s39StockWords s39Goal 7 := by
  apply lowerDag _ _ _ _ s39Autos _ _ _ s39Known _ s39Roots s39Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s39StockWords; decide +kernel
  · decide +kernel
  · simp only [s39Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s40Mask : Nat := 0xf0f00000f0f00000f0f00000f0f
abbrev s40Goal : Nat := sGoal &&& s40Mask
abbrev s40StockWords : List Nat := projectDAGStock s40Mask sBase [0, 1, 3, 5, 6]
def s40Fact : (Nat × List Nat × Nat × Nat) := (s40Mask, s40StockWords, 7, s40Goal)
def s40Cuts : List (Nat × List Nat × Nat × Nat) := [s13Fact, s18Fact, s19Fact, s1Fact]
def s40Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 33, 40, 65, 66, 72, 9, 9, 9, 9, 9, 9, 3, 10, 34, 96, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s40Sample : (Nat × Nat) := (0xc06830188446230184144a201080241110a8142a1108c02210502c060b040240209, 15)
def s40Witnesses := unpackWitnesses s40StockWords [49760, 577632, 807946, 1098786, 312416]
def s40Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xe1 0xb88101f202001f 5 2 11 2 1 2
def s40Data : (Nat → Nat × Nat) := fun i => decodeNode 2 7 0x1f50fc i
def s40Tags := dagTraceTags s40Mask 15 (dagTagBases s40StockWords 0x7f00f1e1133db76093f 0x6a00f1401128a760115 15) 6 s40Data
def s40States := dagTrace s40Mask s40StockWords 6 s40Data
def s40Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def s40Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def s40MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [9]), s40Move0Map, s40Move0Inverse)]
def s40Moves := dagMoves s40MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Autos : DagMovesOK s40Mask s40Goal 256 s40Moves := dagMovesOfCheck (by decide +kernel)
def s40Check := dagCheckNode s40Mask s40Goal s40Chart (dagKnownCloses s40Goal s40Cuts) 3 s40States s40Moves s40Links s40Sample s40Tags
def s40RootAt (token : Nat) : Bool :=
  let s := rootState s40StockWords 6 token
  !dagAllowedRoot s40Witnesses s.2.1 || dagLocal s40Mask s40Goal s40Chart (dagKnownCloses s40Goal s40Cuts) s ||
  dagRef 3 s40States s40Moves s40Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40RootBlock0 : treeBlock 0 32 s40RootAt = true := by decide +kernel
theorem s40Roots : dagCheckRoots s40Mask s40Goal s40Chart (dagKnownCloses s40Goal s40Cuts) s40Witnesses (dagRef 3 s40States s40Moves s40Links 0) s40StockWords 6 = true := s40RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Block0 : treeBlock 0 3 s40Check = true := by decide +kernel
theorem s40Blocks : treeBlock 0 3 s40Check = true := s40Block0
theorem s40Known : Known s40Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s1Stock) s19Stock) s18Stock) s13Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Stock : Lower s40Mask s40StockWords s40Goal 7 := by
  apply lowerDag _ _ _ _ s40Autos _ _ _ s40Known _ s40Roots s40Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s40StockWords; decide +kernel
  · decide +kernel
  · simp only [s40Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s41Mask : Nat := 0x3333000033330000333300003333
abbrev s41Goal : Nat := sGoal &&& s41Mask
abbrev s41StockWords : List Nat := projectDAGStock s41Mask sBase [0, 2, 3, 5, 6]
def s41Fact : (Nat × List Nat × Nat × Nat) := (s41Mask, s41StockWords, 7, s41Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Stock : Lower s41Mask s41StockWords s41Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [13, 1]) s40Stock (by decide +kernel)
def s42Mask : Nat := 0xf000f000f000f000f000f000f000f
abbrev s42Goal : Nat := sGoal &&& s42Mask
abbrev s42StockWords : List Nat := projectDAGStock s42Mask sBase [0, 1, 4, 5, 6]
def s42Fact : (Nat × List Nat × Nat × Nat) := (s42Mask, s42StockWords, 7, s42Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Stock : Lower s42Mask s42StockWords s42Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [21, 29, 19, 20]) s40Stock (by decide +kernel)
def s43Mask : Nat := 0x330033003300330033003300330033
abbrev s43Goal : Nat := sGoal &&& s43Mask
abbrev s43StockWords : List Nat := projectDAGStock s43Mask sBase [0, 2, 4, 5, 6]
def s43Fact : (Nat × List Nat × Nat × Nat) := (s43Mask, s43StockWords, 7, s43Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Stock : Lower s43Mask s43StockWords s43Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [13, 2, 8, 1]) s37Stock (by decide +kernel)
def s44Mask : Nat := 0xf000f000f000f000f000f000f000f0
abbrev s44Goal : Nat := sGoal &&& s44Mask
abbrev s44StockWords : List Nat := projectDAGStock s44Mask sBase [0, 1, 4, 5, 6]
def s44Witnesses := unpackWitnesses s44StockWords [35396, 567364, 298052, 837700, 1091604]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Stock : Lower s44Mask s44StockWords s44Goal 6 := by
  apply essentialLift (witnesses := s44Witnesses) (cut := s22Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s22StockWords) (by decide +kernel)
  · exact s22Stock
  · decide +kernel
def s45Mask : Nat := 0xff00ff0000000000ff00ff00000000
abbrev s45Goal : Nat := sGoal &&& s45Mask
abbrev s45StockWords : List Nat := projectDAGStock s45Mask sBase [0, 1, 2, 4, 6]
def s45Witnesses := unpackWitnesses s45StockWords [49760, 575584, 312416, 843872, 1105968]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Stock : Lower s45Mask s45StockWords s45Goal 6 := by
  apply essentialLift (witnesses := s45Witnesses) (cut := s23Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s23StockWords) (by decide +kernel)
  · exact s23Stock
  · decide +kernel
def s46Mask : Nat := 0x3030303030303030303030303030303
abbrev s46Goal : Nat := sGoal &&& s46Mask
abbrev s46StockWords : List Nat := projectDAGStock s46Mask sBase [0, 3, 4, 5, 6]
def s46Fact : (Nat × List Nat × Nat × Nat) := (s46Mask, s46StockWords, 7, s46Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Stock : Lower s46Mask s46StockWords s46Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [9, 14, 12, 7, 20, 1]) s39Stock (by decide +kernel)
def s47Mask : Nat := 0x5050505050505050505050505050505
abbrev s47Goal : Nat := sGoal &&& s47Mask
abbrev s47StockWords : List Nat := projectDAGStock s47Mask sBase [1, 3, 4, 5, 6]
def s47Fact : (Nat × List Nat × Nat × Nat) := (s47Mask, s47StockWords, 7, s47Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Stock : Lower s47Mask s47StockWords s47Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [24, 29, 18, 7, 8]) s37Stock (by decide +kernel)
def s48Mask : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
abbrev s48Goal : Nat := sGoal &&& s48Mask
abbrev s48StockWords : List Nat := projectDAGStock s48Mask sBase [0, 3, 4, 5, 6]
def s48Fact : (Nat × List Nat × Nat × Nat) := (s48Mask, s48StockWords, 6, s48Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Stock : Lower s48Mask s48StockWords s48Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [21, 14, 18, 2, 1, 15, 30]) s45Stock (by decide +kernel)
def s49Mask : Nat := 0xf0f0f0f000000000f0f0f0f00000000
abbrev s49Goal : Nat := sGoal &&& s49Mask
abbrev s49StockWords : List Nat := projectDAGStock s49Mask sBase [0, 1, 3, 4, 6]
def s49Fact : (Nat × List Nat × Nat × Nat) := (s49Mask, s49StockWords, 6, s49Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Stock : Lower s49Mask s49StockWords s49Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [11]) s45Stock (by decide +kernel)
def s50Mask : Nat := 0x30303030303030303030303030303030
abbrev s50Goal : Nat := sGoal &&& s50Mask
abbrev s50StockWords : List Nat := projectDAGStock s50Mask sBase [0, 3, 4, 5, 6]
def s50Fact : (Nat × List Nat × Nat × Nat) := (s50Mask, s50StockWords, 6, s50Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Stock : Lower s50Mask s50StockWords s50Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [9, 14, 12, 2, 23, 15]) s44Stock (by decide +kernel)
def s51Mask : Nat := 0x55555555000000005555555500000000
abbrev s51Goal : Nat := sGoal &&& s51Mask
abbrev s51StockWords : List Nat := projectDAGStock s51Mask sBase [1, 2, 3, 4, 6]
def s51Fact : (Nat × List Nat × Nat × Nat) := (s51Mask, s51StockWords, 6, s51Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Stock : Lower s51Mask s51StockWords s51Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [31, 11]) s45Stock (by decide +kernel)
def s52Mask : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
abbrev s52Goal : Nat := sGoal &&& s52Mask
abbrev s52StockWords : List Nat := projectDAGStock s52Mask sBase [0, 1, 3, 4, 7]
def s52Fact : (Nat × List Nat × Nat × Nat) := (s52Mask, s52StockWords, 7, s52Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52Stock : Lower s52Mask s52StockWords s52Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [6]) s39Stock (by decide +kernel)
def s53Mask : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
abbrev s53Goal : Nat := sGoal &&& s53Mask
abbrev s53StockWords : List Nat := projectDAGStock s53Mask sBase [0, 1, 3, 5, 7]
def s53Fact : (Nat × List Nat × Nat × Nat) := (s53Mask, s53StockWords, 8, s53Goal)
def s53Witnesses := unpackWitnesses s53StockWords [66176, 594048, 868480, 1131554, 328832]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Stock : Lower s53Mask s53StockWords s53Goal 8 := by
  apply essentialLift (witnesses := s53Witnesses) (cut := s27Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s27StockWords) (by decide +kernel)
  · exact s27Stock
  · decide +kernel
def s54Mask : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
abbrev s54Goal : Nat := sGoal &&& s54Mask
abbrev s54StockWords : List Nat := projectDAGStock s54Mask sBase [0, 1, 4, 5, 7]
def s54Fact : (Nat × List Nat × Nat × Nat) := (s54Mask, s54StockWords, 7, s54Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Stock : Lower s54Mask s54StockWords s54Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [7, 6]) s39Stock (by decide +kernel)
def s55Mask : Nat := 0x30303030303030300000000000000000303030303030303
abbrev s55Goal : Nat := sGoal &&& s55Mask
abbrev s55StockWords : List Nat := projectDAGStock s55Mask sBase [0, 3, 4, 5, 7]
def s55Fact : (Nat × List Nat × Nat × Nat) := (s55Mask, s55StockWords, 8, s55Goal)
def s55Witnesses := unpackWitnesses s55StockWords [66176, 331904, 598144, 868480, 1138736]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Stock : Lower s55Mask s55StockWords s55Goal 8 := by
  apply essentialLift (witnesses := s55Witnesses) (cut := s27Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s27StockWords) (by decide +kernel)
  · exact s27Stock
  · decide +kernel
def s56Mask : Nat := 0x50505050505050500000000000000000505050505050505
abbrev s56Goal : Nat := sGoal &&& s56Mask
abbrev s56StockWords : List Nat := projectDAGStock s56Mask sBase [1, 3, 4, 5, 7]
def s56Fact : (Nat × List Nat × Nat × Nat) := (s56Mask, s56StockWords, 8, s56Goal)
def s56Cuts : List (Nat × List Nat × Nat × Nat) := [s26Fact, s28Fact, s29Fact, s30Fact, s7Fact, s9Fact]
def s56Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[18, 40, 130, 136, 144, 160, 18, 18, 18, 18, 18, 18, 10, 24, 34, 48, 128, 10, 10, 10, 10, 10, 10, 10], rfl⟩
def s56Sample : (Nat × Nat) := (0x60b04028044a00c2610090052290088402080482180e03038180c84432110a8142a110a0301a050683012, 19)
def s56Witnesses := unpackWitnesses s56StockWords [66688, 598144, 331904, 868480, 1138736]
def s56Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x920000000003cc3c01 0x6f0e2392c4d88033140f0e0a92c08c507c391b0e1d937664b25637b18ae162054cde431f44c505037300ac401304020001f 9 4 12 3 3 4
def s56Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0xc391c38103710131c3823142008101f0 i
def s56Tags := dagTraceTags s56Mask 19 (dagTagBases s56StockWords 0x7fc00e07f130f1c599f02cf7 0x25800a05d120e14508b9247a 19) 7 s56Data
def s56States := dagTrace s56Mask s56StockWords 7 s56Data
def s56Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def s56Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def s56Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 3, 2, 1, 5, 4, 6, 7] 0 i.val)
def s56Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 3, 2, 1, 5, 4, 6, 7] 0 i.val)
def s56Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 5, 2, 1, 3, 4, 6, 7] 0 i.val)
def s56Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 3, 2, 4, 5, 1, 6, 7] 0 i.val)
def s56Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def s56Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def s56Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 5, 1, 3, 6, 7] 0 i.val)
def s56Move4Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 5, 1, 3, 6, 7] 0 i.val)
def s56MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [7]), s56Move0Map, s56Move0Inverse), ((moveSchedule moveStages [10, 8]), s56Move1Map, s56Move1Inverse), ((moveSchedule moveStages [29, 7, 8]), s56Move2Map, s56Move2Inverse), ((moveSchedule moveStages [14]), s56Move3Map, s56Move3Inverse), ((moveSchedule moveStages [14, 7]), s56Move4Map, s56Move4Inverse)]
def s56Moves := dagMoves s56MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Autos : DagMovesOK s56Mask s56Goal 256 s56Moves := dagMovesOfCheck (by decide +kernel)
def s56Check := dagCheckNode s56Mask s56Goal s56Chart (dagKnownCloses s56Goal s56Cuts) 8 s56States s56Moves s56Links s56Sample s56Tags
def s56RootAt (token : Nat) : Bool :=
  let s := rootState s56StockWords 7 token
  !dagAllowedRoot s56Witnesses s.2.1 || dagLocal s56Mask s56Goal s56Chart (dagKnownCloses s56Goal s56Cuts) s ||
  dagRef 8 s56States s56Moves s56Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56RootBlock0 : treeBlock 0 32 s56RootAt = true := by decide +kernel
theorem s56Roots : dagCheckRoots s56Mask s56Goal s56Chart (dagKnownCloses s56Goal s56Cuts) s56Witnesses (dagRef 8 s56States s56Moves s56Links 0) s56StockWords 7 = true := s56RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Block0 : treeBlock 0 8 s56Check = true := by decide +kernel
theorem s56Blocks : treeBlock 0 8 s56Check = true := s56Block0
theorem s56Known : Known s56Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s9Stock) s7Stock) s30Stock) s29Stock) s28Stock) s26Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Stock : Lower s56Mask s56StockWords s56Goal 8 := by
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
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s57Mask : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
abbrev s57Goal : Nat := sGoal &&& s57Mask
abbrev s57StockWords : List Nat := projectDAGStock s57Mask sBase [0, 1, 3, 6, 7]
def s57Witnesses := unpackWitnesses s57StockWords [99008, 626880, 824330, 361664, 1119242]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s57Stock : Lower s57Mask s57StockWords s57Goal 6 := by
  apply essentialLift (witnesses := s57Witnesses) (cut := s31Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s31StockWords) (by decide +kernel)
  · exact s31Stock
  · decide +kernel
def s58Mask : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
abbrev s58Goal : Nat := sGoal &&& s58Mask
abbrev s58StockWords : List Nat := projectDAGStock s58Mask sBase [0, 1, 4, 6, 7]
def s58Fact : (Nat × List Nat × Nat × Nat) := (s58Mask, s58StockWords, 6, s58Goal)
def s58Witnesses := unpackWitnesses s58StockWords [99008, 630976, 361664, 827408, 1122320]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Stock : Lower s58Mask s58StockWords s58Goal 6 := by
  apply essentialLift (witnesses := s58Witnesses) (cut := s33Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s33StockWords) (by decide +kernel)
  · exact s33Stock
  · decide +kernel
def s59Mask : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f0
abbrev s59Goal : Nat := sGoal &&& s59Mask
abbrev s59StockWords : List Nat := projectDAGStock s59Mask sBase [0, 1, 4, 6, 7]
def s59Fact : (Nat × List Nat × Nat × Nat) := (s59Mask, s59StockWords, 6, s59Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59Stock : Lower s59Mask s59StockWords s59Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [23]) s58Stock (by decide +kernel)
def s60Mask : Nat := 0x3030303000000000303030300000000030303030000000003030303
abbrev s60Goal : Nat := sGoal &&& s60Mask
abbrev s60StockWords : List Nat := projectDAGStock s60Mask sBase [0, 3, 4, 6, 7]
def s60Fact : (Nat × List Nat × Nat × Nat) := (s60Mask, s60StockWords, 6, s60Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Stock : Lower s60Mask s60StockWords s60Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [9, 14, 12, 2]) s58Stock (by decide +kernel)
def s61Mask : Nat := 0x50505050000000005050505000000000505050500000000050505050
abbrev s61Goal : Nat := sGoal &&& s61Mask
abbrev s61StockWords : List Nat := projectDAGStock s61Mask sBase [1, 3, 4, 6, 7]
def s61Fact : (Nat × List Nat × Nat × Nat) := (s61Mask, s61StockWords, 6, s61Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61Stock : Lower s61Mask s61StockWords s61Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 10, 11, 2, 32]) s57Stock (by decide +kernel)
def s62Mask : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
abbrev s62Goal : Nat := sGoal &&& s62Mask
abbrev s62StockWords : List Nat := projectDAGStock s62Mask sBase [0, 1, 5, 6, 7]
def s62Fact : (Nat × List Nat × Nat × Nat) := (s62Mask, s62StockWords, 6, s62Goal)
def s62Witnesses := unpackWitnesses s62StockWords [99008, 639168, 836642, 361664, 1163360]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62Stock : Lower s62Mask s62StockWords s62Goal 6 := by
  apply essentialLift (witnesses := s62Witnesses) (cut := s35Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s35StockWords) (by decide +kernel)
  · exact s35Stock
  · decide +kernel
def s63Mask : Nat := 0x3300000033000000330000003300000033000000330000003300000033
abbrev s63Goal : Nat := sGoal &&& s63Mask
abbrev s63StockWords : List Nat := projectDAGStock s63Mask sBase [0, 2, 5, 6, 7]
def s63Fact : (Nat × List Nat × Nat × Nat) := (s63Mask, s63StockWords, 6, s63Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Stock : Lower s63Mask s63StockWords s63Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [27, 20, 6]) s38Stock (by decide +kernel)
def s64Mask : Nat := 0x30300000303000003030000030300000303000003030000030300000303
abbrev s64Goal : Nat := sGoal &&& s64Mask
abbrev s64StockWords : List Nat := projectDAGStock s64Mask sBase [0, 3, 5, 6, 7]
def s64Fact : (Nat × List Nat × Nat × Nat) := (s64Mask, s64StockWords, 8, s64Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Stock : Lower s64Mask s64StockWords s64Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [7, 20, 5]) s55Stock (by decide +kernel)
def s65Mask : Nat := 0x111100001111000011110000111100001111000011110000111100001111
abbrev s65Goal : Nat := sGoal &&& s65Mask
abbrev s65StockWords : List Nat := projectDAGStock s65Mask sBase [2, 3, 5, 6, 7]
def s65Fact : (Nat × List Nat × Nat × Nat) := (s65Mask, s65StockWords, 6, s65Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Stock : Lower s65Mask s65StockWords s65Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [9, 10, 27, 20, 6]) s38Stock (by decide +kernel)
def s66Mask : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
abbrev s66Goal : Nat := sGoal &&& s66Mask
abbrev s66StockWords : List Nat := projectDAGStock s66Mask sBase [0, 4, 5, 6, 7]
def s66Fact : (Nat × List Nat × Nat × Nat) := (s66Mask, s66StockWords, 7, s66Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Stock : Lower s66Mask s66StockWords s66Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [21, 29, 22, 19, 28, 6]) s39Stock (by decide +kernel)
def s67Mask : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
abbrev s67Goal : Nat := sGoal &&& s67Mask
abbrev s67StockWords : List Nat := projectDAGStock s67Mask sBase [1, 4, 5, 6, 7]
def s67Fact : (Nat × List Nat × Nat × Nat) := (s67Mask, s67StockWords, 7, s67Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Stock : Lower s67Mask s67StockWords s67Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [3, 29, 22, 2, 8, 1, 6]) s40Stock (by decide +kernel)
def s68Mask : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f00000000
abbrev s68Goal : Nat := sGoal &&& s68Mask
abbrev s68StockWords : List Nat := projectDAGStock s68Mask sBase [0, 1, 4, 6, 7]
def s68Fact : (Nat × List Nat × Nat × Nat) := (s68Mask, s68StockWords, 6, s68Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Stock : Lower s68Mask s68StockWords s68Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [26, 27, 5, 30, 33]) s45Stock (by decide +kernel)
def s69Mask : Nat := 0x55005500000000005500550000000000550055000000000055005500000000
abbrev s69Goal : Nat := sGoal &&& s69Mask
abbrev s69StockWords : List Nat := projectDAGStock s69Mask sBase [1, 2, 4, 6, 7]
def s69Fact : (Nat × List Nat × Nat × Nat) := (s69Mask, s69StockWords, 6, s69Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Stock : Lower s69Mask s69StockWords s69Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [31, 26, 27, 5, 30, 33]) s45Stock (by decide +kernel)
def s70Mask : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
abbrev s70Goal : Nat := sGoal &&& s70Mask
abbrev s70StockWords : List Nat := projectDAGStock s70Mask sBase [3, 4, 5, 6, 7]
def s70Fact : (Nat × List Nat × Nat × Nat) := (s70Mask, s70StockWords, 6, s70Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s70Stock : Lower s70Mask s70StockWords s70Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [9, 14, 11, 2]) s62Stock (by decide +kernel)
def s71Mask : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
abbrev s71Goal : Nat := sGoal &&& s71Mask
abbrev s71StockWords : List Nat := projectDAGStock s71Mask sBase [0, 1, 2, 4, 5, 6]
def s71Witnesses := unpackWitnesses s71StockWords [49760, 843872, 312416, 1099844, 575584, 1368112]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Stock : Lower s71Mask s71StockWords s71Goal 8 := by
  apply essentialLift (witnesses := s71Witnesses) (cut := s43Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s43StockWords) (by decide +kernel)
  · exact s43Stock
  · decide +kernel
def s72Mask : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev s72Goal : Nat := sGoal &&& s72Mask
abbrev s72StockWords : List Nat := projectDAGStock s72Mask sBase [0, 1, 3, 4, 5, 6]
def s72Fact : (Nat × List Nat × Nat × Nat) := (s72Mask, s72StockWords, 10, s72Goal)
def s72Cuts : List (Nat × List Nat × Nat × Nat) := [s37Fact, s39Fact, s40Fact, s42Fact, s46Fact, s47Fact, s48Fact, s49Fact, s12Fact, s19Fact, s21Fact, s24Fact, s1Fact, s2Fact, s3Fact, s5Fact]
def s72Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 17, 18, 33, 40, 65, 66, 72, 80, 9, 9, 9, 3, 10, 24, 34, 48, 96, 3, 3, 3, 3, 3, 3], rfl⟩
def s72Sample : (Nat × Nat) := (0xc070181c0c0683018844623018430580c140c0482012030480512006433010806423010480410090460380c0e06032110c86031110a8142a300a06028110a044230188cc02118084442100884301a0506830190184c14120184830110184402110502c060b040240209, 47)
def s72Witnesses := unpackWitnesses s72StockWords [49760, 577632, 843872, 312416, 1077272, 1368112]
def s72Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xc77609ad1a000000590ac435e2ad100000015249c6cd0a6052e1960c438000000851c2060c30418108001fc4e6c71100000000007008001b840000000000000d636248000000c025f0ad14000b02570ab04000a2500000013c49c100026840000000002414000000000000110874a3621a08c460000000000b0a0000000000000523000000000000000000000000002428c3006e001 0x11d250a97a768bd12ed89cb6c38b84a7619939446289804f3b01aa180a4e003a520110e004463d12a1885a0c38504961418a430c4120f44ab6216930e2f5286b292cc8321ab18ad3cc409634342195980c7c9c63a1631456310048020200110af44053102824b010c4122f44ac6212824b00cc4128f44b1621d6b1094d870a492cc5321a898ad3cc40943434719ba08cacdc63e04314a37a6118c72d12986801c1e18e503101364a13ac40ca61c5e2536cd2839692c3c326e0190530c56966204a18a2000a8cc03c3a0108a9282424b11c6283831c1b18e0d0040646393ec40b532047c942a9e9c8af44bc6272230e2e929c7663543314a11881046288004e180081c98d0d80986a040394a71a0138d92826a3403419549c940f989e7ac383c4a71da4d8e8c9c706363718a198138c5e886092c2101a433d10b18704c620201a10e0cd8b18705092c1f0200d00a249e885092c253100f0d08646544cc38253101131008925846f442149a1024b07c66a3c3141c61c0da4b06863a32314957a2173108b58705692c2a3219498ac9cc40483141d0210c00aa1de891ac380d496039880492580c314877a208b0e014c411af441262108b0e031258086200d7a20624b00cc400ef440662102b0e01125806620167a20ab10851870269431049607990c38c56166200a1a1848cac2063e04314817a257b10e5d8859cc38b24a1ea24df612597e643d531bad18ad60c418c3435719baa8cad5063e9c31449021a300dcfc0566401f2f0098b8044040100003f 13 5 13 7 1 5
def s72Data : (Nat → Nat × Nat) := fun i => decodeNode 7 20 0x61c5b31581496593100119b81310561958118f8161c4f4964f315cf496503104f18a019284a315ca3104a18a4a021814964718a4701b817a24061c40314c03104018a400274001581627b361c334a73349b33327334a73931b3318a334a0b41a034195340273300f817a23049630009816211861c1861c2c496183219831598496283101861c253102518a187a21e4962249a1e4961e19a9e18a1e0211861c194961918e9918a1901518008817a2026210261c024a1826211161c114960232182315827a20c4960c310021a1821958218f827a2036210361c03496033100318a020040101f80 i
def s72Tags := dagTraceTags s72Mask 47 (dagTagBases s72StockWords 0x3ffff00000007e001fffe000c3003e003fe045e063e0703c60383630dc60204e107e67f 0x2d31601080007e4297bdc00043203a212880066021007528206816725d60005200222b5 47) 9 s72Data
def s72States := dagTrace s72Mask s72StockWords 9 s72Data
def s72Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 3, 1, 0, 7] 0 i.val)
def s72Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 5, 2, 4, 3, 1, 0, 7] 0 i.val)
def s72MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [24, 29, 2]), s72Move0Map, s72Move0Inverse)]
def s72Moves := dagMoves s72MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Autos : DagMovesOK s72Mask s72Goal 256 s72Moves := dagMovesOfCheck (by decide +kernel)
def s72Check := dagCheckNode s72Mask s72Goal s72Chart (dagKnownCloses s72Goal s72Cuts) 92 s72States s72Moves s72Links s72Sample s72Tags
def s72RootAt (token : Nat) : Bool :=
  let s := rootState s72StockWords 9 token
  !dagAllowedRoot s72Witnesses s.2.1 || dagLocal s72Mask s72Goal s72Chart (dagKnownCloses s72Goal s72Cuts) s ||
  dagRef 92 s72States s72Moves s72Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72RootBlock0 : treeBlock 0 64 s72RootAt = true := by decide +kernel
theorem s72Roots : dagCheckRoots s72Mask s72Goal s72Chart (dagKnownCloses s72Goal s72Cuts) s72Witnesses (dagRef 92 s72States s72Moves s72Links 0) s72StockWords 9 = true := s72RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Block0 : treeBlock 0 16 s72Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Block16 : treeBlock 16 16 s72Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Block32 : treeBlock 32 16 s72Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Block48 : treeBlock 48 16 s72Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Block64 : treeBlock 64 16 s72Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Block80 : treeBlock 80 12 s72Check = true := by decide +kernel
theorem s72Verified : treeBlock 0 92 s72Check = true := (@treeBlock_merge 0 48 44 s72Check (@treeBlock_merge 0 16 32 s72Check s72Block0 (@treeBlock_merge 16 16 16 s72Check s72Block16 s72Block32)) (@treeBlock_merge 48 16 28 s72Check s72Block48 (@treeBlock_merge 64 16 12 s72Check s72Block64 s72Block80)))
theorem s72Blocks : treeBlock 0 92 s72Check = true := s72Verified
theorem s72Known : Known s72Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s5Stock) s3Stock) s2Stock) s1Stock) s24Stock) s21Stock) s19Stock) s12Stock) s49Stock) s48Stock) s47Stock) s46Stock) s42Stock) s40Stock) s39Stock) s37Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Stock : Lower s72Mask s72StockWords s72Goal 10 := by
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
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s73Mask : Nat := 0x33333333333333333333333333333333
abbrev s73Goal : Nat := sGoal &&& s73Mask
abbrev s73StockWords : List Nat := projectDAGStock s73Mask sBase [0, 2, 3, 4, 5, 6]
def s73Cuts : List (Nat × List Nat × Nat × Nat) := [s41Fact, s43Fact, s46Fact, s38Fact, s50Fact, s17Fact]
def s73Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 17, 33, 36, 40, 65, 72, 80, 9, 9, 9, 9, 28, 5, 48, 68, 96, 28, 28, 28, 28, 28, 28, 28], rfl⟩
def s73Sample : (Nat × Nat) := (0xc070181c0c06830190886430184385c22150605022130884502914c04100904383c180e038380c0e06034180c4882402890c02100884381d008440a0d, 27)
def s73Witnesses := unpackWitnesses s73StockWords [49760, 577632, 843872, 1099844, 313440, 1368112]
def s73Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x91c4400f2003840000610016200002483001 0xcf44398e8cc514082cf44118a2b104fe885008298e0fd105870ef446e21af0e1208680373008900242010003f 9 4 12 4 1 4
def s73Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0xf441c431f44cc381c41a04310371f447011131c50091f442c382008103f0 i
def s73Tags := dagTraceTags s73Mask 27 (dagTagBases s73StockWords 0x3fff0007e01ff8c383f0c44878146dc8b2821e09f 0x2f5a0287a449904283f0804058102dca32800a02b 27) 8 s73Data
def s73States := dagTrace s73Mask s73StockWords 8 s73Data
def s73MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := []
def s73Moves := dagMoves s73MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Autos : DagMovesOK s73Mask s73Goal 256 s73Moves := dagMovesOfCheck (by decide +kernel)
def s73Check := dagCheckNode s73Mask s73Goal s73Chart (dagKnownCloses s73Goal s73Cuts) 15 s73States s73Moves s73Links s73Sample s73Tags
def s73RootAt (token : Nat) : Bool :=
  let s := rootState s73StockWords 8 token
  !dagAllowedRoot s73Witnesses s.2.1 || dagLocal s73Mask s73Goal s73Chart (dagKnownCloses s73Goal s73Cuts) s ||
  dagRef 15 s73States s73Moves s73Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73RootBlock0 : treeBlock 0 64 s73RootAt = true := by decide +kernel
theorem s73Roots : dagCheckRoots s73Mask s73Goal s73Chart (dagKnownCloses s73Goal s73Cuts) s73Witnesses (dagRef 15 s73States s73Moves s73Links 0) s73StockWords 8 = true := s73RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Block0 : treeBlock 0 15 s73Check = true := by decide +kernel
theorem s73Blocks : treeBlock 0 15 s73Check = true := s73Block0
theorem s73Known : Known s73Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s17Stock) s50Stock) s38Stock) s46Stock) s43Stock) s41Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Stock : Lower s73Mask s73StockWords s73Goal 9 := by
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
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s74Mask : Nat := 0xcccccccccccccccccccccccccccccccc
abbrev s74Goal : Nat := sGoal &&& s74Mask
abbrev s74StockWords : List Nat := projectDAGStock s74Mask sBase [0, 2, 3, 4, 5, 6]
def s74Witnesses := unpackWitnesses s74StockWords [17954, 545826, 812066, 1072142, 281634, 1360930]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Stock : Lower s74Mask s74StockWords s74Goal 7 := by
  apply essentialLift (witnesses := s74Witnesses) (cut := s48Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s48StockWords) (by decide +kernel)
  · exact s48Stock
  · decide +kernel
def s75Mask : Nat := 0xffffffff00000000ffffffff00000000
abbrev s75Goal : Nat := sGoal &&& s75Mask
abbrev s75StockWords : List Nat := projectDAGStock s75Mask sBase [0, 1, 2, 3, 4, 6]
def s75Witnesses := unpackWitnesses s75StockWords [49760, 575584, 839776, 312416, 1106016, 1368112]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Stock : Lower s75Mask s75StockWords s75Goal 7 := by
  apply essentialLift (witnesses := s75Witnesses) (cut := s51Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s51StockWords) (by decide +kernel)
  · exact s51Stock
  · decide +kernel
def s76Mask : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
abbrev s76Goal : Nat := sGoal &&& s76Mask
abbrev s76StockWords : List Nat := projectDAGStock s76Mask sBase [0, 1, 3, 4, 5, 7]
def s76Fact : (Nat × List Nat × Nat × Nat) := (s76Mask, s76StockWords, 10, s76Goal)
def s76Cuts : List (Nat × List Nat × Nat × Nat) := [s53Fact, s55Fact, s56Fact, s37Fact, s52Fact, s54Fact, s25Fact]
def s76Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 17, 18, 33, 40, 129, 130, 136, 144, 160, 9, 9, 3, 10, 24, 34, 48, 128, 3, 3, 3, 3, 3, 3], rfl⟩
def s76Sample : (Nat × Nat) := (0x182c044a2402803098402406090052290088402081482402040281180e03038180c84432180c4442a050a844230188c301a0506830190184c201208044060b, 28)
def s76Witnesses := unpackWitnesses s76StockWords [66176, 594048, 860288, 328832, 1130624, 1400880]
def s76Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xbb00b18d0000008164590000513b0e01 0xabd1149432a4b106346c9412c4d631068c38398d90940549412f4ebb138e64e1bd106f442bd108c43130e1cf44db10e2c385990cc63709880003f 8 3 13 4 1 3
def s76Data : (Nat → Nat × Nat) := fun i => decodeNode 4 17 0x3d1064a18c41c3218c941de9ce9408327398dc5e884c4327a21b0e08c40203f0 i
def s76Tags := dagTraceTags s76Mask 28 (dagTagBases s76StockWords 0xfff0000e00ff809c0f87e130c67142c37ed003099b 0x29a0000c40bd00940e856124427042417a90010089 28) 9 s76Data
def s76States := dagTrace s76Mask s76StockWords 9 s76Data
def s76Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def s76Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def s76MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [7]), s76Move0Map, s76Move0Inverse)]
def s76Moves := dagMoves s76MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Autos : DagMovesOK s76Mask s76Goal 256 s76Moves := dagMovesOfCheck (by decide +kernel)
def s76Check := dagCheckNode s76Mask s76Goal s76Chart (dagKnownCloses s76Goal s76Cuts) 15 s76States s76Moves s76Links s76Sample s76Tags
def s76RootAt (token : Nat) : Bool :=
  let s := rootState s76StockWords 9 token
  !dagAllowedRoot s76Witnesses s.2.1 || dagLocal s76Mask s76Goal s76Chart (dagKnownCloses s76Goal s76Cuts) s ||
  dagRef 15 s76States s76Moves s76Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76RootBlock0 : treeBlock 0 64 s76RootAt = true := by decide +kernel
theorem s76Roots : dagCheckRoots s76Mask s76Goal s76Chart (dagKnownCloses s76Goal s76Cuts) s76Witnesses (dagRef 15 s76States s76Moves s76Links 0) s76StockWords 9 = true := s76RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Block0 : treeBlock 0 15 s76Check = true := by decide +kernel
theorem s76Blocks : treeBlock 0 15 s76Check = true := s76Block0
theorem s76Known : Known s76Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s25Stock) s54Stock) s52Stock) s37Stock) s56Stock) s55Stock) s53Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Stock : Lower s76Mask s76StockWords s76Goal 10 := by
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
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s77Mask : Nat := 0x333333333333333300000000000000003333333333333333
abbrev s77Goal : Nat := sGoal &&& s77Mask
abbrev s77StockWords : List Nat := projectDAGStock s77Mask sBase [0, 2, 3, 4, 5, 7]
def s77Witnesses := unpackWitnesses s77StockWords [68228, 596100, 862340, 1132676, 288816, 1400880]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s77Stock : Lower s77Mask s77StockWords s77Goal 9 := by
  apply essentialLift (witnesses := s77Witnesses) (cut := s55Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s55StockWords) (by decide +kernel)
  · exact s55Stock
  · decide +kernel
def s78Mask : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
abbrev s78Goal : Nat := sGoal &&& s78Mask
abbrev s78StockWords : List Nat := projectDAGStock s78Mask sBase [0, 1, 3, 4, 6, 7]
def s78Witnesses := unpackWitnesses s78StockWords [99008, 626880, 893120, 361664, 1093656, 1388568]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s78Stock : Lower s78Mask s78StockWords s78Goal 8 := by
  apply essentialLift (witnesses := s78Witnesses) (cut := s52Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s52StockWords) (by decide +kernel)
  · exact s52Stock
  · decide +kernel
def s79Mask : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
abbrev s79Goal : Nat := sGoal &&& s79Mask
abbrev s79StockWords : List Nat := projectDAGStock s79Mask sBase [0, 1, 3, 4, 6, 7]
def s79Fact : (Nat × List Nat × Nat × Nat) := (s79Mask, s79StockWords, 8, s79Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Stock : Lower s79Mask s79StockWords s79Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [23]) s78Stock (by decide +kernel)
def s80Mask : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
abbrev s80Goal : Nat := sGoal &&& s80Mask
abbrev s80StockWords : List Nat := projectDAGStock s80Mask sBase [0, 1, 2, 5, 6, 7]
def s80Fact : (Nat × List Nat × Nat × Nat) := (s80Mask, s80StockWords, 7, s80Goal)
def s80Witnesses := unpackWitnesses s80StockWords [101060, 903364, 575584, 1098786, 363716, 1425504]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Stock : Lower s80Mask s80StockWords s80Goal 7 := by
  apply essentialLift (witnesses := s80Witnesses) (cut := s63Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s63StockWords) (by decide +kernel)
  · exact s63Stock
  · decide +kernel
def s81Mask : Nat := 0x333300003333000033330000333300003333000033330000333300003333
abbrev s81Goal : Nat := sGoal &&& s81Mask
abbrev s81StockWords : List Nat := projectDAGStock s81Mask sBase [0, 2, 3, 5, 6, 7]
def s81Fact : (Nat × List Nat × Nat × Nat) := (s81Mask, s81StockWords, 9, s81Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s81Stock : Lower s81Mask s81StockWords s81Goal 9 := dagShiftLower (width := 256) (moveSchedule moveStages [27, 20]) s77Stock (by decide +kernel)
def s82Mask : Nat := 0x555500005555000055550000555500005555000055550000555500005555
abbrev s82Goal : Nat := sGoal &&& s82Mask
abbrev s82StockWords : List Nat := projectDAGStock s82Mask sBase [1, 2, 3, 5, 6, 7]
def s82Fact : (Nat × List Nat × Nat × Nat) := (s82Mask, s82StockWords, 7, s82Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82Stock : Lower s82Mask s82StockWords s82Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [9]) s80Stock (by decide +kernel)
def s83Mask : Nat := 0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc
abbrev s83Goal : Nat := sGoal &&& s83Mask
abbrev s83StockWords : List Nat := projectDAGStock s83Mask sBase [0, 2, 3, 5, 6, 7]
def s83Fact : (Nat × List Nat × Nat × Nat) := (s83Mask, s83StockWords, 7, s83Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s83Stock : Lower s83Mask s83StockWords s83Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [20, 6]) s74Stock (by decide +kernel)
def s84Mask : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
abbrev s84Goal : Nat := sGoal &&& s84Mask
abbrev s84StockWords : List Nat := projectDAGStock s84Mask sBase [0, 1, 4, 5, 6, 7]
def s84Fact : (Nat × List Nat × Nat × Nat) := (s84Mask, s84StockWords, 9, s84Goal)
def s84Cuts : List (Nat × List Nat × Nat × Nat) := [s42Fact, s54Fact, s66Fact, s67Fact, s58Fact, s62Fact, s68Fact]
def s84Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[17, 18, 33, 65, 66, 80, 129, 130, 144, 160, 17, 17, 3, 34, 48, 96, 192, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s84Sample : (Nat × Nat) := (0x60380c0e06034180c26030460b0112880281301c06070111880241180c844321108c0623080440211, 18)
def s84Witnesses := unpackWitnesses s84StockWords [99008, 630976, 361664, 901312, 1105968, 1425504]
def s84Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x2a0044e1 0x292c292c492c36291620003f 5 2 12 3 1 2
def s84Data : (Nat → Nat × Nat) := fun i => decodeNode 3 15 0x49616293258988081f8 i
def s84Tags := dagTraceTags s84Mask 18 (dagTagBases s84StockWords 0xff003e3c0c6ef09333122f0244f 0xb8003e20046ee01122022700445 18) 8 s84Data
def s84States := dagTrace s84Mask s84StockWords 8 s84Data
def s84MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := []
def s84Moves := dagMoves s84MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Autos : DagMovesOK s84Mask s84Goal 256 s84Moves := dagMovesOfCheck (by decide +kernel)
def s84Check := dagCheckNode s84Mask s84Goal s84Chart (dagKnownCloses s84Goal s84Cuts) 5 s84States s84Moves s84Links s84Sample s84Tags
def s84RootAt (token : Nat) : Bool :=
  let s := rootState s84StockWords 8 token
  !dagAllowedRoot s84Witnesses s.2.1 || dagLocal s84Mask s84Goal s84Chart (dagKnownCloses s84Goal s84Cuts) s ||
  dagRef 5 s84States s84Moves s84Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84RootBlock0 : treeBlock 0 64 s84RootAt = true := by decide +kernel
theorem s84Roots : dagCheckRoots s84Mask s84Goal s84Chart (dagKnownCloses s84Goal s84Cuts) s84Witnesses (dagRef 5 s84States s84Moves s84Links 0) s84StockWords 8 = true := s84RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Block0 : treeBlock 0 5 s84Check = true := by decide +kernel
theorem s84Blocks : treeBlock 0 5 s84Check = true := s84Block0
theorem s84Known : Known s84Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s68Stock) s62Stock) s58Stock) s67Stock) s66Stock) s54Stock) s42Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Stock : Lower s84Mask s84StockWords s84Goal 9 := by
  apply lowerDag _ _ _ _ s84Autos _ _ _ s84Known _ s84Roots s84Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s84StockWords; decide +kernel
  · decide +kernel
  · simp only [s84Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s85Mask : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
abbrev s85Goal : Nat := sGoal &&& s85Mask
abbrev s85StockWords : List Nat := projectDAGStock s85Mask sBase [0, 2, 4, 5, 6, 7]
def s85Fact : (Nat × List Nat × Nat × Nat) := (s85Mask, s85StockWords, 9, s85Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Stock : Lower s85Mask s85StockWords s85Goal 9 := dagShiftLower (width := 256) (moveSchedule moveStages [27, 20]) s73Stock (by decide +kernel)
def s86Mask : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
abbrev s86Goal : Nat := sGoal &&& s86Mask
abbrev s86StockWords : List Nat := projectDAGStock s86Mask sBase [1, 2, 4, 5, 6, 7]
def s86Fact : (Nat × List Nat × Nat × Nat) := (s86Mask, s86StockWords, 8, s86Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s86Stock : Lower s86Mask s86StockWords s86Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [34, 17, 27, 20]) s71Stock (by decide +kernel)
def s87Mask : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
abbrev s87Goal : Nat := sGoal &&& s87Mask
abbrev s87StockWords : List Nat := projectDAGStock s87Mask sBase [0, 1, 2, 4, 6, 7]
def s87Fact : (Nat × List Nat × Nat × Nat) := (s87Mask, s87StockWords, 7, s87Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Stock : Lower s87Mask s87StockWords s87Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [27, 5, 30, 33]) s75Stock (by decide +kernel)
def s88Mask : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
abbrev s88Goal : Nat := sGoal &&& s88Mask
abbrev s88StockWords : List Nat := projectDAGStock s88Mask sBase [0, 3, 4, 5, 6, 7]
def s88Fact : (Nat × List Nat × Nat × Nat) := (s88Mask, s88StockWords, 10, s88Goal)
def s88Cuts : List (Nat × List Nat × Nat × Nat) := [s55Fact, s64Fact, s46Fact, s66Fact, s60Fact, s70Fact, s15Fact, s20Fact, s32Fact, s35Fact, s36Fact, s3Fact]
def s88Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 17, 33, 40, 65, 72, 80, 129, 136, 144, 160, 9, 24, 48, 96, 192, 1, 24, 24, 24, 24, 24, 24, 24], rfl⟩
def s88Sample : (Nat × Nat) := (0x180e160380c0e06034180c86030460b018280309860240309008241808840220308804221808100a04c070181c0c06830184305860140c050081418048301218041301040241180e03038180c43028040a060210088430190c0440211040240209, 43)
def s88Witnesses := unpackWitnesses s88StockWords [99008, 364736, 630976, 901312, 1105968, 1425504]
def s88Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xbe2000b59af6ab4a38a030009f19d29c10009669240009118c50008b17ed7d10007a379172700000071170100063d0000005f45e15a459157200056100054253100051200000000000050100046a00000045142300000040234c0003310000000003212a80002642420002310000000002211d50000000001a300010a01f001 0x3919a880c52f1e899ac424d3149e1882bc6865e31f1718a878c514801f86c404318e170136a8082540110e0041680d4e0052520110d00464bd1130c6a92620cc1a1230cd29c06a4e0110c0042424b09863a163144c620210074940228a634be7a224b10921258886422418e850c53158708a31423014848021152688c9344418a110106ac06a100084231b5ebd11398849a92c4b321a518ad1cc4086342b00219b80ad0403e400111600483802018c407cf44a819a828c5010c407ef443d6211e24b2c46866c32b1518a818c506c02034010b69285bbd3ab589c74c38b84a71ca4b0b466a703293718e9b0c526409c3201214004598132d0080680283300e1418d288c8056340271944e810098c6944c402218e1098a0ad8803e0401b014118cd07806846934287a213b108992584a62b24310110d08846283a0421a015098020792693ac401f0200e80706c0503401c31928183d38bd8705c64e2d31b161880a869c52336201940e01386406c240081318e098ca2564a12cf4e1761c0b18a454c412434e1419b090c7a11e8916c420b314821882218801031c0919a04a4d215e8818c420b496051880206840cf44056210224b20de890ec428d4a18824b43d2581c3430d195838c740c62804027bb7a260310b3d286a692d51496280d0d3c6568031d3b18a4c010cd40566402718009888024040100003f 12 4 13 7 1 4
def s88Data : (Nat → Nat × Nat) := fun i => decodeNode 7 20 0x49681007d2496011a1811958162141496416204c321c1315c162148496483104149a4449a4518a441a14131b4200fc118e817a23c7a23e6213c4963c18a0161c3649636194b618eb618a36015810143300e3301381928197a71961c193271931b19310196202b1a71919b197a2216212149621315a13102149a231a12118a21194190201d49a1e00e1d027190141a00e1a01b190098161c12314923101219b121941318f120048149682496021a1821958262108496083100849a091a10818e827a204621044960418a02013820040101f80 i
def s88Tags := dagTraceTags s88Mask 43 (dagTagBases s88StockWords 0x3ffff0000007e001fff000e3003c01fc025e06783870223c28c6c9c200620727f 0x3713204a0007e2456de00023003c9548007642483d60028c0802cd00002001025 43) 9 s88Data
def s88States := dagTrace s88Mask s88StockWords 9 s88Data
def s88Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 6, 5, 4, 3] 0 i.val)
def s88Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 6, 5, 4, 3] 0 i.val)
def s88MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [27, 20]), s88Move0Map, s88Move0Inverse)]
def s88Moves := dagMoves s88MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Autos : DagMovesOK s88Mask s88Goal 256 s88Moves := dagMovesOfCheck (by decide +kernel)
def s88Check := dagCheckNode s88Mask s88Goal s88Chart (dagKnownCloses s88Goal s88Cuts) 84 s88States s88Moves s88Links s88Sample s88Tags
def s88RootAt (token : Nat) : Bool :=
  let s := rootState s88StockWords 9 token
  !dagAllowedRoot s88Witnesses s.2.1 || dagLocal s88Mask s88Goal s88Chart (dagKnownCloses s88Goal s88Cuts) s ||
  dagRef 84 s88States s88Moves s88Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88RootBlock0 : treeBlock 0 64 s88RootAt = true := by decide +kernel
theorem s88Roots : dagCheckRoots s88Mask s88Goal s88Chart (dagKnownCloses s88Goal s88Cuts) s88Witnesses (dagRef 84 s88States s88Moves s88Links 0) s88StockWords 9 = true := s88RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Block0 : treeBlock 0 16 s88Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Block16 : treeBlock 16 16 s88Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Block32 : treeBlock 32 16 s88Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Block48 : treeBlock 48 16 s88Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Block64 : treeBlock 64 16 s88Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Block80 : treeBlock 80 4 s88Check = true := by decide +kernel
theorem s88Verified : treeBlock 0 84 s88Check = true := (@treeBlock_merge 0 48 36 s88Check (@treeBlock_merge 0 16 32 s88Check s88Block0 (@treeBlock_merge 16 16 16 s88Check s88Block16 s88Block32)) (@treeBlock_merge 48 16 20 s88Check s88Block48 (@treeBlock_merge 64 16 4 s88Check s88Block64 s88Block80)))
theorem s88Blocks : treeBlock 0 84 s88Check = true := s88Verified
theorem s88Known : Known s88Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s3Stock) s36Stock) s35Stock) s32Stock) s20Stock) s15Stock) s70Stock) s60Stock) s66Stock) s46Stock) s64Stock) s55Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Stock : Lower s88Mask s88StockWords s88Goal 10 := by
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
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s89Mask : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
abbrev s89Goal : Nat := sGoal &&& s89Mask
abbrev s89StockWords : List Nat := projectDAGStock s89Mask sBase [1, 3, 4, 5, 6, 7]
def s89Fact : (Nat × List Nat × Nat × Nat) := (s89Mask, s89StockWords, 9, s89Goal)
def s89Witnesses := unpackWitnesses s89StockWords [99520, 630976, 364736, 901312, 1105968, 1425504]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Stock : Lower s89Mask s89StockWords s89Goal 9 := by
  apply essentialLift (witnesses := s89Witnesses) (cut := s56Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s56StockWords) (by decide +kernel)
  · exact s56Stock
  · decide +kernel
def s90Mask : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
abbrev s90Goal : Nat := sGoal &&& s90Mask
abbrev s90StockWords : List Nat := projectDAGStock s90Mask sBase [0, 3, 4, 5, 6, 7]
def s90Fact : (Nat × List Nat × Nat × Nat) := (s90Mask, s90StockWords, 7, s90Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90Stock : Lower s90Mask s90StockWords s90Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [21, 14, 18, 27, 28, 5, 6]) s75Stock (by decide +kernel)
def s91Mask : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
abbrev s91Goal : Nat := sGoal &&& s91Mask
abbrev s91StockWords : List Nat := projectDAGStock s91Mask sBase [2, 3, 4, 5, 6, 7]
def s91Fact : (Nat × List Nat × Nat × Nat) := (s91Mask, s91StockWords, 7, s91Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Stock : Lower s91Mask s91StockWords s91Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [9, 14]) s80Stock (by decide +kernel)
def s92Mask : Nat := 0x5555555500000000555555550000000055555555000000005555555500000000
abbrev s92Goal : Nat := sGoal &&& s92Mask
abbrev s92StockWords : List Nat := projectDAGStock s92Mask sBase [1, 2, 3, 4, 6, 7]
def s92Fact : (Nat × List Nat × Nat × Nat) := (s92Mask, s92StockWords, 7, s92Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Stock : Lower s92Mask s92StockWords s92Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [31, 11, 27, 5, 30, 33]) s75Stock (by decide +kernel)
def s93Mask : Nat := 0xffffffffffffffffffffffffffffffff
abbrev s93Goal : Nat := sGoal &&& s93Mask
abbrev s93StockWords : List Nat := projectDAGStock s93Mask sBase [0, 1, 2, 3, 4, 5, 6]
def s93Fact : (Nat × List Nat × Nat × Nat) := (s93Mask, s93StockWords, 11, s93Goal)
def s93Witnesses := unpackWitnesses s93StockWords [49760, 839776, 1106016, 312416, 1361988, 575584, 1630256]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Stock : Lower s93Mask s93StockWords s93Goal 11 := by
  apply essentialLift (witnesses := s93Witnesses) (cut := s72Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s72StockWords) (by decide +kernel)
  · exact s72Stock
  · decide +kernel
def s94Mask : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
abbrev s94Goal : Nat := sGoal &&& s94Mask
abbrev s94StockWords : List Nat := projectDAGStock s94Mask sBase [0, 1, 2, 3, 4, 5, 7]
def s94Fact : (Nat × List Nat × Nat × Nat) := (s94Mask, s94StockWords, 11, s94Goal)
def s94Witnesses := unpackWitnesses s94StockWords [68228, 858244, 1124484, 330884, 1394820, 550960, 1663024]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Stock : Lower s94Mask s94StockWords s94Goal 11 := by
  apply essentialLift (witnesses := s94Witnesses) (cut := s76Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s76StockWords) (by decide +kernel)
  · exact s76Stock
  · decide +kernel
def s95Mask : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
abbrev s95Goal : Nat := sGoal &&& s95Mask
abbrev s95StockWords : List Nat := projectDAGStock s95Mask sBase [0, 1, 2, 3, 5, 6, 7]
def s95Fact : (Nat × List Nat × Nat × Nat) := (s95Mask, s95StockWords, 10, s95Goal)
def s95Witnesses := unpackWitnesses s95StockWords [101060, 891076, 1165508, 575584, 1360930, 363716, 1687648]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Stock : Lower s95Mask s95StockWords s95Goal 10 := by
  apply essentialLift (witnesses := s95Witnesses) (cut := s81Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s81StockWords) (by decide +kernel)
  · exact s81Stock
  · decide +kernel
def s96Mask : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
abbrev s96Goal : Nat := sGoal &&& s96Mask
abbrev s96StockWords : List Nat := projectDAGStock s96Mask sBase [0, 1, 2, 4, 5, 6, 7]
def s96Fact : (Nat × List Nat × Nat × Nat) := (s96Mask, s96StockWords, 10, s96Goal)
def s96Witnesses := unpackWitnesses s96StockWords [101060, 895172, 363716, 1165508, 575584, 1368112, 1687648]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Stock : Lower s96Mask s96StockWords s96Goal 10 := by
  apply essentialLift (witnesses := s96Witnesses) (cut := s85Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s85StockWords) (by decide +kernel)
  · exact s85Stock
  · decide +kernel
def s97Mask : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev s97Goal : Nat := sGoal &&& s97Mask
abbrev s97StockWords : List Nat := projectDAGStock s97Mask sBase [0, 1, 3, 4, 5, 6, 7]
def s97Fact : (Nat × List Nat × Nat × Nat) := (s97Mask, s97StockWords, 11, s97Goal)
def s97Witnesses := unpackWitnesses s97StockWords [99008, 626880, 893120, 361664, 1163456, 1368112, 1687648]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Stock : Lower s97Mask s97StockWords s97Goal 11 := by
  apply essentialLift (witnesses := s97Witnesses) (cut := s88Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s88StockWords) (by decide +kernel)
  · exact s88Stock
  · decide +kernel
def s98Mask : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
abbrev s98Goal : Nat := sGoal &&& s98Mask
abbrev s98StockWords : List Nat := projectDAGStock s98Mask sBase [0, 2, 3, 4, 5, 6, 7]
def s98Fact : (Nat × List Nat × Nat × Nat) := (s98Mask, s98StockWords, 11, s98Goal)
def s98Witnesses := unpackWitnesses s98StockWords [101060, 628932, 895172, 1165508, 313440, 1368112, 1687648]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Stock : Lower s98Mask s98StockWords s98Goal 11 := by
  apply essentialLift (witnesses := s98Witnesses) (cut := s88Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s88StockWords) (by decide +kernel)
  · exact s88Stock
  · decide +kernel
def s99Mask : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
abbrev s99Goal : Nat := sGoal &&& s99Mask
abbrev s99StockWords : List Nat := projectDAGStock s99Mask sBase [1, 2, 3, 4, 5, 6, 7]
def s99Fact : (Nat × List Nat × Nat × Nat) := (s99Mask, s99StockWords, 10, s99Goal)
def s99Witnesses := unpackWitnesses s99StockWords [101572, 895172, 313440, 1165508, 628932, 1368112, 1687648]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s99Stock : Lower s99Mask s99StockWords s99Goal 10 := by
  apply essentialLift (witnesses := s99Witnesses) (cut := s89Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s89StockWords) (by decide +kernel)
  · exact s89Stock
  · decide +kernel
def s100Mask : Nat := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
abbrev s100Goal : Nat := sGoal &&& s100Mask
abbrev s100StockWords : List Nat := projectDAGStock s100Mask sBase [0, 2, 3, 4, 5, 6, 7]
def s100Fact : (Nat × List Nat × Nat × Nat) := (s100Mask, s100StockWords, 8, s100Goal)
def s100Witnesses := unpackWitnesses s100StockWords [17954, 545826, 812066, 1072142, 281634, 1360930, 1655842]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s100Stock : Lower s100Mask s100StockWords s100Goal 8 := by
  apply essentialLift (witnesses := s100Witnesses) (cut := s90Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s90StockWords) (by decide +kernel)
  · exact s90Stock
  · decide +kernel
def s101Mask : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
abbrev s101Goal : Nat := sGoal &&& s101Mask
abbrev s101StockWords : List Nat := projectDAGStock s101Mask sBase [0, 1, 3, 4, 5, 6, 7]
def s101Fact : (Nat × List Nat × Nat × Nat) := (s101Mask, s101StockWords, 9, s101Goal)
def s101Witnesses := unpackWitnesses s101StockWords [101060, 628932, 895172, 363716, 1165508, 1357852, 1652764]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s101Stock : Lower s101Mask s101StockWords s101Goal 9 := by
  apply essentialLift (witnesses := s101Witnesses) (cut := s79Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s79StockWords) (by decide +kernel)
  · exact s79Stock
  · decide +kernel
def s102Mask : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
abbrev s102Goal : Nat := sGoal &&& s102Mask
abbrev s102StockWords : List Nat := projectDAGStock s102Mask sBase [0, 1, 2, 3, 4, 6, 7]
def s102Fact : (Nat × List Nat × Nat × Nat) := (s102Mask, s102StockWords, 8, s102Goal)
def s102Witnesses := unpackWitnesses s102StockWords [49760, 575584, 839776, 312416, 1106016, 1368112, 1687648]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s102Stock : Lower s102Mask s102StockWords s102Goal 8 := by
  apply essentialLift (witnesses := s102Witnesses) (cut := s92Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s92StockWords) (by decide +kernel)
  · exact s92Stock
  · decide +kernel
def s103Mask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
abbrev s103Goal : Nat := sGoal &&& s103Mask
abbrev s103StockWords : List Nat := projectDAGStock s103Mask sBase [0, 1, 2, 3, 4, 5, 6, 7]
def s103Cuts : List (Nat × List Nat × Nat × Nat) := [s93Fact, s94Fact, s97Fact, s98Fact, s95Fact, s96Fact, s99Fact, s81Fact, s84Fact, s89Fact, s101Fact, s79Fact, s86Fact, s100Fact, s102Fact, s80Fact, s82Fact, s83Fact, s87Fact, s91Fact, s92Fact, s59Fact, s61Fact, s65Fact, s69Fact, s34Fact]
def s103Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 17, 18, 33, 36, 40, 65, 66, 72, 80, 129, 130, 7, 14, 28, 196, 34, 48, 96, 7, 7, 7, 7, 7], rfl⟩
def s103Sample : (Nat × Nat) := (0x188e43038188d46233188c66231444a240280389c0a2501c8e03a1cc070181c0c06830190c06211188c0610e1702854301401c4e30130184c301200e4730114c04230104383c180e03038180d038340a0d06032110c86031070b8382c110a86028110a010280389c4426070980e261108c602100884381e07078381d0c068141a0385c1c160385838150a05420120704802110703c0e0f0702c1009028240209, 71)
def s103Witnesses := unpackWitnesses s103StockWords [101060, 891076, 1157316, 363716, 1427652, 575584, 1630256, 1949792]
def s103Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x29c6a4aa8c6a0a8000000276c9cce6d69a8e637966a572958655100024c990300008fc40008da63518d063318ae22a18a0a271863e171854a141839800000020d1000209480d9fa97d55f327c49eb67a840007991df776d0000000000075580007504000726dbfa6f49bc16ec5ba10001b286bcdab46a0da716949a410001a310001a0365319316449901625d881000187160598015f897c25ec57925dc97525c156f15b856b35a496725985651590563157d15a553754a300014550001441000000050894114fc80004f853a44e440004e040004d4d2d84a8d2914a05235488520200011f146d11a10001182454c000000114144891110000000438c000434400000010c14198fe83eccf743d0ceaa3a0800039c400038d0dd63704d843588d4233d4cc30000ca23118c040000bd30000ba32e44b812d10ac8000000000000000000a930000a8100000000000a530000a4100009f5278400026cc9a1260800000009530000000000094123d4869000085100007f600000001e940001e0877100007611d447411bd400000006c31ac46a10000000000000019906150000000180400000005f116944fb103c3f10f483c10dd4000000036100003330b942d10ac82a10a442630944000090422208080000788000074400000001b205d00f80078001 0x10a61c1fe9373cd2586280dc7a00883a008431e9a84bd11046269fcc433c98706a8d34c41a18f231d0706288880a1087a21fac433c5870618d0c7818e83631441de887e310cf061c1d0936308686548cdc961948ee31d0686288780a50d928218f443e929a7b24d4ef4961ce62a30009a6a0104bc01a92a01d1d80220c8020ee61c0ea31d060628813d34ed7a21a464d1d0c520b98810a01a1d8f441ccc520b1880eb7a21ccc422a0c864a18d47231482a62042006a84bd15077a2202c433a987072a4d8d11a194e33724c652388c741418a206f44391268813d10e3620207250409e887124d0a61a69a034128466a490ca47018e8263144164a0823d10fa626a02c38384c50528134cf0209760372800524880746f0088240083fc0507cc940e049a14834d2e46824f8cd4901948dc31d0446287e80a4df3141bc6283758807cc940f77a71b89342e06824f0cd48f1948da31d0406286da4d0f761c1b4628364c507f4944fc9281f6f4f3e9e9c7c3d10f66271b062833809e7a810ca202096c0352740524700746c00881e0083b987076bd10f301a1d8f443ade885a990c8d31a8d6629038c407880d4ee0201189411a926a06a4b0ec0209daf453ade8866990c8b31a8d2629030c40793d14f07a21dec433a9870660d0cb319b9143291a063a058c50e67a21c09422c8686338c740a18a1bc64c368c683318a4093101ccf44389284658d0c8919a8ca31d02062871b0e0e37a219433519063a038c50e47a21bc9413892586480d4b00158c60110180106ebd10af19a8c431d0146286ebd10db62115c335220652308c740418a1b692c381e886fb10cde6211b8c3836928464010cd901b95802921c03a300044030041d0f4439d88672b0e0e13211b063631c0865580dc860148be01100801069bd10851941a4f442100384198d0d39281a4f4429989a683104cd61c19693627066c410ca0ca49a1363342046506830e0c93141340282000386418a0990140fe01c1f8c6866b0e07d19419494032925865b0e0c932019063635a4a06abd10c06269a8c4134587052a534cf4a099c9373312586398a8980150f801c1000201f8c70c501407c31c2fe4a0523134b962096ac382c926c1e8c70c30148780100ecc505fc940bd7a716ec412d187058a4d83a18e07231c2f58701c0040b031406e0100d802057a4d03518e15c9340d063856a4d03318e1732502e1e885bb0e0ac3140640100c4c501818a0b5928168f440bc63857a5002e18e15a9400b46381600402b18e05431c0a463857bd10ae61c15a92c0a0020594940b17a216064e2b0c68138040c4928985250305e9e603d38be7a2178c4e2ed29e5d250ca24a096c9352cd2585598a81f008151250291e9c4fb138a892814cf4e28589c44a5009c1a714cc382924a051bd109b1a0142c382680804424d09f92813cf4421cc504c81389b4a013692c2718704d19009931b15325029de8852b138a262114094e2752844318d098027128f4424188646b0e084020118f44251e8849310c8b61c112936208684408d009261c1000402212684849408f7a210e6281fc09c463d108c7a20fc642235e8845b0e07d1a1110c382258704398d88361c106f4420526a3f24b0814960fc92c215e884224d4824961006351fcc563e9880967a212ac4324d87048a50c8e49b91492c218c543e01087561c0a431410006c3a3d105131007e3421e805039bd105031007c3421c9e8837310c6b61c0ce936170c862c18dc5631089e6200f46843c00a44e18a0700341d4068353d106662109a92c1cc06a3a3d14727a20e0c431a587032a4d84c3100c89341c18703198a04b18a06e0361892681a8d006149a0683401ba4a036bd10603140943140c8068353d10494960626421a9e882424b06b7a20d2c3816cc6e2a98844731005e336199e883125084631005c342199e88322508453100c892c1106281600a82b19a054334189e8830b0e04318a05002819de8832b0e0633210c063616866e2a0c544218a04e0361724a02da4b05a3150b125015a4a02ab0e05449b0a4028135e8824b0e04649b04c642140052128cd04d7a2090c3811526c2218a043314048334125e882430e02331b044328119e8822b0e04432108663608466c28bd144f7a209cc4313187025a50c4a49b88e92c108c54100cd84000e076f440d526a18a4b02e31504c3140f803a1dbd10396210669350c12581698a83949604a0080b06381598a02a3140526280d5e881a30e03349605031c09001018bd103061c0463140acc681498d02b61c05492c0a4c401100202e7a205ac380b0684140ca02100404431c088650133d10254a104862908cc40108c783f7a287af440f18861d30e0384a106e6430d8c6e1918a42f31004e31e0800103cbd14777a20ecc431c587037a50c6c49b8d092c17cc542f0d0c5d19f8b233715c656298c544118a03e0360618700bbd101d01402cf44055e8808b10c0e61c01493606c0520c00d00d7a2012c4205806a0bbd14157a2026c430318700424d80749a026c38018c5002a4d00449a023250041e880198a00d7a201af44039e880630e0097a200a942025e8803a5080749600af44011870053d100861c00c64200cc6c0e3d141a7a2032c4305187009250c0f49b81692c008c54883d150e7a2216c4341987080250cf449b9d292c35cc5463010caa01b92e02b1ec03a0f0044010040000ff 14 4 13 9 1 4
def s103Data : (Nat → Nat × Nat) := fun i => decodeNode 9 22 0x14445e8a01014c3de8801928431e890c6218040690a7a2c1c06b087a241d87001928405e8901928409e890261c405286010143fe4a2f5014bf64a0f57a7bd5e9cf59283e5e88f561c3dd89cf5021bd526e0101a3cde8aea01abc5e88ea621ba8080ee7a2bac082ec7a23ad870ea496005e88d8621b61e88e661c361e88e27a238d258e2321361e88d9621b65884d97a2375870d949636d284d901bb64c6cd83150064a0c77a231d882c7928349e88d261c31d870d04a0b1d26ec761c335258c761c321258ca320320c6cc831531c086010143164a2ab014b0e4a0ab7a7aade9cab9282fde88ab61c2f589cab4a7aad286ab9282dde88b761c2dd26aab9282d1e88b44962ae4a0ac7a22b0c9cac7a22b5870ad4962b4c68ac3152ac06e019282624a0a87a2261870a66272624a0a37a228d8849861c28529c98928279e889e4a12618709949626cc809931b26409c98015805e887c6219f1e889461c1f1870924a19f24a08f7a223d26e7c7a222de888c61c22d2587c61c21d8708831b21cc547c7a21f526a7d7a220d2587d496204c6a7d3159f52587e3101f40847c00e8040507a7a287c052787a207d8861f01a1d5e8a7201a9cde887261c07d870704a187e4a06d7a21b526e1f7a21a5e886a61c1a52581f7a2181e886661c18125864321181e886161c184c6c6031507c6861f19f87e4a05a496168c545a19b87e4a05819587e4a05461c15126c5418a87c050527a2908052507a2109886427a2135870424a190926e427a212187048496109e884361c10cc844331b10cc544218a07c038407a288003a3e7a2081886207a20ed870204960e528420321880c6e207a20cd870334960ccc52207a20c187030310081e882861c0a06842861c0a5258293100a46502818f081e88214a1084c52213100846502218f0840102001b07c02201014075e8a0201486de8802621808068187a285406a167a20558700261c04d28602928041e881049b809e880c7a20358700c496009e88037a20258700349601cc84037a20118700431b00cc54020040041fe00 i
def s103Tags := dagTraceTags s103Mask 71 (dagTagBases s103StockWords 0xfff000000000000001f81ffff800000000030c3f800fffffc000010660e01ff0007ffc010a213c381f80f807f79e23764e30f1cf8c028c308a0351f37cdc0208101a010239267f 0xbd0000000000000001f8174ab80000000001083f957539c98000000620c01fd5015870000a01282a1890fa95979e03544630b1cfae808c10880155f13c5c000800100002482853 71) 12 s103Data
def s103States := dagTrace s103Mask s103StockWords 12 s103Data
def s103MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := []
def s103Moves := dagMoves s103MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Autos : DagMovesOK s103Mask s103Goal 256 s103Moves := dagMovesOfCheck (by decide +kernel)
def s103Check := dagCheckNode s103Mask s103Goal s103Chart (dagKnownCloses s103Goal s103Cuts) 274 s103States s103Moves s103Links s103Sample s103Tags
def s103RootAt (token : Nat) : Bool :=
  let s := rootState s103StockWords 12 token
  !dagAllowedRoot s103Witnesses s.2.1 || dagLocal s103Mask s103Goal s103Chart (dagKnownCloses s103Goal s103Cuts) s ||
  dagRef 274 s103States s103Moves s103Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103RootBlock0 : treeBlock 0 64 s103RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103RootBlock64 : treeBlock 64 64 s103RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103RootBlock128 : treeBlock 128 64 s103RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103RootBlock192 : treeBlock 192 64 s103RootAt = true := by decide +kernel
theorem s103RootVerified : treeBlock 0 256 s103RootAt = true := (@treeBlock_merge 0 128 128 s103RootAt (@treeBlock_merge 0 64 64 s103RootAt s103RootBlock0 s103RootBlock64) (@treeBlock_merge 128 64 64 s103RootAt s103RootBlock128 s103RootBlock192))
theorem s103Roots : dagCheckRoots s103Mask s103Goal s103Chart (dagKnownCloses s103Goal s103Cuts) s103Witnesses (dagRef 274 s103States s103Moves s103Links 0) s103StockWords 12 = true := s103RootVerified
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block128 : treeBlock 128 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block144 : treeBlock 144 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block160 : treeBlock 160 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block176 : treeBlock 176 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block192 : treeBlock 192 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block208 : treeBlock 208 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block224 : treeBlock 224 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block240 : treeBlock 240 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block256 : treeBlock 256 16 s103Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Block272 : treeBlock 272 2 s103Check = true := by decide +kernel
theorem s103Verified : treeBlock 0 274 s103Check = true := (@treeBlock_merge 0 144 130 s103Check (@treeBlock_merge 0 64 80 s103Check (@treeBlock_merge 0 32 32 s103Check (@treeBlock_merge 0 16 16 s103Check s103Block0 s103Block16) (@treeBlock_merge 32 16 16 s103Check s103Block32 s103Block48)) (@treeBlock_merge 64 32 48 s103Check (@treeBlock_merge 64 16 16 s103Check s103Block64 s103Block80) (@treeBlock_merge 96 16 32 s103Check s103Block96 (@treeBlock_merge 112 16 16 s103Check s103Block112 s103Block128)))) (@treeBlock_merge 144 64 66 s103Check (@treeBlock_merge 144 32 32 s103Check (@treeBlock_merge 144 16 16 s103Check s103Block144 s103Block160) (@treeBlock_merge 176 16 16 s103Check s103Block176 s103Block192)) (@treeBlock_merge 208 32 34 s103Check (@treeBlock_merge 208 16 16 s103Check s103Block208 s103Block224) (@treeBlock_merge 240 16 18 s103Check s103Block240 (@treeBlock_merge 256 16 2 s103Check s103Block256 s103Block272)))))
theorem s103Blocks : treeBlock 0 274 s103Check = true := s103Verified
theorem s103Known : Known s103Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s34Stock) s69Stock) s65Stock) s61Stock) s59Stock) s92Stock) s91Stock) s87Stock) s83Stock) s82Stock) s80Stock) s102Stock) s100Stock) s86Stock) s79Stock) s101Stock) s89Stock) s84Stock) s81Stock) s99Stock) s96Stock) s95Stock) s98Stock) s97Stock) s94Stock) s93Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Stock : Lower s103Mask s103StockWords s103Goal 13 := by
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
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def monoCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [5, 10]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [16, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_28348

open PEqualNP.Outside.L_meta_28348 in
theorem PEqualNP.Outside.L_meta_28348 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates out legal _ computes
  let target : (Fin 8 → Bool) → Bool := fun x => decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
  let raw : List (BitVec 256) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
  let goal : BitVec 256 := 0xffffffffffffffeeffffffffffffffeefffffffeffffffeefffefffaeeeeaa00
  have root : Lower (fullMask 256) (raw.map BitVec.toNat) goal.toNat 13 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s103Stock
  have fan : ∀ g ∈ gates, g.op ∈ ({.and, .or, .not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    exact legal g hg
  have hit : PEqualNP.MetaComplexity.HasCircuitSize 8 target gates.length :=
    ⟨⟨gates, out⟩, fan, Nat.le_refl _, computes⟩
  have size := hcsLower raw goal 13 target (by decide +kernel) (by decide +kernel) root _ hit
  have monoEval : ∀ x, monoCircuit.eval (List.ofFn x) = target x := by
    intro x
    have clean : PEqualNP.MetaComplexity.FanInTwo monoCircuit := by
      intro gate member
      simp only [monoCircuit, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    exact hcsWitnessEval raw goal monoCircuit target clean (by decide +kernel) (by decide +kernel) (by decide +kernel) x
  refine ⟨monoCircuit.gates, monoCircuit.output, ?_, ?_, monoEval⟩
  · intro gate member
    simp only [monoCircuit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : monoCircuit.gates.length ≤ 13) size

