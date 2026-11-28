import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_44162

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
def sGoal : Nat := 0xfeeefae8fee8faa0
def s0Mask : Nat := 0xff00000000
abbrev s0Goal : Nat := sGoal &&& s0Mask
abbrev s0StockWords : List Nat := projectDAGStock s0Mask sBase [0, 1, 2]
def s0Fact : (Nat × List Nat × Nat × Nat) := (s0Mask, s0StockWords, 4, s0Goal)
def s0Cuts : List (Nat × List Nat × Nat × Nat) := []
def s0Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[35, 37, 38, 35, 35, 35, 35, 35, 35, 35, 35, 35, 33, 34, 36, 33, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s0Sample : (Nat × Nat) := (0x1209842251108c4426120944223, 6)
def s0Witnesses := unpackWitnesses s0StockWords [17954, 280097, 543265]
def s0Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s0Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s0Tags := dagTraceTags s0Mask 6 (dagTagBases s0StockWords 0x36b5b 0x22311 6) 3 s0Data
def s0States := dagTrace s0Mask s0StockWords 3 s0Data
def s0Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])]
def s0Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s0Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s0Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])]
def s0Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s0Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s0Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x8181818181818181, 0), (0x202020202020202, 1), (0x404040404040404, 2), (0x808080808080808, 3)], [(0x4040404040404040, 1), (0x2020202020202020, 2), (0x1010101010101010, 3)])]
def s0Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val)
def s0Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val)
def s0Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x8181818181818181, 0), (0x2020202020202020, 1), (0x808080808080808, 2), (0x202020202020202, 3)], [(0x404040404040404, 1), (0x1010101010101010, 2), (0x4040404040404040, 3)])]
def s0Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val)
def s0Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val)
def s0Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s0Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s0Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s0MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s0Move0Stages, s0Move0Map, s0Move0Inverse), (s0Move1Stages, s0Move1Map, s0Move1Inverse), (s0Move2Stages, s0Move2Map, s0Move2Inverse), (s0Move3Stages, s0Move3Map, s0Move3Inverse), (s0Move4Stages, s0Move4Map, s0Move4Inverse)]
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
def s1Mask : Nat := 0xff0000
abbrev s1Goal : Nat := sGoal &&& s1Mask
abbrev s1StockWords : List Nat := projectDAGStock s1Mask sBase [0, 1, 2]
def s1Fact : (Nat × List Nat × Nat × Nat) := (s1Mask, s1StockWords, 4, s1Goal)
def s1Cuts : List (Nat × List Nat × Nat × Nat) := []
def s1Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[19, 21, 22, 19, 19, 19, 19, 19, 19, 19, 19, 19, 17, 18, 20, 17, 17, 17, 17, 17, 17, 17, 17, 17], rfl⟩
def s1Sample : (Nat × Nat) := (0xa05822150904c24160a0542213, 6)
def s1Witnesses := unpackWitnesses s1StockWords [9746, 271889, 535057]
def s1Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s1Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s1Tags := dagTraceTags s1Mask 6 (dagTagBases s1StockWords 0x36b5b 0x22311 6) 3 s1Data
def s1States := dagTrace s1Mask s1StockWords 3 s1Data
def s1Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])]
def s1Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s1Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s1Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])]
def s1Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s1Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s1Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x8181818181818181, 0), (0x202020202020202, 1), (0x404040404040404, 2), (0x808080808080808, 3)], [(0x4040404040404040, 1), (0x2020202020202020, 2), (0x1010101010101010, 3)])]
def s1Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val)
def s1Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val)
def s1Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x8181818181818181, 0), (0x2020202020202020, 1), (0x808080808080808, 2), (0x202020202020202, 3)], [(0x404040404040404, 1), (0x1010101010101010, 2), (0x4040404040404040, 3)])]
def s1Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val)
def s1Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val)
def s1Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s1Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s1Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s1MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s1Move0Stages, s1Move0Map, s1Move0Inverse), (s1Move1Stages, s1Move1Map, s1Move1Inverse), (s1Move2Stages, s1Move2Map, s1Move2Inverse), (s1Move3Stages, s1Move3Map, s1Move3Inverse), (s1Move4Stages, s1Move4Map, s1Move4Inverse)]
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
def s2Mask : Nat := 0xf0f0000
abbrev s2Goal : Nat := sGoal &&& s2Mask
abbrev s2StockWords : List Nat := projectDAGStock s2Mask sBase [0, 1, 3]
def s2Fact : (Nat × List Nat × Nat × Nat) := (s2Mask, s2StockWords, 4, s2Goal)
def s2Cuts : List (Nat × List Nat × Nat × Nat) := []
def s2Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[19, 25, 26, 19, 19, 19, 19, 19, 19, 19, 19, 19, 17, 18, 24, 17, 17, 17, 17, 17, 17, 17, 17, 17], rfl⟩
def s2Sample : (Nat × Nat) := (0xc06822190904c241a0c0642213, 6)
def s2Witnesses := unpackWitnesses s2StockWords [9746, 271889, 537105]
def s2Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s2Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s2Tags := dagTraceTags s2Mask 6 (dagTagBases s2StockWords 0x36b5b 0x22311 6) 3 s2Data
def s2States := dagTrace s2Mask s2StockWords 3 s2Data
def s2Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcc33cc33cc33cc33, 0), (0xcc00cc00cc00cc, 6)], [(0x3300330033003300, 6)])]
def s2Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)
def s2Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)
def s2Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])]
def s2Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s2Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s2Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x8811881188118811, 0), (0x22002200220022, 1), (0x44004400440044, 6), (0x88008800880088, 7)], [(0x4400440044004400, 1), (0x2200220022002200, 6), (0x1100110011001100, 7)])]
def s2Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 0, 2, 1, 4, 5] 0 i.val)
def s2Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 3, 2, 0, 4, 5] 0 i.val)
def s2Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x8811881188118811, 0), (0x2200220022002200, 1), (0x88008800880088, 6), (0x22002200220022, 7)], [(0x44004400440044, 1), (0x1100110011001100, 6), (0x4400440044004400, 7)])]
def s2Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 3, 2, 0, 4, 5] 0 i.val)
def s2Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 0, 2, 1, 4, 5] 0 i.val)
def s2Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])]
def s2Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s2Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s2MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s2Move0Stages, s2Move0Map, s2Move0Inverse), (s2Move1Stages, s2Move1Map, s2Move1Inverse), (s2Move2Stages, s2Move2Map, s2Move2Inverse), (s2Move3Stages, s2Move3Map, s2Move3Inverse), (s2Move4Stages, s2Move4Map, s2Move4Inverse)]
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
def s3Mask : Nat := 0xf000f00000000
abbrev s3Goal : Nat := sGoal &&& s3Mask
abbrev s3StockWords : List Nat := projectDAGStock s3Mask sBase [0, 1, 4]
def s3Fact : (Nat × List Nat × Nat × Nat) := (s3Mask, s3StockWords, 4, s3Goal)
def s3Cuts : List (Nat × List Nat × Nat × Nat) := []
def s3Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[35, 49, 50, 35, 35, 35, 35, 35, 35, 35, 35, 35, 33, 34, 48, 33, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s3Sample : (Nat × Nat) := (0x180c842311108c4432180c44223, 6)
def s3Witnesses := unpackWitnesses s3StockWords [17954, 280097, 549409]
def s3Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s3Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s3Tags := dagTraceTags s3Mask 6 (dagTagBases s3StockWords 0x36b5b 0x22311 6) 3 s3Data
def s3States := dagTrace s3Mask s3StockWords 3 s3Data
def s3Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])]
def s3Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s3Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s3Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])]
def s3Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s3Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s3Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x8888111188881111, 0), (0x222200002222, 1), (0x444400004444, 14), (0x888800008888, 15)], [(0x4444000044440000, 1), (0x2222000022220000, 14), (0x1111000011110000, 15)])]
def s3Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 0, 2, 3, 1, 5] 0 i.val)
def s3Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 4, 2, 3, 0, 5] 0 i.val)
def s3Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x8888111188881111, 0), (0x2222000022220000, 1), (0x888800008888, 14), (0x222200002222, 15)], [(0x444400004444, 1), (0x1111000011110000, 14), (0x4444000044440000, 15)])]
def s3Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 4, 2, 3, 0, 5] 0 i.val)
def s3Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 0, 2, 3, 1, 5] 0 i.val)
def s3Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaaaa5555aaaa5555, 0), (0xaaaa0000aaaa, 15)], [(0x5555000055550000, 15)])]
def s3Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s3Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s3MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s3Move0Stages, s3Move0Map, s3Move0Inverse), (s3Move1Stages, s3Move1Map, s3Move1Inverse), (s3Move2Stages, s3Move2Map, s3Move2Inverse), (s3Move3Stages, s3Move3Map, s3Move3Inverse), (s3Move4Stages, s3Move4Map, s3Move4Inverse)]
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
def s4Mask : Nat := 0xf0000000f0000
abbrev s4Goal : Nat := sGoal &&& s4Mask
abbrev s4StockWords : List Nat := projectDAGStock s4Mask sBase [0, 1, 5]
def s4Fact : (Nat × List Nat × Nat × Nat) := (s4Mask, s4StockWords, 4, s4Goal)
def s4Cuts : List (Nat × List Nat × Nat × Nat) := []
def s4Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[19, 49, 50, 19, 19, 19, 19, 19, 19, 19, 19, 19, 17, 18, 48, 17, 17, 17, 17, 17, 17, 17, 17, 17], rfl⟩
def s4Sample : (Nat × Nat) := (0x180c822310904c2432180c42213, 6)
def s4Witnesses := unpackWitnesses s4StockWords [9746, 271889, 549393]
def s4Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s4Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s4Tags := dagTraceTags s4Mask 6 (dagTagBases s4StockWords 0x36b5b 0x22311 6) 3 s4Data
def s4States := dagTrace s4Mask s4StockWords 3 s4Data
def s4Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccccccc33333333, 0), (0xcccccccc, 30)], [(0x3333333300000000, 30)])]
def s4Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 5, 2, 3, 4, 1] 0 i.val)
def s4Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 5, 2, 3, 4, 1] 0 i.val)
def s4Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])]
def s4Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s4Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s4Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x8888888811111111, 0), (0x22222222, 1), (0x44444444, 30), (0x88888888, 31)], [(0x4444444400000000, 1), (0x2222222200000000, 30), (0x1111111100000000, 31)])]
def s4Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [5, 0, 2, 3, 4, 1] 0 i.val)
def s4Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 5, 2, 3, 4, 0] 0 i.val)
def s4Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x8888888811111111, 0), (0x2222222200000000, 1), (0x88888888, 30), (0x22222222, 31)], [(0x44444444, 1), (0x1111111100000000, 30), (0x4444444400000000, 31)])]
def s4Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 5, 2, 3, 4, 0] 0 i.val)
def s4Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [5, 0, 2, 3, 4, 1] 0 i.val)
def s4Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaaaaaaaa55555555, 0), (0xaaaaaaaa, 31)], [(0x5555555500000000, 31)])]
def s4Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [5, 1, 2, 3, 4, 0] 0 i.val)
def s4Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [5, 1, 2, 3, 4, 0] 0 i.val)
def s4MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s4Move0Stages, s4Move0Map, s4Move0Inverse), (s4Move1Stages, s4Move1Map, s4Move1Inverse), (s4Move2Stages, s4Move2Map, s4Move2Inverse), (s4Move3Stages, s4Move3Map, s4Move3Inverse), (s4Move4Stages, s4Move4Map, s4Move4Inverse)]
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
def s5Mask : Nat := 0x3333
abbrev s5Goal : Nat := sGoal &&& s5Mask
abbrev s5StockWords : List Nat := projectDAGStock s5Mask sBase [0, 2, 3]
def s5Fact : (Nat × List Nat × Nat × Nat) := (s5Mask, s5StockWords, 4, s5Goal)
def s5Cuts : List (Nat × List Nat × Nat × Nat) := []
def s5Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 9, 12, 5, 5, 5, 5, 5, 5, 5, 5, 5, 1, 4, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1], rfl⟩
def s5Sample : (Nat × Nat) := (0x4030020902014080c040240205, 6)
def s5Witnesses := unpackWitnesses s5StockWords [2564, 264705, 528897]
def s5Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s5Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s5Tags := dagTraceTags s5Mask 6 (dagTagBases s5StockWords 0x36b5b 0x22311 6) 3 s5Data
def s5States := dagTrace s5Mask s5StockWords 3 s5Data
def s5Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s5Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s5Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s5Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s5Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s5Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s5Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa005a005a005a005, 0), (0xa000a000a000a, 3), (0x50005000500050, 4), (0xa000a000a000a0, 7)], [(0x5000500050005000, 3), (0xa000a000a000a00, 4), (0x500050005000500, 7)])]
def s5Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s5Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s5Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa005a005a005a005, 0), (0xa000a000a000a00, 3), (0xa000a000a000a0, 4), (0xa000a000a000a, 7)], [(0x50005000500050, 3), (0x500050005000500, 4), (0x5000500050005000, 7)])]
def s5Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s5Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s5Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])]
def s5Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s5Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s5MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s5Move0Stages, s5Move0Map, s5Move0Inverse), (s5Move1Stages, s5Move1Map, s5Move1Inverse), (s5Move2Stages, s5Move2Map, s5Move2Inverse), (s5Move3Stages, s5Move3Map, s5Move3Inverse), (s5Move4Stages, s5Move4Map, s5Move4Inverse)]
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
def s6Mask : Nat := 0x333300000000
abbrev s6Goal : Nat := sGoal &&& s6Mask
abbrev s6StockWords : List Nat := projectDAGStock s6Mask sBase [0, 2, 3]
def s6Fact : (Nat × List Nat × Nat × Nat) := (s6Mask, s6StockWords, 4, s6Goal)
def s6Cuts : List (Nat × List Nat × Nat × Nat) := []
def s6Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[37, 41, 44, 37, 37, 37, 37, 37, 37, 37, 37, 37, 33, 36, 40, 33, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s6Sample : (Nat × Nat) := (0x140b0422912094482c140a44225, 6)
def s6Witnesses := unpackWitnesses s6StockWords [18980, 281121, 545313]
def s6Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s6Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s6Tags := dagTraceTags s6Mask 6 (dagTagBases s6StockWords 0x36b5b 0x22311 6) 3 s6Data
def s6States := dagTrace s6Mask s6StockWords 3 s6Data
def s6Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s6Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s6Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s6Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s6Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s6Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s6Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa005a005a005a005, 0), (0xa000a000a000a, 3), (0x50005000500050, 4), (0xa000a000a000a0, 7)], [(0x5000500050005000, 3), (0xa000a000a000a00, 4), (0x500050005000500, 7)])]
def s6Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s6Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s6Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa005a005a005a005, 0), (0xa000a000a000a00, 3), (0xa000a000a000a0, 4), (0xa000a000a000a, 7)], [(0x50005000500050, 3), (0x500050005000500, 4), (0x5000500050005000, 7)])]
def s6Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s6Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s6Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])]
def s6Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s6Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s6MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s6Move0Stages, s6Move0Map, s6Move0Inverse), (s6Move1Stages, s6Move1Map, s6Move1Inverse), (s6Move2Stages, s6Move2Map, s6Move2Inverse), (s6Move3Stages, s6Move3Map, s6Move3Inverse), (s6Move4Stages, s6Move4Map, s6Move4Inverse)]
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
def s7Mask : Nat := 0x33330000
abbrev s7Goal : Nat := sGoal &&& s7Mask
abbrev s7StockWords : List Nat := projectDAGStock s7Mask sBase [0, 2, 3]
def s7Fact : (Nat × List Nat × Nat × Nat) := (s7Mask, s7StockWords, 4, s7Goal)
def s7Cuts : List (Nat × List Nat × Nat × Nat) := []
def s7Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[21, 25, 28, 21, 21, 21, 21, 21, 21, 21, 21, 21, 17, 20, 24, 17, 17, 17, 17, 17, 17, 17, 17, 17], rfl⟩
def s7Sample : (Nat × Nat) := (0xc07022190a054281c0c0642215, 6)
def s7Witnesses := unpackWitnesses s7StockWords [10772, 272913, 537105]
def s7Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s7Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s7Tags := dagTraceTags s7Mask 6 (dagTagBases s7StockWords 0x36b5b 0x22311 6) 3 s7Data
def s7States := dagTrace s7Mask s7StockWords 3 s7Data
def s7Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s7Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s7Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s7Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s7Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s7Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s7Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa005a005a005a005, 0), (0xa000a000a000a, 3), (0x50005000500050, 4), (0xa000a000a000a0, 7)], [(0x5000500050005000, 3), (0xa000a000a000a00, 4), (0x500050005000500, 7)])]
def s7Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s7Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s7Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa005a005a005a005, 0), (0xa000a000a000a00, 3), (0xa000a000a000a0, 4), (0xa000a000a000a, 7)], [(0x50005000500050, 3), (0x500050005000500, 4), (0x5000500050005000, 7)])]
def s7Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s7Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s7Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])]
def s7Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s7Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s7MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s7Move0Stages, s7Move0Map, s7Move0Inverse), (s7Move1Stages, s7Move1Map, s7Move1Inverse), (s7Move2Stages, s7Move2Map, s7Move2Inverse), (s7Move3Stages, s7Move3Map, s7Move3Inverse), (s7Move4Stages, s7Move4Map, s7Move4Inverse)]
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
def s8Mask : Nat := 0xcccc
abbrev s8Goal : Nat := sGoal &&& s8Mask
abbrev s8StockWords : List Nat := projectDAGStock s8Mask sBase [0, 2, 3]
def s8Fact : (Nat × List Nat × Nat × Nat) := (s8Mask, s8StockWords, 4, s8Goal)
def s8Cuts : List (Nat × List Nat × Nat × Nat) := []
def s8Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[7, 11, 14, 7, 7, 7, 7, 7, 7, 7, 7, 7, 3, 6, 10, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s8Sample : (Nat × Nat) := (0x5038060b0301c0c0e0502c0607, 6)
def s8Witnesses := unpackWitnesses s8StockWords [3590, 265731, 529923]
def s8Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s8Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s8Tags := dagTraceTags s8Mask 6 (dagTagBases s8StockWords 0x36b5b 0x22311 6) 3 s8Data
def s8States := dagTrace s8Mask s8StockWords 3 s8Data
def s8Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s8Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s8Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s8Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s8Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s8Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s8Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa005a005a005a005, 0), (0xa000a000a000a, 3), (0x50005000500050, 4), (0xa000a000a000a0, 7)], [(0x5000500050005000, 3), (0xa000a000a000a00, 4), (0x500050005000500, 7)])]
def s8Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s8Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s8Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa005a005a005a005, 0), (0xa000a000a000a00, 3), (0xa000a000a000a0, 4), (0xa000a000a000a, 7)], [(0x50005000500050, 3), (0x500050005000500, 4), (0x5000500050005000, 7)])]
def s8Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s8Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s8Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])]
def s8Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s8Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s8MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s8Move0Stages, s8Move0Map, s8Move0Inverse), (s8Move1Stages, s8Move1Map, s8Move1Inverse), (s8Move2Stages, s8Move2Map, s8Move2Inverse), (s8Move3Stages, s8Move3Map, s8Move3Inverse), (s8Move4Stages, s8Move4Map, s8Move4Inverse)]
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
def s9Mask : Nat := 0xcc00cc
abbrev s9Goal : Nat := sGoal &&& s9Mask
abbrev s9StockWords : List Nat := projectDAGStock s9Mask sBase [0, 2, 4]
def s9Fact : (Nat × List Nat × Nat × Nat) := (s9Mask, s9StockWords, 4, s9Goal)
def s9Cuts : List (Nat × List Nat × Nat × Nat) := []
def s9Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[7, 19, 22, 7, 7, 7, 7, 7, 7, 7, 7, 7, 3, 6, 18, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s9Sample : (Nat × Nat) := (0x905806130301c0c160904c0607, 6)
def s9Witnesses := unpackWitnesses s9StockWords [3590, 265731, 534019]
def s9Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s9Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s9Tags := dagTraceTags s9Mask 6 (dagTagBases s9StockWords 0x36b5b 0x22311 6) 3 s9Data
def s9States := dagTrace s9Mask s9StockWords 3 s9Data
def s9Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])]
def s9Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s9Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s9Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s9Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s9Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s9Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa0a00505a0a00505, 0), (0xa0a00000a0a, 3), (0x505000005050, 12), (0xa0a00000a0a0, 15)], [(0x5050000050500000, 3), (0xa0a00000a0a0000, 12), (0x505000005050000, 15)])]
def s9Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 0, 3, 2, 5] 0 i.val)
def s9Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 4, 3, 0, 5] 0 i.val)
def s9Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa0a00505a0a00505, 0), (0xa0a00000a0a0000, 3), (0xa0a00000a0a0, 12), (0xa0a00000a0a, 15)], [(0x505000005050, 3), (0x505000005050000, 12), (0x5050000050500000, 15)])]
def s9Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 4, 3, 0, 5] 0 i.val)
def s9Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 0, 3, 2, 5] 0 i.val)
def s9Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaaaa5555aaaa5555, 0), (0xaaaa0000aaaa, 15)], [(0x5555000055550000, 15)])]
def s9Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s9Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s9MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s9Move0Stages, s9Move0Map, s9Move0Inverse), (s9Move1Stages, s9Move1Map, s9Move1Inverse), (s9Move2Stages, s9Move2Map, s9Move2Inverse), (s9Move3Stages, s9Move3Map, s9Move3Inverse), (s9Move4Stages, s9Move4Map, s9Move4Inverse)]
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
def s10Mask : Nat := 0xcc000000cc
abbrev s10Goal : Nat := sGoal &&& s10Mask
abbrev s10StockWords : List Nat := projectDAGStock s10Mask sBase [0, 2, 5]
def s10Fact : (Nat × List Nat × Nat × Nat) := (s10Mask, s10StockWords, 4, s10Goal)
def s10Cuts : List (Nat × List Nat × Nat × Nat) := []
def s10Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[7, 35, 38, 7, 7, 7, 7, 7, 7, 7, 7, 7, 3, 6, 34, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s10Sample : (Nat × Nat) := (0x1109806230301c0c261108c0607, 6)
def s10Witnesses := unpackWitnesses s10StockWords [3590, 265731, 542211]
def s10Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s10Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s10Tags := dagTraceTags s10Mask 6 (dagTagBases s10StockWords 0x36b5b 0x22311 6) 3 s10Data
def s10States := dagTrace s10Mask s10StockWords 3 s10Data
def s10Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f0f0f00f0f0f0f, 0), (0xf0f0f0f0, 28)], [(0xf0f0f0f00000000, 28)])]
def s10Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 4, 2] 0 i.val)
def s10Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 4, 2] 0 i.val)
def s10Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s10Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s10Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s10Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa0a0a0a005050505, 0), (0xa0a0a0a, 3), (0x50505050, 28), (0xa0a0a0a0, 31)], [(0x5050505000000000, 3), (0xa0a0a0a00000000, 28), (0x505050500000000, 31)])]
def s10Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [5, 1, 0, 3, 4, 2] 0 i.val)
def s10Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 5, 3, 4, 0] 0 i.val)
def s10Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa0a0a0a005050505, 0), (0xa0a0a0a00000000, 3), (0xa0a0a0a0, 28), (0xa0a0a0a, 31)], [(0x50505050, 3), (0x505050500000000, 28), (0x5050505000000000, 31)])]
def s10Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 5, 3, 4, 0] 0 i.val)
def s10Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [5, 1, 0, 3, 4, 2] 0 i.val)
def s10Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaaaaaaaa55555555, 0), (0xaaaaaaaa, 31)], [(0x5555555500000000, 31)])]
def s10Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [5, 1, 2, 3, 4, 0] 0 i.val)
def s10Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [5, 1, 2, 3, 4, 0] 0 i.val)
def s10MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s10Move0Stages, s10Move0Map, s10Move0Inverse), (s10Move1Stages, s10Move1Map, s10Move1Inverse), (s10Move2Stages, s10Move2Map, s10Move2Inverse), (s10Move3Stages, s10Move3Map, s10Move3Inverse), (s10Move4Stages, s10Move4Map, s10Move4Inverse)]
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
def s11Mask : Nat := 0xc0c0c0c
abbrev s11Goal : Nat := sGoal &&& s11Mask
abbrev s11StockWords : List Nat := projectDAGStock s11Mask sBase [0, 3, 4]
def s11Fact : (Nat × List Nat × Nat × Nat) := (s11Mask, s11StockWords, 4, s11Goal)
def s11Cuts : List (Nat × List Nat × Nat × Nat) := []
def s11Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[11, 19, 26, 11, 11, 11, 11, 11, 11, 11, 11, 11, 3, 10, 18, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s11Sample : (Nat × Nat) := (0x906806130502c141a0904c060b, 6)
def s11Witnesses := unpackWitnesses s11StockWords [5642, 267779, 534019]
def s11Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s11Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s11Tags := dagTraceTags s11Mask 6 (dagTagBases s11StockWords 0x36b5b 0x22311 6) 3 s11Data
def s11States := dagTrace s11Mask s11StockWords 3 s11Data
def s11Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])]
def s11Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)
def s11Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)
def s11Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])]
def s11Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s11Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s11Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaa000055aa000055, 0), (0xaa000000aa, 7), (0x550000005500, 8), (0xaa000000aa00, 15)], [(0x5500000055000000, 7), (0xaa000000aa0000, 8), (0x55000000550000, 15)])]
def s11Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 0, 3, 5] 0 i.val)
def s11Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 4, 0, 5] 0 i.val)
def s11Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaa000055aa000055, 0), (0xaa000000aa0000, 7), (0xaa000000aa00, 8), (0xaa000000aa, 15)], [(0x550000005500, 7), (0x55000000550000, 8), (0x5500000055000000, 15)])]
def s11Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 4, 0, 5] 0 i.val)
def s11Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 0, 3, 5] 0 i.val)
def s11Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaaaa5555aaaa5555, 0), (0xaaaa0000aaaa, 15)], [(0x5555000055550000, 15)])]
def s11Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s11Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s11MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s11Move0Stages, s11Move0Map, s11Move0Inverse), (s11Move1Stages, s11Move1Map, s11Move1Inverse), (s11Move2Stages, s11Move2Map, s11Move2Inverse), (s11Move3Stages, s11Move3Map, s11Move3Inverse), (s11Move4Stages, s11Move4Map, s11Move4Inverse)]
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
def s12Mask : Nat := 0xc000c000c000c
abbrev s12Goal : Nat := sGoal &&& s12Mask
abbrev s12StockWords : List Nat := projectDAGStock s12Mask sBase [0, 4, 5]
def s12Fact : (Nat × List Nat × Nat × Nat) := (s12Mask, s12StockWords, 4, s12Goal)
def s12Cuts : List (Nat × List Nat × Nat × Nat) := []
def s12Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[19, 35, 50, 19, 19, 19, 19, 19, 19, 19, 19, 19, 3, 18, 34, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s12Sample : (Nat × Nat) := (0x110c806230904c24321108c0613, 6)
def s12Witnesses := unpackWitnesses s12StockWords [9746, 271875, 542211]
def s12Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s12Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s12Tags := dagTraceTags s12Mask 6 (dagTagBases s12StockWords 0x36b5b 0x22311 6) 3 s12Data
def s12States := dagTrace s12Mask s12StockWords 3 s12Data
def s12Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])]
def s12Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s12Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s12Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaaaa5555aaaa5555, 0), (0xaaaa0000aaaa, 15)], [(0x5555000055550000, 15)])]
def s12Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s12Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s12Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaaaa000000005555, 0), (0xaaaa, 15), (0x55550000, 16), (0xaaaa0000, 31)], [(0x5555000000000000, 15), (0xaaaa00000000, 16), (0x555500000000, 31)])]
def s12Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [5, 1, 2, 3, 0, 4] 0 i.val)
def s12Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 5, 0] 0 i.val)
def s12Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaaaa000000005555, 0), (0xaaaa00000000, 15), (0xaaaa0000, 16), (0xaaaa, 31)], [(0x55550000, 15), (0x555500000000, 16), (0x5555000000000000, 31)])]
def s12Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 5, 0] 0 i.val)
def s12Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [5, 1, 2, 3, 0, 4] 0 i.val)
def s12Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaaaaaaaa55555555, 0), (0xaaaaaaaa, 31)], [(0x5555555500000000, 31)])]
def s12Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [5, 1, 2, 3, 4, 0] 0 i.val)
def s12Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [5, 1, 2, 3, 4, 0] 0 i.val)
def s12MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s12Move0Stages, s12Move0Map, s12Move0Inverse), (s12Move1Stages, s12Move1Map, s12Move1Inverse), (s12Move2Stages, s12Move2Map, s12Move2Inverse), (s12Move3Stages, s12Move3Map, s12Move3Inverse), (s12Move4Stages, s12Move4Map, s12Move4Inverse)]
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
def s13Mask : Nat := 0x55550000
abbrev s13Goal : Nat := sGoal &&& s13Mask
abbrev s13StockWords : List Nat := projectDAGStock s13Mask sBase [1, 2, 3]
def s13Fact : (Nat × List Nat × Nat × Nat) := (s13Mask, s13StockWords, 4, s13Goal)
def s13Cuts : List (Nat × List Nat × Nat × Nat) := []
def s13Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[22, 26, 28, 22, 22, 22, 22, 22, 22, 22, 22, 22, 18, 20, 24, 18, 18, 18, 18, 18, 18, 18, 18, 18], rfl⟩
def s13Sample : (Nat × Nat) := (0xc070241a0a058281c0c0682416, 6)
def s13Witnesses := unpackWitnesses s13StockWords [11284, 273426, 537618]
def s13Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s13Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s13Tags := dagTraceTags s13Mask 6 (dagTagBases s13StockWords 0x36b5b 0x22311 6) 3 s13Data
def s13States := dagTrace s13Mask s13StockWords 3 s13Data
def s13Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s13Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s13Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s13Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])]
def s13Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s13Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s13Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc003c003c003c003, 0), (0xc000c000c000c, 2), (0x30003000300030, 4), (0xc000c000c000c0, 6)], [(0x3000300030003000, 2), (0xc000c000c000c00, 4), (0x300030003000300, 6)])]
def s13Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)
def s13Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val)
def s13Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc003c003c003c003, 0), (0xc000c000c000c00, 2), (0xc000c000c000c0, 4), (0xc000c000c000c, 6)], [(0x30003000300030, 2), (0x300030003000300, 4), (0x3000300030003000, 6)])]
def s13Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val)
def s13Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)
def s13Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcc33cc33cc33cc33, 0), (0xcc00cc00cc00cc, 6)], [(0x3300330033003300, 6)])]
def s13Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)
def s13Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)
def s13MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s13Move0Stages, s13Move0Map, s13Move0Inverse), (s13Move1Stages, s13Move1Map, s13Move1Inverse), (s13Move2Stages, s13Move2Map, s13Move2Inverse), (s13Move3Stages, s13Move3Map, s13Move3Inverse), (s13Move4Stages, s13Move4Map, s13Move4Inverse)]
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
def s14Mask : Nat := 0xa000a000a000a
abbrev s14Goal : Nat := sGoal &&& s14Mask
abbrev s14StockWords : List Nat := projectDAGStock s14Mask sBase [1, 4, 5]
def s14Fact : (Nat × List Nat × Nat × Nat) := (s14Mask, s14StockWords, 4, s14Goal)
def s14Cuts : List (Nat × List Nat × Nat × Nat) := []
def s14Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[19, 35, 49, 19, 19, 19, 19, 19, 19, 19, 19, 19, 3, 17, 33, 3, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s14Sample : (Nat × Nat) := (0x108c406230884c22311088c0613, 6)
def s14Witnesses := unpackWitnesses s14StockWords [9745, 271875, 542211]
def s14Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s14Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s14Tags := dagTraceTags s14Mask 6 (dagTagBases s14StockWords 0x36b5b 0x22311 6) 3 s14Data
def s14States := dagTrace s14Mask s14StockWords 3 s14Data
def s14Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])]
def s14Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s14Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s14Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])]
def s14Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s14Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s14Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc000000003333, 0), (0xcccc, 14), (0x33330000, 16), (0xcccc0000, 30)], [(0x3333000000000000, 14), (0xcccc00000000, 16), (0x333300000000, 30)])]
def s14Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 5, 2, 3, 1, 4] 0 i.val)
def s14Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 5, 1] 0 i.val)
def s14Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc000000003333, 0), (0xcccc00000000, 14), (0xcccc0000, 16), (0xcccc, 30)], [(0x33330000, 14), (0x333300000000, 16), (0x3333000000000000, 30)])]
def s14Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 5, 1] 0 i.val)
def s14Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 5, 2, 3, 1, 4] 0 i.val)
def s14Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccccccc33333333, 0), (0xcccccccc, 30)], [(0x3333333300000000, 30)])]
def s14Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 5, 2, 3, 4, 1] 0 i.val)
def s14Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 5, 2, 3, 4, 1] 0 i.val)
def s14MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s14Move0Stages, s14Move0Map, s14Move0Inverse), (s14Move1Stages, s14Move1Map, s14Move1Inverse), (s14Move2Stages, s14Move2Map, s14Move2Inverse), (s14Move3Stages, s14Move3Map, s14Move3Inverse), (s14Move4Stages, s14Move4Map, s14Move4Inverse)]
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
theorem s14RootBlock0 : treeBlock 0 8 s14RootAt = true := by decide +kernel
theorem s14Roots : dagCheckRoots s14Mask s14Goal s14Chart (dagKnownCloses s14Goal s14Cuts) s14Witnesses (dagRef 1 s14States s14Moves s14Links 0) s14StockWords 3 = true := s14RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Block0 : treeBlock 0 1 s14Check = true := by decide +kernel
theorem s14Blocks : treeBlock 0 1 s14Check = true := s14Block0
theorem s14Known : Known s14Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
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
    exact False.elim h
def s15Mask : Nat := 0x44444444
abbrev s15Goal : Nat := sGoal &&& s15Mask
abbrev s15StockWords : List Nat := projectDAGStock s15Mask sBase [2, 3, 4]
def s15Fact : (Nat × List Nat × Nat × Nat) := (s15Mask, s15StockWords, 4, s15Goal)
def s15Cuts : List (Nat × List Nat × Nat × Nat) := []
def s15Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[14, 22, 26, 14, 14, 14, 14, 14, 14, 14, 14, 14, 6, 10, 18, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩
def s15Sample : (Nat × Nat) := (0x90680c1605038141a090580c0e, 6)
def s15Witnesses := unpackWitnesses s15StockWords [7178, 269318, 535558]
def s15Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s15Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s15Tags := dagTraceTags s15Mask 6 (dagTagBases s15StockWords 0x36b5b 0x22311 6) 3 s15Data
def s15States := dagTrace s15Mask s15StockWords 3 s15Data
def s15Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])]
def s15Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)
def s15Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)
def s15Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s15Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s15Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s15Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf000000ff000000f, 0), (0xf0000000f0, 4), (0xf0000000f00, 8), (0xf0000000f000, 12)], [(0xf0000000f000000, 4), (0xf0000000f00000, 8), (0xf0000000f0000, 12)])]
def s15Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 2, 3, 5] 0 i.val)
def s15Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 4, 2, 5] 0 i.val)
def s15Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf000000ff000000f, 0), (0xf0000000f00000, 4), (0xf0000000f000, 8), (0xf0000000f0, 12)], [(0xf0000000f00, 4), (0xf0000000f0000, 8), (0xf0000000f000000, 12)])]
def s15Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 4, 2, 5] 0 i.val)
def s15Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 2, 3, 5] 0 i.val)
def s15Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])]
def s15Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s15Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s15MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s15Move0Stages, s15Move0Map, s15Move0Inverse), (s15Move1Stages, s15Move1Map, s15Move1Inverse), (s15Move2Stages, s15Move2Map, s15Move2Inverse), (s15Move3Stages, s15Move3Map, s15Move3Inverse), (s15Move4Stages, s15Move4Map, s15Move4Inverse)]
def s15Moves := dagMoves s15MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Autos : DagMovesOK s15Mask s15Goal 64 s15Moves := dagMovesOfCheck (by decide +kernel)
def s15Check := dagCheckNode s15Mask s15Goal s15Chart (dagKnownCloses s15Goal s15Cuts) 1 s15States s15Moves s15Links s15Sample s15Tags
def s15RootAt (token : Nat) : Bool :=
  let s := rootState s15StockWords 3 token
  !dagAllowedRoot s15Witnesses s.2.1 || dagLocal s15Mask s15Goal s15Chart (dagKnownCloses s15Goal s15Cuts) s ||
  dagRef 1 s15States s15Moves s15Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15RootBlock0 : treeBlock 0 8 s15RootAt = true := by decide +kernel
theorem s15Roots : dagCheckRoots s15Mask s15Goal s15Chart (dagKnownCloses s15Goal s15Cuts) s15Witnesses (dagRef 1 s15States s15Moves s15Links 0) s15StockWords 3 = true := s15RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Block0 : treeBlock 0 1 s15Check = true := by decide +kernel
theorem s15Blocks : treeBlock 0 1 s15Check = true := s15Block0
theorem s15Known : Known s15Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Stock : Lower s15Mask s15StockWords s15Goal 4 := by
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
    exact False.elim h
def s16Mask : Nat := 0x44004400440044
abbrev s16Goal : Nat := sGoal &&& s16Mask
abbrev s16StockWords : List Nat := projectDAGStock s16Mask sBase [2, 4, 5]
def s16Fact : (Nat × List Nat × Nat × Nat) := (s16Mask, s16StockWords, 4, s16Goal)
def s16Cuts : List (Nat × List Nat × Nat × Nat) := []
def s16Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[22, 38, 50, 22, 22, 22, 22, 22, 22, 22, 22, 22, 6, 18, 34, 6, 6, 6, 6, 6, 6, 6, 6, 6], rfl⟩
def s16Sample : (Nat × Nat) := (0x110c80c26090582432110980c16, 6)
def s16Witnesses := unpackWitnesses s16StockWords [11282, 273414, 543750]
def s16Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9 0x7 2 1 3 1 3 1
def s16Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s16Tags := dagTraceTags s16Mask 6 (dagTagBases s16StockWords 0x36b5b 0x22311 6) 3 s16Data
def s16States := dagTrace s16Mask s16StockWords 3 s16Data
def s16Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])]
def s16Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s16Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s16Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])]
def s16Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s16Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s16Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f0000000000f0f, 0), (0xf0f0, 12), (0xf0f0000, 16), (0xf0f00000, 28)], [(0xf0f000000000000, 12), (0xf0f000000000, 16), (0xf0f00000000, 28)])]
def s16Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 2, 4] 0 i.val)
def s16Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 5, 2] 0 i.val)
def s16Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f0000000000f0f, 0), (0xf0f000000000, 12), (0xf0f00000, 16), (0xf0f0, 28)], [(0xf0f0000, 12), (0xf0f00000000, 16), (0xf0f000000000000, 28)])]
def s16Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 5, 2] 0 i.val)
def s16Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 2, 4] 0 i.val)
def s16Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f0f0f00f0f0f0f, 0), (0xf0f0f0f0, 28)], [(0xf0f0f0f00000000, 28)])]
def s16Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 4, 2] 0 i.val)
def s16Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 4, 2] 0 i.val)
def s16MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s16Move0Stages, s16Move0Map, s16Move0Inverse), (s16Move1Stages, s16Move1Map, s16Move1Inverse), (s16Move2Stages, s16Move2Map, s16Move2Inverse), (s16Move3Stages, s16Move3Map, s16Move3Inverse), (s16Move4Stages, s16Move4Map, s16Move4Inverse)]
def s16Moves := dagMoves s16MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Autos : DagMovesOK s16Mask s16Goal 64 s16Moves := dagMovesOfCheck (by decide +kernel)
def s16Check := dagCheckNode s16Mask s16Goal s16Chart (dagKnownCloses s16Goal s16Cuts) 1 s16States s16Moves s16Links s16Sample s16Tags
def s16RootAt (token : Nat) : Bool :=
  let s := rootState s16StockWords 3 token
  !dagAllowedRoot s16Witnesses s.2.1 || dagLocal s16Mask s16Goal s16Chart (dagKnownCloses s16Goal s16Cuts) s ||
  dagRef 1 s16States s16Moves s16Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16RootBlock0 : treeBlock 0 8 s16RootAt = true := by decide +kernel
theorem s16Roots : dagCheckRoots s16Mask s16Goal s16Chart (dagKnownCloses s16Goal s16Cuts) s16Witnesses (dagRef 1 s16States s16Moves s16Links 0) s16StockWords 3 = true := s16RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Block0 : treeBlock 0 1 s16Check = true := by decide +kernel
theorem s16Blocks : treeBlock 0 1 s16Check = true := s16Block0
theorem s16Known : Known s16Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Stock : Lower s16Mask s16StockWords s16Goal 4 := by
  apply lowerDag _ _ _ _ s16Autos _ _ _ s16Known _ s16Roots s16Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s16StockWords; decide +kernel
  · decide +kernel
  · simp only [s16Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s17Mask : Nat := 0xffff0000
abbrev s17Goal : Nat := sGoal &&& s17Mask
abbrev s17StockWords : List Nat := projectDAGStock s17Mask sBase [0, 1, 2, 3]
def s17Fact : (Nat × List Nat × Nat × Nat) := (s17Mask, s17StockWords, 7, s17Goal)
def s17Cuts : List (Nat × List Nat × Nat × Nat) := [s1Fact, s13Fact, s2Fact, s7Fact]
def s17Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[19, 21, 22, 25, 26, 28, 19, 19, 19, 19, 19, 19, 17, 18, 20, 24, 17, 17, 17, 17, 17, 17, 17, 17], rfl⟩
def s17Sample : (Nat × Nat) := (0xa05822190c07028150884c301a0c06424160a07022150904c241a, 12)
def s17Witnesses := unpackWitnesses s17StockWords [9746, 271889, 535057, 799249]
def s17Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x1c0c9e4303719a4c242e4702cc3401 0x2b92c0b620323140932815010386290831e07029740110501c743366432a140360402a3292c22620023140a92c2662b816200632b8331f613143302b2301f03013010080000f 9 4 12 4 4 4
def s17Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x620b92c1328931e7029732b101c502a401313142008100f0 i
def s17Tags := dagTraceTags s17Mask 12 (dagTagBases s17StockWords 0x669b1c8d35a6 0x260908013484 12) 6 s17Data
def s17States := dagTrace s17Mask s17StockWords 6 s17Data
def s17Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s17Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s17Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s17Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])]
def s17Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s17Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)
def s17Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc003c003c003c003, 0), (0xc000c000c000c, 2), (0x30003000300030, 4), (0xc000c000c000c0, 6)], [(0x3000300030003000, 2), (0xc000c000c000c00, 4), (0x300030003000300, 6)])]
def s17Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)
def s17Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val)
def s17Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc003c003c003c003, 0), (0xc000c000c000c00, 2), (0xc000c000c000c0, 4), (0xc000c000c000c, 6)], [(0x30003000300030, 2), (0x300030003000300, 4), (0x3000300030003000, 6)])]
def s17Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val)
def s17Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)
def s17Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcc33cc33cc33cc33, 0), (0xcc00cc00cc00cc, 6)], [(0x3300330033003300, 6)])]
def s17Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)
def s17Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 3, 2, 1, 4, 5] 0 i.val)
def s17Move5Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])]
def s17Move5Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s17Move5Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s17Move6Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9009900990099009, 0), (0x2002200220022002, 1), (0x40004000400040, 3), (0x90009000900090, 4), (0x20002000200020, 5)], [(0x4004400440044004, 1), (0x200020002000200, 3), (0x900090009000900, 4), (0x400040004000400, 5)])]
def s17Move6Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)
def s17Move6Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)
def s17Move7Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s17Move7Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s17Move7Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s17MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s17Move0Stages, s17Move0Map, s17Move0Inverse), (s17Move1Stages, s17Move1Map, s17Move1Inverse), (s17Move2Stages, s17Move2Map, s17Move2Inverse), (s17Move3Stages, s17Move3Map, s17Move3Inverse), (s17Move4Stages, s17Move4Map, s17Move4Inverse), (s17Move5Stages, s17Move5Map, s17Move5Inverse), (s17Move6Stages, s17Move6Map, s17Move6Inverse), (s17Move7Stages, s17Move7Map, s17Move7Inverse)]
def s17Moves := dagMoves s17MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Autos : DagMovesOK s17Mask s17Goal 64 s17Moves := dagMovesOfCheck (by decide +kernel)
def s17Check := dagCheckNode s17Mask s17Goal s17Chart (dagKnownCloses s17Goal s17Cuts) 12 s17States s17Moves s17Links s17Sample s17Tags
def s17RootAt (token : Nat) : Bool :=
  let s := rootState s17StockWords 6 token
  !dagAllowedRoot s17Witnesses s.2.1 || dagLocal s17Mask s17Goal s17Chart (dagKnownCloses s17Goal s17Cuts) s ||
  dagRef 12 s17States s17Moves s17Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17RootBlock0 : treeBlock 0 16 s17RootAt = true := by decide +kernel
theorem s17Roots : dagCheckRoots s17Mask s17Goal s17Chart (dagKnownCloses s17Goal s17Cuts) s17Witnesses (dagRef 12 s17States s17Moves s17Links 0) s17StockWords 6 = true := s17RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Block0 : treeBlock 0 12 s17Check = true := by decide +kernel
theorem s17Blocks : treeBlock 0 12 s17Check = true := s17Block0
theorem s17Known : Known s17Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s7Stock) s2Stock) s13Stock) s1Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Stock : Lower s17Mask s17StockWords s17Goal 7 := by
  apply lowerDag _ _ _ _ s17Autos _ _ _ s17Known _ s17Roots s17Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s17StockWords; decide +kernel
  · decide +kernel
  · simp only [s17Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s18Mask : Nat := 0xf000f000f000f
abbrev s18Goal : Nat := sGoal &&& s18Mask
abbrev s18StockWords : List Nat := projectDAGStock s18Mask sBase [0, 1, 4, 5]
def s18Fact : (Nat × List Nat × Nat × Nat) := (s18Mask, s18StockWords, 7, s18Goal)
def s18Cuts : List (Nat × List Nat × Nat × Nat) := [s3Fact, s14Fact, s4Fact, s12Fact]
def s18Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[19, 35, 49, 50, 19, 19, 19, 19, 19, 19, 19, 19, 3, 17, 18, 33, 34, 48, 3, 3, 3, 3, 3, 3], rfl⟩
def s18Sample : (Nat × Nat) := (0x1088c24321108c0613180c824130884c42310188c4432180c42231, 12)
def s18Witnesses := unpackWitnesses s18StockWords [9746, 271889, 534019, 804355]
def s18Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x1c0c9e4303719a4c242e4702cc3401 0x2b92c0b6203231409930153243893108626070317401905624746326462614332043263292c22620023140a92c2662781620063278331b61314330272301b0300f010080000f 9 4 12 4 4 4
def s18Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x620b92c193096267031732716245326400f13142008100f0 i
def s18Tags := dagTraceTags s18Mask 12 (dagTagBases s18StockWords 0xe9f5f7fecb7b 0xa964e374c939 12) 6 s18Data
def s18States := dagTrace s18Mask s18StockWords 6 s18Data
def s18Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])]
def s18Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s18Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s18Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])]
def s18Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s18Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s18Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc000000003333, 0), (0xcccc, 14), (0x33330000, 16), (0xcccc0000, 30)], [(0x3333000000000000, 14), (0xcccc00000000, 16), (0x333300000000, 30)])]
def s18Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 5, 2, 3, 1, 4] 0 i.val)
def s18Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 5, 1] 0 i.val)
def s18Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc000000003333, 0), (0xcccc00000000, 14), (0xcccc0000, 16), (0xcccc, 30)], [(0x33330000, 14), (0x333300000000, 16), (0x3333000000000000, 30)])]
def s18Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 5, 1] 0 i.val)
def s18Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 5, 2, 3, 1, 4] 0 i.val)
def s18Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccccccc33333333, 0), (0xcccccccc, 30)], [(0x3333333300000000, 30)])]
def s18Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 5, 2, 3, 4, 1] 0 i.val)
def s18Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 5, 2, 3, 4, 1] 0 i.val)
def s18Move5Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])]
def s18Move5Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s18Move5Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s18Move6Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9999000000009999, 0), (0x2222000000002222, 1), (0x44440000, 15), (0x99990000, 16), (0x22220000, 17)], [(0x4444000000004444, 1), (0x222200000000, 15), (0x999900000000, 16), (0x444400000000, 17)])]
def s18Move6Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 5, 4] 0 i.val)
def s18Move6Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 5, 4] 0 i.val)
def s18Move7Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaaaa5555aaaa5555, 0), (0xaaaa0000aaaa, 15)], [(0x5555000055550000, 15)])]
def s18Move7Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s18Move7Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s18MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s18Move0Stages, s18Move0Map, s18Move0Inverse), (s18Move1Stages, s18Move1Map, s18Move1Inverse), (s18Move2Stages, s18Move2Map, s18Move2Inverse), (s18Move3Stages, s18Move3Map, s18Move3Inverse), (s18Move4Stages, s18Move4Map, s18Move4Inverse), (s18Move5Stages, s18Move5Map, s18Move5Inverse), (s18Move6Stages, s18Move6Map, s18Move6Inverse), (s18Move7Stages, s18Move7Map, s18Move7Inverse)]
def s18Moves := dagMoves s18MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Autos : DagMovesOK s18Mask s18Goal 64 s18Moves := dagMovesOfCheck (by decide +kernel)
def s18Check := dagCheckNode s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) 12 s18States s18Moves s18Links s18Sample s18Tags
def s18RootAt (token : Nat) : Bool :=
  let s := rootState s18StockWords 6 token
  !dagAllowedRoot s18Witnesses s.2.1 || dagLocal s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) s ||
  dagRef 12 s18States s18Moves s18Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18RootBlock0 : treeBlock 0 16 s18RootAt = true := by decide +kernel
theorem s18Roots : dagCheckRoots s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) s18Witnesses (dagRef 12 s18States s18Moves s18Links 0) s18StockWords 6 = true := s18RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Block0 : treeBlock 0 12 s18Check = true := by decide +kernel
theorem s18Blocks : treeBlock 0 12 s18Check = true := s18Block0
theorem s18Known : Known s18Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s12Stock) s4Stock) s14Stock) s3Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Stock : Lower s18Mask s18StockWords s18Goal 7 := by
  apply lowerDag _ _ _ _ s18Autos _ _ _ s18Known _ s18Roots s18Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s18StockWords; decide +kernel
  · decide +kernel
  · simp only [s18Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s19Mask : Nat := 0xcccccccc
abbrev s19Goal : Nat := sGoal &&& s19Mask
abbrev s19StockWords : List Nat := projectDAGStock s19Mask sBase [0, 2, 3, 4]
def s19Fact : (Nat × List Nat × Nat × Nat) := (s19Mask, s19StockWords, 7, s19Goal)
def s19Cuts : List (Nat × List Nat × Nat × Nat) := [s8Fact, s15Fact, s9Fact, s11Fact]
def s19Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[7, 11, 14, 19, 22, 26, 7, 7, 7, 7, 7, 7, 3, 6, 10, 18, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s19Sample : (Nat × Nat) := (0x5038061309068140b0181c24160904c0c0e05068060b0301c0c16, 12)
def s19Witnesses := unpackWitnesses s19StockWords [3590, 265731, 529923, 796163]
def s19Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x1c0c9e4303719a4c242e4702cc3401 0x2b92c0b620323140932815010386290831e07029740110501c743366432a140360402a3292c22620023140a92c2662b816200632b8331f613143302b2301f03013010080000f 9 4 12 4 4 4
def s19Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x620b92c1328931e7029732b101c502a401313142008100f0 i
def s19Tags := dagTraceTags s19Mask 12 (dagTagBases s19StockWords 0x669b1c8d35a6 0x260908013484 12) 6 s19Data
def s19States := dagTrace s19Mask s19StockWords 6 s19Data
def s19Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])]
def s19Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)
def s19Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)
def s19Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s19Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s19Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s19Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf000000ff000000f, 0), (0xf0000000f0, 4), (0xf0000000f00, 8), (0xf0000000f000, 12)], [(0xf0000000f000000, 4), (0xf0000000f00000, 8), (0xf0000000f0000, 12)])]
def s19Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 2, 3, 5] 0 i.val)
def s19Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 4, 2, 5] 0 i.val)
def s19Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf000000ff000000f, 0), (0xf0000000f00000, 4), (0xf0000000f000, 8), (0xf0000000f0, 12)], [(0xf0000000f00, 4), (0xf0000000f0000, 8), (0xf0000000f000000, 12)])]
def s19Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 4, 2, 5] 0 i.val)
def s19Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 2, 3, 5] 0 i.val)
def s19Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])]
def s19Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s19Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s19Move5Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s19Move5Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s19Move5Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s19Move6Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa50000a5a50000a5, 0), (0xa00000a0a00000a, 3), (0x500000005000, 5), (0xa5000000a500, 8), (0xa0000000a00, 11)], [(0x5000005050000050, 3), (0xa0000000a0000, 5), (0xa5000000a50000, 8), (0x50000000500000, 11)])]
def s19Move6Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 4, 3, 5] 0 i.val)
def s19Move6Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 4, 3, 5] 0 i.val)
def s19Move7Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])]
def s19Move7Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s19Move7Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s19MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s19Move0Stages, s19Move0Map, s19Move0Inverse), (s19Move1Stages, s19Move1Map, s19Move1Inverse), (s19Move2Stages, s19Move2Map, s19Move2Inverse), (s19Move3Stages, s19Move3Map, s19Move3Inverse), (s19Move4Stages, s19Move4Map, s19Move4Inverse), (s19Move5Stages, s19Move5Map, s19Move5Inverse), (s19Move6Stages, s19Move6Map, s19Move6Inverse), (s19Move7Stages, s19Move7Map, s19Move7Inverse)]
def s19Moves := dagMoves s19MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Autos : DagMovesOK s19Mask s19Goal 64 s19Moves := dagMovesOfCheck (by decide +kernel)
def s19Check := dagCheckNode s19Mask s19Goal s19Chart (dagKnownCloses s19Goal s19Cuts) 12 s19States s19Moves s19Links s19Sample s19Tags
def s19RootAt (token : Nat) : Bool :=
  let s := rootState s19StockWords 6 token
  !dagAllowedRoot s19Witnesses s.2.1 || dagLocal s19Mask s19Goal s19Chart (dagKnownCloses s19Goal s19Cuts) s ||
  dagRef 12 s19States s19Moves s19Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19RootBlock0 : treeBlock 0 16 s19RootAt = true := by decide +kernel
theorem s19Roots : dagCheckRoots s19Mask s19Goal s19Chart (dagKnownCloses s19Goal s19Cuts) s19Witnesses (dagRef 12 s19States s19Moves s19Links 0) s19StockWords 6 = true := s19RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Block0 : treeBlock 0 12 s19Check = true := by decide +kernel
theorem s19Blocks : treeBlock 0 12 s19Check = true := s19Block0
theorem s19Known : Known s19Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s11Stock) s9Stock) s15Stock) s8Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Stock : Lower s19Mask s19StockWords s19Goal 7 := by
  apply lowerDag _ _ _ _ s19Autos _ _ _ s19Known _ s19Roots s19Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s19StockWords; decide +kernel
  · decide +kernel
  · simp only [s19Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s20Mask : Nat := 0xcc00cc00cc00cc
abbrev s20Goal : Nat := sGoal &&& s20Mask
abbrev s20StockWords : List Nat := projectDAGStock s20Mask sBase [0, 2, 4, 5]
def s20Fact : (Nat × List Nat × Nat × Nat) := (s20Mask, s20StockWords, 7, s20Goal)
def s20Cuts : List (Nat × List Nat × Nat × Nat) := [s9Fact, s16Fact, s10Fact, s12Fact]
def s20Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[7, 19, 22, 35, 38, 50, 7, 7, 7, 7, 7, 7, 3, 6, 18, 34, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s20Sample : (Nat × Nat) := (0x90580623110c824130181c44261108c0c16090c806130301c0c26, 12)
def s20Witnesses := unpackWitnesses s20StockWords [3590, 265731, 534019, 804355]
def s20Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x1c0c9e4303719a4c242e4702cc3401 0x2b92c0b620323140932815010386290831e07029740110501c743366432a140360402a3292c22620023140a92c2662b816200632b8331f613143302b2301f03013010080000f 9 4 12 4 4 4
def s20Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x620b92c1328931e7029732b101c502a401313142008100f0 i
def s20Tags := dagTraceTags s20Mask 12 (dagTagBases s20StockWords 0x669b1c8d35a6 0x260908013484 12) 6 s20Data
def s20States := dagTrace s20Mask s20StockWords 6 s20Data
def s20Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])]
def s20Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s20Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s20Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])]
def s20Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s20Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s20Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f0000000000f0f, 0), (0xf0f0, 12), (0xf0f0000, 16), (0xf0f00000, 28)], [(0xf0f000000000000, 12), (0xf0f000000000, 16), (0xf0f00000000, 28)])]
def s20Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 2, 4] 0 i.val)
def s20Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 5, 2] 0 i.val)
def s20Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f0000000000f0f, 0), (0xf0f000000000, 12), (0xf0f00000, 16), (0xf0f0, 28)], [(0xf0f0000, 12), (0xf0f00000000, 16), (0xf0f000000000000, 28)])]
def s20Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 5, 2] 0 i.val)
def s20Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 2, 4] 0 i.val)
def s20Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f0f0f00f0f0f0f, 0), (0xf0f0f0f0, 28)], [(0xf0f0f0f00000000, 28)])]
def s20Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 4, 2] 0 i.val)
def s20Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 4, 2] 0 i.val)
def s20Move5Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s20Move5Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s20Move5Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s20Move6Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a500000000a5a5, 0), (0xa0a000000000a0a, 3), (0x50500000, 13), (0xa5a50000, 16), (0xa0a0000, 19)], [(0x5050000000005050, 3), (0xa0a00000000, 13), (0xa5a500000000, 16), (0x505000000000, 19)])]
def s20Move6Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 5, 4] 0 i.val)
def s20Move6Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 5, 4] 0 i.val)
def s20Move7Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaaaa5555aaaa5555, 0), (0xaaaa0000aaaa, 15)], [(0x5555000055550000, 15)])]
def s20Move7Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s20Move7Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s20MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s20Move0Stages, s20Move0Map, s20Move0Inverse), (s20Move1Stages, s20Move1Map, s20Move1Inverse), (s20Move2Stages, s20Move2Map, s20Move2Inverse), (s20Move3Stages, s20Move3Map, s20Move3Inverse), (s20Move4Stages, s20Move4Map, s20Move4Inverse), (s20Move5Stages, s20Move5Map, s20Move5Inverse), (s20Move6Stages, s20Move6Map, s20Move6Inverse), (s20Move7Stages, s20Move7Map, s20Move7Inverse)]
def s20Moves := dagMoves s20MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Autos : DagMovesOK s20Mask s20Goal 64 s20Moves := dagMovesOfCheck (by decide +kernel)
def s20Check := dagCheckNode s20Mask s20Goal s20Chart (dagKnownCloses s20Goal s20Cuts) 12 s20States s20Moves s20Links s20Sample s20Tags
def s20RootAt (token : Nat) : Bool :=
  let s := rootState s20StockWords 6 token
  !dagAllowedRoot s20Witnesses s.2.1 || dagLocal s20Mask s20Goal s20Chart (dagKnownCloses s20Goal s20Cuts) s ||
  dagRef 12 s20States s20Moves s20Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20RootBlock0 : treeBlock 0 16 s20RootAt = true := by decide +kernel
theorem s20Roots : dagCheckRoots s20Mask s20Goal s20Chart (dagKnownCloses s20Goal s20Cuts) s20Witnesses (dagRef 12 s20States s20Moves s20Links 0) s20StockWords 6 = true := s20RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Block0 : treeBlock 0 12 s20Check = true := by decide +kernel
theorem s20Blocks : treeBlock 0 12 s20Check = true := s20Block0
theorem s20Known : Known s20Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s12Stock) s10Stock) s16Stock) s9Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Stock : Lower s20Mask s20StockWords s20Goal 7 := by
  apply lowerDag _ _ _ _ s20Autos _ _ _ s20Known _ s20Roots s20Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s20StockWords; decide +kernel
  · decide +kernel
  · simp only [s20Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s21Mask : Nat := 0xffff00000000
abbrev s21Goal : Nat := sGoal &&& s21Mask
abbrev s21StockWords : List Nat := projectDAGStock s21Mask sBase [0, 1, 2, 3]
def s21Fact : (Nat × List Nat × Nat × Nat) := (s21Mask, s21StockWords, 5, s21Goal)
def s21Witnesses := unpackWitnesses s21StockWords [17954, 280097, 543265, 807457]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Stock : Lower s21Mask s21StockWords s21Goal 5 := by
  apply essentialLift (witnesses := s21Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s22Mask : Nat := 0xff00ff
abbrev s22Goal : Nat := sGoal &&& s22Mask
abbrev s22StockWords : List Nat := projectDAGStock s22Mask sBase [0, 1, 2, 4]
def s22Fact : (Nat × List Nat × Nat × Nat) := (s22Mask, s22StockWords, 5, s22Goal)
def s22Witnesses := unpackWitnesses s22StockWords [2564, 271889, 526849, 796163]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Stock : Lower s22Mask s22StockWords s22Goal 5 := by
  apply essentialLift (witnesses := s22Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
def s23Mask : Nat := 0xff00ff00000000
abbrev s23Goal : Nat := sGoal &&& s23Mask
abbrev s23StockWords : List Nat := projectDAGStock s23Mask sBase [0, 1, 2, 4]
def s23Fact : (Nat × List Nat × Nat × Nat) := (s23Mask, s23StockWords, 5, s23Goal)
def s23Witnesses := unpackWitnesses s23StockWords [17954, 280097, 543265, 811553]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Stock : Lower s23Mask s23StockWords s23Goal 5 := by
  apply essentialLift (witnesses := s23Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s24Mask : Nat := 0xff000000ff
abbrev s24Goal : Nat := sGoal &&& s24Mask
abbrev s24StockWords : List Nat := projectDAGStock s24Mask sBase [0, 1, 2, 5]
def s24Fact : (Nat × List Nat × Nat × Nat) := (s24Mask, s24StockWords, 5, s24Goal)
def s24Witnesses := unpackWitnesses s24StockWords [2564, 280097, 526849, 804355]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Stock : Lower s24Mask s24StockWords s24Goal 5 := by
  apply essentialLift (witnesses := s24Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s25Mask : Nat := 0xf0f0f0f00000000
abbrev s25Goal : Nat := sGoal &&& s25Mask
abbrev s25StockWords : List Nat := projectDAGStock s25Mask sBase [0, 1, 3, 4]
def s25Fact : (Nat × List Nat × Nat × Nat) := (s25Mask, s25StockWords, 5, s25Goal)
def s25Witnesses := unpackWitnesses s25StockWords [17954, 280097, 545313, 811553]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Stock : Lower s25Mask s25StockWords s25Goal 5 := by
  apply essentialLift (witnesses := s25Witnesses) (cut := s3Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s3StockWords) (by decide +kernel)
  · exact s3Stock
  · decide +kernel
def s26Mask : Nat := 0x3333333300000000
abbrev s26Goal : Nat := sGoal &&& s26Mask
abbrev s26StockWords : List Nat := projectDAGStock s26Mask sBase [0, 2, 3, 4]
def s26Fact : (Nat × List Nat × Nat × Nat) := (s26Mask, s26StockWords, 5, s26Goal)
def s26Witnesses := unpackWitnesses s26StockWords [18980, 281121, 545313, 811553]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Stock : Lower s26Mask s26StockWords s26Goal 5 := by
  apply essentialLift (witnesses := s26Witnesses) (cut := s6Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s6StockWords) (by decide +kernel)
  · exact s6Stock
  · decide +kernel
def s27Mask : Nat := 0x3333000033330000
abbrev s27Goal : Nat := sGoal &&& s27Mask
abbrev s27StockWords : List Nat := projectDAGStock s27Mask sBase [0, 2, 3, 5]
def s27Fact : (Nat × List Nat × Nat × Nat) := (s27Mask, s27StockWords, 5, s27Goal)
def s27Witnesses := unpackWitnesses s27StockWords [10772, 272913, 537105, 811537]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Stock : Lower s27Mask s27StockWords s27Goal 5 := by
  apply essentialLift (witnesses := s27Witnesses) (cut := s7Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s7StockWords) (by decide +kernel)
  · exact s7Stock
  · decide +kernel
def s28Mask : Nat := 0xcccc0000cccc
abbrev s28Goal : Nat := sGoal &&& s28Mask
abbrev s28StockWords : List Nat := projectDAGStock s28Mask sBase [0, 2, 3, 5]
def s28Fact : (Nat × List Nat × Nat × Nat) := (s28Mask, s28StockWords, 5, s28Goal)
def s28Witnesses := unpackWitnesses s28StockWords [3590, 265731, 529923, 804355]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Stock : Lower s28Mask s28StockWords s28Goal 5 := by
  apply essentialLift (witnesses := s28Witnesses) (cut := s8Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s8StockWords) (by decide +kernel)
  · exact s8Stock
  · decide +kernel
def s29Mask : Nat := 0x55555555
abbrev s29Goal : Nat := sGoal &&& s29Mask
abbrev s29StockWords : List Nat := projectDAGStock s29Mask sBase [1, 2, 3, 4]
def s29Fact : (Nat × List Nat × Nat × Nat) := (s29Mask, s29StockWords, 5, s29Goal)
def s29Witnesses := unpackWitnesses s29StockWords [11284, 268296, 530436, 797702]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Stock : Lower s29Mask s29StockWords s29Goal 5 := by
  apply essentialLift (witnesses := s29Witnesses) (cut := s13Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s13StockWords) (by decide +kernel)
  · exact s13Stock
  · decide +kernel
def s30Mask : Nat := 0x5555000055550000
abbrev s30Goal : Nat := sGoal &&& s30Mask
abbrev s30StockWords : List Nat := projectDAGStock s30Mask sBase [1, 2, 3, 5]
def s30Fact : (Nat × List Nat × Nat × Nat) := (s30Mask, s30StockWords, 5, s30Goal)
def s30Witnesses := unpackWitnesses s30StockWords [11284, 273426, 537618, 812050]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Stock : Lower s30Mask s30StockWords s30Goal 5 := by
  apply essentialLift (witnesses := s30Witnesses) (cut := s13Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s13StockWords) (by decide +kernel)
  · exact s13Stock
  · decide +kernel
def s31Mask : Nat := 0x55005500550055
abbrev s31Goal : Nat := sGoal &&& s31Mask
abbrev s31StockWords : List Nat := projectDAGStock s31Mask sBase [1, 2, 4, 5]
def s31Fact : (Nat × List Nat × Nat × Nat) := (s31Mask, s31StockWords, 5, s31Goal)
def s31Witnesses := unpackWitnesses s31StockWords [11284, 273426, 535558, 805894]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Stock : Lower s31Mask s31StockWords s31Goal 5 := by
  apply essentialLift (witnesses := s31Witnesses) (cut := s16Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s16StockWords) (by decide +kernel)
  · exact s16Stock
  · decide +kernel
def s32Mask : Nat := 0xaa00aa00aa00aa
abbrev s32Goal : Nat := sGoal &&& s32Mask
abbrev s32StockWords : List Nat := projectDAGStock s32Mask sBase [1, 2, 4, 5]
def s32Fact : (Nat × List Nat × Nat × Nat) := (s32Mask, s32StockWords, 5, s32Goal)
def s32Witnesses := unpackWitnesses s32StockWords [9745, 264705, 534019, 804355]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Stock : Lower s32Mask s32StockWords s32Goal 5 := by
  apply essentialLift (witnesses := s32Witnesses) (cut := s14Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s14StockWords) (by decide +kernel)
  · exact s14Stock
  · decide +kernel
def s33Mask : Nat := 0xa0a0a0a0a0a0a0a
abbrev s33Goal : Nat := sGoal &&& s33Mask
abbrev s33StockWords : List Nat := projectDAGStock s33Mask sBase [1, 3, 4, 5]
def s33Fact : (Nat × List Nat × Nat × Nat) := (s33Mask, s33StockWords, 5, s33Goal)
def s33Witnesses := unpackWitnesses s33StockWords [9745, 266753, 534019, 804355]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Stock : Lower s33Mask s33StockWords s33Goal 5 := by
  apply essentialLift (witnesses := s33Witnesses) (cut := s14Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s14StockWords) (by decide +kernel)
  · exact s14Stock
  · decide +kernel
def s34Mask : Nat := 0x4444444444444444
abbrev s34Goal : Nat := sGoal &&& s34Mask
abbrev s34StockWords : List Nat := projectDAGStock s34Mask sBase [2, 3, 4, 5]
def s34Fact : (Nat × List Nat × Nat × Nat) := (s34Mask, s34StockWords, 5, s34Goal)
def s34Witnesses := unpackWitnesses s34StockWords [7178, 269318, 535558, 805894]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Stock : Lower s34Mask s34StockWords s34Goal 5 := by
  apply essentialLift (witnesses := s34Witnesses) (cut := s15Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s15StockWords) (by decide +kernel)
  · exact s15Stock
  · decide +kernel
def s35Mask : Nat := 0xffffffff
abbrev s35Goal : Nat := sGoal &&& s35Mask
abbrev s35StockWords : List Nat := projectDAGStock s35Mask sBase [0, 1, 2, 3, 4]
def s35Fact : (Nat × List Nat × Nat × Nat) := (s35Mask, s35StockWords, 8, s35Goal)
def s35Witnesses := unpackWitnesses s35StockWords [2564, 271889, 526849, 791041, 1058307]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Stock : Lower s35Mask s35StockWords s35Goal 8 := by
  apply essentialLift (witnesses := s35Witnesses) (cut := s17Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s17StockWords) (by decide +kernel)
  · exact s17Stock
  · decide +kernel
def s36Mask : Nat := 0xffffffff
abbrev s36Goal : Nat := sGoal &&& s36Mask
abbrev s36StockWords : List Nat := projectDAGStock s36Mask sBase [0, 1, 2, 3, 4, 6]
def s36Fact : (Nat × List Nat × Nat × Nat) := (s36Mask, s36StockWords, 8, s36Goal)
def s36Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact]
def s36Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 9, 12, 19, 22, 26, 5, 5, 5, 5, 5, 5, 3, 6, 10, 17, 18, 20, 24, 3, 3, 3, 3, 3], rfl⟩
def s36Sample : (Nat × Nat) := (0xc07022190503830190a0540c0e0502c060b0c030140c088242013000140815000240c0c08854141a0a058281c0184c24160c0680c070082406070884c100903058100c090682413, 32)
def s36Witnesses := unpackWitnesses s36StockWords [271889, 526849, 791041, 1058307]
def s36Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x108020e0c1818283040608040828082fe0dfc03f807d08fa01f403e807d00fa01f403e807d00fa01f403e807c04e93dd203a017400e609cc039417280e405c8038827100e105c2038017000df05b6236c06d02da01b4036026c00d705ae035816b00d505a2234016800ce099c033415bacb6056a0acc25902b1055e12bc05780ae055032a005382a6054a0a8c25102a10542026874c8298052e0a5424a029305221240147828e051c0234146808c050e2a181430086010a09f873e827b08f409e413c807804f001e003c007800f001e003c007800f001e0037146e00dc01b8037006e00dc0190a32006400c8019003200610cc20184030025f04be017812f005e00ba096832d005a00ae195c02b805604aa09501288650049e093c027804e0496192c025804b009018d531a0234006410c80188230046000b8217002d045a00b0115042a005208a40148029005200a40140222180500002 0xa96300a833c0a763c0a66300b063c0ac33c0ab63c2abc3c09a0340980300ac6400ab63c07e01c07c0180a002809f01c1a89351a79310a992c0a86350a76310a66200a53350a43310a33140a202a09302608b01e08701a0a101209e00e00302409b03c09a02409833009603009001c09401009203009002408e02409333009103408f01c08d01008b03008902808801008603008402408202408733008503408302808101000300c07f33007e03007c3302aec3d0b5c381b39411b293d0b492c0b36410b263d0b16200af3410ae33d0ad3320aa33109d33009c31409903609703209502a08c02608a01e08001a07d01207b00e03a33000302407803c04c02404b33000302404a33007501000303006892c05662000831407301107200e07100806f03003833000302406c03c04902404803003733006892c05462004732604132503532400731400200803403003333000302406403c04602404503005f31805e31806103013001005f02402e03005c03005a32405e62805d34005b33402b03005901002a33005562405692c05462004432604032502832400631400200800300c05233003f03003e33004e02404e33404c93604b93204a92c04962904862504762004632904532504431404300804192c04062003f33603e33203d32a01332601031e00e31a00c31403c00802962001a31403600803001c03231803001002d01c02f62802e33402c01002962001931400300802401811e01011e01c02432811f03402301c02000c21e01c01e01002031c01f03401d02801a62001931400300803a92d03962b03862703762103562003432b03332703131f02b31b02a31502831402702b02602702501f02201b02101301c00f01b00901800800303001693001503001333000301801163001003000e33000303000c33000b03400901000302400892c007620006314005029004026002008079c3907793707693307492d07092c06e63706d63306b62b06a62706962106762006633706533306332b06232706031f05831b05731505331405103705003304f02b04d02704202603b02501702401401f01201b00f01300d00f00a00900100807a03f00003e 15 6 12 8 4 6
def s36Data : (Nat → Nat × Nat) := fun i => decodeNode 8 20 0xc387b92c7b6417b63d7b6207b63cb03417b33d7b3327b640ab63cab3317b92c9e6359e6319e6209e3359e3319e3149e02a9e0129e0289f01c9f00e9e3307b3147b03c9a0249a0367b330980327b0309602a7b010943308d030920348d0249001c8d0248e0108d0267b0308b01e7b02888010883308103086034810248402881024820108101a7b3307e0307e0127b3307c00e7b03f00c390103c7893701933010107592d010117100e710087192c010306f637016330103c6c62b01627016210192c6862001337013330103c6432b01327010306131f010245f62859340590305c334593245a0105931b013150192c5462455620543140133052037010330102b013344e02701936439324392c43629436254362043329433254331443008430260192c3c6203c3363c3323c32a3c0083c0250192d1862b186271862118008366201832b18327183183231f18010306282c3342c01c2d0102c31b1831518620293141802b180271801f183282301c2301b180131831c1d0341d0101e0281d00f180091862019314190081802401930150301501f013301301b016301003010013013300e00f013300b0340b009010100992c026200231402029020260202403008020080103e00 i
def s36Tags := dagTraceTags s36Mask 32 (dagTagBases s36StockWords 0xa4c1760ed814fe2bf7e35296accdb54c27106f6b5b3e89f1 0xbedf771fd8b0b623b2c042140c05310827414d4b412088e0 32) 7 s36Data
def s36States := dagTrace s36Mask s36StockWords 7 s36Data
def s36Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s36Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s36Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s36Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])]
def s36Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s36Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s36Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc00c3003c00c3003, 0), (0xc0003000c00030, 4), (0xc0000000c00, 10), (0xc00c0000c00c, 14), (0xc0000000c0, 18)], [(0xc0003000c000300, 4), (0x30000000300000, 10), (0x3003000030030000, 14), (0x300000003000000, 18)])]
def s36Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 3, 2, 1, 5] 0 i.val)
def s36Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 3, 2, 1, 5] 0 i.val)
def s36Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s36Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s36Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s36Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa005a005a005a005, 0), (0xa000a000a000a, 3), (0x50005000500050, 4), (0xa000a000a000a0, 7)], [(0x5000500050005000, 3), (0xa000a000a000a00, 4), (0x500050005000500, 7)])]
def s36Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s36Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s36Move5Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa005a005a005a005, 0), (0xa000a000a000a00, 3), (0xa000a000a000a0, 4), (0xa000a000a000a, 7)], [(0x50005000500050, 3), (0x500050005000500, 4), (0x5000500050005000, 7)])]
def s36Move5Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s36Move5Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s36Move6Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x8484212184842121, 0), (0x808020208080202, 3), (0x404000004040, 11), (0x848400008484, 14), (0x80800000808, 17)], [(0x4040101040401010, 3), (0x202000002020000, 11), (0x2121000021210000, 14), (0x1010000010100000, 17)])]
def s36Move6Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 4, 0, 3, 1, 5] 0 i.val)
def s36Move6Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 4, 0, 3, 1, 5] 0 i.val)
def s36Move7Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])]
def s36Move7Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s36Move7Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s36MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s36Move0Stages, s36Move0Map, s36Move0Inverse), (s36Move1Stages, s36Move1Map, s36Move1Inverse), (s36Move2Stages, s36Move2Map, s36Move2Inverse), (s36Move3Stages, s36Move3Map, s36Move3Inverse), (s36Move4Stages, s36Move4Map, s36Move4Inverse), (s36Move5Stages, s36Move5Map, s36Move5Inverse), (s36Move6Stages, s36Move6Map, s36Move6Inverse), (s36Move7Stages, s36Move7Map, s36Move7Inverse)]
def s36Moves := dagMoves s36MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Autos : DagMovesOK s36Mask s36Goal 64 s36Moves := dagMovesOfCheck (by decide +kernel)
def s36Check := dagCheckNode s36Mask s36Goal s36Chart (dagKnownCloses s36Goal s36Cuts) 182 s36States s36Moves s36Links s36Sample s36Tags
def s36RootAt (token : Nat) : Bool :=
  let s := rootState s36StockWords 7 token
  !dagAllowedRoot s36Witnesses s.2.1 || dagLocal s36Mask s36Goal s36Chart (dagKnownCloses s36Goal s36Cuts) s ||
  dagRef 182 s36States s36Moves s36Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36RootBlock0 : treeBlock 0 64 s36RootAt = true := by decide +kernel
theorem s36Roots : dagCheckRoots s36Mask s36Goal s36Chart (dagKnownCloses s36Goal s36Cuts) s36Witnesses (dagRef 182 s36States s36Moves s36Links 0) s36StockWords 7 = true := s36RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block0 : treeBlock 0 16 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block16 : treeBlock 16 16 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block32 : treeBlock 32 16 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block48 : treeBlock 48 16 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block64 : treeBlock 64 16 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block80 : treeBlock 80 16 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block96 : treeBlock 96 16 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block112 : treeBlock 112 16 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block128 : treeBlock 128 16 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block144 : treeBlock 144 16 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block160 : treeBlock 160 16 s36Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Block176 : treeBlock 176 6 s36Check = true := by decide +kernel
theorem s36Verified : treeBlock 0 182 s36Check = true := (@treeBlock_merge 0 96 86 s36Check (@treeBlock_merge 0 48 48 s36Check (@treeBlock_merge 0 16 32 s36Check s36Block0 (@treeBlock_merge 16 16 16 s36Check s36Block16 s36Block32)) (@treeBlock_merge 48 16 32 s36Check s36Block48 (@treeBlock_merge 64 16 16 s36Check s36Block64 s36Block80))) (@treeBlock_merge 96 48 38 s36Check (@treeBlock_merge 96 16 32 s36Check s36Block96 (@treeBlock_merge 112 16 16 s36Check s36Block112 s36Block128)) (@treeBlock_merge 144 16 22 s36Check s36Block144 (@treeBlock_merge 160 16 6 s36Check s36Block160 s36Block176))))
theorem s36Blocks : treeBlock 0 182 s36Check = true := s36Verified
theorem s36Known : Known s36Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s17Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Stock : Lower s36Mask s36StockWords s36Goal 8 := by
  apply lowerDag _ _ _ _ s36Autos _ _ _ s36Known _ s36Roots s36Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s36StockWords; decide +kernel
  · decide +kernel
  · simp only [s36Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s37Mask : Nat := 0xffffffff
abbrev s37Goal : Nat := sGoal &&& s37Mask
abbrev s37StockWords : List Nat := projectDAGStock s37Mask sBase [0, 1, 2, 3, 4, 8]
def s37Fact : (Nat × List Nat × Nat × Nat) := (s37Mask, s37StockWords, 8, s37Goal)
def s37Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact]
def s37Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 9, 12, 19, 22, 26, 5, 5, 5, 5, 5, 5, 3, 6, 10, 17, 18, 20, 24, 3, 3, 3, 3, 3], rfl⟩
def s37Sample : (Nat × Nat) := (0xa07030190502c301c08854140e03038060b0a03030090502420160001402150003006090a054141a0884c22190305824130c0680607020300c070a058100c0184c1009090682416, 32)
def s37Witnesses := unpackWitnesses s37StockWords [2564, 271889, 791041, 1058307]
def s37Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x10b02140c241838506060c041418281040608040c18102fe11fc03f027d82fb01f603e037c00f801e823d007a00f401e803c827900f201e403c807900f009e00384f7002e001bc137806e82dd01ba037016e00db05b6036816d00da01b0136006b82d701ac0b5806a82d111a2034015d2cb905700ad825a82b4056412c805900b1055632ac05502a905500a9825282a40548029005200a10d343a6414b8496052a0a5404a02940128025004a009401280250045148a01140228045008a0100520004000800100020003e867d00fa01f013d827a04f209d833b007600e619c8138827004e001c0037826c0cb2996012c005608ac015412a805404a41148028825100a201440258c4b0094092802482480490011822300450488090822100410482010011e863d007808ec11d803a047400e411c8038046628c81190030086000bc117802e045c00b8016822d005a00b4016802a0c5400a801482221c0500002 0xa36300033240b733c0a93240a83300b43300b23300b03240a00240b163409f3300af31c0ae01c0ac63c0a633c0a563c2a5c3c0a96340a86300a66400a563c0956280936240a131c0a001c09b32809a01089093588e9310a392c0a262a09f62609e33509d33109c31d09931909831409003508e03108c01d08801908000800331809663009533009363009063c08e63c08c33008a02808901c08733008532408332408863008603408402808201c0803302aac3d0b9c3888f94188d93d0b892c0b66360b56320b362a0ad6260ab3410aa33d0a73320a433109733009431d09231909131408f04108d03d08b01d08101907f00805333000332407c33c06132406063000332405f63007901c00333006c92c03262000c31407701d07601a07500807333005163000332407033c05e32405d33005063004592c06b31406a00806c92c05c62605962506962403162000a31400200800331806763005833005763006332406363406193606093205f92c05e62905d62505c62005b31402802902602500900805992c05863605763205662a03862603662005531401201d01001900800804562000731404f00883f01c04b31883f01083f01c04962884033404801004562000631400300802101804100c23f01c03f01004131c04003403e02805392d05262b05162705062104e62004d32b04c32704a31f04731b04631504431402d02b02b02704301f01e01b04201303d00f00e00900500800333003b93003a33003863000333003663003503403301003292c03162000431403002902f02600200802d63002b63000332402933c02832402663001c01802433001b01802201002001c02132801a03401f01c01d01001c32401a63001833001632401e63001b32801904001703401501c00331801363001233001063000e63000b62400762000631400300800332400c92c00a62000932600832500532400431400200807dc3907b93707a93307892d07492c07263707163306f62b06e62706d62106862006633706533306432b06232705a32605432503c32403931f03731b03431502e31402c03702a03302702b02502702301f01401b01101300f00f00d00900100807e03f00003b 15 6 12 8 4 6
def s37Data : (Nat → Nat × Nat) := fun i => decodeNode 8 20 0xc387f92c7f33cb76367f6327f330b462a7f330b2634ae324b031cae01cae6267f63cac3417f33d7f634a8630a83327f640a563ca53317f92c9862a9831ca001ca062698335983319831d983289a0109a31998314983307f630953309531d7f630933197f3147f63c900417f63c8e03d7f3308c01d7f0288901c8963082330870348232485028823248301c820197f330800087f03f00c390133c7c937019330101c7992d0101d7501a750087592c0133073637016330133c7062b01627016210192c693146a0086a624696200163067337013330132b0163463327019365b9325b92c5b6295b6255b6205b3145b3260192c55636556325562a55314553250192d3d62b3d6273d6213d0084f6203d32b3d3273d3184b31f3d628480104831b3d3153d620453143d01f3d0133d31c3e0343e0103f0283e00f3d324019303a3303a31f016303831b016303503435315010103392c2f6202f0292f0262f314016302d037016302b0330133c283242802b0163026027013302401f01010223281f01c2001c1f630150101d3241c328156301a0401533018034153241601c1501b016301233012013016301000f016300e0090192c026240b6200232602325026200631406324023140232403008020080103b00 i
def s37Tags := dagTraceTags s37Mask 32 (dagTagBases s37StockWords 0x6161760ed814fe2bf7e352969e9e89f127106f6b696db54c 0x7d7f771fd8d0b62374604214828088e027214d4b09053108 32) 7 s37Data
def s37States := dagTrace s37Mask s37StockWords 7 s37Data
def s37Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s37Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s37Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s37Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])]
def s37Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s37Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s37Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc00c3003c00c3003, 0), (0xc0003000c00030, 4), (0xc0000000c00, 10), (0xc00c0000c00c, 14), (0xc0000000c0, 18)], [(0xc0003000c000300, 4), (0x30000000300000, 10), (0x3003000030030000, 14), (0x300000003000000, 18)])]
def s37Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 3, 2, 1, 5] 0 i.val)
def s37Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 3, 2, 1, 5] 0 i.val)
def s37Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s37Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s37Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s37Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa005a005a005a005, 0), (0xa000a000a000a, 3), (0x50005000500050, 4), (0xa000a000a000a0, 7)], [(0x5000500050005000, 3), (0xa000a000a000a00, 4), (0x500050005000500, 7)])]
def s37Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s37Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s37Move5Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa005a005a005a005, 0), (0xa000a000a000a00, 3), (0xa000a000a000a0, 4), (0xa000a000a000a, 7)], [(0x50005000500050, 3), (0x500050005000500, 4), (0x5000500050005000, 7)])]
def s37Move5Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)
def s37Move5Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)
def s37Move6Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x8484212184842121, 0), (0x808020208080202, 3), (0x404000004040, 11), (0x848400008484, 14), (0x80800000808, 17)], [(0x4040101040401010, 3), (0x202000002020000, 11), (0x2121000021210000, 14), (0x1010000010100000, 17)])]
def s37Move6Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 4, 0, 3, 1, 5] 0 i.val)
def s37Move6Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 4, 0, 3, 1, 5] 0 i.val)
def s37Move7Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])]
def s37Move7Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s37Move7Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [3, 1, 2, 0, 4, 5] 0 i.val)
def s37MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s37Move0Stages, s37Move0Map, s37Move0Inverse), (s37Move1Stages, s37Move1Map, s37Move1Inverse), (s37Move2Stages, s37Move2Map, s37Move2Inverse), (s37Move3Stages, s37Move3Map, s37Move3Inverse), (s37Move4Stages, s37Move4Map, s37Move4Inverse), (s37Move5Stages, s37Move5Map, s37Move5Inverse), (s37Move6Stages, s37Move6Map, s37Move6Inverse), (s37Move7Stages, s37Move7Map, s37Move7Inverse)]
def s37Moves := dagMoves s37MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Autos : DagMovesOK s37Mask s37Goal 64 s37Moves := dagMovesOfCheck (by decide +kernel)
def s37Check := dagCheckNode s37Mask s37Goal s37Chart (dagKnownCloses s37Goal s37Cuts) 186 s37States s37Moves s37Links s37Sample s37Tags
def s37RootAt (token : Nat) : Bool :=
  let s := rootState s37StockWords 7 token
  !dagAllowedRoot s37Witnesses s.2.1 || dagLocal s37Mask s37Goal s37Chart (dagKnownCloses s37Goal s37Cuts) s ||
  dagRef 186 s37States s37Moves s37Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37RootBlock0 : treeBlock 0 64 s37RootAt = true := by decide +kernel
theorem s37Roots : dagCheckRoots s37Mask s37Goal s37Chart (dagKnownCloses s37Goal s37Cuts) s37Witnesses (dagRef 186 s37States s37Moves s37Links 0) s37StockWords 7 = true := s37RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block0 : treeBlock 0 16 s37Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block16 : treeBlock 16 16 s37Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block32 : treeBlock 32 16 s37Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block48 : treeBlock 48 16 s37Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block64 : treeBlock 64 16 s37Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block80 : treeBlock 80 16 s37Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block96 : treeBlock 96 16 s37Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block112 : treeBlock 112 16 s37Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block128 : treeBlock 128 16 s37Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block144 : treeBlock 144 16 s37Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block160 : treeBlock 160 16 s37Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block176 : treeBlock 176 10 s37Check = true := by decide +kernel
theorem s37Verified : treeBlock 0 186 s37Check = true := (@treeBlock_merge 0 96 90 s37Check (@treeBlock_merge 0 48 48 s37Check (@treeBlock_merge 0 16 32 s37Check s37Block0 (@treeBlock_merge 16 16 16 s37Check s37Block16 s37Block32)) (@treeBlock_merge 48 16 32 s37Check s37Block48 (@treeBlock_merge 64 16 16 s37Check s37Block64 s37Block80))) (@treeBlock_merge 96 48 42 s37Check (@treeBlock_merge 96 16 32 s37Check s37Block96 (@treeBlock_merge 112 16 16 s37Check s37Block112 s37Block128)) (@treeBlock_merge 144 16 26 s37Check s37Block144 (@treeBlock_merge 160 16 10 s37Check s37Block160 s37Block176))))
theorem s37Blocks : treeBlock 0 186 s37Check = true := s37Verified
theorem s37Known : Known s37Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s17Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Stock : Lower s37Mask s37StockWords s37Goal 8 := by
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
    rcases h with rfl <;> decide +kernel
def s38Mask : Nat := 0xffff0000ffff0000
abbrev s38Goal : Nat := sGoal &&& s38Mask
abbrev s38StockWords : List Nat := projectDAGStock s38Mask sBase [0, 1, 2, 3, 5]
def s38Fact : (Nat × List Nat × Nat × Nat) := (s38Mask, s38StockWords, 8, s38Goal)
def s38Witnesses := unpackWitnesses s38StockWords [9746, 271889, 535057, 799249, 1073681]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Stock : Lower s38Mask s38StockWords s38Goal 8 := by
  apply essentialLift (witnesses := s38Witnesses) (cut := s17Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s17StockWords) (by decide +kernel)
  · exact s17Stock
  · decide +kernel
def s39Mask : Nat := 0xffff0000ffff0000
abbrev s39Goal : Nat := sGoal &&& s39Mask
abbrev s39StockWords : List Nat := projectDAGStock s39Mask sBase [0, 1, 2, 3, 5, 6]
def s39Fact : (Nat × List Nat × Nat × Nat) := (s39Mask, s39StockWords, 8, s39Goal)
def s39Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact]
def s39Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[19, 21, 22, 25, 26, 28, 49, 50, 19, 19, 19, 19, 17, 18, 52, 56, 17, 17, 17, 17, 17, 17, 17, 17], rfl⟩
def s39Sample : (Nat × Nat) := (0x703a1c0e420311c070681c0806468160805420131a0c870320906824130885422131a0d8223108864703c0905824321a0f0301a1a0d43019, 25)
def s39Witnesses := unpackWitnesses s39StockWords [271889, 535057, 799249, 1073681]
def s39Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x1480a405202885440a2051028054009e14f027813c09e04f027813c09e04d8e6c13419a04d026812e39704b065812c0960498e4c12609114806401200900468de2af007803c01e00f007803c01c8ce407203809c00e007003801a10d0068034019c2ca26503281902bc65e02f01704b805c02e01700a885402985482a024f0a6892c49604a0a409200900470a3051808a14219e18f007803b09c88e407203901c80e026463201900c806403201900bc65e02e09700b805632b01504a805402a0138c9c04e027013809c04e027010980be002 0x7bc981f40a0ef280790403bb18198070e00506f01c370081b18d0d40686901c34008198cd0c80686302831008180ca0be6385e3302e01a16c0a0b40387fc413f61c3ea505f127a7c9353dc961e9904f0c7a766353ab101d0d04e667a723143881b1b40c8d6054670263280f184068ba0245900e214960818800e6285302a2900f144020952684e03425e1c1298988cc40343351898c87cc509203a060082280e11a4d08806041028214960e58a43cc40053142001280802070c683d0341d61c0d18d472c40383261818d090c501c022040081780e0d4c60692682d318178140b98d0640202e634148080bc0405cc5027010140140a0ca0506382a6281481409c070632683063416b140b0d005666826010118140918d0440601d0281049607d8a43cc40033140e0128080202e080160280a80e04d8d118080110340800e038cd0180800b0340501401e4b00cc52056200219480cc500401057c392b49b9564cca925a5092c27b1b9358cc98c564862923b1390d8847ec403e3371e1998eccac6e652363271998f894c6c4262a1b3140d01b8640cc30056140270900f83c06c1a0260900f04004804020b007e0003e 13 5 12 7 2 5
def s39Data : (Nat → Nat × Nat) := fun i => decodeNode 7 19 0xc41b3871640a3ec9ad992cb2c8364103cb1ed9630eec6b65882c9a0d933db2629640dac8146e01cdc021b80cacb1a6c02ab2069a0073400868026b26699807ac81a62028c40218806ac9945f31cbe6617804ac81a5a028b40396803ac81f80c390326e064cc0c968102aa203d440228c960163702069398cc0b1581c3892c4d240764b1481627032691007228184462103259000a20812c06200266e040d1e9998132b03870e1881c193383290264e04c61ac9a3431f02020ca4d1331a260105ec50b98a131a0263344cc509c0a1398e2801c4e02098c6c0b1a220284606088c540c961c62938c40700a0e8129c3140206e040cc0815810402a05054070a813816342603e040d0800e1001b026683804c08200a034140502803c08048192c04c52098801194823140401008020081f00 i
def s39Tags := dagTraceTags s39Mask 25 (dagTagBases s39StockWords 0x269c4f9c0c35adc10668d829aa0bec68cb1d83 0x3ffe4ffb4c24ad020228520828006060000d80 25) 7 s39Data
def s39States := dagTrace s39Mask s39StockWords 7 s39Data
def s39Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s39Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s39Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s39Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])]
def s39Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s39Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s39Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9009900990099009, 0), (0x2002200220022002, 1), (0x40004000400040, 3), (0x90009000900090, 4), (0x20002000200020, 5)], [(0x4004400440044004, 1), (0x200020002000200, 3), (0x900090009000900, 4), (0x400040004000400, 5)])]
def s39Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)
def s39Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)
def s39MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s39Move0Stages, s39Move0Map, s39Move0Inverse), (s39Move1Stages, s39Move1Map, s39Move1Inverse), (s39Move2Stages, s39Move2Map, s39Move2Inverse)]
def s39Moves := dagMoves s39MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Autos : DagMovesOK s39Mask s39Goal 64 s39Moves := dagMovesOfCheck (by decide +kernel)
def s39Check := dagCheckNode s39Mask s39Goal s39Chart (dagKnownCloses s39Goal s39Cuts) 128 s39States s39Moves s39Links s39Sample s39Tags
def s39RootAt (token : Nat) : Bool :=
  let s := rootState s39StockWords 7 token
  !dagAllowedRoot s39Witnesses s.2.1 || dagLocal s39Mask s39Goal s39Chart (dagKnownCloses s39Goal s39Cuts) s ||
  dagRef 128 s39States s39Moves s39Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39RootBlock0 : treeBlock 0 64 s39RootAt = true := by decide +kernel
theorem s39Roots : dagCheckRoots s39Mask s39Goal s39Chart (dagKnownCloses s39Goal s39Cuts) s39Witnesses (dagRef 128 s39States s39Moves s39Links 0) s39StockWords 7 = true := s39RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Block0 : treeBlock 0 16 s39Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Block16 : treeBlock 16 16 s39Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Block32 : treeBlock 32 16 s39Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Block48 : treeBlock 48 16 s39Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Block64 : treeBlock 64 16 s39Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Block80 : treeBlock 80 16 s39Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Block96 : treeBlock 96 16 s39Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Block112 : treeBlock 112 16 s39Check = true := by decide +kernel
theorem s39Verified : treeBlock 0 128 s39Check = true := (@treeBlock_merge 0 64 64 s39Check (@treeBlock_merge 0 32 32 s39Check (@treeBlock_merge 0 16 16 s39Check s39Block0 s39Block16) (@treeBlock_merge 32 16 16 s39Check s39Block32 s39Block48)) (@treeBlock_merge 64 32 32 s39Check (@treeBlock_merge 64 16 16 s39Check s39Block64 s39Block80) (@treeBlock_merge 96 16 16 s39Check s39Block96 s39Block112)))
theorem s39Blocks : treeBlock 0 128 s39Check = true := s39Verified
theorem s39Known : Known s39Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s17Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Stock : Lower s39Mask s39StockWords s39Goal 8 := by
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
    rcases h with rfl <;> decide +kernel
def s40Mask : Nat := 0xffff0000ffff0000
abbrev s40Goal : Nat := sGoal &&& s40Mask
abbrev s40StockWords : List Nat := projectDAGStock s40Mask sBase [0, 1, 2, 3, 5, 7]
def s40Fact : (Nat × List Nat × Nat × Nat) := (s40Mask, s40StockWords, 8, s40Goal)
def s40Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact]
def s40Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[19, 21, 22, 25, 26, 28, 49, 50, 19, 19, 19, 19, 17, 18, 52, 56, 17, 17, 17, 17, 17, 17, 17, 17], rfl⟩
def s40Sample : (Nat × Nat) := (0x703a1c0e420321c070681c0806820161a05420131a0c470310886422130905824131a0d4243209068703c0885422311a0f030191a0d8301a, 25)
def s40Witnesses := unpackWitnesses s40StockWords [9746, 535057, 799249, 1073681]
def s40Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x1480a405202885440a2051028054009e14f027813c09e04f026c73609a0cd02681340971cb825832c09604b024c726093049824c1222900c8024012008d1c681e2af007803c01e00f007803c01c8ce407203809c00e007003801a10d0068034019c2ca26503281902bc65e02f01704b805c02e01700a885402985482a024f0a6892c49604a0a409200900470a3051808a14219e18f007803b09c88e407203901c80e026463201900c806403201900bc65e02e09700b805632b01504a805402a0138c9c04e027013809c04e027010980be002 0x7bc981f4ca0ef280790403bb181a4c70e66507231c388081bd8d0da6686c31c358081a4cd0ce6686632832808184ca0c06385f3302e81a1700a0b60387fc413f61c3ea505f127a7c9353dc961e9904f0c7a766353ab101d0cd8e06646e32a351931a0c78c8634630413101e978044b401a59008214960818800e6285302a2900f144020952684e03425e1c1298988cc40343351898c87cc509203a060082280e11a4d08806041028214960e58a43cc40053142001280802070c683d0341d61c0d18d472c40383261818d090c501c022040081780e0d4c60692682d318178140b98d0640202e634148080bc0405cc5027010140140a0ca0506382a6281481409c070632683063416b140b0d005666826010118140918d0440601d0281049607d8a43cc40033140e0128080202e080160280a80e04d8d118080110340800e038cd0180800b0340501401e4b00cc52056200219480cc500401057c392b49b9564cca925a5092c27b1b9358cc98c564862923b1390d8847ec403e3371e1998eccac6e652363271998f894c6c4262a1b3140d01b8640cc30056140270900f83c06c1a0260900f04004804020b007e0003d 13 5 12 7 2 5
def s40Data : (Nat → Nat × Nat) := fun i => decodeNode 7 19 0xc41b387164ca3ec9ad992cb2c8364103cb1ed9630eec6b65882c99b59328e2639c4043899959634de65564cd3598e6b010d664d64cd3498f59334ca65194043298d59041b207b64ca3018e60330be023640d2d8145b01cb601b64022c81f80c390326e064cc0c968102aa203d440228c960163702069398cc0b1581c3892c4d240764b1481627032691007228184462103259000a20812c06200266e040d1e9998132b03870e1881c193383290264e04c61ac9a3431f02020ca4d1331a260105ec50b98a131a0263344cc509c0a1398e2801c4e02098c6c0b1a220284606088c540c961c62938c40700a0e8129c3140206e040cc0815810402a05054070a813816342603e040d0800e1001b026683804c08200a034140502803c08048192c04c52098801194823140401008020081e80 i
def s40Tags := dagTraceTags s40Mask 25 (dagTagBases s40StockWords 0x165c4f9c0c35adc10668d829aa9a3b0683f634 0x3ffe4ffb2c24ad0202284a0828001b00003030 25) 7 s40Data
def s40States := dagTrace s40Mask s40StockWords 7 s40Data
def s40Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s40Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s40Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s40Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])]
def s40Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s40Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s40Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9009900990099009, 0), (0x2002200220022002, 1), (0x40004000400040, 3), (0x90009000900090, 4), (0x20002000200020, 5)], [(0x4004400440044004, 1), (0x200020002000200, 3), (0x900090009000900, 4), (0x400040004000400, 5)])]
def s40Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)
def s40Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)
def s40MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s40Move0Stages, s40Move0Map, s40Move0Inverse), (s40Move1Stages, s40Move1Map, s40Move1Inverse), (s40Move2Stages, s40Move2Map, s40Move2Inverse)]
def s40Moves := dagMoves s40MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Autos : DagMovesOK s40Mask s40Goal 64 s40Moves := dagMovesOfCheck (by decide +kernel)
def s40Check := dagCheckNode s40Mask s40Goal s40Chart (dagKnownCloses s40Goal s40Cuts) 128 s40States s40Moves s40Links s40Sample s40Tags
def s40RootAt (token : Nat) : Bool :=
  let s := rootState s40StockWords 7 token
  !dagAllowedRoot s40Witnesses s.2.1 || dagLocal s40Mask s40Goal s40Chart (dagKnownCloses s40Goal s40Cuts) s ||
  dagRef 128 s40States s40Moves s40Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40RootBlock0 : treeBlock 0 64 s40RootAt = true := by decide +kernel
theorem s40Roots : dagCheckRoots s40Mask s40Goal s40Chart (dagKnownCloses s40Goal s40Cuts) s40Witnesses (dagRef 128 s40States s40Moves s40Links 0) s40StockWords 7 = true := s40RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Block0 : treeBlock 0 16 s40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Block16 : treeBlock 16 16 s40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Block32 : treeBlock 32 16 s40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Block48 : treeBlock 48 16 s40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Block64 : treeBlock 64 16 s40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Block80 : treeBlock 80 16 s40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Block96 : treeBlock 96 16 s40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Block112 : treeBlock 112 16 s40Check = true := by decide +kernel
theorem s40Verified : treeBlock 0 128 s40Check = true := (@treeBlock_merge 0 64 64 s40Check (@treeBlock_merge 0 32 32 s40Check (@treeBlock_merge 0 16 16 s40Check s40Block0 s40Block16) (@treeBlock_merge 32 16 16 s40Check s40Block32 s40Block48)) (@treeBlock_merge 64 32 32 s40Check (@treeBlock_merge 64 16 16 s40Check s40Block64 s40Block80) (@treeBlock_merge 96 16 16 s40Check s40Block96 s40Block112)))
theorem s40Blocks : treeBlock 0 128 s40Check = true := s40Verified
theorem s40Known : Known s40Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s17Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Stock : Lower s40Mask s40StockWords s40Goal 8 := by
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
    rcases h with rfl <;> decide +kernel
def s41Mask : Nat := 0xffff0000ffff0000
abbrev s41Goal : Nat := sGoal &&& s41Mask
abbrev s41StockWords : List Nat := projectDAGStock s41Mask sBase [0, 1, 2, 3, 5, 8]
def s41Fact : (Nat × List Nat × Nat × Nat) := (s41Mask, s41StockWords, 8, s41Goal)
def s41Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact]
def s41Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[19, 21, 22, 25, 26, 28, 49, 50, 19, 19, 19, 19, 17, 18, 52, 56, 17, 17, 17, 17, 17, 17, 17, 17], rfl⟩
def s41Sample : (Nat × Nat) := (0x681c0805820151c0e870321c0c428161a054303c0a070201c0a054701a0906822131c0e42416090c868351a0d8683c088c422190904c301a08854703c, 27)
def s41Witnesses := unpackWitnesses s41StockWords [9746, 271889, 799249, 1073681]
def s41Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x5b02d81682b40590ac43620af15782bc15a2a925406a01500a70d3829c13e89f04f827833c09e04e0a7013809b0cd826832c49604b025812c0931c982483240910c88244122091048823871c08d0bb5dd80ea17503a81d02e807403a01c46e206a3b501a80d40690b4818ccc41610af897c0bc15e02f01742ba05c0ae01700a885402a01500a4252029014809864c025852829404a025012808e347023051808c0431a1810c084142021010807863c01d84e827403a01d00e807403719b80d826c03601b00cc66603209808b845c02e01684b405812821400a004e127013809c04e027010980be002 0x2300d05c0282280f0530282125007d94021c100773281d80a085c3c2124d07964020d8907c93410c0a07e9311e58d47d6251f1882673291a4c506702917c020799341dcc707601c1cd8a0716281d64d0746341c8c707001c1b4cd06c3281ac0406963419e500630341880a06101c17d8d08dc4122f0f889c382225048693d20a4d48192c2018d87f6351ed8d07a6321e18a86f626998d066533d1b8c746a3191a0c50660411940f46401d1800645e0081718d0590281564b0283140200203a92c09d8800731415c0a8560291500a05300813e4c03992c099880063141400c84e02a1340204363410d8c04b9301298d04803410c0a0439301170e0449311098a83d620104c7425314100074050080f64d03c0300ea4c83992c091880043140e0094020080d98a035630874d00313280c00402e63485cd002c3340ac0402802809e4c82692c0958a42462000cc5002008088ca0213300741001c02806c0701963405c10016034054070136280498c01000c0380a00c01c0380400c010040c700f0400340d00b0280200a00793201a4b005629011880033140080205bc3916a4dc5893314a4c85192d1324b04963711d8cc4662b0fd8a43e6270ed884376200d0cdc333330c8cac2f3270b4c7c2a31b0a4c54233140800dc1f0330780ac1a02706007c1401b04404c0a00f024024010081740fc0003b 13 5 12 8 2 5
def s41Data : (Nat → Nat × Nat) := fun i => decodeNode 8 20 0xc415e0348cc3e5e03c8ac385e9415e0408793d5ec3c8393483624839355e92c5e6365e6355e9317c6257c6207c6345e6325e9347962a5e31c7601c7693470634706287331c706287101c706265e31d5e3346b3286b0106b3195e634693145e940670415e03d5e01d5e034610286101c610195e6345f0085e03f006345cc390193701028599330102a530295392c5502853008539320192d010324d9304f02a4d0084d92c019304a6344a63701034486330162b01c3840931409304362a4031d4001d4062901627019343c0303c621019323892c3802538620016283663035337013330132b013283001030327016342e31f013342b0102b31b0131501028289322492c246292462024314013282233021037010330102b010401b0281b01c1b027016341901f01040150341501c1501b0162813630120130131c0b0400b0100e0340b0100c0280b00f0100901028089320292c02629026200231402008020080103b00 i
def s41Tags := dagTraceTags s41Mask 27 (dagTagBases s41StockWords 0x703d1e0e40be190ed0abc7e170d683b46128993a 0x1f2bf1fce849c11c8900b06a07000013040001032 27) 7 s41Data
def s41States := dagTrace s41Mask s41StockWords 7 s41Data
def s41Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])]
def s41Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s41Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)
def s41Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])]
def s41Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s41Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)
def s41Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0x9009900990099009, 0), (0x2002200220022002, 1), (0x40004000400040, 3), (0x90009000900090, 4), (0x20002000200020, 5)], [(0x4004400440044004, 1), (0x200020002000200, 3), (0x900090009000900, 4), (0x400040004000400, 5)])]
def s41Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)
def s41Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)
def s41MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s41Move0Stages, s41Move0Map, s41Move0Inverse), (s41Move1Stages, s41Move1Map, s41Move1Inverse), (s41Move2Stages, s41Move2Map, s41Move2Inverse)]
def s41Moves := dagMoves s41MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Autos : DagMovesOK s41Mask s41Goal 64 s41Moves := dagMovesOfCheck (by decide +kernel)
def s41Check := dagCheckNode s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) 142 s41States s41Moves s41Links s41Sample s41Tags
def s41RootAt (token : Nat) : Bool :=
  let s := rootState s41StockWords 7 token
  !dagAllowedRoot s41Witnesses s.2.1 || dagLocal s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) s ||
  dagRef 142 s41States s41Moves s41Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41RootBlock0 : treeBlock 0 64 s41RootAt = true := by decide +kernel
theorem s41Roots : dagCheckRoots s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) s41Witnesses (dagRef 142 s41States s41Moves s41Links 0) s41StockWords 7 = true := s41RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block0 : treeBlock 0 16 s41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block16 : treeBlock 16 16 s41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block32 : treeBlock 32 16 s41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block48 : treeBlock 48 16 s41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block64 : treeBlock 64 16 s41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block80 : treeBlock 80 16 s41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block96 : treeBlock 96 16 s41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block112 : treeBlock 112 16 s41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block128 : treeBlock 128 14 s41Check = true := by decide +kernel
theorem s41Verified : treeBlock 0 142 s41Check = true := (@treeBlock_merge 0 64 78 s41Check (@treeBlock_merge 0 32 32 s41Check (@treeBlock_merge 0 16 16 s41Check s41Block0 s41Block16) (@treeBlock_merge 32 16 16 s41Check s41Block32 s41Block48)) (@treeBlock_merge 64 32 46 s41Check (@treeBlock_merge 64 16 16 s41Check s41Block64 s41Block80) (@treeBlock_merge 96 16 30 s41Check s41Block96 (@treeBlock_merge 112 16 14 s41Check s41Block112 s41Block128))))
theorem s41Blocks : treeBlock 0 142 s41Check = true := s41Verified
theorem s41Known : Known s41Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s17Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Stock : Lower s41Mask s41StockWords s41Goal 8 := by
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
def s42Mask : Nat := 0xff00ff00ff00ff
abbrev s42Goal : Nat := sGoal &&& s42Mask
abbrev s42StockWords : List Nat := projectDAGStock s42Mask sBase [0, 1, 2, 4, 5]
def s42Fact : (Nat × List Nat × Nat × Nat) := (s42Mask, s42StockWords, 8, s42Goal)
def s42Witnesses := unpackWitnesses s42StockWords [2564, 271889, 526849, 796163, 1066499]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Stock : Lower s42Mask s42StockWords s42Goal 8 := by
  apply essentialLift (witnesses := s42Witnesses) (cut := s18Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s18StockWords) (by decide +kernel)
  · exact s18Stock
  · decide +kernel
def s43Mask : Nat := 0xff00ff00ff00ff
abbrev s43Goal : Nat := sGoal &&& s43Mask
abbrev s43StockWords : List Nat := projectDAGStock s43Mask sBase [0, 1, 2, 4, 5, 6]
def s43Fact : (Nat × List Nat × Nat × Nat) := (s43Mask, s43StockWords, 8, s43Goal)
def s43Cuts : List (Nat × List Nat × Nat × Nat) := [s18Fact]
def s43Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 19, 22, 35, 38, 49, 50, 5, 5, 5, 5, 5, 3, 6, 17, 18, 33, 34, 52, 3, 3, 3, 3, 3], rfl⟩
def s43Sample : (Nat × Nat) := (0x42250a0540c070181c60311108c04230104c08070201406050001460321a0986816108142205110c802051088c2816090580c26088c442310305806231209822150884c44260184c2432120942413, 35)
def s43Witnesses := unpackWitnesses s43StockWords [271889, 526849, 796163, 1066499]
def s43Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xb40b40b40b40b40b40b40b40b40b40b40b40b40b40b40b40b40ae3ae0ae0ae0a83a808338208208208208207a47a07a07627417216e26e06c16c06a16626606416215e25e05e05645605605605605415405405215205205204a44a04a04a04814804804614604604604604604604604603e405d002 0x3e0343d0283c0103a3303932438318cbc41cac3d4cc384b9414a93d4992c4864147620463414533d4431443036420324102a400263f01e3b01a370123600e1e92c136200531430008273282b030263282b6242c6242a03c280242631c2731c250302302422328249342131c1e92c12620043140200819328163341392c1262003314020080e63c0b9300592c04620033140200834c3933937329333192d2f92c2e6372d6332962b206271f6211d6201c3371b3331a32b183271731f1531b1431511314100370f0330d02b0c0270a01f0901b080130700f06009010083503f0003e 12 5 12 7 1 5
def s43Data : (Nat → Nat × Nat) := fun i => decodeNode 6 18 0x30e36941da4f7692cd99076620d8d07633dd8c536036d80cb602ad809b601ed80d3c028f0043c01ad8cc38324e0c638012d803b603f030e41937064cc192d04023092c058dc163305892a624ac0f2a62b04092831c94c726030964d210248cca2231c8589c1621064b1e62004cdc133304cac132864c9c131f04cd1631b04c54192c498812314040dc1033058f0e02b0409c19302c07c101b0404c100f04024192c098802314080202008040f80 i
def s43Tags := dagTraceTags s43Mask 35 (dagTagBases s43StockWords 0x39394a470629d96490a4dcdbe1ef5cb48de3979defff8d8d6b 0x1bf79394bc607a8492480e8d0cac18c14a08dc81198ec810d8d68 35) 7 s43Data
def s43States := dagTrace s43Mask s43StockWords 7 s43Data
def s43Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])]
def s43Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s43Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s43MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s43Move0Stages, s43Move0Map, s43Move0Inverse)]
def s43Moves := dagMoves s43MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Autos : DagMovesOK s43Mask s43Goal 64 s43Moves := dagMovesOfCheck (by decide +kernel)
def s43Check := dagCheckNode s43Mask s43Goal s43Chart (dagKnownCloses s43Goal s43Cuts) 77 s43States s43Moves s43Links s43Sample s43Tags
def s43RootAt (token : Nat) : Bool :=
  let s := rootState s43StockWords 7 token
  !dagAllowedRoot s43Witnesses s.2.1 || dagLocal s43Mask s43Goal s43Chart (dagKnownCloses s43Goal s43Cuts) s ||
  dagRef 77 s43States s43Moves s43Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43RootBlock0 : treeBlock 0 64 s43RootAt = true := by decide +kernel
theorem s43Roots : dagCheckRoots s43Mask s43Goal s43Chart (dagKnownCloses s43Goal s43Cuts) s43Witnesses (dagRef 77 s43States s43Moves s43Links 0) s43StockWords 7 = true := s43RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Block0 : treeBlock 0 16 s43Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Block16 : treeBlock 16 16 s43Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Block32 : treeBlock 32 16 s43Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Block48 : treeBlock 48 16 s43Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Block64 : treeBlock 64 13 s43Check = true := by decide +kernel
theorem s43Verified : treeBlock 0 77 s43Check = true := (@treeBlock_merge 0 32 45 s43Check (@treeBlock_merge 0 16 16 s43Check s43Block0 s43Block16) (@treeBlock_merge 32 16 29 s43Check s43Block32 (@treeBlock_merge 48 16 13 s43Check s43Block48 s43Block64)))
theorem s43Blocks : treeBlock 0 77 s43Check = true := s43Verified
theorem s43Known : Known s43Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s18Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Stock : Lower s43Mask s43StockWords s43Goal 8 := by
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
    rcases h with rfl <;> decide +kernel
def s44Mask : Nat := 0xff00ff00ff00ff
abbrev s44Goal : Nat := sGoal &&& s44Mask
abbrev s44StockWords : List Nat := projectDAGStock s44Mask sBase [0, 1, 2, 4, 5, 10]
def s44Fact : (Nat × List Nat × Nat × Nat) := (s44Mask, s44StockWords, 8, s44Goal)
def s44Cuts : List (Nat × List Nat × Nat × Nat) := [s18Fact]
def s44Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 19, 22, 35, 38, 49, 50, 5, 5, 5, 5, 5, 3, 6, 17, 18, 33, 34, 52, 3, 3, 3, 3, 3], rfl⟩
def s44Sample : (Nat × Nat) := (0x60321209442250a0580c070181c02311a05802150104c02131201442050301406050904c68310905808051088c6836180c40205030982231030584231090c84423120982215110c828150188c2213110980613, 37)
def s44Witnesses := unpackWitnesses s44StockWords [2564, 271889, 526849, 1066499]
def s44Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9c09c09c09c09a19a09819809809809619609609609609419409409409409409409406f36e06e06e06e06e06646606606606606416406405c45c05c05c05a15a05a05a05a05a05a05245205205205205205205205204c34c04c04c04634604604604604604603e405d002 0x4233c406283c6343793045c4144c3d43c38419363f9323e6413d6293b6253a620393413833d363293532534314330413203d31029300252f0082192c176200531429008246402192c1662004314020081dc3c1792c1662003314020080f0400e0340d01c0b63c0a630096240592c0462003314020082dc392c9372b9332a92d2892c27637266332562b2362722621206201f3371e3331c32b1b3271a31f1931b183151531414037130331202b110271001f0c01b080130700f06009010082e03f00037 12 5 12 7 1 5
def s44Data : (Nat → Nat × Nat) := fun i => decodeNode 7 19 0x31057e1eafc385e6790a4d97b14409325ec82bd8a57b1a3c6255ec40bcd05799eaf9306e652bcc95798a2f0415e07abc0a57812af0085e07e030e40c9b819330325a040214c960163702c66058ac0b202462702c42064b10b100133702666070f0e995813270263e04c6c098a8192c2cc4058c50081b81033020560409c080f810401a06834070680d8163c12c602589048098100f02012064b01310023140401008020081b80 i
def s44Tags := dagTraceTags s44Mask 37 (dagTagBases s44StockWords 0x1b078cc315c4013b7aa93e1ccf3abecf35a34a75856575eddff6d55d 0x1bbf8cdb57c231385a29101cc92a2c8a54a240311d056564d542544d 37) 7 s44Data
def s44States := dagTrace s44Mask s44StockWords 7 s44Data
def s44Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])]
def s44Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s44Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)
def s44MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s44Move0Stages, s44Move0Map, s44Move0Inverse)]
def s44Moves := dagMoves s44MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Autos : DagMovesOK s44Mask s44Goal 64 s44Moves := dagMovesOfCheck (by decide +kernel)
def s44Check := dagCheckNode s44Mask s44Goal s44Chart (dagKnownCloses s44Goal s44Cuts) 70 s44States s44Moves s44Links s44Sample s44Tags
def s44RootAt (token : Nat) : Bool :=
  let s := rootState s44StockWords 7 token
  !dagAllowedRoot s44Witnesses s.2.1 || dagLocal s44Mask s44Goal s44Chart (dagKnownCloses s44Goal s44Cuts) s ||
  dagRef 70 s44States s44Moves s44Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44RootBlock0 : treeBlock 0 64 s44RootAt = true := by decide +kernel
theorem s44Roots : dagCheckRoots s44Mask s44Goal s44Chart (dagKnownCloses s44Goal s44Cuts) s44Witnesses (dagRef 70 s44States s44Moves s44Links 0) s44StockWords 7 = true := s44RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Block0 : treeBlock 0 16 s44Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Block16 : treeBlock 16 16 s44Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Block32 : treeBlock 32 16 s44Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Block48 : treeBlock 48 16 s44Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Block64 : treeBlock 64 6 s44Check = true := by decide +kernel
theorem s44Verified : treeBlock 0 70 s44Check = true := (@treeBlock_merge 0 32 38 s44Check (@treeBlock_merge 0 16 16 s44Check s44Block0 s44Block16) (@treeBlock_merge 32 16 22 s44Check s44Block32 (@treeBlock_merge 48 16 6 s44Check s44Block48 s44Block64)))
theorem s44Blocks : treeBlock 0 70 s44Check = true := s44Verified
theorem s44Known : Known s44Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s18Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Stock : Lower s44Mask s44StockWords s44Goal 8 := by
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
    rcases h with rfl <;> decide +kernel
def s45Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev s45Goal : Nat := sGoal &&& s45Mask
abbrev s45StockWords : List Nat := projectDAGStock s45Mask sBase [0, 1, 3, 4, 5]
def s45Fact : (Nat × List Nat × Nat × Nat) := (s45Mask, s45StockWords, 8, s45Goal)
def s45Witnesses := unpackWitnesses s45StockWords [4616, 271889, 528897, 796163, 1066499]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Stock : Lower s45Mask s45StockWords s45Goal 8 := by
  apply essentialLift (witnesses := s45Witnesses) (cut := s18Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s18StockWords) (by decide +kernel)
  · exact s18Stock
  · decide +kernel
def s46Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev s46Goal : Nat := sGoal &&& s46Mask
abbrev s46StockWords : List Nat := projectDAGStock s46Mask sBase [0, 1, 3, 4, 5, 6]
def s46Fact : (Nat × List Nat × Nat × Nat) := (s46Mask, s46StockWords, 8, s46Goal)
def s46Cuts : List (Nat × List Nat × Nat × Nat) := [s18Fact]
def s46Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 19, 26, 35, 49, 50, 9, 9, 9, 9, 9, 9, 3, 17, 18, 33, 42, 56, 3, 3, 3, 3, 3, 3], rfl⟩
def s46Sample : (Nat × Nat) := (0x180c8443205068301908864140b0182c60311108c04230104c100b1082422090402400091c0c8701a1506802091c0e82213108c40623090c8543a0c06842290906822311088c0613140a42413, 34)
def s46Witnesses := unpackWitnesses s46StockWords [271889, 528897, 796163, 1066499]
def s46Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xec0ec0ea1ea0ea0e81e80e42e40e40e40e40e40e40e40e40e40de3de0de0de0da2da0da0d81d80d61ce4ce0ce0ce0c83c80a14a00a00a009e19e09e09e09459409409409219209019009008658418408218208208208208207477407407217207017007006c26c06c06c06256206206206016005e15e05c15825425405215014e14e04c14c04a14a04a04a04a04a04a040505e002 0x600285b6405b6344c0185393052324510244d01c480104a328483284c6344b034490284701045330443244331861c415fc3d5ec38d8941d793d5d92c5c6415a63559620583415733d5631455036540325002a4f0264e01e4601a420124100e3d01c3092c1d620063143a01e390083503c3331c3092c296291c6200531402008283342d0342ac38296202832a2731e203140b011040082433422334206341f0301d92c1c620033141b025020081763c1501c1300c123340e018119300d0180f3280e6240d3280b334090340692c056200432903314020083fc393e9373c9333b92d3892c37637366333462b32627316212f6202e3372c3332b32b26329253272331f2131b1e3151a31419037180331602b140271001f0c01b0a0130800f07009010084003f0003e 12 5 12 7 1 5
def s46Data : (Nat → Nat × Nat) := fun i => decodeNode 7 19 0x3106081460c3d83871064b20b20c1634b6c6b0588209a0c133d82629040da081941930a2649440928815410268203d040726b1a470348e651280a23994480108e03504cc2199243318860250403a081f80c390326e04071ec998192d0203ce4021cc960163702c66040f1ab158131c66c4e058840c96306200266e040d169998132b038709d88139952731e4e65204c9c099a2431f0266888c6c0b1a1f0303e62a064b0db101b02536628040dc08198163c2e05604070a8138100c266684a4c0880f813281ec4838ca0680d8133416026040d048078100903258098801194823140401008020081f00 i
def s46Tags := dagTraceTags s46Mask 34 (dagTagBases s46StockWords 0xe000e8e8307022f5af920eeed4f87de1e2e6f0edeb47ffc5c5f 0xf5f3e8e8f0623a94a9904ccac4d04ba18266e021c9428305c5c 34) 7 s46Data
def s46States := dagTrace s46Mask s46StockWords 7 s46Data
def s46Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])]
def s46Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s46Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s46MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s46Move0Stages, s46Move0Map, s46Move0Inverse)]
def s46Moves := dagMoves s46MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Autos : DagMovesOK s46Mask s46Goal 64 s46Moves := dagMovesOfCheck (by decide +kernel)
def s46Check := dagCheckNode s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) 98 s46States s46Moves s46Links s46Sample s46Tags
def s46RootAt (token : Nat) : Bool :=
  let s := rootState s46StockWords 7 token
  !dagAllowedRoot s46Witnesses s.2.1 || dagLocal s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) s ||
  dagRef 98 s46States s46Moves s46Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46RootBlock0 : treeBlock 0 64 s46RootAt = true := by decide +kernel
theorem s46Roots : dagCheckRoots s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) s46Witnesses (dagRef 98 s46States s46Moves s46Links 0) s46StockWords 7 = true := s46RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block0 : treeBlock 0 16 s46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block16 : treeBlock 16 16 s46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block32 : treeBlock 32 16 s46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block48 : treeBlock 48 16 s46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block64 : treeBlock 64 16 s46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block80 : treeBlock 80 16 s46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block96 : treeBlock 96 2 s46Check = true := by decide +kernel
theorem s46Verified : treeBlock 0 98 s46Check = true := (@treeBlock_merge 0 48 50 s46Check (@treeBlock_merge 0 16 32 s46Check s46Block0 (@treeBlock_merge 16 16 16 s46Check s46Block16 s46Block32)) (@treeBlock_merge 48 32 18 s46Check (@treeBlock_merge 48 16 16 s46Check s46Block48 s46Block64) (@treeBlock_merge 80 16 2 s46Check s46Block80 s46Block96)))
theorem s46Blocks : treeBlock 0 98 s46Check = true := s46Verified
theorem s46Known : Known s46Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s18Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Stock : Lower s46Mask s46StockWords s46Goal 8 := by
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
def s47Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev s47Goal : Nat := sGoal &&& s47Mask
abbrev s47StockWords : List Nat := projectDAGStock s47Mask sBase [0, 1, 3, 4, 5, 10]
def s47Fact : (Nat × List Nat × Nat × Nat) := (s47Mask, s47StockWords, 8, s47Goal)
def s47Cuts : List (Nat × List Nat × Nat × Nat) := [s18Fact]
def s47Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 19, 26, 35, 49, 50, 9, 9, 9, 9, 9, 9, 3, 17, 18, 33, 42, 56, 3, 3, 3, 3, 3, 3], rfl⟩
def s47Sample : (Nat × Nat) := (0x6032110c8301a050687039008c454231c06802190104c02131082414090182470190402422190182c44230904c2231108c442230188c703a0502c241a108a42432180c42213150e80613, 33)
def s47Witnesses := unpackWitnesses s47StockWords [4616, 271889, 528897, 1066499]
def s47Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0xda0da0da0da0d81d80d61d60d60d41d40d21d20d01d00d00d00d00ce1cc1cc0cc0cc0cc0cc0cc0cc0c63c60c609f49e09e09e09e09e09e09459409409409218c38c08c08c08a18a07c77c07c07c07827807806e56e06e06e06c16c06a16a06816806616606606606605c55c05c05c05c05c05c05a15a05a05a05815045005005004a34a04a04a04a04a04a04a040505e002 0x5c33c5a6285762855634536344e6344d9304793046624453245fc415ec3d5dc385b936599325864156635546295262551620503414f33d4c3294b3254a314490414803d4402943025420082a92c1c620063143c02a3b0083762831934380343601c3201c33c38316262d6203031d1b31412019050082d9342c0302a92c1a62004314290250200825c3c23328216341f3341c92c1b6291a62003314020081301c0f6281293411040100340e01c0c63c0b6300a6240692c0562904620033140200840c393f9373e9333d92d3a92c39637356333462b2f6292e6272b6212862027337263332432b223272031f1e31b1d3151931418037170331602b150271401f0d01b090130800f07009010084103f00037 12 5 12 7 1 5
def s47Data : (Nat → Nat × Nat) := fun i => decodeNode 7 19 0xc418587b0b0e2119e5c93684c516a4ca1320c2628aec6b098d2ab14c2634a6c4b0988211a0c233d84c693a4c26994c23258462908106101ec29308ac4914c922814c202584011080fc061c8193703266064b408153b00877258058dc081a366286e038d98cc0b1581c3860038c9899818eb062902c4e064d160182c62103258a40954b100133702666070f12995813284664e058d1098f813343e63604c540c961a62934c4068c50081b81033020560409c080f8101c2726838100701a0e6281e0383806c0b1e0a63014c482804c08078100903258098a41310023140401008020081b80 i
def s47Tags := dagTraceTags s47Mask 33 (dagTagBases s47StockWords 0x8758d419c005f3afde29caf9ccfe078bcd81cfae1dfffead 0x15bf59d4796244d2aa90298ae1d85806094931c5a609699e25 33) 7 s47Data
def s47States := dagTrace s47Mask s47StockWords 7 s47Data
def s47Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])]
def s47Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s47Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s47MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s47Move0Stages, s47Move0Map, s47Move0Inverse)]
def s47Moves := dagMoves s47MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Autos : DagMovesOK s47Mask s47Goal 64 s47Moves := dagMovesOfCheck (by decide +kernel)
def s47Check := dagCheckNode s47Mask s47Goal s47Chart (dagKnownCloses s47Goal s47Cuts) 96 s47States s47Moves s47Links s47Sample s47Tags
def s47RootAt (token : Nat) : Bool :=
  let s := rootState s47StockWords 7 token
  !dagAllowedRoot s47Witnesses s.2.1 || dagLocal s47Mask s47Goal s47Chart (dagKnownCloses s47Goal s47Cuts) s ||
  dagRef 96 s47States s47Moves s47Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47RootBlock0 : treeBlock 0 64 s47RootAt = true := by decide +kernel
theorem s47Roots : dagCheckRoots s47Mask s47Goal s47Chart (dagKnownCloses s47Goal s47Cuts) s47Witnesses (dagRef 96 s47States s47Moves s47Links 0) s47StockWords 7 = true := s47RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Block0 : treeBlock 0 16 s47Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Block16 : treeBlock 16 16 s47Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Block32 : treeBlock 32 16 s47Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Block48 : treeBlock 48 16 s47Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Block64 : treeBlock 64 16 s47Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Block80 : treeBlock 80 16 s47Check = true := by decide +kernel
theorem s47Verified : treeBlock 0 96 s47Check = true := (@treeBlock_merge 0 48 48 s47Check (@treeBlock_merge 0 16 32 s47Check s47Block0 (@treeBlock_merge 16 16 16 s47Check s47Block16 s47Block32)) (@treeBlock_merge 48 16 32 s47Check s47Block48 (@treeBlock_merge 64 16 16 s47Check s47Block64 s47Block80)))
theorem s47Blocks : treeBlock 0 96 s47Check = true := s47Verified
theorem s47Known : Known s47Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s18Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Stock : Lower s47Mask s47StockWords s47Goal 8 := by
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
    rcases h with rfl <;> decide +kernel
def s48Mask : Nat := 0xcccccccccccccccc
abbrev s48Goal : Nat := sGoal &&& s48Mask
abbrev s48StockWords : List Nat := projectDAGStock s48Mask sBase [0, 2, 3, 4, 5]
def s48Fact : (Nat × List Nat × Nat × Nat) := (s48Mask, s48StockWords, 8, s48Goal)
def s48Witnesses := unpackWitnesses s48StockWords [3590, 265731, 529923, 796163, 1066499]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Stock : Lower s48Mask s48StockWords s48Goal 8 := by
  apply essentialLift (witnesses := s48Witnesses) (cut := s19Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s19StockWords) (by decide +kernel)
  · exact s19Stock
  · decide +kernel
def s49Mask : Nat := 0xcccccccccccccccc
abbrev s49Goal : Nat := sGoal &&& s49Mask
abbrev s49StockWords : List Nat := projectDAGStock s49Mask sBase [0, 2, 3, 4, 5, 6]
def s49Fact : (Nat × List Nat × Nat × Nat) := (s49Mask, s49StockWords, 8, s49Goal)
def s49Cuts : List (Nat × List Nat × Nat × Nat) := [s19Fact]
def s49Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[7, 11, 14, 19, 22, 26, 35, 38, 50, 7, 7, 7, 3, 6, 18, 42, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s49Sample : (Nat × Nat) := (0x423150c8542615068540e0102c04070104c2432030380c160188c0c07090680607150b8060b150e80c260184c2416150ac2413, 23)
def s49Witnesses := unpackWitnesses s49StockWords [265731, 529923, 796163, 1066499]
def s49Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x13102600cbc197812d0a541ca80950126124c04980930126024c049809301240a480454f8a811502280c50089831302240c480888311021e143c087030d061a04301840908020e0c14282030402060c0c08102fe11fc03f417e80fb09f40be807c82f901f00bd047a00f305e603c427802f001de0bbc07702ea11a8b34c16902d1059e133816604cc0198032c1628cc501880b0c16102c10582030015e08bb057602d075982b2056012bc15780af015e02bc05780af015a12b405194a30146028c05180a30132526404b0696012c025804a829405260a48147868f011e023c047808f01181a2c145028a011402241430685050809c5338807004e001bc136846c04d801ac133886700cc0990232006304c6018c031805d18ba017012e005b04b6016812d005808b0015c12b025210a2093c227024b0c9409241230646008a0910121044200820904020023e087228e401c0238006c10d801a8234046800cc117882f005c08b8016822d005a00b4016802a0c5400a801482221c0500002 0xbd9340c36400c29400c60401c39340af0280ac0240c36340c263009c01c0990180bb01c0ba0100c0c380bf9360be9322b56292b36250bd6200b53290b33250b13140bc0360b90320b801e0a301a09201208f00e0b59400b39400b16340af3280ad01c0a80100ab3280033280a83280ac6340aa0280a901c0a70100a53340a103409f0100a13340a132809f3280a36340a20340a001c09e01009c33409a01c09501000333409732809532809963409803409602809401009263408b03409001c08b33408d32808b32808f63408e03408c02808a01c1c7c410c9c382b49412b293d0c892c0c76410c563d0c46360c16350b76340b66200b43410b233d0b03140ae0360a60320a402a09d02609b01e09301a09101208900e05b63406d32800332806c63408501c00302806b63408301800333407492c03962000b31408101e08001907f00807d33405463406a32800362807802831264006833407931c07701c05363407492c06762a06462905062803862000a31400200806333400333406263407103404632431332806901006ec3806d62a06c62606b62006a31d06831906731403001d02d019009008065c3806462006332a06232606131e04231a03d31401701101400d00800805262000731400300824c01c05a32424c01024c02805863424d32805701005292c00631405100804e02404c01004c02804e33404d02804b01c01d32804900c05f92d05e92c05d62b05c62705b62105932b05632705531f05431b05331505031404f02b04a02703401f03201b04801302500f00d00900500804663404433421332804001000333404002804263421234004133403f01000301c03d63403c03003a00c03992c03862000431403702a03602500200803463403263403032811302802e01c02c32800332802d63411204002b02802a01c02400c02833402201801d02802631c01c03402102801b02801b02802432802302801a01002163401d02801c33401f01c01d01001b01c01c32801a01c02563402232802004001e03401901c01733401302801501c01363400333401032801463401204001103400f02800d63400662800792c00631400300800332800b92c00a62000932a008329005328004314002008087c3908693708493308292d07e92c07c63707b63307a62b07662707562107362007233707033306f32b06632a06032904732804532704331f03e31b03b31503531403303703103302f02b02902702701f01801b01601300e00f00c00900100808803f00003e 15 6 12 8 4 6
def s49Data : (Nat → Nat × Nat) := fun i => decodeNode 8 20 0xc388992c8964189040c663d8963689634c2630c263589c38b8936b8932b8620b8036b801cba010ba032b801eb86348962089940b534189940b333d89634b131489328af0368901cad634a7328ab028a701ca7328a8010a703289334a502a896349e0349e328a101c9e3289f0109e026893349c01e8901c9a63494034943289702894328950109401a89634920128901c906348a0348a3288d0288a3288b01c8a00e8903f00c39019370101c85933010188392d0101e7f0197f0087f92c013347d637016330162b0131c770287801c77627016210192c746200133701034713330132b01c386762a67626676206731d6701069319673146732a01c38616206132a613266131e613290192d4892c4862b4862748621483245a32b4863457010573274831f4831b483154892c51008513144802b483344b0284b0284c01c4b0274800c49013483280163446327013344431f016343f3343f028400103f31b016343c0303c3150100c3a92c366203602a360253631401634340370163432033013283002b0101c2e6342a3282c0282a01c2a027013342801f0131c2663419328230282332819634210401901c1f034190101d3281a01c1b01c1a01c1901b01334170130101c156340f634130400f0340f328100280f00f016340d0090192c026200232a023290292c0631406328023140232803008020080103e00 i
def s49Tags := dagTraceTags s49Mask 23 (dagTagBases s49StockWords 0x1e395a7048b251a45a388b88a9aca438d4b 0x3ffb5bbc00a200840af0028801a08000948 23) 7 s49Data
def s49States := dagTrace s49Mask s49StockWords 7 s49Data
def s49Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])]
def s49Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val)
def s49Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val)
def s49Move1Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])]
def s49Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s49Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)
def s49Move2Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xf0000f0000f0000f, 0), (0xf0000f0000f0, 12), (0xf0000f00, 24), (0xf000, 36)], [(0xf0000f0000f0000, 12), (0xf0000f00000000, 24), (0xf000000000000, 36)])]
def s49Move2Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 5, 2, 3] 0 i.val)
def s49Move2Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 4, 5, 2, 3] 0 i.val)
def s49Move3Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])]
def s49Move3Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s49Move3Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)
def s49Move4Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa500a50000a500a5, 0), (0xa000a00000a000a, 3), (0x50005000, 21), (0xa500a500, 24), (0xa000a00, 27)], [(0x5000500000500050, 3), (0xa000a00000000, 21), (0xa500a500000000, 24), (0x50005000000000, 27)])]
def s49Move4Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 5, 4, 3] 0 i.val)
def s49Move4Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 5, 4, 3] 0 i.val)
def s49Move5Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa0a00505a0a00505, 0), (0xa0a00000a0a, 3), (0x505000005050, 12), (0xa0a00000a0a0, 15)], [(0x5050000050500000, 3), (0xa0a00000a0a0000, 12), (0x505000005050000, 15)])]
def s49Move5Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 0, 3, 2, 5] 0 i.val)
def s49Move5Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 4, 3, 0, 5] 0 i.val)
def s49Move6Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xa0a00505a0a00505, 0), (0xa0a00000a0a0000, 3), (0xa0a00000a0a0, 12), (0xa0a00000a0a, 15)], [(0x505000005050, 3), (0x505000005050000, 12), (0x5050000050500000, 15)])]
def s49Move6Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 4, 3, 0, 5] 0 i.val)
def s49Move6Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 0, 3, 2, 5] 0 i.val)
def s49Move7Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xaaaa5555aaaa5555, 0), (0xaaaa0000aaaa, 15)], [(0x5555000055550000, 15)])]
def s49Move7Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s49Move7Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [4, 1, 2, 3, 0, 5] 0 i.val)
def s49MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s49Move0Stages, s49Move0Map, s49Move0Inverse), (s49Move1Stages, s49Move1Map, s49Move1Inverse), (s49Move2Stages, s49Move2Map, s49Move2Inverse), (s49Move3Stages, s49Move3Map, s49Move3Inverse), (s49Move4Stages, s49Move4Map, s49Move4Inverse), (s49Move5Stages, s49Move5Map, s49Move5Inverse), (s49Move6Stages, s49Move6Map, s49Move6Inverse), (s49Move7Stages, s49Move7Map, s49Move7Inverse)]
def s49Moves := dagMoves s49MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Autos : DagMovesOK s49Mask s49Goal 64 s49Moves := dagMovesOfCheck (by decide +kernel)
def s49Check := dagCheckNode s49Mask s49Goal s49Chart (dagKnownCloses s49Goal s49Cuts) 202 s49States s49Moves s49Links s49Sample s49Tags
def s49RootAt (token : Nat) : Bool :=
  let s := rootState s49StockWords 7 token
  !dagAllowedRoot s49Witnesses s.2.1 || dagLocal s49Mask s49Goal s49Chart (dagKnownCloses s49Goal s49Cuts) s ||
  dagRef 202 s49States s49Moves s49Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49RootBlock0 : treeBlock 0 64 s49RootAt = true := by decide +kernel
theorem s49Roots : dagCheckRoots s49Mask s49Goal s49Chart (dagKnownCloses s49Goal s49Cuts) s49Witnesses (dagRef 202 s49States s49Moves s49Links 0) s49StockWords 7 = true := s49RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block0 : treeBlock 0 16 s49Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block16 : treeBlock 16 16 s49Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block32 : treeBlock 32 16 s49Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block48 : treeBlock 48 16 s49Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block64 : treeBlock 64 16 s49Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block80 : treeBlock 80 16 s49Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block96 : treeBlock 96 16 s49Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block112 : treeBlock 112 16 s49Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block128 : treeBlock 128 16 s49Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block144 : treeBlock 144 16 s49Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block160 : treeBlock 160 16 s49Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block176 : treeBlock 176 16 s49Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Block192 : treeBlock 192 10 s49Check = true := by decide +kernel
theorem s49Verified : treeBlock 0 202 s49Check = true := (@treeBlock_merge 0 96 106 s49Check (@treeBlock_merge 0 48 48 s49Check (@treeBlock_merge 0 16 32 s49Check s49Block0 (@treeBlock_merge 16 16 16 s49Check s49Block16 s49Block32)) (@treeBlock_merge 48 16 32 s49Check s49Block48 (@treeBlock_merge 64 16 16 s49Check s49Block64 s49Block80))) (@treeBlock_merge 96 48 58 s49Check (@treeBlock_merge 96 16 32 s49Check s49Block96 (@treeBlock_merge 112 16 16 s49Check s49Block112 s49Block128)) (@treeBlock_merge 144 32 26 s49Check (@treeBlock_merge 144 16 16 s49Check s49Block144 s49Block160) (@treeBlock_merge 176 16 10 s49Check s49Block176 s49Block192))))
theorem s49Blocks : treeBlock 0 202 s49Check = true := s49Verified
theorem s49Known : Known s49Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s19Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Stock : Lower s49Mask s49StockWords s49Goal 8 := by
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
def s50Mask : Nat := 0xffffffff00000000
abbrev s50Goal : Nat := sGoal &&& s50Mask
abbrev s50StockWords : List Nat := projectDAGStock s50Mask sBase [0, 1, 2, 3, 4]
def s50Fact : (Nat × List Nat × Nat × Nat) := (s50Mask, s50StockWords, 7, s50Goal)
def s50Cuts : List (Nat × List Nat × Nat × Nat) := [s21Fact, s23Fact, s25Fact, s26Fact]
def s50Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[35, 37, 38, 41, 44, 49, 50, 35, 35, 35, 35, 35, 33, 42, 52, 56, 33, 33, 33, 33, 33, 33, 33, 33], rfl⟩
def s50Sample : (Nat × Nat) := (0x1a0f05029120984225108c442291c0f0703a1a0d4543a120b044261088c4423, 14)
def s50Witnesses := unpackWitnesses s50StockWords [17954, 280097, 543265, 807457, 1073697]
def s50Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x141f 3 1 5 1 1 1
def s50Data : (Nat → Nat × Nat) := fun i => decodeNode 1 6 0x47e i
def s50Tags := dagTraceTags s50Mask 14 (dagTagBases s50StockWords 0x22f0c762cac215d723 0x20e043428280054702 14) 6 s50Data
def s50States := dagTrace s50Mask s50StockWords 6 s50Data
def s50Move0Stages : (List (List (Nat × Nat) × List (Nat × Nat))) := [([(0xc30000c3c30000c3, 0), (0xc00000c0c00000c, 2), (0x300000003000, 6), (0xc3000000c300, 8), (0xc0000000c00, 10)], [(0x3000003030000030, 2), (0xc0000000c0000, 6), (0xc3000000c30000, 8), (0x30000000300000, 10)])]
def s50Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val)
def s50Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 2, 1, 4, 3, 5] 0 i.val)
def s50MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(s50Move0Stages, s50Move0Map, s50Move0Inverse)]
def s50Moves := dagMoves s50MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Autos : DagMovesOK s50Mask s50Goal 64 s50Moves := dagMovesOfCheck (by decide +kernel)
def s50Check := dagCheckNode s50Mask s50Goal s50Chart (dagKnownCloses s50Goal s50Cuts) 2 s50States s50Moves s50Links s50Sample s50Tags
def s50RootAt (token : Nat) : Bool :=
  let s := rootState s50StockWords 6 token
  !dagAllowedRoot s50Witnesses s.2.1 || dagLocal s50Mask s50Goal s50Chart (dagKnownCloses s50Goal s50Cuts) s ||
  dagRef 2 s50States s50Moves s50Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50RootBlock0 : treeBlock 0 32 s50RootAt = true := by decide +kernel
theorem s50Roots : dagCheckRoots s50Mask s50Goal s50Chart (dagKnownCloses s50Goal s50Cuts) s50Witnesses (dagRef 2 s50States s50Moves s50Links 0) s50StockWords 6 = true := s50RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Block0 : treeBlock 0 2 s50Check = true := by decide +kernel
theorem s50Blocks : treeBlock 0 2 s50Check = true := s50Block0
theorem s50Known : Known s50Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s26Stock) s25Stock) s23Stock) s21Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Stock : Lower s50Mask s50StockWords s50Goal 7 := by
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
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s51Mask : Nat := 0x5555555555555555
abbrev s51Goal : Nat := sGoal &&& s51Mask
abbrev s51StockWords : List Nat := projectDAGStock s51Mask sBase [1, 2, 3, 4, 5]
def s51Fact : (Nat × List Nat × Nat × Nat) := (s51Mask, s51StockWords, 7, s51Goal)
def s51Cuts : List (Nat × List Nat × Nat × Nat) := [s29Fact, s30Fact, s31Fact, s34Fact]
def s51Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[12, 22, 26, 38, 50, 12, 12, 12, 12, 12, 12, 12, 6, 18, 42, 52, 56, 6, 6, 6, 6, 6, 6, 6], rfl⟩
def s51Sample : (Nat × Nat) := (0x443211098241a030580c261a0f02416090c848260c068141a02030100c, 13)
def s51Witnesses := unpackWitnesses s51StockWords [11284, 268296, 530436, 797702, 1068038]
def s51Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x119 0x71401f 3 1 10 1 1 1
def s51Data : (Nat → Nat × Nat) := fun i => decodeNode 1 11 0x31483e i
def s51Tags := dagTraceTags s51Mask 13 (dagTagBases s51StockWords 0x19b0b76123d7a7f7c 0x18902740034725f64 13) 6 s51Data
def s51States := dagTrace s51Mask s51StockWords 6 s51Data
def s51MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s51Moves := dagMoves s51MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Autos : DagMovesOK s51Mask s51Goal 64 s51Moves := dagMovesOfCheck (by decide +kernel)
def s51Check := dagCheckNode s51Mask s51Goal s51Chart (dagKnownCloses s51Goal s51Cuts) 2 s51States s51Moves s51Links s51Sample s51Tags
def s51RootAt (token : Nat) : Bool :=
  let s := rootState s51StockWords 6 token
  !dagAllowedRoot s51Witnesses s.2.1 || dagLocal s51Mask s51Goal s51Chart (dagKnownCloses s51Goal s51Cuts) s ||
  dagRef 2 s51States s51Moves s51Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51RootBlock0 : treeBlock 0 32 s51RootAt = true := by decide +kernel
theorem s51Roots : dagCheckRoots s51Mask s51Goal s51Chart (dagKnownCloses s51Goal s51Cuts) s51Witnesses (dagRef 2 s51States s51Moves s51Links 0) s51StockWords 6 = true := s51RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Block0 : treeBlock 0 2 s51Check = true := by decide +kernel
theorem s51Blocks : treeBlock 0 2 s51Check = true := s51Block0
theorem s51Known : Known s51Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s34Stock) s31Stock) s30Stock) s29Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Stock : Lower s51Mask s51StockWords s51Goal 7 := by
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
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s52Mask : Nat := 0xffff0000ffff
abbrev s52Goal : Nat := sGoal &&& s52Mask
abbrev s52StockWords : List Nat := projectDAGStock s52Mask sBase [0, 1, 2, 3, 5]
def s52Fact : (Nat × List Nat × Nat × Nat) := (s52Mask, s52StockWords, 6, s52Goal)
def s52Witnesses := unpackWitnesses s52StockWords [2564, 280097, 526849, 791041, 1066499]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52Stock : Lower s52Mask s52StockWords s52Goal 6 := by
  apply essentialLift (witnesses := s52Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s53Mask : Nat := 0x3333333333333333
abbrev s53Goal : Nat := sGoal &&& s53Mask
abbrev s53StockWords : List Nat := projectDAGStock s53Mask sBase [0, 2, 3, 4, 5]
def s53Fact : (Nat × List Nat × Nat × Nat) := (s53Mask, s53StockWords, 6, s53Goal)
def s53Witnesses := unpackWitnesses s53StockWords [2564, 264705, 528897, 811553, 1073681]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Stock : Lower s53Mask s53StockWords s53Goal 6 := by
  apply essentialLift (witnesses := s53Witnesses) (cut := s5Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s5StockWords) (by decide +kernel)
  · exact s5Stock
  · decide +kernel
def s54Mask : Nat := 0xaaaaaaaaaaaaaaaa
abbrev s54Goal : Nat := sGoal &&& s54Mask
abbrev s54StockWords : List Nat := projectDAGStock s54Mask sBase [1, 2, 3, 4, 5]
def s54Fact : (Nat × List Nat × Nat × Nat) := (s54Mask, s54StockWords, 6, s54Goal)
def s54Witnesses := unpackWitnesses s54StockWords [9745, 264705, 528897, 796163, 1066499]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Stock : Lower s54Mask s54StockWords s54Goal 6 := by
  apply essentialLift (witnesses := s54Witnesses) (cut := s32Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s32StockWords) (by decide +kernel)
  · exact s32Stock
  · decide +kernel
def s55Mask : Nat := 0xffffffffffffffff
abbrev s55Goal : Nat := sGoal &&& s55Mask
abbrev s55StockWords : List Nat := projectDAGStock s55Mask sBase [0, 1, 2, 3, 4, 5]
def s55Cuts : List (Nat × List Nat × Nat × Nat) := [s38Fact, s45Fact, s48Fact, s42Fact, s51Fact, s18Fact, s35Fact, s17Fact, s20Fact, s50Fact, s19Fact, s21Fact, s54Fact, s39Fact, s36Fact, s41Fact, s46Fact, s43Fact, s40Fact, s47Fact, s5Fact, s53Fact, s44Fact, s49Fact, s37Fact, s24Fact, s33Fact, s26Fact, s31Fact, s22Fact, s0Fact, s6Fact, s52Fact, s28Fact, s27Fact, s32Fact, s1Fact]
def s55Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[5, 9, 12, 19, 22, 26, 35, 38, 49, 50, 5, 5, 3, 6, 17, 18, 33, 42, 52, 56, 3, 3, 3, 3], rfl⟩
def s55Sample : (Nat × Nat) := (0x1082442050201460321508c141a150b82816120142805030144432150ac68320182c68261a0c406130c06422190904c241a0884c060708854703c0309868351a0f04223088c40c16090c85029108c4301a090580c0e0301c543a1089448260188c4229, 44)
def s55Witnesses := unpackWitnesses s55StockWords [2564, 271889, 526849, 791041, 1058307, 1328643]
def s55Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x8438218208208208207a47a07437407026e16e06a26a06816615a65a05625605415215205204e24e04c14c04c04823e53e03e03a23a03a03a03a03813803803802a72a02a02a0281223220220030001 0x58c38263372032b0e31b60f445ec3f5c03f3a03358f443e34338333426200c31b4a0114e92c1a01d4a3363603c5032b4c32a3403d1802b4801346011426201231f3e92c320343631c2c0363294c2e92c2c33d3ac4d38c383463d300362a02a2725024c3e1a328212501e93f1c93e1833f1632714325123140a92c0ef440c92c0802a66f4464c38629435a9415692c546435262044333403143c043280332202b1001f0600f04009020080003f 12 5 13 6 1 5
def s55Data : (Nat → Nat × Nat) := fun i => decodeNode 6 19 0x7a202c38052860bd12e61fdc03fb92820bd12c4960264304c4008cae34964e32a8c66d2804e3008c633304c4108c5014963e0430589aab0e1518e3663d55298c80d954962c33d58054a80cc192824c3e480560c940949f9293e2465068cfc919392325246284807c17a20892c11258280a840078200904010080fc0 i
def s55Tags := dagTraceTags s55Mask 44 (dagTagBases s55StockWords 0x1a1d807ee1f1514fedbb90860a344855163e101f90ec1f1f4f259f6e8eafb9662b 0xda9d805c61d1145beda9800e08204051021e580390640e3a4d218f2c002538620b 44) 10 s55Data
def s55States := dagTrace s55Mask s55StockWords 10 s55Data
def s55MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s55Moves := dagMoves s55MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Autos : DagMovesOK s55Mask s55Goal 64 s55Moves := dagMovesOfCheck (by decide +kernel)
def s55Check := dagCheckNode s55Mask s55Goal s55Chart (dagKnownCloses s55Goal s55Cuts) 52 s55States s55Moves s55Links s55Sample s55Tags
def s55RootAt (token : Nat) : Bool :=
  let s := rootState s55StockWords 10 token
  !dagAllowedRoot s55Witnesses s.2.1 || dagLocal s55Mask s55Goal s55Chart (dagKnownCloses s55Goal s55Cuts) s ||
  dagRef 52 s55States s55Moves s55Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55RootBlock0 : treeBlock 0 64 s55RootAt = true := by decide +kernel
theorem s55Roots : dagCheckRoots s55Mask s55Goal s55Chart (dagKnownCloses s55Goal s55Cuts) s55Witnesses (dagRef 52 s55States s55Moves s55Links 0) s55StockWords 10 = true := s55RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Block0 : treeBlock 0 16 s55Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Block16 : treeBlock 16 16 s55Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Block32 : treeBlock 32 16 s55Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Block48 : treeBlock 48 4 s55Check = true := by decide +kernel
theorem s55Verified : treeBlock 0 52 s55Check = true := (@treeBlock_merge 0 32 20 s55Check (@treeBlock_merge 0 16 16 s55Check s55Block0 s55Block16) (@treeBlock_merge 32 16 4 s55Check s55Block32 s55Block48))
theorem s55Blocks : treeBlock 0 52 s55Check = true := s55Verified
theorem s55Known : Known s55Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s1Stock) s32Stock) s27Stock) s28Stock) s52Stock) s6Stock) s0Stock) s22Stock) s31Stock) s26Stock) s33Stock) s24Stock) s37Stock) s49Stock) s44Stock) s53Stock) s5Stock) s47Stock) s40Stock) s43Stock) s46Stock) s41Stock) s36Stock) s39Stock) s54Stock) s21Stock) s19Stock) s50Stock) s20Stock) s17Stock) s35Stock) s18Stock) s51Stock) s42Stock) s48Stock) s45Stock) s38Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Stock : Lower s55Mask s55StockWords s55Goal 11 := by
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
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
end PEqualNP.Outside.L_meta_44162

open PEqualNP.Outside.L_meta_44162 in
theorem PEqualNP.Outside.L_meta_44162 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4276681376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4276681376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro t h
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
  let goal : BitVec 64 := 0xfeeefae8fee8faa0
  have root : Lower (fullMask 64) (raw.map BitVec.toNat) goal.toNat 11 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s55Stock
  have size : 11 ≤ t :=
    hcsLower (n := 6) raw goal 11 _ (by decide +kernel) (by decide +kernel) root t h
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [12, 9]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [14, 15]⟩], 16⟩
  refine ⟨circuit, ?_, ?_, by decide +kernel⟩
  · intro gate member
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : circuit.size ≤ 11) size
