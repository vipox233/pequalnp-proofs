import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43098

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

def full : ℕ := ((1 <<< 144) - 1)

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

def rowM : ℕ := (1 <<< 0) ||| (1 <<< 12) ||| (1 <<< 24) ||| (1 <<< 36) ||| (1 <<< 48) ||| (1 <<< 60) ||| (1 <<< 72) ||| (1 <<< 84) ||| (1 <<< 96) ||| (1 <<< 108) ||| (1 <<< 120) ||| (1 <<< 132)

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
        (if ws.length == fuel + 1 then !dagPartition true ws goal (mask ^^^ goal)
         else !dagPartition false ws goal (mask ^^^ goal)) ||
        (if ws.length == fuel + 1 then
           chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c)))
         else false) || cut state))

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

def pageLinks (idx codeAt : Nat → Nat) (sizeBits tokenBits destinationBits trials : Nat) :
    (Nat → Nat → Option (Nat × Nat)) := fun parent token =>
  let entry := idx parent
  let size := entry &&& ((1 <<< sizeBits) - 1)
  let offset := entry >>> sizeBits
  (Nat.rec (motive := fun _ => Nat → Nat → Option (Nat × Nat)) (fun _ _ => none)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo+hi)/2
        let code := codeAt mid
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

def moveStage0 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])
def moveStage1 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcc33cc33cc33cc33, 0), (0xcc00cc00cc00cc, 6)], [(0x3300330033003300, 6)])
def moveStage2 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])
def moveStage3 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])
def moveStage4 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])
def moveStage5 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])
def moveStages : Array (List (Nat × Nat) × List (Nat × Nat)) := [moveStage0, moveStage1, moveStage2, moveStage3, moveStage4, moveStage5].toArray
def sBase : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def sGoal : Nat := 0xfee8eee0eee0eac0
def cbits (ws : List Nat) : Nat := ws.foldr (fun a z => (z <<< 64) ||| a) 0
def st14 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])
def pm0 : List (List (Nat × Nat) × List (Nat × Nat)) := [st14]
def st15 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcccccccc33333333, 0), (0xcccccccc, 30)], [(0x3333333300000000, 30)])
def pm1 : List (List (Nat × Nat) × List (Nat × Nat)) := [st14, st15]
def s0Blob175541 : Nat := (cbits [0x8540a150281c0607, 0xc422502894261708, 0x233118cc26331189, 0x70981c0207188d46, 0x8854261500854460, 0x9422170285c06171, 0x627188944625008, 0x33018cc42270289c, 0x88d40a35108cc22, 0x8dc4637098dc4235, 0x406151081c220718, 0x2171185c02171085, 0x70089c2225018946, 0x8d402331889c262, 0xdc0637118d426350, 0x6207108dc2237028, 0x2709894421711854, 0x8dc0635028cc22])
def s0Blob175931 : Nat := (cbits [0xb5f1e73e3f1c7793, 0xdffeffffc7fff8ff, 0xe6ff07cff81f8f1c, 0xf8fff80fffe00fe0])
def s0Blob176046 : Nat := (cbits [0x4a1c4a4609456391, 0x2020000042080026, 0x1944d41a90932d18, 0x78886ad24c24ec0])
def s0Mask : Nat := 0xaa00aa00aa00aa
abbrev s0Goal : Nat := sGoal &&& s0Mask
abbrev s0StockWords : List Nat := [0x88008800880088, 0xa000a000a000a0, 0xaa000000aa0000, 0xaa00aa00000000]
def s0Fact : Nat × List Nat × Nat × Nat := (s0Mask, s0StockWords, 6, s0Goal)
def s0Cuts : List (Nat × List Nat × Nat × Nat) := []
def s0Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 21, 37, 51, 7, 21, 37, 51, 7, 21, 37, 51, 5, 19, 35, 49, 5, 19, 35, 49, 5, 19, 35, 49], rfl⟩
def s0Witnesses := unpackWitnesses s0StockWords [3589, 265731, 535045, 805381]
def s0Index (i : Nat) : Nat := unpack 0xa28301 6 i
def s0Codes (i : Nat) : Nat := unpack (cbits [0x31010c504010000f, 0x1292c5]) 17 i
def s0Forest (i : Nat) : Nat := unpack 0x3144010803c 15 i
def s0Links := pageLinks s0Index s0Codes 3 13 2 4
def s0Data (i : Nat) : Nat × Nat :=
  let e := s0Forest i
  (e &&& 3, e >>> 2)
def s0Sample : Nat × Nat := (s0Blob175541, 64)
def s0Tags := dagTraceTags s0Mask 64 (dagTagBases s0StockWords s0Blob175931 s0Blob176046 64) 5 s0Data
def s0States := dagTrace s0Mask s0StockWords 5 s0Data
def s0MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 5, 2, 3, 1, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 5, 1] 0 i.val)))]
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 64 s0Moves := dagMovesOfCheck (by decide +kernel)
def s0Check := dagCheckNode s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) 3 s0States s0Moves s0Links s0Sample s0Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Roots : dagCheckRoots s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s0Witnesses (dagRef 3 s0States s0Moves s0Links 0) s0StockWords 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block0 : treeBlock 0 3 s0Check = true := by decide +kernel
theorem s0Blocks : treeBlock 0 3 s0Check = true := s0Block0
theorem s0Known : Known s0Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Stock : Lower s0Mask s0StockWords s0Goal 6 := by
  apply lowerDag _ _ _ _ s0Autos _ _ _ s0Known _ s0Roots s0Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s0Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s1Blob178927 : Nat := (cbits [0xd46235190cc6233, 0x460331a0d864361a, 0x437188dc6036180d, 0x6190d468331a0dc6, 0x180dc623])
def s1Blob179053 : Nat := 0xefbcdf73becf
def s1Blob179094 : Nat := 0x182824124205
def s1Mask : Nat := 0xff000000000000
abbrev s1Goal : Nat := sGoal &&& s1Mask
abbrev s1StockWords : List Nat := [0xaa000000000000, 0xcc000000000000, 0xf0000000000000]
def s1Fact : Nat × List Nat × Nat × Nat := (s1Mask, s1StockWords, 4, s1Goal)
def s1Cuts : List (Nat × List Nat × Nat × Nat) := []
def s1Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[51, 53, 54, 51, 53, 54, 51, 53, 54, 51, 53, 54, 49, 50, 52, 49, 50, 52, 49, 50, 52, 49, 50, 52], rfl⟩
def s1Witnesses := unpackWitnesses s1StockWords [26162, 288305, 551473]
def s1Index (i : Nat) : Nat := unpack 0x9 2 i
def s1Codes (i : Nat) : Nat := unpack 0x7 15 i
def s1Forest (i : Nat) : Nat := unpack 0xe 14 i
def s1Links := pageLinks s1Index s1Codes 1 13 1 2
def s1Data (i : Nat) : Nat × Nat :=
  let e := s1Forest i
  (e &&& 1, e >>> 1)
def s1Sample : Nat × Nat := (s1Blob178927, 16)
def s1Tags := dagTraceTags s1Mask 16 (dagTagBases s1StockWords s1Blob179053 s1Blob179094 16) 3 s1Data
def s1States := dagTrace s1Mask s1StockWords 3 s1Data
def s1MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s1Moves := dagMoves s1MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Autos : DagMovesOK s1Mask s1Goal 64 s1Moves := dagMovesOfCheck (by decide +kernel)
def s1Check := dagCheckNode s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) 1 s1States s1Moves s1Links s1Sample s1Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Roots : dagCheckRoots s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) s1Witnesses (dagRef 1 s1States s1Moves s1Links 0) s1StockWords 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Block0 : treeBlock 0 1 s1Check = true := by decide +kernel
theorem s1Blocks : treeBlock 0 1 s1Check = true := s1Block0
theorem s1Known : Known s1Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Stock : Lower s1Mask s1StockWords s1Goal 4 := by
  apply lowerDag _ _ _ _ s1Autos _ _ _ s1Known _ s1Roots s1Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s1Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s2Mask : Nat := 0xff000000ff0000
abbrev s2Goal : Nat := sGoal &&& s2Mask
abbrev s2StockWords : List Nat := [0xaa000000aa0000, 0xcc000000cc0000, 0xf0000000f00000, 0xff000000000000]
def s2Fact : Nat × List Nat × Nat × Nat := (s2Mask, s2StockWords, 5, s2Goal)
def s2Witnesses := unpackWitnesses s2StockWords [10772, 273428, 535057, 812563]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Stock : Lower s2Mask s2StockWords s2Goal 5 := by
  apply essentialLift (witnesses := s2Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
def st45 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])
def pm2 : List (List (Nat × Nat) × List (Nat × Nat)) := [st45]
def s3Mask : Nat := 0xff00ff00000000
abbrev s3Goal : Nat := sGoal &&& s3Mask
abbrev s3StockWords : List Nat := [0xaa00aa00000000, 0xcc00cc00000000, 0xf000f000000000, 0xff000000000000]
def s3Fact : Nat × List Nat × Nat × Nat := (s3Mask, s3StockWords, 5, s3Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Stock : Lower s3Mask s3StockWords s3Goal 5 := dagShiftLower (width := 64) pm2 s2Stock (by decide +kernel)
def s4Blob185459 : Nat := (cbits [0x81c0607020180406, 0x82815088540a1502, 0xa250985c28160905, 0x6110984825108940, 0x18cc26331189c482, 0xd46235190cc62331, 0x61a0d864361a0, 0x6090180a0601818, 0x81c48061101828, 0x81c26070201c0407, 0x4201502054021511, 0x4161a05462150985, 0x6098582016020580, 0x285c06171a058641, 0x9428170905c22170, 0x4625100940825008, 0x2601098682518894, 0x1909846261009808, 0x89c0a270189c6826, 0xc06331209c442710, 0x433108cc2433088c, 0x5088d40a35180cc4, 0x80d44835108d4283, 0xd844360a0d824361, 0x4637098dc6036120, 0x61a0dc6437188dc, 0x1001826060801802])
def s4Blob186027 : Nat := (cbits [0x7ff03ff803f9e7c, 0xffcfe38f0f83fffe, 0xfffc0ffff81ffc0f, 0xfffffffffff0ffff, 0xff03f0fffff03f, 0xfffffc0001ffff0, 0xffe0000000fffc00, 0xfffffff])
def s4Blob186209 : Nat := (cbits [0x4327219c86178e3c, 0x2a4ba2855380b2ce, 0x45940552c909648d, 0x14528a2254a0555a, 0x18fd03e008295025, 0x6ece6981861cf3c4, 0xe780c30860fef800, 0x8f738e39])
def s4Mask : Nat := 0xff00ff00ff00ff
abbrev s4Goal : Nat := sGoal &&& s4Mask
abbrev s4StockWords : List Nat := [0xaa00aa00aa00aa, 0xcc00cc00cc00cc, 0xf000f000f000f0, 0xff000000ff0000, 0xff00ff00000000]
def s4Fact : Nat × List Nat × Nat × Nat := (s4Mask, s4StockWords, 8, s4Goal)
def s4Cuts : List (Nat × List Nat × Nat × Nat) := [s0Fact, s2Fact, s3Fact, s1Fact]
def s4Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 21, 37, 51, 6, 21, 37, 51, 6, 21, 37, 51, 5, 19, 35, 49, 50, 52, 5, 19, 35, 49, 50, 52], rfl⟩
def s4Witnesses := unpackWitnesses s4StockWords [10772, 265220, 527362, 797189, 1067525]
def s4Index (i : Nat) : Nat := unpack (cbits [0xc0201008034c3801, 0x2c16099cc2613081, 0xb158]) 9 i
def s4Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xc6c831508c50001f, 0x3233348c9cc31f28, 0x6336989d86215188, 0xc11883cc38724b3a, 0x9b0e0692]) else (cbits [0x883093c424c0e024, 0x6620db0e1692c11, 0x5a4b])) 18 (i % 16)
def s4Forest (i : Nat) : Nat := unpack (cbits [0x96118808628201f0, 0x238c7c4636231514, 0x59880464e2930701, 0x24b04c4e26211496]) 17 i
def s4Links := pageLinks s4Index s4Codes 4 13 4 5
def s4Data (i : Nat) : Nat × Nat :=
  let e := s4Forest i
  (e &&& 15, e >>> 4)
def s4Sample : Nat × Nat := (s4Blob185459, 96)
def s4Tags := dagTraceTags s4Mask 96 (dagTagBases s4StockWords s4Blob186027 s4Blob186209 96) 7 s4Data
def s4States := dagTrace s4Mask s4StockWords 7 s4Data
def s4MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)))]
def s4Moves := dagMoves s4MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Autos : DagMovesOK s4Mask s4Goal 64 s4Moves := dagMovesOfCheck (by decide +kernel)
def s4Check := dagCheckNode s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) 15 s4States s4Moves s4Links s4Sample s4Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Roots : dagCheckRoots s4Mask s4Goal s4Chart (dagKnownCloses s4Goal s4Cuts) s4Witnesses (dagRef 15 s4States s4Moves s4Links 0) s4StockWords 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Block0 : treeBlock 0 15 s4Check = true := by decide +kernel
theorem s4Blocks : treeBlock 0 15 s4Check = true := s4Block0
theorem s4Known : Known s4Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s1Stock) s3Stock) s2Stock) s0Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Stock : Lower s4Mask s4StockWords s4Goal 8 := by
  apply lowerDag _ _ _ _ s4Autos _ _ _ s4Known _ s4Roots s4Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s4Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def st03 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xaa55aa55aa55aa55, 0), (0xaa00aa00aa00aa, 7)], [(0x5500550055005500, 7)])
def st12 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])
def pm3 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st12]
def s5Mask : Nat := 0x5555555555555555
abbrev s5Goal : Nat := sGoal &&& s5Mask
abbrev s5StockWords : List Nat := [0x4444444444444444, 0x5050505050505050, 0x5500550055005500, 0x5555000055550000, 0x5555555500000000]
def s5Fact : Nat × List Nat × Nat × Nat := (s5Mask, s5StockWords, 8, s5Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Stock : Lower s5Mask s5StockWords s5Goal 8 := dagShiftLower (width := 64) pm3 s4Stock (by decide +kernel)
def st01 : List (Nat × Nat) × List (Nat × Nat) := ([( 0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])
def st23 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])
def pm4 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st23]
def st02 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])
def st13 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcc33cc33cc33cc33, 0), (0xcc00cc00cc00cc, 6)], [(0x3300330033003300, 6)])
def pm5 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02, st13]
def s6Blob190700 : Nat := (cbits [0x81c0607020180406, 0xc060b04024020902, 0x40e060340a0d0502, 0x5088540a15060381, 0x985c281609058281, 0x68141a0c06422190, 0x381d0986c301a090, 0x60181800060e078, 0x90181806050180a, 0x1c04070081c2806, 0x4060900024260702, 0x2090602414090282, 0xb0102c020b0c0242, 0x2034020d0982c100, 0x38040e0e034100d0, 0x60f0e038100e020, 0x150603c140f0283c, 0x985420150205402, 0x580816010583815, 0xc06170e058261608, 0x8170905c22170285, 0x9080641019008642, 0x4068041a0e064261, 0x6c381a09868201a0, 0x241b0886c141b018, 0x1d060740a1d0c06c, 0x5078301d0a07422])
def s6Blob191268 : Nat := (cbits [0xff0ffffe018e73fc, 0xfef38ccf7fe0ffc1, 0x83ff07fe0ff0f01f, 0xffff001fff03ff0f, 0x3fc0ff0fc0007ff, 0xfffff8000fffffe0, 0xf000000003fff000, 0xffffffff])
def s6Blob191454 : Nat := (cbits [0x930194d21886315c, 0xa8b284c514a849d0, 0x816942528510a154, 0x2aaa028953015b0a, 0x63580ea02c1084a5, 0xca5290210ccc4b00, 0xc0888c1183efe000, 0x739ce739])
def s6Mask : Nat := 0xffffffff
abbrev s6Goal : Nat := sGoal &&& s6Mask
abbrev s6StockWords : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def s6Fact : Nat × List Nat × Nat × Nat := (s6Mask, s6StockWords, 7, s6Goal)
def s6Cuts : List (Nat × List Nat × Nat × Nat) := []
def s6Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 9, 21, 26, 6, 9, 21, 26, 6, 9, 21, 26, 5, 10, 19, 28, 5, 10, 19, 28, 5, 10, 19, 28], rfl⟩
def s6Witnesses := unpackWitnesses s6StockWords [4616, 265220, 527362, 791041, 1059333]
def s6Index (i : Nat) : Nat := unpack 0xc30341 6 i
def s6Codes (i : Nat) : Nat := unpack (cbits [0x31028c504010001f, 0x9871a92c9]) 17 i
def s6Forest (i : Nat) : Nat := unpack 0xc384010807c 15 i
def s6Links := pageLinks s6Index s6Codes 3 13 2 4
def s6Data (i : Nat) : Nat × Nat :=
  let e := s6Forest i
  (e &&& 3, e >>> 2)
def s6Sample : Nat × Nat := (s6Blob190700, 96)
def s6Tags := dagTraceTags s6Mask 96 (dagTagBases s6StockWords s6Blob191268 s6Blob191454 96) 6 s6Data
def s6States := dagTrace s6Mask s6StockWords 6 s6Data
def s6MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val))), (pm5, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val))), (pm3, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 4, 5] 0 i.val)))]
def s6Moves := dagMoves s6MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Autos : DagMovesOK s6Mask s6Goal 64 s6Moves := dagMovesOfCheck (by decide +kernel)
def s6Check := dagCheckNode s6Mask s6Goal s6Chart (dagKnownCloses s6Goal s6Cuts) 3 s6States s6Moves s6Links s6Sample s6Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Roots : dagCheckRoots s6Mask s6Goal s6Chart (dagKnownCloses s6Goal s6Cuts) s6Witnesses (dagRef 3 s6States s6Moves s6Links 0) s6StockWords 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Block0 : treeBlock 0 3 s6Check = true := by decide +kernel
theorem s6Blocks : treeBlock 0 3 s6Check = true := s6Block0
theorem s6Known : Known s6Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Stock : Lower s6Mask s6StockWords s6Goal 7 := by
  apply lowerDag _ _ _ _ s6Autos _ _ _ s6Known _ s6Roots s6Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s6Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s7Blob194628 : Nat := (cbits [0x680a15028340a07, 0x404070c068241a05, 0x150503c0a0f0403, 0xa0106824170285c2, 0xc0740a1d08068101, 0x3424070501c00070, 0x40f0c034140d000, 0x150905400150403c, 0x6820170105c30, 0x7c0a1f08074101d, 0xc10070c07c241f05, 0xf08034040d0801, 0x501054300f0903c0, 0xc05c14170005c101, 0x7c241d05074001d0, 0x30070807c101f010, 0x1705054200f09034, 0x7c041d0286810])
def s7Blob195011 : Nat := (cbits [0xdfffffff7fff1fc7, 0xb5e39cfce31cfb79, 0xe6fc1f3f83e3e3ba, 0xf8ffe03ffc03fc3c])
def s7Blob195126 : Nat := (cbits [0x2000000400010907, 0x4a39291829583258, 0x194b506912ca42a8, 0x7921ab258929430])
def s7Mask : Nat := 0xa5a5a5a5
abbrev s7Goal : Nat := sGoal &&& s7Mask
abbrev s7StockWords : List Nat := [0xa0a0a0a0, 0x84848484, 0xa500a500, 0xa5a50000]
def s7Fact : Nat × List Nat × Nat × Nat := (s7Mask, s7StockWords, 6, s7Goal)
def s7Cuts : List (Nat × List Nat × Nat × Nat) := []
def s7Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 13, 21, 26, 7, 13, 21, 26, 7, 13, 21, 26, 5, 10, 18, 24, 5, 10, 18, 24, 5, 10, 18, 24], rfl⟩
def s7Witnesses := unpackWitnesses s7StockWords [3586, 265733, 530949, 797189]
def s7Index (i : Nat) : Nat := unpack 0xa28a28301 6 i
def s7Codes (i : Nat) : Nat := unpack (cbits [0x31010c504010000f, 0x892c3]) 17 i
def s7Forest (i : Nat) : Nat := unpack (cbits [0x310118a100410078, 0x4961]) 16 i
def s7Links := pageLinks s7Index s7Codes 3 13 3 4
def s7Data (i : Nat) : Nat × Nat :=
  let e := s7Forest i
  (e &&& 7, e >>> 3)
def s7Sample : Nat × Nat := (s7Blob194628, 64)
def s7Tags := dagTraceTags s7Mask 64 (dagTagBases s7StockWords s7Blob195011 s7Blob195126 64) 5 s7Data
def s7States := dagTrace s7Mask s7StockWords 5 s7Data
def s7MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s7Moves := dagMoves s7MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Autos : DagMovesOK s7Mask s7Goal 64 s7Moves := dagMovesOfCheck (by decide +kernel)
def s7Check := dagCheckNode s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) 5 s7States s7Moves s7Links s7Sample s7Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Roots : dagCheckRoots s7Mask s7Goal s7Chart (dagKnownCloses s7Goal s7Cuts) s7Witnesses (dagRef 5 s7States s7Moves s7Links 0) s7StockWords 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Block0 : treeBlock 0 5 s7Check = true := by decide +kernel
theorem s7Blocks : treeBlock 0 5 s7Check = true := s7Block0
theorem s7Known : Known s7Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Stock : Lower s7Mask s7StockWords s7Goal 6 := by
  apply lowerDag _ _ _ _ s7Autos _ _ _ s7Known _ s7Roots s7Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s7Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s8Mask : Nat := 0xcc33cc33
abbrev s8Goal : Nat := sGoal &&& s8Mask
abbrev s8StockWords : List Nat := [0x88228822, 0xcc00cc00, 0xc030c030, 0xcc330000]
def s8Fact : Nat × List Nat × Nat × Nat := (s8Mask, s8StockWords, 6, s8Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Stock : Lower s8Mask s8StockWords s8Goal 6 := dagShiftLower (width := 64) pm4 s7Stock (by decide +kernel)
def s9Mask : Nat := 0x5500550055005500
abbrev s9Goal : Nat := sGoal &&& s9Mask
abbrev s9StockWords : List Nat := [0x4400440044004400, 0x5000500050005000, 0x5500000055000000, 0x5500550000000000]
def s9Fact : Nat × List Nat × Nat × Nat := (s9Mask, s9StockWords, 6, s9Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Stock : Lower s9Mask s9StockWords s9Goal 6 := dagShiftLower (width := 64) pm3 s0Stock (by decide +kernel)
def pm6 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st12, st01]
def s10Mask : Nat := 0x5555000055550000
abbrev s10Goal : Nat := sGoal &&& s10Mask
abbrev s10StockWords : List Nat := [0x4444000044440000, 0x5050000050500000, 0x5500000055000000, 0x5555000000000000]
def s10Fact : Nat × List Nat × Nat × Nat := (s10Mask, s10StockWords, 5, s10Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Stock : Lower s10Mask s10StockWords s10Goal 5 := dagShiftLower (width := 64) pm6 s2Stock (by decide +kernel)
def pm7 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st12, st01, st45]
def s11Mask : Nat := 0x5555555500000000
abbrev s11Goal : Nat := sGoal &&& s11Mask
abbrev s11StockWords : List Nat := [0x4444444400000000, 0x5050505000000000, 0x5500550000000000, 0x5555000000000000]
def s11Fact : Nat × List Nat × Nat × Nat := (s11Mask, s11StockWords, 5, s11Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Stock : Lower s11Mask s11StockWords s11Goal 5 := dagShiftLower (width := 64) pm7 s2Stock (by decide +kernel)
def s12Blob207228 : Nat := (cbits [0x81c0607020180406, 0xc060b04024020902, 0x40e060340a0d0502, 0x5088540a15060381, 0x985c281609058281, 0x68141a0c06422190, 0x381d0986c301a090, 0x2a1209844260e078, 0x160b8502a110a814, 0xe8643a1a0d86436, 0x683c160f0383c1c, 0xa060181800061c0f, 0x6090181806050180, 0x81c480611018280, 0x2426070201c04070, 0x1409028240609000, 0x90c024220906024, 0x402c040b0082c50, 0x34080d00834260b, 0x8040e16034380d04, 0x80e0e038100e0203, 0xf0503c0a0f0183c5, 0x8054081500854180, 0x5868150e05426150, 0x2616080580816010, 0x171a05864160e058, 0x905c22170285c06])
def s12Blob207797 : Nat := (cbits [0xfffe0000018e73fc, 0xfef38ccff01ff83f, 0xffe07fc1e01fff0f, 0x1ffff38f03ff0f, 0xf3fc0ff0fffffffe, 0x7fffffe000fc, 0xff03fff000, 0xfc000000ffff8000, 0xff])
def s12Blob207987 : Nat := (cbits [0x24d206000086315c, 0x34b284c571049803, 0x952428414154aa05, 0x28954728b015b0a, 0xd3580ea02a5956b4, 0x20867389b0018b8, 0xc1060df03efe000, 0xec000000cf9e0211, 0xc100420100180ef])
def s12Mask : Nat := 0x55555555ffffffff
abbrev s12Goal : Nat := sGoal &&& s12Mask
abbrev s12StockWords : List Nat := [0xaaaaaaaa, 0x44444444cccccccc, 0x50505050f0f0f0f0, 0x55005500ff00ff00, 0x55550000ffff0000, 0x5555555500000000]
def s12Fact : Nat × List Nat × Nat × Nat := (s12Mask, s12StockWords, 10, s12Goal)
def s12Cuts : List (Nat × List Nat × Nat × Nat) := [s5Fact, s6Fact, s7Fact, s8Fact, s9Fact, s10Fact, s11Fact]
def s12Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 9, 21, 26, 42, 60, 6, 9, 21, 26, 42, 60, 5, 10, 19, 28, 44, 50, 52, 56, 5, 10, 19, 28], rfl⟩
def s12Witnesses := unpackWitnesses s12StockWords [4616, 265220, 527362, 791041, 1059333, 1332234]
def s12Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 10 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0xb480bd801b0001, 0x210c401880310062, 0x6610cc0190432006, 0xd001a003400]) else (cbits [0xe401a903500681, 0x450e801c84390072, 0x7e00fc01f803f007, 0xfc01f803f00])) else (if j < 3 then (cbits [0x110022003f287e0, 0x2012402214440088, 0xc201368249049009, 0x184030806100]) else (if j < 4 then (cbits [0x198030946100c20, 0xc0198033006600cc, 0xcc4198033006600c, 0x1a8035006a00]) else (cbits [0x1c4036146c00d42, 0xaf1d4038907100e2, 0x83210042008400e, 0x21c043808701])))) else (if j < 7 then (if j < 6 then (cbits [0x2204440088010e1, 0x6122c045048a0114, 0x180230046008c011, 0x284c46548c01]) else (cbits [0x29c05380a7014e0, 0x402a805500a7194e, 0x5802b005600aa115, 0x2bc05780ac19])) else (if j < 8 then (cbits [0x2d405a80af315e0, 0x52e005a8cb5016a, 0x7a02f405e80bd017, 0x30406004bd19]) else (if j < 9 then (cbits [0x43100608cc101820, 0x4332806408c80188, 0xba1339e6684cd019, 0x37806f00de01]) else (cbits [0x39807300e601bc8, 0xe139c07380e609cc, 0xd413a807484e809c, 0x3d427a80eb51]))))) else (if j < 15 then (if j < 12 then (if j < 11 then (cbits [0x3e007c00f611ec0, 0x2a3e227c00f801f0, 0x2814500898513021, 0x45408a811502]) else (cbits [0x145408a8115022a0, 0xe045828b0116022a, 0x3e047c08f05173a2, 0x47c08f811f02])) else (if j < 13 then (cbits [0x248c4900d1f0a3e0, 0xc04b049509271a4a, 0x7814c5698052e125, 0x51409ea13d02]) else (if j < 14 then (cbits [0x5140a28145028a0, 0xe151c0a305450a8a, 0xa405442a4a1480a8, 0x54c2a981520a]) else (cbits [0x5a40aad15502a81, 0x405a80b4856902d2, 0xdc05b80b5116a02d, 0x5c00b7096e02])))) else (if j < 18 then (if j < 16 then (cbits [0x45d40ba817502e05, 0x206240bcc17902ea, 0x1206240c48189031, 0x6240c4818903]) else (if j < 17 then (cbits [0x6252c4818903120, 0x406480c901920324, 0x46068c0d10592832, 0x6900d185a303]) else (cbits [0x96900d201a403480, 0xc06b80d701ad0b48, 0x6a06b8ed701ae035, 0x6d40da81b503]))) else (if j < 19 then (cbits [0x7280e311b58b6a0, 0x40735ae50dca0394, 0xb6076c0ed81da0bb, 0x79c4edb1db03]) else (if j < 20 then (cbits [0x7e80fd01e98bd20, 0x207f96ff01fa23f4, 0x2218251048209041, 0x848109021204]) else 0x2231c251))))) 15 (i % 16)
def s12Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 17 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x50c500102100003f, 0x18f8ba31b11c62a1, 0x372986664e0c9c8a, 0x2709880d91a19943, 0x8319a046273d4c4, 0x468c868998dd]) else (cbits [0x6a4f526499a4092c, 0x621a6cc394c18709, 0x90080109fbd113a, 0x605804c0900780e0, 0xf01581c02703403, 0x5407e0880d4])) else (if j < 3 then (cbits [0xe0c6c1b18a82e314, 0x19f83c32b07464e0, 0x3f08cc4e1018801f, 0xe13a4b4254960486, 0x318a052f440a127, 0x15258021880]) else (cbits [0x500d0081a000cf44, 0x4020330030c600, 0x2c04cc40090c5008, 0xa018c501601a0289, 0x1949603062004866, 0x106280d3d10]))) else (if j < 6 then (if j < 5 then (cbits [0xa4b018310026335, 0x19a80a314089e881, 0x440852580c988014, 0x80d18800618a04cf, 0x202104cc3808925, 0xb063e158c6c]) else (cbits [0x78cdc2e19985a327, 0x3108626200c06861, 0x370e0c661b989c36, 0x61da4b03a3218726, 0x4161c07e93d0f926, 0x11188621b0e4])) else (if j < 7 then (cbits [0x924b00302108af44, 0x7a2068c380cd27a1, 0x380c925802010835, 0x81998803d7a2078c, 0x3449600a042101e8, 0x10187a1e30e0]) else (cbits [0xaa4b046199084f44, 0x27084f440f58701, 0x3e124654240c9807, 0x42798a84b3130943, 0x553210a463e144c6, 0x1612582b9938])))) else (if j < 12 then (if j < 10 then (if j < 9 then (cbits [0xdbd105a6248b2c38, 0x32009801c1724a02, 0x1c1412782719304d, 0x2b18f0543260a60, 0x640090bc01002008, 0x1a0628048138]) else (cbits [0x78cf86c19a8d6332, 0x1a60ea3411c06803, 0x2912cc403e0d3477, 0x84018c87f3150fa6, 0x8361c10493e20525, 0x21de8842b124])) else (if j < 11 then (cbits [0x1045f004113250, 0x4960c26201306283, 0x4019406831b0e062, 0x8348cc0670260cc0, 0x6d1a00ca0101a867, 0x28084370d30]) else (cbits [0x924b07131009a314, 0x80e8f441cd27a3, 0x141d8698368cd066, 0xa3ca4b07831009c3, 0x670080f6c381e927, 0x1d8680370cd0]))) else (if j < 14 then (if j < 13 then (cbits [0x899006100e0fc93c, 0x18e0c401c1e0c983, 0x341e4c9839190084, 0x8318070731a610c3, 0x743260f664c22063, 0x13c628058138]) else (cbits [0x598807f18d0fa319, 0x49e11c9322352584, 0x4925927c4a24f48f, 0x84cb1249861c12e9, 0x8c49e137250269e8, 0x140628060108])) else (if j < 15 then (cbits [0x824b08c3100fc319, 0x7a2124c3d2458704, 0x3c2558904ab12093, 0xc49b120924a4122c, 0x6b19313a31403409, 0x28067c4f0ca8]) else (if j < 16 then (cbits [0x1a4b0803130a2620, 0x49e14b250291e885, 0x102886505080409f, 0x8070138b300914e0, 0xb61950de3262d462, 0x2e0698500cc8]) else (cbits [0x99045231018034d, 0x61c18893d30d2586, 0x50321e88633124c5, 0x8548104a80041932, 0xad31015633514c62, 0x2bd2585718c4])))))) else (if j < 26 then (if j < 21 then (if j < 19 then (if j < 18 then (cbits [0x93d10b161c16093d, 0x261586302a92785, 0x351506285ba4f0b4, 0x85e18c4bb3101723, 0xbf61c17c93d2f525, 0x2d00205d18c0]) else (cbits [0x124f0b91a6156010, 0xe1743402b00206, 0x282b80205d9930ad, 0x8578070bc1a616e3, 0xc719a1600102f4c9, 0x2fcc98588070])) else (if j < 20 then (cbits [0xa8c500f02716401c, 0x31e1966203046622, 0x313512586998f4cd, 0x6ba524d649e9aa9, 0x1002119833c3624a, 0x3086622b0c50]) else (cbits [0x824c4cf49619c620, 0x49e1a4f4434527a6, 0x48344c906818f0cf, 0x2b8c50110201a49, 0xdc4961b6649368c4, 0x3798706ea524]))) else (if j < 23 then (if j < 22 then (cbits [0x98100120201bec49, 0x211c00340500800, 0x2738c63e710c6c17, 0x6738cdce51999c83, 0x583108626203a068, 0x30cc6651989c]) else (cbits [0x4a4b0da321996637, 0x61c1da93d3b12667, 0x443c988678b0e4ef, 0x80c0108e61a61e6f, 0xeb7a21d4c380c925, 0x3b9e88199880])) else (if j < 24 then (cbits [0x530e034496032042, 0x1991e0f443b987a7, 0x443ad8701aa4b0f4, 0xc7b0c681b0271e0f, 0xf919f1f03323dc63, 0x204c4a1b1880]) else (if j < 25 then (cbits [0xda4f8fa499116629, 0x61c1fa94e3f12847, 0x50401e887fb124fe, 0x21b8c501c0272032, 0x431020631d1ac63, 0x3e92588298f9]) else (cbits [0xe81390792820cf44, 0x18e8de3190e06280, 0x2031067a410c9509, 0x27da4b1053192146, 0xd61ea18c3842d28, 0x441e8887b125]))))) else (if j < 30 then (if j < 28 then (if j < 27 then (cbits [0xba4f112928222f4e, 0x18a03c04e4392685, 0x313f0c408a0cf439, 0x28ba4f5164962166, 0x1500823325046129, 0x46c6921d0c51]) else (cbits [0xea5251c4961fa620, 0x2123ec494798708, 0x27164c421d988020, 0xe6298cc983159066, 0xe94961b8643350c6, 0x4312667f24b4])) else (if j < 29 then (cbits [0xb0e11c4a1a2c937, 0x7a2248c4348d8729, 0x380f125810810925, 0x1ea4b1227a21d4c, 0x23027244f443ad87, 0x28064a1f0c50]) else (cbits [0x61880d51a0a4e329, 0x31ea50629414c4a7, 0x4e4a9e8894a4b10d, 0x88718f12c928256f, 0x8518d8b43150fc62, 0x31867e4c8c7c]))) else (if j < 32 then (if j < 31 then (cbits [0xf9884ed3101ae343, 0x7a223064343cc7e7, 0x2c100c4097bd152e, 0x6988c7c250211dc9, 0x413102663434c865, 0x21cc4e2d9884]) else (cbits [0xf190ca431993462b, 0x499a0092d3bd2586, 0x3d4858708f250d06, 0x89a8cf9347a225cc, 0x227a21e0c3810925, 0x4dc63c138139])) else (if j < 33 then (cbits [0x418f44331027032a, 0x61c22093d3c52586, 0x504bd8929530f523, 0x9d8d244418a2732, 0x3d324a226313c8c4, 0x4ad2629224b1]) else (if j < 34 then (cbits [0xcc93c00827c949, 0x3138b8621114c40a, 0x3f294c664d98ac89, 0xa79a4b0d83219926, 0x1249fa0e93340525, 0x4958708ca50d]) else (cbits [0xcbd15347a2258c3f, 0x7a21e892c118c409, 0x135]))))))) 23 (i % 16)
def s12Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 10 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x100202100407e00, 0x9600cc400318a00c, 0x8008004809e88034, 0x98080680a0078086, 0xe0200d808c600c00, 0x1580804]) else (cbits [0x6281201a80866010, 0x1f80925812310048, 0x401818a008068160, 0xa809e8818496060c, 0x6021938086360218, 0x19f80865])) else (if j < 3 then (cbits [0xe8821496084c4002, 0x96008c7e02313809, 0x7e02496809e88264, 0xd8ac628017a20092, 0x62b1938ac63e2b18, 0x19b8ac66]) else (if j < 4 then (cbits [0x258323100ac6862b, 0xa20c98703249e8c9, 0x662b3138acc422b7, 0x60acc862b31b8acc, 0x62b7a20f18703c49, 0x49e8ad26]) else (cbits [0xe884261c0ade8840, 0xa20ad8862b61c8ad, 0x4c4818a804664467, 0x312067c481951206, 0x84c3201300384c31, 0x315120c9])))) else (if j < 7 then (if j < 6 then (cbits [0xc7c4831912127850, 0x21120c985300e14c, 0x5848327120c78563, 0x21218924861c1212, 0x5e18d8064a0487a, 0x417c02]) else (cbits [0x2585f31017c0825f, 0x1a1940245e61c17d, 0x285e026194080650, 0x9178678691981a46, 0x86d1a01b466a5e19, 0x19f17869])) else (if j < 8 then (cbits [0x258713101c46805e, 0xa0979e887149e9c5, 0x40781a6178698761, 0xc1e127a784961e0c, 0x87e31497869a5e61, 0x31517927]) else (if j < 9 then (cbits [0x27c5e496178c645e, 0x249786388461c179, 0x38887a2178668866, 0x22c63e019281786, 0x48b49622d2788c31, 0x49e22d26]) else (cbits [0x87a9061c24125890, 0x2425527a8b7a2241, 0x708b4a4a2d27c8b6, 0x822de888b624a2d8, 0x49d18a27464e0192, 0x49e27c65]))))) else (if j < 15 then (if j < 12 then (if j < 11 then (cbits [0x650a100828467c9d, 0x28275e889d496274, 0x10a800829c666019, 0xaaa1278aa020aa00, 0x2a83102a0c60ac19, 0x4962a0c6]) else (cbits [0xe88a861c2a127aa8, 0x8a29c098b400929d, 0x98a749e2dc654a71, 0x2e4c60ba19aae46, 0xab94962e4c62b931, 0x61c2e527])) else (if j < 13 then (cbits [0x278c2320a9c69aa7, 0x1c29d27aa749629d, 0x88a719a31d892a76, 0x32c66e0192829de, 0xce31e32c678cc31, 0x496338c4]) else (if j < 14 then (cbits [0xe88ce49eb39262ce, 0x98b2d258cb31eb2d, 0xa0cb4a4b2d27acb4, 0x4b68c40da1a18064, 0xda4a4b69258da32, 0x624b6987]) else (cbits [0x636e2310004068e0, 0x99b8864ee218fb88, 0x86e219bb88698e61, 0x23a9870ea4963886, 0x8ee49eb89266e27a, 0x61c389e8])))) else (if j < 18 then (if j < 16 then (cbits [0x886e261cb89e88f0, 0x10804664f47a2389, 0x64f618f3d8634f63, 0xf3d9264f619f3d86, 0xf64a73d9284f649, 0x624bd987]) else (if j < 17 then (cbits [0xc4e019283d9e88f6, 0x1f40cc410318ec0c, 0x660192840de89033, 0xc24c410918ec24c, 0x90e61ec25871094a, 0x624c2526]) else (cbits [0x4a1097a7425e8909, 0x845467b1431b806, 0x931449ec51259140, 0x4c6cc86019284512, 0x11b4a4c6d2591b1a, 0x624c6d87]))) else (if j < 19 then (cbits [0xe892261c48525801, 0xa24858872161cc85, 0x5327194c9d266017, 0x749de892749649cc, 0x92e49e8064a1277a, 0x7a2cb9e8]) else (if j < 20 then (cbits [0x6573118fcc587001, 0x9f4d5e89311a1cc4, 0x553718f4dd872011, 0x4ced886019284dc6, 0x33b324cec0213c1a, 0x7a200529]) else 0x66540))))) 22 (i % 16)
def s12Links := pageLinks s12Index s12Codes 5 13 9 6
def s12Data (i : Nat) : Nat × Nat :=
  let e := s12Forest i
  (e &&& 511, e >>> 9)
def s12Sample : Nat × Nat := (s12Blob207228, 96)
def s12Tags := dagTraceTags s12Mask 96 (dagTagBases s12StockWords s12Blob207797 s12Blob207987 96) 9 s12Data
def s12States := dagTrace s12Mask s12StockWords 9 s12Data
def s12MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s12Moves := dagMoves s12MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Autos : DagMovesOK s12Mask s12Goal 64 s12Moves := dagMovesOfCheck (by decide +kernel)
def s12Check := dagCheckNode s12Mask s12Goal s12Chart (dagKnownCloses s12Goal s12Cuts) 321 s12States s12Moves s12Links s12Sample s12Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Roots : dagCheckRoots s12Mask s12Goal s12Chart (dagKnownCloses s12Goal s12Cuts) s12Witnesses (dagRef 321 s12States s12Moves s12Links 0) s12StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block0 : treeBlock 0 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block24 : treeBlock 24 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block48 : treeBlock 48 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block72 : treeBlock 72 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block96 : treeBlock 96 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block120 : treeBlock 120 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block144 : treeBlock 144 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block168 : treeBlock 168 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block192 : treeBlock 192 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block216 : treeBlock 216 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block240 : treeBlock 240 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block264 : treeBlock 264 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block288 : treeBlock 288 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block312 : treeBlock 312 9 s12Check = true := by decide +kernel
theorem s12Group24_48 : treeBlock 24 48 s12Check = true := treeBlock_merge (start := 24) (left := 24) (right := 24) (check := s12Check) s12Block24 s12Block48
theorem s12Group0_72 : treeBlock 0 72 s12Check = true := treeBlock_merge (start := 0) (left := 24) (right := 48) (check := s12Check) s12Block0 s12Group24_48
theorem s12Group72_48 : treeBlock 72 48 s12Check = true := treeBlock_merge (start := 72) (left := 24) (right := 24) (check := s12Check) s12Block72 s12Block96
theorem s12Group120_48 : treeBlock 120 48 s12Check = true := treeBlock_merge (start := 120) (left := 24) (right := 24) (check := s12Check) s12Block120 s12Block144
theorem s12Group72_96 : treeBlock 72 96 s12Check = true := treeBlock_merge (start := 72) (left := 48) (right := 48) (check := s12Check) s12Group72_48 s12Group120_48
theorem s12Group0_168 : treeBlock 0 168 s12Check = true := treeBlock_merge (start := 0) (left := 72) (right := 96) (check := s12Check) s12Group0_72 s12Group72_96
theorem s12Group192_48 : treeBlock 192 48 s12Check = true := treeBlock_merge (start := 192) (left := 24) (right := 24) (check := s12Check) s12Block192 s12Block216
theorem s12Group168_72 : treeBlock 168 72 s12Check = true := treeBlock_merge (start := 168) (left := 24) (right := 48) (check := s12Check) s12Block168 s12Group192_48
theorem s12Group240_48 : treeBlock 240 48 s12Check = true := treeBlock_merge (start := 240) (left := 24) (right := 24) (check := s12Check) s12Block240 s12Block264
theorem s12Group288_33 : treeBlock 288 33 s12Check = true := treeBlock_merge (start := 288) (left := 24) (right := 9) (check := s12Check) s12Block288 s12Block312
theorem s12Group240_81 : treeBlock 240 81 s12Check = true := treeBlock_merge (start := 240) (left := 48) (right := 33) (check := s12Check) s12Group240_48 s12Group288_33
theorem s12Group168_153 : treeBlock 168 153 s12Check = true := treeBlock_merge (start := 168) (left := 72) (right := 81) (check := s12Check) s12Group168_72 s12Group240_81
theorem s12Group0_321 : treeBlock 0 321 s12Check = true := treeBlock_merge (start := 0) (left := 168) (right := 153) (check := s12Check) s12Group0_168 s12Group168_153
theorem s12Blocks : treeBlock 0 321 s12Check = true := s12Group0_321
theorem s12Known : Known s12Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s11Stock) s10Stock) s9Stock) s8Stock) s7Stock) s6Stock) s5Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Stock : Lower s12Mask s12StockWords s12Goal 10 := by
  apply lowerDag _ _ _ _ s12Autos _ _ _ s12Known _ s12Roots s12Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s12Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s13Mask : Nat := 0xff00ffffffffff
abbrev s13Goal : Nat := sGoal &&& s13Mask
abbrev s13StockWords : List Nat := [0xaa00aaaaaaaaaa, 0xcc00cccccccccc, 0xf000f0f0f0f0f0, 0xff00ff00, 0xff0000ffff0000, 0xff00ff00000000]
def s13Fact : Nat × List Nat × Nat × Nat := (s13Mask, s13StockWords, 10, s13Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Stock : Lower s13Mask s13StockWords s13Goal 10 := dagShiftLower (width := 64) pm3 s12Stock (by decide +kernel)
def pm8 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st12, st45]
def s14Mask : Nat := 0xffffff00ffffff
abbrev s14Goal : Nat := sGoal &&& s14Mask
abbrev s14StockWords : List Nat := [0xaaaaaa00aaaaaa, 0xcccccc00cccccc, 0xf0f0f000f0f0f0, 0xff000000ff00, 0xff000000ff0000, 0xffffff00000000]
def s14Fact : Nat × List Nat × Nat × Nat := (s14Mask, s14StockWords, 10, s14Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Stock : Lower s14Mask s14StockWords s14Goal 10 := dagShiftLower (width := 64) pm8 s12Stock (by decide +kernel)
def s15Mask : Nat := 0xf0f0f0fffffffff
abbrev s15Goal : Nat := sGoal &&& s15Mask
abbrev s15StockWords : List Nat := [0xa0a0a0aaaaaaaaa, 0xc0c0c0ccccccccc, 0xf0f0f0f0, 0xf000f00ff00ff00, 0xf0f0000ffff0000, 0xf0f0f0f00000000]
def s15Fact : Nat × List Nat × Nat × Nat := (s15Mask, s15StockWords, 10, s15Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Stock : Lower s15Mask s15StockWords s15Goal 10 := dagShiftLower (width := 64) pm5 s12Stock (by decide +kernel)
def pm9 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02, st13, st45]
def s16Mask : Nat := 0xf0fffff0f0fffff
abbrev s16Goal : Nat := sGoal &&& s16Mask
abbrev s16StockWords : List Nat := [0xa0aaaaa0a0aaaaa, 0xc0ccccc0c0ccccc, 0xf0f00000f0f0, 0xf00ff000f00ff00, 0xf0f00000f0f0000, 0xf0fffff00000000]
def s16Fact : Nat × List Nat × Nat × Nat := (s16Mask, s16StockWords, 10, s16Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Stock : Lower s16Mask s16StockWords s16Goal 10 := dagShiftLower (width := 64) pm9 s12Stock (by decide +kernel)
def s17Mask : Nat := 0x3333333333333333
abbrev s17Goal : Nat := sGoal &&& s17Mask
abbrev s17StockWords : List Nat := [0x2222222222222222, 0x3030303030303030, 0x3300330033003300, 0x3333000033330000, 0x3333333300000000]
def s17Fact : Nat × List Nat × Nat × Nat := (s17Mask, s17StockWords, 8, s17Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Stock : Lower s17Mask s17StockWords s17Goal 8 := dagShiftLower (width := 64) pm5 s4Stock (by decide +kernel)
def s18Mask : Nat := 0x3030303030303030
abbrev s18Goal : Nat := sGoal &&& s18Mask
abbrev s18StockWords : List Nat := [0x2020202020202020, 0x3000300030003000, 0x3030000030300000, 0x3030303000000000]
def s18Fact : Nat × List Nat × Nat × Nat := (s18Mask, s18StockWords, 6, s18Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Stock : Lower s18Mask s18StockWords s18Goal 6 := dagShiftLower (width := 64) pm5 s0Stock (by decide +kernel)
def s19Mask : Nat := 0x3333000033330000
abbrev s19Goal : Nat := sGoal &&& s19Mask
abbrev s19StockWords : List Nat := [0x2222000022220000, 0x3030000030300000, 0x3300000033000000, 0x3333000000000000]
def s19Fact : Nat × List Nat × Nat × Nat := (s19Mask, s19StockWords, 5, s19Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Stock : Lower s19Mask s19StockWords s19Goal 5 := dagShiftLower (width := 64) pm5 s2Stock (by decide +kernel)
def s20Mask : Nat := 0x3333333300000000
abbrev s20Goal : Nat := sGoal &&& s20Mask
abbrev s20StockWords : List Nat := [0x2222222200000000, 0x3030303000000000, 0x3300330000000000, 0x3333000000000000]
def s20Fact : Nat × List Nat × Nat × Nat := (s20Mask, s20StockWords, 5, s20Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Stock : Lower s20Mask s20StockWords s20Goal 5 := dagShiftLower (width := 64) pm9 s2Stock (by decide +kernel)
def pm10 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st23, st45]
def s21Blob219943 : Nat := (cbits [0x240209020180406, 0x8140e060340a0d04, 0x815088540a150603, 0x9088642816090582, 0xc068241a05068301, 0x940a250e078381d0, 0x4826110984825108, 0x2a050a85029108a4, 0x160b8582d140a844, 0xd864361a0d46235, 0x8643a1c0e462391a, 0x83c160f0383c1c0e, 0x60281800061c0f06, 0xa018240606018140, 0x2400091201844060, 0x2209060241409028, 0xd1402442090c024, 0xe034100d0203402, 0x38080e01038580d, 0x4021516038380e04, 0x2150e05420150205, 0x60205804161a0546, 0xa05864160e058201, 0x6420190406402191, 0x41a1c06462190e0, 0x1a0e068201a04068, 0x60740a1d1c06864])
def s21Blob220512 : Nat := (cbits [0xfff000334674673c, 0xb98b98c3c0fc0fc1, 0x3f03f03e000ff0cc, 0xf00fff0fc1fc1ff3, 0xfe0fe0fcc003ffff, 0xfffc003ffff00ff0, 0xfff000fff00, 0xfff00000ffffffc0, 0xfff])
def s21Blob220710 : Nat := (cbits [0x1520201102302314, 0x1881884140440440, 0x1101100200454044, 0xa0aaa70ac15c15b2, 0xec0ec0e8c822aab5, 0xaaa88239cac0cba0, 0x83030dff000f7e00, 0xf7e000003cf3cf10, 0x30c30c210c0c0eff])
def s21Mask : Nat := 0x7777777777777777
abbrev s21Goal : Nat := sGoal &&& s21Mask
abbrev s21StockWords : List Nat := [0x2222222222222222, 0x4444444444444444, 0x7070707070707070, 0x7700770077007700, 0x7777000077770000, 0x7777777700000000]
def s21Fact : Nat × List Nat × Nat × Nat := (s21Mask, s21StockWords, 10, s21Goal)
def s21Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact, s5Fact, s18Fact, s9Fact, s19Fact, s20Fact]
def s21Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 9, 21, 26, 37, 42, 60, 6, 9, 21, 26, 37, 5, 10, 28, 44, 49, 50, 52, 56, 5, 10, 28, 44], rfl⟩
def s21Witnesses := unpackWitnesses s21StockWords [4616, 265220, 527362, 791041, 1059333, 1329669]
def s21Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xc81902e43a40e801, 0x82700d89b0360648, 0x440881101d53]) else (if j < 2 then (cbits [0x582b0560a8550228, 0xc0d09a02c8580ac5, 0x882f21e03666]) else 0xa612a62ac50)) 11 (i % 16)
def s21Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x85989c04c400003f, 0xe052589e63f0f319, 0x22ec38cf49fc7a4c, 0x4216218eb0fc6d87, 0x98124b16de8aaef4, 0x449]) else (if j < 2 then (cbits [0x83b0e4158708893f, 0x515e8814c430861f, 0x86f440361c23bd1, 0xc097a6033d100d87, 0x50698f830c4012c3, 0x4d32]) else (cbits [0x818813a4a01cf44, 0x6118702264a0d319, 0x2af4e147a209b0f, 0x31231e093d305a4a, 0xf8724cc152583004, 0x5649]))) else (if j < 4 then (cbits [0x8cbd135987f0ac38, 0x219e880cc381a7a2, 0xb0ec381449e83a4b, 0x5a9280e3d2a5187, 0x8c424b044c621062, 0x9149]) else (if j < 5 then (cbits [0x103d3071e883cc38, 0x424c403ef4c5c928, 0x124931894960918c, 0xd153188518807d87, 0x8c524b088c92aa63, 0x9549]) else 0x1030f289293aa93d))) 21 (i % 16)
def s21Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x692c08c40080fc0, 0x4419870124cc261c, 0x9e984b0fc261c84f, 0xc61880c31382c430, 0x31982f4430c7]) else (if j < 2 then (cbits [0xa0f4c48c94818810, 0x5041e9c83d11061e, 0x1e88c010d861c032, 0xe0bd29c61c82f456, 0x7a63ec387987]) else 0x649898860bd31e)) 19 (i % 16)
def s21Links := pageLinks s21Index s21Codes 4 13 6 5
def s21Data (i : Nat) : Nat × Nat :=
  let e := s21Forest i
  (e &&& 63, e >>> 6)
def s21Sample : Nat × Nat := (s21Blob219943, 96)
def s21Tags := dagTraceTags s21Mask 96 (dagTagBases s21StockWords s21Blob220512 s21Blob220710 96) 9 s21Data
def s21States := dagTrace s21Mask s21StockWords 9 s21Data
def s21MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm4, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val))), (pm10, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 5, 4] 0 i.val)))]
def s21Moves := dagMoves s21MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Autos : DagMovesOK s21Mask s21Goal 64 s21Moves := dagMovesOfCheck (by decide +kernel)
def s21Check := dagCheckNode s21Mask s21Goal s21Chart (dagKnownCloses s21Goal s21Cuts) 35 s21States s21Moves s21Links s21Sample s21Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Roots : dagCheckRoots s21Mask s21Goal s21Chart (dagKnownCloses s21Goal s21Cuts) s21Witnesses (dagRef 35 s21States s21Moves s21Links 0) s21StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Block0 : treeBlock 0 24 s21Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Block24 : treeBlock 24 11 s21Check = true := by decide +kernel
theorem s21Group0_35 : treeBlock 0 35 s21Check = true := treeBlock_merge (start := 0) (left := 24) (right := 11) (check := s21Check) s21Block0 s21Block24
theorem s21Blocks : treeBlock 0 35 s21Check = true := s21Group0_35
theorem s21Known : Known s21Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s20Stock) s19Stock) s9Stock) s18Stock) s5Stock) s17Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Stock : Lower s21Mask s21StockWords s21Goal 10 := by
  apply lowerDag _ _ _ _ s21Autos _ _ _ s21Known _ s21Roots s21Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s21Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s22Mask : Nat := 0xfff0fff0fff0fff
abbrev s22Goal : Nat := sGoal &&& s22Mask
abbrev s22StockWords : List Nat := [0xaaa0aaa0aaa0aaa, 0xccc0ccc0ccc0ccc, 0xf000f000f000f0, 0xf000f000f000f00, 0xfff00000fff0000, 0xfff0fff00000000]
def s22Fact : Nat × List Nat × Nat × Nat := (s22Mask, s22StockWords, 10, s22Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Stock : Lower s22Mask s22StockWords s22Goal 10 := dagShiftLower (width := 64) pm5 s21Stock (by decide +kernel)
def s23Mask : Nat := 0x33333333ffffffff
abbrev s23Goal : Nat := sGoal &&& s23Mask
abbrev s23StockWords : List Nat := [0x22222222aaaaaaaa, 0xcccccccc, 0x30303030f0f0f0f0, 0x33003300ff00ff00, 0x33330000ffff0000, 0x3333333300000000]
def s23Fact : Nat × List Nat × Nat × Nat := (s23Mask, s23StockWords, 10, s23Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Stock : Lower s23Mask s23StockWords s23Goal 10 := dagShiftLower (width := 64) pm4 s12Stock (by decide +kernel)
def s24Mask : Nat := 0x3333ffff3333ffff
abbrev s24Goal : Nat := sGoal &&& s24Mask
abbrev s24StockWords : List Nat := [0x2222aaaa2222aaaa, 0xcccc0000cccc, 0x3030f0f03030f0f0, 0x3300ff003300ff00, 0x3333000033330000, 0x3333ffff00000000]
def s24Fact : Nat × List Nat × Nat × Nat := (s24Mask, s24StockWords, 10, s24Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Stock : Lower s24Mask s24StockWords s24Goal 10 := dagShiftLower (width := 64) pm10 s12Stock (by decide +kernel)
def s25Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev s25Goal : Nat := sGoal &&& s25Mask
abbrev s25StockWords : List Nat := [0xa0a0a0a0a0a0a0a, 0xc0c0c0c0c0c0c0c, 0xf000f000f000f00, 0xf0f00000f0f0000, 0xf0f0f0f00000000]
def s25Fact : Nat × List Nat × Nat × Nat := (s25Mask, s25StockWords, 8, s25Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Stock : Lower s25Mask s25StockWords s25Goal 8 := dagShiftLower (width := 64) pm4 s4Stock (by decide +kernel)
def s26Mask : Nat := 0xc0c0c0c0c0c0c0c
abbrev s26Goal : Nat := sGoal &&& s26Mask
abbrev s26StockWords : List Nat := [0x808080808080808, 0xc000c000c000c00, 0xc0c00000c0c0000, 0xc0c0c0c00000000]
def s26Fact : Nat × List Nat × Nat × Nat := (s26Mask, s26StockWords, 6, s26Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Stock : Lower s26Mask s26StockWords s26Goal 6 := dagShiftLower (width := 64) pm4 s0Stock (by decide +kernel)
def pm11 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23]
def s27Mask : Nat := 0xf0f00000f0f0000
abbrev s27Goal : Nat := sGoal &&& s27Mask
abbrev s27StockWords : List Nat := [0xa0a00000a0a0000, 0xc0c00000c0c0000, 0xf0000000f000000, 0xf0f000000000000]
def s27Fact : Nat × List Nat × Nat × Nat := (s27Mask, s27StockWords, 5, s27Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Stock : Lower s27Mask s27StockWords s27Goal 5 := dagShiftLower (width := 64) pm11 s2Stock (by decide +kernel)
def pm12 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23, st45]
def s28Mask : Nat := 0xf0f0f0f00000000
abbrev s28Goal : Nat := sGoal &&& s28Mask
abbrev s28StockWords : List Nat := [0xa0a0a0a00000000, 0xc0c0c0c00000000, 0xf000f0000000000, 0xf0f000000000000]
def s28Fact : Nat × List Nat × Nat × Nat := (s28Mask, s28StockWords, 5, s28Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Stock : Lower s28Mask s28StockWords s28Goal 5 := dagShiftLower (width := 64) pm12 s2Stock (by decide +kernel)
def s29Blob228920 : Nat := (cbits [0x240209020180406, 0x8140e0502c060b04, 0x2190a05824160603, 0xa09068141a0c0642, 0x1098381e0986c301, 0xa85029108a448261, 0x462b140a8442a050, 0x33118cc2633160b8, 0x1a0d86436190cc62, 0xe8643a1c0e46239, 0x683c160f0383c1c, 0x4060181800061c0f, 0x60a0182406060181, 0x1824000912018440, 0x2422090602414090, 0x20b1402442090c0, 0xb0982c100b0102c, 0x4038080e0103846, 0x58041616038380e, 0x8381609858201602, 0x190086468161905, 0x90e0642619080641, 0x4068041a1c064621, 0x68381a09868201a0, 0x141b0186c701a190, 0x1e0c06c241b0886c, 0xa078241e0607814])
def s29Blob229487 : Nat := (cbits [0x1fff00033d188c3c, 0xffe7f3f30f80fe00, 0xffff01ffff00ff0c, 0xe000fff0c20703c3, 0x3f9fcfcf00001ff, 0xfffffe03ffff00ff, 0xfffc01ff00, 0xfffe0000fffffffc, 0xff])
def s29Blob229682 : Nat := (cbits [0x195202011d088414, 0x6d62b17102885220, 0x55a910a43a065604, 0x4008a87082050282, 0x2b158e8a010214b, 0x3952a44384ac0cba, 0x83030dff401ef00, 0xfbde0000ce7cf9f1, 0x60c18210c0c0ef])
def s29Mask : Nat := 0x5f5f5f5f5f5f5f5f
abbrev s29Goal : Nat := sGoal &&& s29Mask
abbrev s29StockWords : List Nat := [0xa0a0a0a0a0a0a0a, 0x4c4c4c4c4c4c4c4c, 0x5050505050505050, 0x5f005f005f005f00, 0x5f5f00005f5f0000, 0x5f5f5f5f00000000]
def s29Fact : Nat × List Nat × Nat × Nat := (s29Mask, s29StockWords, 10, s29Goal)
def s29Cuts : List (Nat × List Nat × Nat × Nat) := [s25Fact, s5Fact, s26Fact, s9Fact, s27Fact, s28Fact]
def s29Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 9, 26, 42, 51, 60, 6, 9, 26, 42, 51, 60, 10, 19, 28, 35, 44, 49, 50, 52, 56, 10, 19, 28], rfl⟩
def s29Witnesses := unpackWitnesses s29StockWords [4616, 265220, 527362, 791041, 1061898, 1332234]
def s29Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xc81902e43a40e801, 0x82700d89b0360648, 0x480889101d53]) else (if j < 2 then (cbits [0x602c0580b0124240, 0xc0d09a02c8580b01, 0x902f31e03666]) else 0x5319cb3824ac90)) 11 (i % 16)
def s29Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x858c9c046280003f, 0xe05258a033f10199, 0x22ec38d049fc824c, 0x4226218eb0fc6d87, 0x98124b16de8aaef4, 0x449]) else (if j < 2 then (cbits [0x83b0e4158708893f, 0x515e8814c430861f, 0x86f440361c23bd1, 0xc097a6033d100d87, 0x5068cf83062812c3, 0x4d1a]) else (cbits [0x700413e4a01ef44, 0x834664223148e194, 0x826c3d8461c090d2, 0x3169280abd2851e8, 0xf8798cc14c403004, 0x5631]))) else (if j < 4 then (cbits [0x8cbd135987f0ac38, 0x219e880c92c1a7a2, 0xb0ec381431e83988, 0x45a9280e3d2a5187, 0x48a8cf4486621031, 0x551a]) else (if j < 5 then (cbits [0xcaa4f6492631092c, 0x71e883cc38d54a4, 0x83ef4c5c928103d3, 0xd89496108cf42462, 0x4850c507d8714293, 0x231a]) else (cbits [0x1030f28d2931492c, 0x217a4])))) 21 (i % 16)
def s29Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x692c08628080fc0, 0x4419870124cc261c, 0x9e984b0fc261c84f, 0xc60c50c19382c430, 0x7a2180103867]) else (if j < 2 then (cbits [0xa234a4462888ccc1, 0x5045e948bd11161e, 0x1e88c010d861c032, 0xe0bd29c61c82f456, 0x7a63ec387987]) else (cbits [0xc6c430467b0bd31e, 0x1a4]))) 19 (i % 16)
def s29Links := pageLinks s29Index s29Codes 4 13 6 5
def s29Data (i : Nat) : Nat × Nat :=
  let e := s29Forest i
  (e &&& 63, e >>> 6)
def s29Sample : Nat × Nat := (s29Blob228920, 96)
def s29Tags := dagTraceTags s29Mask 96 (dagTagBases s29StockWords s29Blob229487 s29Blob229682 96) 9 s29Data
def s29States := dagTrace s29Mask s29StockWords 9 s29Data
def s29MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm5, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val))), (pm9, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 5, 4] 0 i.val)))]
def s29Moves := dagMoves s29MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Autos : DagMovesOK s29Mask s29Goal 64 s29Moves := dagMovesOfCheck (by decide +kernel)
def s29Check := dagCheckNode s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) 36 s29States s29Moves s29Links s29Sample s29Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Roots : dagCheckRoots s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) s29Witnesses (dagRef 36 s29States s29Moves s29Links 0) s29StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block0 : treeBlock 0 24 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block24 : treeBlock 24 12 s29Check = true := by decide +kernel
theorem s29Group0_36 : treeBlock 0 36 s29Check = true := treeBlock_merge (start := 0) (left := 24) (right := 12) (check := s29Check) s29Block0 s29Block24
theorem s29Blocks : treeBlock 0 36 s29Check = true := s29Group0_36
theorem s29Known : Known s29Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s28Stock) s27Stock) s9Stock) s26Stock) s5Stock) s25Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Stock : Lower s29Mask s29StockWords s29Goal 10 := by
  apply lowerDag _ _ _ _ s29Autos _ _ _ s29Known _ s29Roots s29Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s29Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s30Mask : Nat := 0x33ff33ff33ff33ff
abbrev s30Goal : Nat := sGoal &&& s30Mask
abbrev s30StockWords : List Nat := [0x22aa22aa22aa22aa, 0xcc00cc00cc00cc, 0x30f030f030f030f0, 0x3300330033003300, 0x33ff000033ff0000, 0x33ff33ff00000000]
def s30Fact : Nat × List Nat × Nat × Nat := (s30Mask, s30StockWords, 10, s30Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Stock : Lower s30Mask s30StockWords s30Goal 10 := dagShiftLower (width := 64) pm4 s29Stock (by decide +kernel)
def s31Blob236003 : Nat := (cbits [0x81c0607020180406, 0x40a1506038140e02, 0x8160905828150885, 0xa09068141a0985c2, 0x8940a250e078301, 0x9c48261109848251, 0x502a110a8142a118, 0x33118cc2633160b8, 0x1a0d46235190cc62, 0xe8643a1a0d86436, 0x683c160f0383c1c, 0xa060181800061c0f, 0x6090181806050180, 0x81c480611018280, 0x1c26070201c04070, 0x100e02038040e118, 0x1500854580e0e038, 0xe05426150805408, 0x5804161a0546215, 0x8381609858201602, 0xa170185c68161905, 0xa0a05c24170885c0, 0x9868201a04068041, 0x78701a19068381a0, 0x281e09078181e050, 0x250209402250c078, 0x1889458251189440])
def s31Blob236573 : Nat := (cbits [0xf83e0000fc2709cc, 0x3ff8fe3ffc003e03, 0x3fffffc07ffff0f, 0xfffffff3c23f8fff, 0x3c0f030ffe03fff, 0x3ffc00007c000fc, 0xf80000fffc00ffc0, 0xffff000003ffffff, 0xfc000000000000ff])
def s31Blob236786 : Nat := (cbits [0x483206005c2308cc, 0x2ce83a15a4020e21, 0x20aa52a44074aa05, 0x968954728215856a, 0x340d0304944254a, 0x42748040870018b8, 0xe21060dff400ef80, 0xfbbe0000839f39f3, 0xf0180183042180ef])
def s31Mask : Nat := 0x55ff55ff55ff55ff
abbrev s31Goal : Nat := sGoal &&& s31Mask
abbrev s31StockWords : List Nat := [0xaa00aa00aa00aa, 0x44cc44cc44cc44cc, 0x50f050f050f050f0, 0x5500550055005500, 0x55ff000055ff0000, 0x55ff55ff00000000]
def s31Fact : Nat × List Nat × Nat × Nat := (s31Mask, s31StockWords, 10, s31Goal)
def s31Cuts : List (Nat × List Nat × Nat × Nat) := [s4Fact, s5Fact, s0Fact, s9Fact, s2Fact, s3Fact]
def s31Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 21, 26, 37, 42, 51, 60, 6, 21, 26, 37, 42, 5, 10, 19, 28, 35, 44, 49, 50, 52, 56, 5, 10], rfl⟩
def s31Witnesses := unpackWitnesses s31StockWords [10772, 265220, 527362, 799762, 1059333, 1329669]
def s31Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x4e02700ac8068001, 0xa4052027113809c0, 0x580ac05222901480, 0x2b09]) else (cbits [0x7403a016b4b02580, 0xf807823c01d08e80, 0x68cf9e7c03e01f00, 0x5002])) else (if j < 3 then (cbits [0xa435202901404a00, 0x604b005802a8d540, 0x5819c8ce05a6ad01, 0x6b03]) else (if j < 4 then (cbits [0xdaa6c0b601b00d61, 0xe00f007803b85dc0, 0xf81e4cf207903c05, 0x7f03]) else (cbits [0x1c28e04701fdefe0, 0x6153009804822401, 0x3168c7460a20d102, 0xab05])))) 13 (i % 16)
def s31Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x22315008c500003f, 0x98ccc5431f0e0c6c, 0x8343598cfc783371, 0x98ce226218098817, 0x643d998fe7863799, 0x2030e378]) else (cbits [0x9ac432430fc8ac39, 0x10c6d8af45603d10, 0xa337020ccc0631f0, 0x18810a343420cfc0, 0x6370498cc1062103, 0x4498fc14])) else (if j < 3 then (cbits [0x1ac3905b0e114643, 0x5bd1020c430730fc, 0xef4403b0e11af454, 0xbd3018f4403a4b10, 0x32a090c981ec3c07, 0xa0cf826]) else (if j < 4 then (cbits [0x2e62a0a98992834a, 0xc9928346420c98f8, 0x6f448424b13464e4, 0x19302c6404dc9403, 0x124c25203093c4b, 0x100c503a]) else (cbits [0x46340110cfa3a335, 0x18d314434a128d04, 0xe6290a98814a34d5, 0x3d122a92c9398a84, 0x400f00d15125014, 0x4f81303e])))) else (if j < 8 then (if j < 6 then (cbits [0x2c314508d204233c, 0xf804048f448b1880, 0x201c130d323e3340, 0x8c642e3145219305, 0x92c8b98824e31a13, 0x1624f056]) else (if j < 7 then (cbits [0x5894818a4f85e93d, 0x93d116294a57a525, 0x6200c0c51652501, 0x31205cf4416a4b23, 0x3261a0c515cc4818, 0x1a8ca844]) else (cbits [0x706410c98806e34a, 0xd3d107293d84a4b0, 0xc3281b24f0772501, 0x1880703310d0c506, 0x2501f3d287a63d85, 0x20807c7f]))) else (if j < 9 then (cbits [0x1662021010e8202b, 0x918ac506270d9884, 0x692c5f990d7663f1, 0xa50f7693f8da4b61, 0x92c223d1486f44df, 0x8630e018]) else (if j < 10 then (cbits [0x1a620a300a88c01e, 0xd24f61a92c1d18f4, 0xc3146249408ef4a9, 0x1880923351b8cc41, 0xc38a498d66e63187, 0x23bd1094]) else (cbits [0x96f4c63c94098f4c, 0x5b0e21e620078c50, 0x620270d24203142, 0x98c3ca719262]))))) 22 (i % 16)
def s31Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x218d8218a0101f80, 0x219b821998218f8, 0x9823108261c07310, 0xa20c61c0231b8231, 0x7a60f61f8261c827]) else (cbits [0x21931218a8162182, 0x163131219f121951, 0xf1249e1831512320, 0x8d817a2123211231, 0x201e01a1e0091d1])) else (if j < 3 then (cbits [0xd19f1d19e2118a1d, 0x261a09d7a2241a01, 0xe297a21d3149d1a6, 0x9e2b4962b18f8100, 0x49eab7a22d4962d4]) else (if j < 4 then (cbits [0x17a22b49f2b62430, 0x361953418a341998, 0xeb4320b41a53449e, 0x9b81928347a23449, 0x9283d7a53d31ebd1]) else (cbits [0x1021c100fc161c01, 0x4661c817a2c17a24, 0xac961f817a54600f, 0xa6497a64b61c4919, 0x1a4ce621817])))) 20 (i % 16)
def s31Links := pageLinks s31Index s31Codes 5 13 7 6
def s31Data (i : Nat) : Nat × Nat :=
  let e := s31Forest i
  (e &&& 127, e >>> 7)
def s31Sample : Nat × Nat := (s31Blob236003, 96)
def s31Tags := dagTraceTags s31Mask 96 (dagTagBases s31StockWords s31Blob236573 s31Blob236786 96) 9 s31Data
def s31States := dagTrace s31Mask s31StockWords 9 s31Data
def s31MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm3, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 4, 5] 0 i.val))), (pm8, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 5, 4] 0 i.val)))]
def s31Moves := dagMoves s31MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Autos : DagMovesOK s31Mask s31Goal 64 s31Moves := dagMovesOfCheck (by decide +kernel)
def s31Check := dagCheckNode s31Mask s31Goal s31Chart (dagKnownCloses s31Goal s31Cuts) 79 s31States s31Moves s31Links s31Sample s31Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Roots : dagCheckRoots s31Mask s31Goal s31Chart (dagKnownCloses s31Goal s31Cuts) s31Witnesses (dagRef 79 s31States s31Moves s31Links 0) s31StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Block0 : treeBlock 0 24 s31Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Block24 : treeBlock 24 24 s31Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Block48 : treeBlock 48 24 s31Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Block72 : treeBlock 72 7 s31Check = true := by decide +kernel
theorem s31Group0_48 : treeBlock 0 48 s31Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s31Check) s31Block0 s31Block24
theorem s31Group48_31 : treeBlock 48 31 s31Check = true := treeBlock_merge (start := 48) (left := 24) (right := 7) (check := s31Check) s31Block48 s31Block72
theorem s31Group0_79 : treeBlock 0 79 s31Check = true := treeBlock_merge (start := 0) (left := 48) (right := 31) (check := s31Check) s31Group0_48 s31Group48_31
theorem s31Blocks : treeBlock 0 79 s31Check = true := s31Group0_79
theorem s31Known : Known s31Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s3Stock) s2Stock) s9Stock) s0Stock) s5Stock) s4Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Stock : Lower s31Mask s31StockWords s31Goal 10 := by
  apply lowerDag _ _ _ _ s31Autos _ _ _ s31Known _ s31Roots s31Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s31Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s32Mask : Nat := 0x3f3f3f3f3f3f3f3f
abbrev s32Goal : Nat := sGoal &&& s32Mask
abbrev s32StockWords : List Nat := [0x2a2a2a2a2a2a2a2a, 0xc0c0c0c0c0c0c0c, 0x3030303030303030, 0x3f003f003f003f00, 0x3f3f00003f3f0000, 0x3f3f3f3f00000000]
def s32Fact : Nat × List Nat × Nat × Nat := (s32Mask, s32StockWords, 10, s32Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Stock : Lower s32Mask s32StockWords s32Goal 10 := dagShiftLower (width := 64) pm4 s31Stock (by decide +kernel)
def s33Mask : Nat := 0x5555ffff5555ffff
abbrev s33Goal : Nat := sGoal &&& s33Mask
abbrev s33StockWords : List Nat := [0xaaaa0000aaaa, 0x4444cccc4444cccc, 0x5050f0f05050f0f0, 0x5500ff005500ff00, 0x5555000055550000, 0x5555ffff00000000]
def s33Fact : Nat × List Nat × Nat × Nat := (s33Mask, s33StockWords, 10, s33Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Stock : Lower s33Mask s33StockWords s33Goal 10 := dagShiftLower (width := 64) pm2 s12Stock (by decide +kernel)
def s34Mask : Nat := 0xa5a5a5a5a5a5a5a5
abbrev s34Goal : Nat := sGoal &&& s34Mask
abbrev s34StockWords : List Nat := [0xa0a0a0a0a0a0a0a0, 0x8484848484848484, 0xa500a500a500a500, 0xa5a50000a5a50000, 0xa5a5a5a500000000]
def s34Fact : Nat × List Nat × Nat × Nat := (s34Mask, s34StockWords, 7, s34Goal)
def s34Witnesses := unpackWitnesses s34StockWords [3586, 265733, 530949, 797189, 1067525]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Stock : Lower s34Mask s34StockWords s34Goal 7 := by
  apply essentialLift (witnesses := s34Witnesses) (cut := s7Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s7StockWords) (by decide +kernel)
  · exact s7Stock
  · decide +kernel
def s35Mask : Nat := 0xaaaaaaaaaaaaaaaa
abbrev s35Goal : Nat := sGoal &&& s35Mask
abbrev s35StockWords : List Nat := [0x8888888888888888, 0xa0a0a0a0a0a0a0a0, 0xaa00aa00aa00aa00, 0xaaaa0000aaaa0000, 0xaaaaaaaa00000000]
def s35Fact : Nat × List Nat × Nat × Nat := (s35Mask, s35StockWords, 7, s35Goal)
def s35Witnesses := unpackWitnesses s35StockWords [3589, 265731, 528897, 797189, 1067525]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Stock : Lower s35Mask s35StockWords s35Goal 7 := by
  apply essentialLift (witnesses := s35Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s36Mask : Nat := 0xf0f0f0f0f0f0f0f0
abbrev s36Goal : Nat := sGoal &&& s36Mask
abbrev s36StockWords : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc0c0c0c0c0c0c0c0, 0xf000f000f000f000, 0xf0f00000f0f00000, 0xf0f0f0f000000000]
def s36Fact : Nat × List Nat × Nat × Nat := (s36Mask, s36StockWords, 7, s36Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Stock : Lower s36Mask s36StockWords s36Goal 7 := dagShiftLower (width := 64) pm5 s35Stock (by decide +kernel)
def s37Mask : Nat := 0xa5a50000a5a5
abbrev s37Goal : Nat := sGoal &&& s37Mask
abbrev s37StockWords : List Nat := [0xa0a00000a0a0, 0x848400008484, 0xa5000000a500, 0xa5a500000000]
def s37Fact : Nat × List Nat × Nat × Nat := (s37Mask, s37StockWords, 6, s37Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Stock : Lower s37Mask s37StockWords s37Goal 6 := dagShiftLower (width := 64) pm2 s7Stock (by decide +kernel)
def s38Blob252205 : Nat := (cbits [0x8340a07020180406, 0x4180e05038180d02, 0x8160905828150285, 0xd0c068241a050682, 0x20940a250e078381, 0xa8142a1209844261, 0x582e160b4502a110, 0x3a1a0d864361a0d4, 0x160f0383c1c0e864, 0x81800061c0f0683c, 0x8240606018140602, 0x4071201844060a01, 0xd04034080d0201c0, 0x2038040e16034380, 0x3c580e0e038100e0, 0x8150603c140f028, 0x161a054381508054, 0xe05820160205804, 0x5c0a171a0586416, 0x8101a01068281709, 0x1a19068381a0806, 0xd0a074181d028747, 0x9078181e05078301, 0x94381f0c078281e0, 0x6825160944025020, 0x2610098082601098, 0x289c68261909858])
def s38Blob252776 : Nat := (cbits [0xfe0fc000283419c, 0x3d7cbe6781f0781c, 0xfe1f87fff0ff0ffc, 0xffffffffcf8fc7ff, 0xf1f0f878fffff81f, 0x1fffe000fff003, 0xff000003fe00ff80, 0xffff0000001fffff, 0xffe0000000000003])
def s38Blob252989 : Nat := (cbits [0x2000080001008c, 0x14341a2180000804, 0x2202822910410550, 0xadbadaa9cb8bc5de, 0xe1d0e870d5b53916, 0x1099d54084dce032, 0xce0840c37e00f700, 0xbfee0000611e679b, 0x79c0060308108303])
def s38Mask : Nat := 0xf5f5f5f5f5f5f5f5
abbrev s38Goal : Nat := sGoal &&& s38Mask
abbrev s38StockWords : List Nat := [0xa0a0a0a0a0a0a0a0, 0xc4c4c4c4c4c4c4c4, 0xf0f0f0f0f0f0f0f0, 0xf500f500f500f500, 0xf5f50000f5f50000, 0xf5f5f5f500000000]
def s38Fact : Nat × List Nat × Nat × Nat := (s38Mask, s38StockWords, 10, s38Goal)
def s38Cuts : List (Nat × List Nat × Nat × Nat) := [s5Fact, s34Fact, s36Fact, s7Fact, s37Fact, s18Fact, s9Fact, s10Fact, s11Fact]
def s38Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 13, 21, 26, 37, 42, 60, 6, 13, 21, 26, 37, 5, 10, 28, 44, 50, 52, 56, 5, 10, 28, 44, 50], rfl⟩
def s38Witnesses := unpackWitnesses s38StockWords [6668, 265220, 527362, 793093, 1059333, 1329669]
def s38Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x5202428948062001, 0xa805402a01500a42, 0x780bc05e02f01514, 0x2f11]) else (if j < 2 then (cbits [0x6a03501a80c86621, 0xf087803a11d00d4a, 0x1810828024002000, 0x430a]) else (cbits [0xa005002709152881, 0x4c0a415202901404, 0xf01780b445432985, 0x5e02]))) else (if j < 4 then (cbits [0xc426203009784bc0, 0xbc4de06f03689912, 0x905c80e217103881, 0x7323]) else (if j < 5 then (cbits [0xf40771bb81dc0ee0, 0x2c10e47a6bd01e80, 0x69e3031808b0c582, 0x9414]) else (cbits [0x4049654b025812c0, 0xc835e3a935216901, 0x302e996a5b315982, 0xc606])))) 13 (i % 16)
def s38Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x900c50040240003f, 0xcd0c41543432a19b, 0x98463f423199f189, 0x8cd49fa6a4cd1925, 0x1ab30fd55872a4c3, 0x5c62]) else (if j < 2 then (cbits [0x100db55e8ba4f44, 0xc3062a1231482021, 0xe203370e199868c9, 0x314496480d0e3867, 0xc8c30e25927e2c93, 0x1a61]) else (cbits [0xcc3d107d88636c3f, 0x1004a060089a7a2, 0x10f440731283188, 0xc831a1018cd81408, 0x45bd102d8701492, 0x402]))) else (if j < 4 then (cbits [0x898f0140681e34c, 0x81866c26f481249e, 0x82ac380a310430d0, 0x2070200b80a255e8, 0x20ab0e02cc411034, 0x197a]) else (if j < 5 then (cbits [0xea50079e9838034, 0xc852583cc3c1d01a, 0x248c38a349f91a4c, 0x42962193b0fc9987, 0x21130e299e8b48f4, 0xa27a]) else (cbits [0x143d3095e8844c38, 0xacc78040102861e, 0x6493d314989824b, 0x12d496161880ce4a, 0xe030c70bde885c93, 0x2d49])))) else (if j < 9 then (if j < 7 then (cbits [0x40c70b8c780e010, 0xcdd2666a92c2f4a4, 0xe74c393861c5ba4f, 0x5b87a21eb10ced87, 0xc5b3d10d987174f4, 0x3661]) else (if j < 8 then (cbits [0x1e30f0f1e9872f44, 0x105e9e80f443f310, 0x88f4e4361c60494, 0x7213100a0c79164a, 0x99aa4b2c0c866063, 0x4349]) else (cbits [0xa4b0e51d8718693f, 0x71de8898c434a61f, 0x4492c1531564bd1, 0xc4b7a6243d10d987, 0x4918c505802496c3, 0x4e19]))) else (if j < 11 then (if j < 10 then (cbits [0x283d38dcc4062341, 0x93cc602e01051928, 0x966643243100c0c7, 0x8c549fa024cce125, 0x2a9bd134587e8ec3, 0x547a]) else (cbits [0x1cb0e0952583262a, 0x98c403431e487a2, 0x5a92504961c1d24b, 0x5719a938c506c02, 0x82dbd31292587662, 0x1c00])) else (if j < 12 then (cbits [0x2cb10169898b063c, 0x78024b26301d008, 0x8786205a19a940c5, 0x2918a0f80492d25, 0xea218c504c4e7a62, 0xc431]) else (cbits [0xa824c531258ba649, 0x16d878bc949d049e]))))) 21 (i % 16)
def s38Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x301b020090101f80, 0x302005012830040, 0xa027a20331283310, 0x8a8261c0a4960a18, 0x1a60f19982193821]) else (if j < 2 then (cbits [0x149e1131e1119b82, 0x8261c15496027a41, 0x21961c0201417499, 0x1a1c61f8261c827a, 0x621827a61c4a01d0]) else (cbits [0x161c224962118a01, 0xa17a22561c21499a, 0x1a17a62861fa161c, 0x102c31e2b19b8162, 0x7a22c498ac4962c3]))) else (if j < 4 then (cbits [0xb49eab498ab4962b, 0x3649635310019282, 0x23961c35499b561c, 0xa63c61fb561cb57a, 0x3103f31381621b57]) else (if j < 5 then (cbits [0x3319817a7bf7a23f, 0x1928437a74361c4, 0xcc77a24861c47496, 0x21c77a64b61fc761, 0x3184f194ce499816]) else (cbits [0x361c019284e7a74e, 0x8161c817a2d37a25, 0x5931e5819ad761f, 0x21817a6576265862, 0x4a4dd324dd6])))) 20 (i % 16)
def s38Links := pageLinks s38Index s38Codes 5 13 7 6
def s38Data (i : Nat) : Nat × Nat :=
  let e := s38Forest i
  (e &&& 127, e >>> 7)
def s38Sample : Nat × Nat := (s38Blob252205, 96)
def s38Tags := dagTraceTags s38Mask 96 (dagTagBases s38StockWords s38Blob252776 s38Blob252989 96) 9 s38Data
def s38States := dagTrace s38Mask s38StockWords 9 s38Data
def s38MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)))]
def s38Moves := dagMoves s38MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Autos : DagMovesOK s38Mask s38Goal 64 s38Moves := dagMovesOfCheck (by decide +kernel)
def s38Check := dagCheckNode s38Mask s38Goal s38Chart (dagKnownCloses s38Goal s38Cuts) 95 s38States s38Moves s38Links s38Sample s38Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Roots : dagCheckRoots s38Mask s38Goal s38Chart (dagKnownCloses s38Goal s38Cuts) s38Witnesses (dagRef 95 s38States s38Moves s38Links 0) s38StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block0 : treeBlock 0 24 s38Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block24 : treeBlock 24 24 s38Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block48 : treeBlock 48 24 s38Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block72 : treeBlock 72 23 s38Check = true := by decide +kernel
theorem s38Group0_48 : treeBlock 0 48 s38Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s38Check) s38Block0 s38Block24
theorem s38Group48_47 : treeBlock 48 47 s38Check = true := treeBlock_merge (start := 48) (left := 24) (right := 23) (check := s38Check) s38Block48 s38Block72
theorem s38Group0_95 : treeBlock 0 95 s38Check = true := treeBlock_merge (start := 0) (left := 48) (right := 47) (check := s38Check) s38Group0_48 s38Group48_47
theorem s38Blocks : treeBlock 0 95 s38Check = true := s38Group0_95
theorem s38Known : Known s38Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s11Stock) s10Stock) s9Stock) s18Stock) s37Stock) s7Stock) s36Stock) s34Stock) s5Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Stock : Lower s38Mask s38StockWords s38Goal 10 := by
  apply lowerDag _ _ _ _ s38Autos _ _ _ s38Known _ s38Roots s38Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s38Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s39Mask : Nat := 0xafafafafafafafaf
abbrev s39Goal : Nat := sGoal &&& s39Mask
abbrev s39StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0x8c8c8c8c8c8c8c8c, 0xa0a0a0a0a0a0a0a0, 0xaf00af00af00af00, 0xafaf0000afaf0000, 0xafafafaf00000000]
def s39Fact : Nat × List Nat × Nat × Nat := (s39Mask, s39StockWords, 10, s39Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Stock : Lower s39Mask s39StockWords s39Goal 10 := dagShiftLower (width := 64) pm5 s38Stock (by decide +kernel)
def st25 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf0f0f0f00f0f0f0f, 0), (0xf0f0f0f0, 28)], [(0xf0f0f0f00000000, 28)])
def pm13 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23, st25]
def s40Blob257948 : Nat := (cbits [0xf026330986c2617, 0xc28171c0f0683c0e, 0x330e07c261f0c06, 0xb098ec6837098dc6, 0x80f0303c0a0f0703, 0x6c68170e05c20171, 0x281f1c06c381b080, 0x331a0cc20330c07c, 0xc0ec60370a0dc70, 0xfc263f080f0603b, 0xc30171c0fc683f0e, 0x1f1806c281b1805, 0x30a0cc701f1a07c2, 0xc0dc3837080dc303, 0xfc683b0e0ec203b1, 0x7017180fc303f0a0, 0x370e0cc601f1a06c, 0x80fc263c0a0ec30])
def s40Blob258338 : Nat := (cbits [0xbffffffdfffc7fc7, 0xd5e39cfe631f9b79, 0xe6fc1f3f83e3e3ba, 0xf8ffe03ffc03fc3c])
def s40Blob258454 : Nat := (cbits [0x4000000400002907, 0x2a39291829589258, 0x194b506892c942a8, 0x7921ab158925430])
def s40Mask : Nat := 0x9999000099990000
abbrev s40Goal : Nat := sGoal &&& s40Mask
abbrev s40StockWords : List Nat := [0x8888000088880000, 0x9090000090900000, 0x9900000099000000, 0x9999000000000000]
def s40Fact : Nat × List Nat × Nat × Nat := (s40Mask, s40StockWords, 6, s40Goal)
def s40Cuts : List (Nat × List Nat × Nat × Nat) := []
def s40Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[23, 27, 51, 60, 23, 27, 51, 60, 23, 27, 51, 60, 19, 28, 52, 56, 19, 28, 52, 56, 19, 28, 52, 56], rfl⟩
def s40Witnesses := unpackWitnesses s40StockWords [11796, 273939, 538131, 812563]
def s40Index (i : Nat) : Nat := unpack 0xa28301 6 i
def s40Codes (i : Nat) : Nat := unpack (cbits [0x31010c504010000f, 0x1492c6]) 17 i
def s40Forest (i : Nat) : Nat := unpack 0x3144010803c 15 i
def s40Links := pageLinks s40Index s40Codes 3 13 2 4
def s40Data (i : Nat) : Nat × Nat :=
  let e := s40Forest i
  (e &&& 3, e >>> 2)
def s40Sample : Nat × Nat := (s40Blob257948, 64)
def s40Tags := dagTraceTags s40Mask 64 (dagTagBases s40StockWords s40Blob258338 s40Blob258454 64) 5 s40Data
def s40States := dagTrace s40Mask s40StockWords 5 s40Data
def s40MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm11, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val))), (pm13, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 5, 2, 4, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 5, 4, 2] 0 i.val)))]
def s40Moves := dagMoves s40MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Autos : DagMovesOK s40Mask s40Goal 64 s40Moves := dagMovesOfCheck (by decide +kernel)
def s40Check := dagCheckNode s40Mask s40Goal s40Chart (dagKnownCloses s40Goal s40Cuts) 3 s40States s40Moves s40Links s40Sample s40Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Roots : dagCheckRoots s40Mask s40Goal s40Chart (dagKnownCloses s40Goal s40Cuts) s40Witnesses (dagRef 3 s40States s40Moves s40Links 0) s40StockWords 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Block0 : treeBlock 0 3 s40Check = true := by decide +kernel
theorem s40Blocks : treeBlock 0 3 s40Check = true := s40Block0
theorem s40Known : Known s40Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Stock : Lower s40Mask s40StockWords s40Goal 6 := by
  apply lowerDag _ _ _ _ s40Autos _ _ _ s40Known _ s40Roots s40Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s40Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s41Mask : Nat := 0x9999999999999999
abbrev s41Goal : Nat := sGoal &&& s41Mask
abbrev s41StockWords : List Nat := [0x8888888888888888, 0x9090909090909090, 0x9900990099009900, 0x9999000099990000, 0x9999999900000000]
def s41Fact : Nat × List Nat × Nat × Nat := (s41Mask, s41StockWords, 7, s41Goal)
def s41Witnesses := unpackWitnesses s41StockWords [3588, 265731, 529923, 812579, 1074707]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Stock : Lower s41Mask s41StockWords s41Goal 7 := by
  apply essentialLift (witnesses := s41Witnesses) (cut := s40Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s40StockWords) (by decide +kernel)
  · exact s40Stock
  · decide +kernel
def s42Mask : Nat := 0xf00ff00ff00ff00f
abbrev s42Goal : Nat := sGoal &&& s42Mask
abbrev s42StockWords : List Nat := [0xa00aa00aa00aa00a, 0xc00cc00cc00cc00c, 0xf000f000f000f000, 0xf00f0000f00f0000, 0xf00ff00f00000000]
def s42Fact : Nat × List Nat × Nat × Nat := (s42Mask, s42StockWords, 7, s42Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Stock : Lower s42Mask s42StockWords s42Goal 7 := dagShiftLower (width := 64) pm5 s41Stock (by decide +kernel)
def s43Mask : Nat := 0xff00ff00ff00ff00
abbrev s43Goal : Nat := sGoal &&& s43Mask
abbrev s43StockWords : List Nat := [0xaa00aa00aa00aa00, 0xcc00cc00cc00cc00, 0xf000f000f000f000, 0xff000000ff000000, 0xff00ff0000000000]
def s43Fact : Nat × List Nat × Nat × Nat := (s43Mask, s43StockWords, 7, s43Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Stock : Lower s43Mask s43StockWords s43Goal 7 := dagShiftLower (width := 64) pm3 s35Stock (by decide +kernel)
def s44Mask : Nat := 0xf00f0000f00f0000
abbrev s44Goal : Nat := sGoal &&& s44Mask
abbrev s44StockWords : List Nat := [0xa00a0000a00a0000, 0xc00c0000c00c0000, 0xf0000000f0000000, 0xf00f000000000000]
def s44Fact : Nat × List Nat × Nat × Nat := (s44Mask, s44StockWords, 6, s44Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Stock : Lower s44Mask s44StockWords s44Goal 6 := dagShiftLower (width := 64) pm5 s40Stock (by decide +kernel)
def s45Mask : Nat := 0xf00ff00f00000000
abbrev s45Goal : Nat := sGoal &&& s45Mask
abbrev s45StockWords : List Nat := [0xa00aa00a00000000, 0xc00cc00c00000000, 0xf000f00000000000, 0xf00f000000000000]
def s45Fact : Nat × List Nat × Nat × Nat := (s45Mask, s45StockWords, 6, s45Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Stock : Lower s45Mask s45StockWords s45Goal 6 := dagShiftLower (width := 64) pm9 s40Stock (by decide +kernel)
def s46Blob269365 : Nat := (cbits [0x2c060b040240209, 0x4180e05038180d05, 0x41a0506830190886, 0xe0e074261b0c0682, 0x50a85029108a4381, 0xb4462b140a8442a0, 0x4633098cc582e160, 0x39188e46433188cc, 0xe0f0703a190e870, 0x82400091c0f0583c, 0x4220906024140901, 0x20b1402442090c02, 0xb0982c100b0102c0, 0xe034100d00834460, 0x38100e01038580d0, 0x140f0183c580e0e0, 0x190406402190603c, 0x1886438190986420, 0x68101a010687019, 0x8641a0e068261a08, 0x21b0506c061b1c06, 0xd06074301b0906c2, 0x6078141e0c074221, 0x7c261f0c078241e0, 0x4029040a402290e0, 0x29188a45829118a4, 0x100a8102a010a870])
def s46Blob269938 : Nat := (cbits [0xff87fffc1fb1b19f, 0x67de5e6c1ff0ff01, 0xe03f1ffe03f87c00, 0x3ff800380606070, 0xf87fffff003fe000, 0xffffffffffffffff, 0xfc000003ff807f80, 0xffff8000003fffff, 0xffc0000000000003])
def s46Blob270153 : Nat := (cbits [0xa480e5480b909085, 0x2596162c0a504510, 0x22150b5221886818, 0x4266002180606050, 0xd06b6b7a04222020, 0x54abb2a54b7712b3, 0xf02220c2fe807d80, 0x7f7d8000183cdcf9, 0x9f0000c180444303])
def s46Mask : Nat := 0xff0fff0fff0fff0f
abbrev s46Goal : Nat := sGoal &&& s46Mask
abbrev s46StockWords : List Nat := [0xaa0aaa0aaa0aaa0a, 0xcc0ccc0ccc0ccc0c, 0xf000f000f000f000, 0xff00ff00ff00ff00, 0xff0f0000ff0f0000, 0xff0fff0f00000000]
def s46Fact : Nat × List Nat × Nat × Nat := (s46Mask, s46StockWords, 10, s46Goal)
def s46Cuts : List (Nat × List Nat × Nat × Nat) := [s25Fact, s42Fact, s43Fact, s26Fact, s9Fact, s44Fact, s45Fact]
def s46Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[9, 14, 26, 42, 51, 60, 9, 14, 26, 42, 51, 60, 10, 19, 28, 35, 44, 49, 50, 56, 10, 19, 28, 35], rfl⟩
def s46Witnesses := unpackWitnesses s46StockWords [4616, 269324, 531466, 791041, 1061898, 1332234]
def s46Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x3a01b10924062001, 0x8004001e10f00742, 0x90c8a04212101004, 0x3501]) else (if j < 2 then (cbits [0x6e03701a88d406a0, 0xec07413a01d00dc6, 0xf88fc07e03c19d84, 0x4101]) else (cbits [0x9014802119042820, 0x2809404a02485240, 0xc81640ae24a6a501, 0x5922]))) else (if j < 5 then (if j < 4 then (cbits [0xbc15e02e85740ba0, 0xa02d00670b3817d0, 0xc09a5ed206903481, 0x7a03]) else (cbits [0x808404202100f4a, 0x1410818404202101, 0x4862030e1860c286, 0x8a4c])) else (if j < 6 then (cbits [0x2c0950ca82541262, 0x7c13e09f04ba2583, 0x582ac13ec9f04f82, 0xab25]) else (cbits [0x712b805c02bd35e0, 0x4c3987cc06587283, 0xe876c5a87d406a03, 0xde0e])))) 13 (i % 16)
def s46Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 7 then (if j < 3 then (if j < 1 then (cbits [0x860074040100003f, 0xca8629420432101b, 0x97833f3c1999a0c9, 0x8d549faaa4cd3925, 0x1b1b0fd81872b6c3, 0x6b62]) else (if j < 2 then (cbits [0x810c5381e8bb6f44, 0x4198710833f04199, 0x816c430961f8430e, 0x40361c443d1619e8, 0x20198801465106f4, 0x77a]) else (cbits [0x868c502987814f4c, 0x24467e223331018d, 0xe2e633163108a188, 0x899321cb98fc64c6, 0x18eb0fc7187234c3, 0x2062]))) else (if j < 5 then (if j < 4 then (cbits [0x7188271e8b34f44, 0x480211ef440f61c, 0x82ac380e310098ca, 0x183180c250255e8, 0xa0dbd10552581e62, 0x1e01]) else (cbits [0x910c507d8783ef4c, 0x89d8944a33d23198, 0x4832829928143d2, 0x70d18e810c509865, 0x995a4b2886864433, 0x2d49])) else (if j < 6 then (cbits [0x9830e4b98715a93f, 0x6b9e8866c433161f, 0x158f442c61c583d1, 0x42c61c0798a40cc4, 0xa1930f0c9e985ef4, 0x3518]) else (cbits [0x1c18fad86946c33e, 0xede9674f44b8325, 0x72628370085d494, 0x1110149e80441001, 0x49f8ca0f86284604, 0x4619])))) else (if j < 10 then (if j < 8 then (cbits [0x1c18c91c6946c332, 0x92de8894c3d4961c, 0x240284d928263d2, 0x51300e8280204cc5, 0x6201880e464c4803, 0x4149]) else (if j < 9 then (cbits [0x2230f90d87084931, 0x104c6890328457a2, 0x8883284331a210ca, 0xf4931995988114c6, 0xfa8b0e53d8719263, 0x5261]) else (cbits [0x68bd173de88a8c43, 0x14de98a0f442c496, 0xa6c3252d18a29b0f, 0x4574a52b24b12867, 0x9ad494165e94b0f4, 0x5c00]))) else (if j < 12 then (if j < 11 then (cbits [0x8d0ca418628ba043, 0xce8c665c620a91a1, 0x9b4c3f4f61c6698f, 0x5073102fbd1579e8, 0x9283d10bd2583663, 0x6100]) else (cbits [0x9818807065210314, 0x96187aa2c384b31e, 0xa12008df928313d2, 0xd27020b200d47403, 0x89d8c9cc46294e04, 0x4719])) else (if j < 13 then (cbits [0xa924b3306929833d, 0x365292b293d57498, 0xcef4c627a232b0e, 0x8667a60f00738a4a, 0xe990c507c03a1400, 0x6819]) else (cbits [0x3330e1a927aa692c, 0x8003a1600869194, 0x2a892c6c1a4998c5, 0x86d19433b0f1b929, 0x353d21a5878d0f4]))))) 21 (i % 16)
def s46Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x318a020040101f80, 0x2194051998261c0, 0xf8261c827a20761c, 0xe81621827a60a61, 0x61c0e3100e18a0d0]) else (if j < 2 then (cbits [0x2008121998d18d8d, 0x8d61c153100d1941, 0xb8d4a0183198d310, 0x1c8d7a21b61c0d31, 0x7a61e01a1e61f8d6]) else (cbits [0x218a2201b816218d, 0x2619ea219424198a, 0x8227a52262522194, 0x1c2c4962b18a0192, 0x7a22f61c2b499ab6]))) else (if j < 5 then (if j < 4 then (cbits [0xb7a63261fab61cab, 0x3518a3519381621a, 0x43931f350083719f, 0x99817a5b57a23531, 0x1943d18a3d008bd1]) else (cbits [0x498c04964031040, 0xbd7a24061f4061c4, 0xc3d194481a53d194, 0xa53d7a23d61ebd61, 0x61c4f496019283d7])) else (if j < 6 then (cbits [0x361fcf61ccf7a250, 0x5649981621cf7a65, 0x5567a2564a556496, 0x9dc61c01928567a, 0x7a2dc7a25c021dc0]) else (cbits [0x17a5610096161c81, 0x6661c6401ae461f8, 0x46919ee87a6647a6, 0xa4ec6218149ee819, 0x4a4ec1946d1])))) 20 (i % 16)
def s46Links := pageLinks s46Index s46Codes 5 13 7 6
def s46Data (i : Nat) : Nat × Nat :=
  let e := s46Forest i
  (e &&& 127, e >>> 7)
def s46Sample : Nat × Nat := (s46Blob269365, 96)
def s46Tags := dagTraceTags s46Mask 96 (dagTagBases s46StockWords s46Blob269938 s46Blob270153 96) 9 s46Data
def s46States := dagTrace s46Mask s46StockWords 9 s46Data
def s46MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)))]
def s46Moves := dagMoves s46MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Autos : DagMovesOK s46Mask s46Goal 64 s46Moves := dagMovesOfCheck (by decide +kernel)
def s46Check := dagCheckNode s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) 111 s46States s46Moves s46Links s46Sample s46Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Roots : dagCheckRoots s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) s46Witnesses (dagRef 111 s46States s46Moves s46Links 0) s46StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block0 : treeBlock 0 24 s46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block24 : treeBlock 24 24 s46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block48 : treeBlock 48 24 s46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block72 : treeBlock 72 24 s46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block96 : treeBlock 96 15 s46Check = true := by decide +kernel
theorem s46Group0_48 : treeBlock 0 48 s46Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s46Check) s46Block0 s46Block24
theorem s46Group72_39 : treeBlock 72 39 s46Check = true := treeBlock_merge (start := 72) (left := 24) (right := 15) (check := s46Check) s46Block72 s46Block96
theorem s46Group48_63 : treeBlock 48 63 s46Check = true := treeBlock_merge (start := 48) (left := 24) (right := 39) (check := s46Check) s46Block48 s46Group72_39
theorem s46Group0_111 : treeBlock 0 111 s46Check = true := treeBlock_merge (start := 0) (left := 48) (right := 63) (check := s46Check) s46Group0_48 s46Group48_63
theorem s46Blocks : treeBlock 0 111 s46Check = true := s46Group0_111
theorem s46Known : Known s46Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s45Stock) s44Stock) s9Stock) s26Stock) s43Stock) s42Stock) s25Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Stock : Lower s46Mask s46StockWords s46Goal 10 := by
  apply lowerDag _ _ _ _ s46Autos _ _ _ s46Known _ s46Roots s46Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s46Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s47Mask : Nat := 0xbbbbbbbbbbbbbbbb
abbrev s47Goal : Nat := sGoal &&& s47Mask
abbrev s47StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0x8888888888888888, 0xb0b0b0b0b0b0b0b0, 0xbb00bb00bb00bb00, 0xbbbb0000bbbb0000, 0xbbbbbbbb00000000]
def s47Fact : Nat × List Nat × Nat × Nat := (s47Mask, s47StockWords, 10, s47Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Stock : Lower s47Mask s47StockWords s47Goal 10 := dagShiftLower (width := 64) pm3 s46Stock (by decide +kernel)
def s48Mask : Nat := 0xccffccffccffccff
abbrev s48Goal : Nat := sGoal &&& s48Mask
abbrev s48StockWords : List Nat := [0x88aa88aa88aa88aa, 0xcccccccccccccccc, 0xc0f0c0f0c0f0c0f0, 0xcc00cc00cc00cc00, 0xccff0000ccff0000, 0xccffccff00000000]
def s48Fact : Nat × List Nat × Nat × Nat := (s48Mask, s48StockWords, 10, s48Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Stock : Lower s48Mask s48StockWords s48Goal 10 := dagShiftLower (width := 64) pm3 s38Stock (by decide +kernel)
def s49Mask : Nat := 0xdddddddddddddddd
abbrev s49Goal : Nat := sGoal &&& s49Mask
abbrev s49StockWords : List Nat := [0x8888888888888888, 0xcccccccccccccccc, 0xd0d0d0d0d0d0d0d0, 0xdd00dd00dd00dd00, 0xdddd0000dddd0000, 0xdddddddd00000000]
def s49Fact : Nat × List Nat × Nat × Nat := (s49Mask, s49StockWords, 10, s49Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Stock : Lower s49Mask s49StockWords s49Goal 10 := dagShiftLower (width := 64) pm5 s46Stock (by decide +kernel)
def s50Mask : Nat := 0xcccccccccccccccc
abbrev s50Goal : Nat := sGoal &&& s50Mask
abbrev s50StockWords : List Nat := [0x8888888888888888, 0xc0c0c0c0c0c0c0c0, 0xcc00cc00cc00cc00, 0xcccc0000cccc0000, 0xcccccccc00000000]
def s50Fact : Nat × List Nat × Nat × Nat := (s50Mask, s50StockWords, 7, s50Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Stock : Lower s50Mask s50StockWords s50Goal 7 := dagShiftLower (width := 64) pm4 s35Stock (by decide +kernel)
def s51Blob280638 : Nat := (cbits [0x8240a070181c0406, 0x80a0d0502c060b00, 0x416088540a150503, 0xa0506822190985c2, 0x8940a250986c241, 0xa842291189c44261, 0x2633118ac442a050, 0x35190cc6233118cc, 0x190e86239190d862, 0x181406028180606, 0xc04070081c440609, 0xa090182446070981, 0xb108242209050240, 0x182c260b0102c020, 0x3c060f01038020d1, 0x261500854140f028, 0x1609858041618854, 0x885c0a170185c64, 0x8642619008642417, 0xc641a09868041a18, 0x41b0886c141b0186, 0xe05078221d028742, 0x189402250987c241, 0x9846260109862251, 0x42270289c0627190, 0x29118a402291109c, 0x190a8462a010a862])
def s51Blob281211 : Nat := (cbits [0xe3f7ffe05f9b9b7e, 0xafececb71fc79f8f, 0xe3f8e7f1fc7bc1ff, 0xfffc01ff300f0fc7, 0xc0f0f0f803fff801, 0xfc00fffe007ffe00, 0xff800000ff00ff00, 0xffff00000000ffff, 0xffff000000000000])
def s51Blob281427 : Nat := (cbits [0xebb777a3579b9b5e, 0xabececb35dd79aae, 0xea7ae5f53d5b8bdd, 0x4020040200010144, 0x2020a000800800, 0x210000400804, 0x9b011088fd00de00, 0xfede00009024d66d, 0xdb36004812022110])
def s51Mask : Nat := 0xeeeeeeeeeeeeeeee
abbrev s51Goal : Nat := sGoal &&& s51Mask
abbrev s51StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xe0e0e0e0e0e0e0e0, 0xee00ee00ee00ee00, 0xeeee0000eeee0000, 0xeeeeeeee00000000]
def s51Fact : Nat × List Nat × Nat × Nat := (s51Mask, s51StockWords, 10, s51Goal)
def s51Cuts : List (Nat × List Nat × Nat × Nat) := [s35Fact, s50Fact, s0Fact, s26Fact]
def s51Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 9, 21, 26, 37, 42, 51, 6, 9, 21, 26, 37, 5, 10, 19, 35, 49, 50, 5, 10, 19, 35, 49, 50], rfl⟩
def s51Witnesses := unpackWitnesses s51StockWords [5642, 265733, 527362, 791041, 1059333, 1329669]
def s51Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x130832d00e0001, 0x542150054014085, 0x8805a41680581160, 0x18846201]) else (cbits [0xc0218c6701904640, 0x8c123008c023008, 0x584960240c8e1238, 0x26109802])) else (if j < 3 then (cbits [0x212880a012800a00, 0xbe029b0a412900a, 0x100c213080be22f8, 0x3118c403]) else (if j < 4 then (cbits [0x403484d203480d01, 0xf213c80d6e3504d, 0xd80f603d80f413d0, 0x3d80f603]) else (cbits [0xa03e04f803e00f61, 0x118146011423eb4f, 0x88522048811a4468, 0x49052404])))) else (if j < 7 then (if j < 6 then (cbits [0x805185441500926d, 0xd4e053054c052094, 0x5055405501540538, 0x56015615]) else (cbits [0xb5f855f05705582, 0x19a1658996065818, 0x70d9c067019c0670, 0x6909a216])) else (if j < 8 then (cbits [0xc06a85a816a01a80, 0x1dc17701af76b05a, 0x8a1e207789de0778, 0x7cd5f207]) else (if j < 9 then (cbits [0x20878a1e087821c1, 0x648288ce22088822, 0x48250193864e0930, 0x9c0252f9]) else 0xaa06a809c72700)))) 14 (i % 16)
def s51Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 11 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x880340100400003f, 0xf04c00f84401c0, 0x144d407e1a80cc2e, 0xf1a8cce2e1954023, 0x4f315888620cd467, 0x584c863098dc]) else (cbits [0xa50e6149bc8892c, 0x61f8fcc391d5871b, 0x455d5e8848310c86, 0x6020c500200f2fcf, 0x731020c33f01866, 0x424c860498dc])) else (if j < 3 then (cbits [0x730fc0d61c816c38, 0x7a2a16f440418860, 0x3840de8801b0e10d, 0x80430e1057a200ac, 0x319501433c421e8, 0x21258029880]) else (if j < 4 then (cbits [0x7b0f00f7a6018f44, 0xf82a0090480100, 0x3f06406e0b80cc16, 0xe0d188119021a2e0, 0x1e61c238643070c6, 0x8d87e10b0e4]) else (cbits [0xbd151e7a204ac43, 0x7a2028c3804cc409, 0x140600600c0d0114, 0x88dbd101b61c0263, 0x1418a03e01907407, 0x81e880da4b0])))) else (if j < 8 then (if j < 6 then (cbits [0x230f0247a6044018, 0x2105003e09c0101, 0x3e4a409c94012829, 0x51598f92b1a50563, 0x2d7a7858f44cacc9, 0xa8060964940]) else (if j < 7 then (cbits [0x7b0e02a020454330, 0x621864c3f0c58721, 0x444c5e8a97bd1034, 0x19b0f0337a6060f, 0x3701505001a0d801, 0xec09c1c8128]) else (cbits [0xe18f60631005631a, 0x4a087c92c0f4c961, 0x50109e9c20bd103f, 0x81d3d30381920872, 0x718a07403c100c7, 0xf86660d0c64]))) else (if j < 9 then (cbits [0x3a4dc4549627c33f, 0x61c892c3851d2862, 0x441398862630fc4b, 0x82330e14b7a2a92f, 0x831009033c519e8, 0x1198700d9894]) else (if j < 10 then (cbits [0x6b0f04d7a6094f44, 0x4a12a064e140c842, 0x3e155871a8253a50, 0xcab3128586210acc, 0x5c7a58b6f4456189, 0x56e4a02fbd3c]) else (cbits [0x918d05431a0a233c, 0x1924a403014c0482, 0x3c1640782bb13052, 0x2ec9605a7a44b23, 0x5d7a40c0c5417989, 0x240102f3d20]))))) else (if j < 16 then (if j < 13 then (if j < 12 then (cbits [0x100f43f01883800d, 0x3150d633e18c6783, 0x411b126b23a4b050, 0x83731386d61c0b09, 0x727a70e2f4a1c1e8, 0x740303a4940]) else (cbits [0xc41d006814008, 0x3150ca32a1906282, 0x3819926b2424b051, 0x353d10696210d0c, 0x533140a462819c06, 0x1986613300f0])) else (if j < 14 then (cbits [0x48cc06831e0a8628, 0x1a40dec4c1bd8783, 0xf1d801235192073, 0xe3c00ae7700d8ee0, 0x7a0218f203f9e006, 0x78632058c50]) else (if j < 15 then (cbits [0x78ca82c18dc3c31a, 0x31b41662050c67e1, 0x37125259a198fe2f, 0x724b0e1744a18b69, 0x7d7a28f8f44dd188, 0x1ec6900f9890]) else (cbits [0x18940c3104f6648, 0x496060636880c4c1, 0x4412987118250a0c, 0x53f80687f007494f, 0x8102550003620005, 0x34628410138])))) else (if j < 19 then (if j < 17 then (cbits [0x88caa2118d042319, 0x31b41a62010467a1, 0x4112d2592098f631, 0x536b1064b61c0da9, 0x7d92810af4e211e9, 0x20c090110c61]) else (if j < 18 then (cbits [0x180340e004506348, 0x1886401e88c01c1, 0x318c8655070c5039, 0xa2e18ac4c3104723, 0x8749ac9892c21cc6, 0x211e8845b0e2]) else (cbits [0x7bd388f7a691af4c, 0x62611033c6124a0c, 0x4c22466044b1008a, 0xc1200340f004118f, 0x3a01886601e89001, 0x8cc655078c50]))) else (if j < 20 then (cbits [0xe98ac4d310474331, 0x49ac9a92c228c6a2, 0x8239e884630e28a, 0xf128038250068200, 0x4201886801e0b401, 0x244092a100f4]) else (if j < 21 then (cbits [0x10cc634195420314, 0x310522349d0867b2, 0x411b8c6a2f98ac4e, 0xb2724b072326adc6, 0x724a6edc9419b926, 0x23587842b0e2]) else (cbits [0x2bd118f61f11ec3d, 0x11cf4824a4a0c])))))) 23 (i % 16)
def s51Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x8078080100203f00, 0x98700a3140261c01, 0x4c3808310010ccc0, 0xc61c010cf028c6e0, 0x7b0fc0987204f440, 0x7a60]) else (cbits [0x80204801a02c4302, 0x801224c381331009, 0x43401801989007c4, 0x261c0d98804806e2, 0xfb0e0480783a6371, 0xc8])) else (if j < 3 then (cbits [0x608987224f441f, 0x588624f4c2461f89, 0xe03e2700413803c0, 0x719f1380c0a80844, 0x7807805e9e4ef442, 0x61c1]) else (if j < 4 then (cbits [0xb0fcbd8725ef4430, 0x806602c432f7a619, 0xc324380151b0020d, 0x60271b3d30e80946, 0xb24b0d8c966c63d3, 0x4a09]) else (cbits [0x3d38d9e886c63c40, 0x92588a620019281b, 0xa33c4849ba2b0e11, 0x561ca2bd11298708, 0xb10d15e989ac3f4, 0x3158])))) else (if j < 7 then (if j < 6 then (cbits [0x98d148678a264250, 0x1870a06345101229, 0x2c42506262bb0f94, 0x7a2283d2164078b, 0x831217a4b0baf4b5, 0x7a7a]) else (cbits [0xf588c6e02c5460, 0x654c83146419e31, 0x8c386401833a4d59, 0x219f313d1191884c, 0x7b13989870c49356, 0x61e3])) else (if j < 8 then (cbits [0xbd3989e94c4f4462, 0x987003250621a439, 0xc02b76007bb0025d, 0x61a43d810dd807ee, 0xfb0e405e8aecf447, 0x73]) else (if j < 9 then (cbits [0x8139fc094fe02a7f, 0x5e9cfef4a7f02441, 0x233c8831ac3b0fc0, 0xc61c43b132218811, 0x3bd1239e990ef4c8, 0x7a6c]) else 0x49424409322c4301)))) 21 (i % 16)
def s51Links := pageLinks s51Index s51Codes 5 13 8 6
def s51Data (i : Nat) : Nat × Nat :=
  let e := s51Forest i
  (e &&& 255, e >>> 8)
def s51Sample : Nat × Nat := (s51Blob280638, 96)
def s51Tags := dagTraceTags s51Mask 96 (dagTagBases s51StockWords s51Blob281211 s51Blob281427 96) 9 s51Data
def s51States := dagTrace s51Mask s51StockWords 9 s51Data
def s51MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm4, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val))), (pm10, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 5, 4] 0 i.val)))]
def s51Moves := dagMoves s51MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Autos : DagMovesOK s51Mask s51Goal 64 s51Moves := dagMovesOfCheck (by decide +kernel)
def s51Check := dagCheckNode s51Mask s51Goal s51Chart (dagKnownCloses s51Goal s51Cuts) 147 s51States s51Moves s51Links s51Sample s51Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Roots : dagCheckRoots s51Mask s51Goal s51Chart (dagKnownCloses s51Goal s51Cuts) s51Witnesses (dagRef 147 s51States s51Moves s51Links 0) s51StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Block0 : treeBlock 0 24 s51Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Block24 : treeBlock 24 24 s51Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Block48 : treeBlock 48 24 s51Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Block72 : treeBlock 72 24 s51Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Block96 : treeBlock 96 24 s51Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Block120 : treeBlock 120 24 s51Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Block144 : treeBlock 144 3 s51Check = true := by decide +kernel
theorem s51Group24_48 : treeBlock 24 48 s51Check = true := treeBlock_merge (start := 24) (left := 24) (right := 24) (check := s51Check) s51Block24 s51Block48
theorem s51Group0_72 : treeBlock 0 72 s51Check = true := treeBlock_merge (start := 0) (left := 24) (right := 48) (check := s51Check) s51Block0 s51Group24_48
theorem s51Group72_48 : treeBlock 72 48 s51Check = true := treeBlock_merge (start := 72) (left := 24) (right := 24) (check := s51Check) s51Block72 s51Block96
theorem s51Group120_27 : treeBlock 120 27 s51Check = true := treeBlock_merge (start := 120) (left := 24) (right := 3) (check := s51Check) s51Block120 s51Block144
theorem s51Group72_75 : treeBlock 72 75 s51Check = true := treeBlock_merge (start := 72) (left := 48) (right := 27) (check := s51Check) s51Group72_48 s51Group120_27
theorem s51Group0_147 : treeBlock 0 147 s51Check = true := treeBlock_merge (start := 0) (left := 72) (right := 75) (check := s51Check) s51Group0_72 s51Group72_75
theorem s51Blocks : treeBlock 0 147 s51Check = true := s51Group0_147
theorem s51Known : Known s51Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s26Stock) s0Stock) s50Stock) s35Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Stock : Lower s51Mask s51StockWords s51Goal 10 := by
  apply lowerDag _ _ _ _ s51Autos _ _ _ s51Known _ s51Roots s51Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s51Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s52Mask : Nat := 0xf0fff0fff0fff0ff
abbrev s52Goal : Nat := sGoal &&& s52Mask
abbrev s52StockWords : List Nat := [0xa0aaa0aaa0aaa0aa, 0xc0ccc0ccc0ccc0cc, 0xf0f0f0f0f0f0f0f0, 0xf000f000f000f000, 0xf0ff0000f0ff0000, 0xf0fff0ff00000000]
def s52Fact : Nat × List Nat × Nat × Nat := (s52Mask, s52StockWords, 10, s52Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52Stock : Lower s52Mask s52StockWords s52Goal 10 := dagShiftLower (width := 64) pm4 s46Stock (by decide +kernel)
def s53Blob287174 : Nat := (cbits [0x86c2617028340209, 0xc4229108940a2509, 0x20d108240a09098c, 0x900894261f0285c0, 0x8cc422d028b4022, 0x342609098ec26371, 0xa1f0086c0217108, 0x37008cc022d028a4, 0x98fc423b108dc0a, 0x86c0a1b1085c260d, 0xc262909894021f10, 0xa3f008ec0237028c, 0xb098b4421f108fc0, 0x8fc0a3])
def s53Blob287477 : Nat := (cbits [0xbc36df9ef9ce188c, 0xc7b9d74bbd33b565, 0xefe0fe0fe0f0fe5d])
def s53Blob287573 : Nat := (cbits [0x89122061801c108c, 0x44841300, 0x180a602302600000])
def s53Mask : Nat := 0x8888222288882222
abbrev s53Goal : Nat := sGoal &&& s53Mask
abbrev s53StockWords : List Nat := [0x8888000088880000, 0x8080202080802020, 0x8800220088002200, 0x8888222200000000]
def s53Fact : Nat × List Nat × Nat × Nat := (s53Mask, s53StockWords, 5, s53Goal)
def s53Cuts : List (Nat × List Nat × Nat × Nat) := []
def s53Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[9, 23, 37, 51, 9, 23, 37, 51, 9, 23, 37, 51, 5, 19, 33, 5, 19, 33, 5, 19, 33, 5, 19, 33], rfl⟩
def s53Witnesses := unpackWitnesses s53StockWords [11781, 273939, 528897, 805381]
def s53Index (i : Nat) : Nat := unpack 0x9 2 i
def s53Codes (i : Nat) : Nat := unpack 0xf 15 i
def s53Forest (i : Nat) : Nat := unpack 0x1e 14 i
def s53Links := pageLinks s53Index s53Codes 1 13 1 2
def s53Data (i : Nat) : Nat × Nat :=
  let e := s53Forest i
  (e &&& 1, e >>> 1)
def s53Sample : Nat × Nat := (s53Blob287174, 48)
def s53Tags := dagTraceTags s53Mask 48 (dagTagBases s53StockWords s53Blob287477 s53Blob287573 48) 4 s53Data
def s53States := dagTrace s53Mask s53StockWords 4 s53Data
def s53MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s53Moves := dagMoves s53MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Autos : DagMovesOK s53Mask s53Goal 64 s53Moves := dagMovesOfCheck (by decide +kernel)
def s53Check := dagCheckNode s53Mask s53Goal s53Chart (dagKnownCloses s53Goal s53Cuts) 1 s53States s53Moves s53Links s53Sample s53Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Roots : dagCheckRoots s53Mask s53Goal s53Chart (dagKnownCloses s53Goal s53Cuts) s53Witnesses (dagRef 1 s53States s53Moves s53Links 0) s53StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Block0 : treeBlock 0 1 s53Check = true := by decide +kernel
theorem s53Blocks : treeBlock 0 1 s53Check = true := s53Block0
theorem s53Known : Known s53Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Stock : Lower s53Mask s53StockWords s53Goal 5 := by
  apply lowerDag _ _ _ _ s53Autos _ _ _ s53Known _ s53Roots s53Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s53Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def pm14 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12, st15, st14]
def s54Mask : Nat := 0xaaaa00000000aaaa
abbrev s54Goal : Nat := sGoal &&& s54Mask
abbrev s54StockWords : List Nat := [0x8888000000008888, 0xa0a000000000a0a0, 0xaa0000000000aa00, 0xaaaa000000000000]
def s54Fact : Nat × List Nat × Nat × Nat := (s54Mask, s54StockWords, 5, s54Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Stock : Lower s54Mask s54StockWords s54Goal 5 := dagShiftLower (width := 64) pm14 s53Stock (by decide +kernel)
def s55Blob294285 : Nat := (cbits [0x8240a070181c0806, 0x8180d02834060b00, 0x815088540a150603, 0xb0886426170a0582, 0x2894381e0e074261, 0x9c48261209442250, 0x582d118ac4229118, 0x33118cc2633160b8, 0x1a0d86835188d462, 0xf0583c0e0f06239, 0x818060281806061a, 0x8070081c48060a01, 0x90182446070981c0, 0x8242209060240a0, 0x34460b0982c020b1, 0x580d0e034080d008, 0xf16038380e02038, 0x854180f0283c06, 0x8543815098540815, 0x8261602058681518, 0xa170185c68160e05, 0x90086428170885c0, 0x186c62190e064261, 0x74181d02874221b0, 0x281e06078281d088, 0x2500894381f0987c, 0x1889458251189408])
def s55Blob294856 : Nat := (cbits [0xf1fffe017deef77e, 0x9eb15897fe7ffe1f, 0x7861fe07e1c1ff0, 0xffe01ffee33f9fe7, 0x3c1e0f8fff81fff, 0x7ffe0007fffe00f, 0x8000000ffc01ff00, 0xfffe000007ffffff, 0xf80000000000000f])
def s55Blob295069 : Nat := (cbits [0xb03f7a313ce6733e, 0xca05012aa2f6e4a, 0x2202424210183810, 0x6fc0c5eec31b8de5, 0x30180c055d895b5, 0x449080844d808046, 0x489088bf401fe00, 0xfbfc00008765d9de, 0xe00101180912110d])
def s55Mask : Nat := 0xfafafafafafafafa
abbrev s55Goal : Nat := sGoal &&& s55Mask
abbrev s55StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xc8c8c8c8c8c8c8c8, 0xf0f0f0f0f0f0f0f0, 0xfa00fa00fa00fa00, 0xfafa0000fafa0000, 0xfafafafa00000000]
def s55Fact : Nat × List Nat × Nat × Nat := (s55Mask, s55StockWords, 10, s55Goal)
def s55Cuts : List (Nat × List Nat × Nat × Nat) := [s35Fact, s36Fact, s0Fact, s18Fact, s54Fact]
def s55Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 9, 21, 37, 51, 60, 6, 9, 21, 37, 51, 60, 5, 19, 28, 35, 44, 49, 52, 5, 19, 28, 35, 44], rfl⟩
def s55Witnesses := unpackWitnesses s55StockWords [6668, 265220, 527875, 791041, 1059333, 1329669]
def s55Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x130832d00e0001, 0x542150054014085, 0x8006001610580160, 0x18806011]) else (cbits [0x201c807011918621, 0xc7701d047401c847, 0x7009c027009c0258, 0x28809c32])) else (if j < 3 then (cbits [0x432900a212880a20, 0xb002a8caa02a80a, 0xd30b212c80b012c0, 0x330ccc02]) else (cbits [0x403500d213480d20, 0xee03534d403500d, 0xc00f003b84ee03b8, 0x3c00f003]))) else (if j < 6 then (if j < 5 then (cbits [0xc23cb4f203c04f00, 0x1180441110044010, 0x7251a14681181460, 0x4b892e04]) else (cbits [0x604d813414d01321, 0x142d4f0d3a14d893, 0x7855c157015c0570, 0x58016005])) else (if j < 7 then (cbits [0x7759816415809600, 0x1940650194065016, 0x381a556901948650, 0x7381ce07]) else (if j < 8 then (cbits [0x8073f5ce07381ce0, 0x20b082820a082060, 0xad22a08a822a08a8, 0x95065218]) else 0x2561)))) 14 (i % 16)
def s55Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 9 then (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x800480100400003f, 0xdc2e01a05c0320, 0x144d807e1b00cc2c, 0x62b8cdc4c1958843, 0x1031540262055c68, 0xcd8c7f1b18ce]) else (cbits [0xba50e5749bc8492c, 0x61f8d6c3918d871a, 0x4558de883e310c72, 0xe020c50020092d6f, 0x731020c34301866, 0x424c7e0498cc])) else (if j < 3 then (cbits [0x6b0fc0c61c814c38, 0x7a2a14f4403d8860, 0x3840de8801b0e10c, 0x80430e1057a200ac, 0x531000631e421e8, 0x2de880424b0]) else (cbits [0x8b0e00e61e01cf4c, 0x621828c3f04d8720, 0x4444de8a88bd1016, 0xab0f0157a6024f, 0x1c00f83600906001, 0x8406e0e80cc]))) else (if j < 6 then (if j < 5 then (cbits [0x1988121021a3a03f, 0x61c24a643094c6e1, 0x430a587e1430e426, 0x943d15267a2056c, 0x1a7a2034c38064c4, 0x7c0680f00a1]) else (cbits [0xc8c50227a404004c, 0x18a248f440918700, 0x4c09de881224b01a, 0xc1680202a61e054f, 0x2e0250620420b807, 0xcc67c988139])) else (if j < 7 then (cbits [0x9a52a3349f26634a, 0x92806af4b0d1e899, 0x4c8bc06817807134, 0xc1b8020327a40600, 0x3902505c0260e003, 0xcc64c1d0138]) else (if j < 8 then (cbits [0x4a4b03d320878620, 0x7a507ef440f927b0, 0x4c0ed87820c94040, 0x6118c640418a0760, 0x4349627833f0f066, 0x51528622a4dc]) else (cbits [0x4b0fc4861c88cc38, 0x7a2a8cf4412d8862, 0x20511e882230e148, 0x82230e02431280a6, 0x4a61e094f4c11de8, 0x13987c26b0e0]))))) else (if j < 14 then (if j < 11 then (if j < 10 then (cbits [0x931394e6250a4c42, 0x7a78a8f4b14de88a, 0x4e13d894a9c94056, 0x82830f0507a60a2f, 0x5061e0ab25813d87, 0x54589028b0f0]) else (cbits [0x28064060040aaf48, 0x4960b003d0f40621, 0x381492822ca4d645, 0x42f3d105b6250b4c, 0x629280c0f4e17de9, 0x174c782e3d30])) else (if j < 12 then (cbits [0xeb0f05c61e0c2648, 0xf8ca00f1900122, 0x3f99806f32809c66, 0xc050c50680218ce0, 0x2619304c32504463, 0x50467e1a0c9e]) else (if j < 13 then (cbits [0x1190c5331b88c620, 0x49fc22936829258b, 0x44d898872330e341, 0x40598806a7a28d2f, 0x2731904e631048c5, 0x82d87023a4b2]) else (cbits [0x6003a477a2424c42, 0x1b4d80261b403c3, 0x141bc09c37012a6d, 0xc140c941318f0183, 0x4831007e33d8a064, 0x8312582d1904])))) else (if j < 16 then (if j < 15 then (cbits [0x430e23f49ec26936, 0x7a70e0f4a9698832, 0x12034010b5494071, 0x71480682900c8280, 0x4001e8720310d403, 0x124628a00124]) else (cbits [0xd8d047319a8a832b, 0x31541a62056c69a2, 0x49900c7b1c98c614, 0x339a4d6494966806, 0x7461c6b694d96d28, 0x1c1e883b30e4])) else (if j < 17 then (cbits [0xdbd387b7a68eef4c, 0x40eaf4c5c24a0b, 0x1a0a80320a80480e, 0x6250c507801ec540, 0xe3100b834115465, 0x9e0c7b0a98aa]) else (if j < 18 then (cbits [0xab0e25c4a0c9492c, 0x40f4f451e5e883, 0x1a0ac0320b00480f, 0x6258c507d024c560, 0xf3100c034d15865, 0x9f4c930b18aa]) else (cbits [0x8b0e2604a6c9692c, 0x61f0f6c3d1dd8783, 0x511fa4a0b8bd117b, 0x3cbd20787a40ff2, 0x1e9e9])))))) 23 (i % 16)
def s55Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x8048080100203f00, 0x98700a3140261c01, 0x4c3808310010cdc0, 0x27a205b0e008c660, 0x13d303987e04c390, 0x6218]) else (cbits [0xbd10498702201201, 0x5e982ac3f1161c88, 0x20081800c80b10c4, 0x80048c30e064c403, 0xf00a0780663001f1, 0x1a0])) else (if j < 3 then (cbits [0x3d208806e3004c1e, 0xc6e30c38243100c, 0xc39187a213b0e06, 0x16218c3d30a987e3, 0x780f8b40105a01b0, 0xe1]) else (cbits [0xbd20c80845a04c2f, 0x5e965af442d19f16, 0xe01e370041b80cc0, 0x761e1d8138dc0946, 0xba4f4dcc826e6203, 0x7a21]))) else (if j < 6 then (if j < 5 then (cbits [0x8c50064a06ef4a37, 0xd26e86c384449621, 0x6c39437a223b0e10, 0x1621a1bd312987e8, 0x7b0f9358709a32b0, 0x6252]) else (cbits [0xb10935e9c9ef4c50, 0x64b0aaf4b4d7a226, 0x3d5819b80bd3d3, 0xc6252c30e16126ab, 0xc3d1160c78baf4c5, 0x7a52])) else (if j < 7 then (cbits [0xc94160c90c2f4e58, 0x1ec80096461c00, 0x80436401fb2007d9, 0xc61c80bd1591e88c, 0x60129b003cd800e6, 0x273]) else (cbits [0xb0fc05e9cd8f4a6c, 0xde98eac387319ab9, 0x3d787a639b0e5c, 0x17a6b9bd15e1e88f, 0xec941f4092fac430, 0x928b])))) 21 (i % 16)
def s55Links := pageLinks s55Index s55Codes 5 13 8 6
def s55Data (i : Nat) : Nat × Nat :=
  let e := s55Forest i
  (e &&& 255, e >>> 8)
def s55Sample : Nat × Nat := (s55Blob294285, 96)
def s55Tags := dagTraceTags s55Mask 96 (dagTagBases s55StockWords s55Blob294856 s55Blob295069 96) 9 s55Data
def s55States := dagTrace s55Mask s55StockWords 9 s55Data
def s55MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm5, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val))), (pm9, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 5, 4] 0 i.val)))]
def s55Moves := dagMoves s55MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Autos : DagMovesOK s55Mask s55Goal 64 s55Moves := dagMovesOfCheck (by decide +kernel)
def s55Check := dagCheckNode s55Mask s55Goal s55Chart (dagKnownCloses s55Goal s55Cuts) 128 s55States s55Moves s55Links s55Sample s55Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Roots : dagCheckRoots s55Mask s55Goal s55Chart (dagKnownCloses s55Goal s55Cuts) s55Witnesses (dagRef 128 s55States s55Moves s55Links 0) s55StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Block0 : treeBlock 0 24 s55Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Block24 : treeBlock 24 24 s55Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Block48 : treeBlock 48 24 s55Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Block72 : treeBlock 72 24 s55Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Block96 : treeBlock 96 24 s55Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Block120 : treeBlock 120 8 s55Check = true := by decide +kernel
theorem s55Group24_48 : treeBlock 24 48 s55Check = true := treeBlock_merge (start := 24) (left := 24) (right := 24) (check := s55Check) s55Block24 s55Block48
theorem s55Group0_72 : treeBlock 0 72 s55Check = true := treeBlock_merge (start := 0) (left := 24) (right := 48) (check := s55Check) s55Block0 s55Group24_48
theorem s55Group96_32 : treeBlock 96 32 s55Check = true := treeBlock_merge (start := 96) (left := 24) (right := 8) (check := s55Check) s55Block96 s55Block120
theorem s55Group72_56 : treeBlock 72 56 s55Check = true := treeBlock_merge (start := 72) (left := 24) (right := 32) (check := s55Check) s55Block72 s55Group96_32
theorem s55Group0_128 : treeBlock 0 128 s55Check = true := treeBlock_merge (start := 0) (left := 72) (right := 56) (check := s55Check) s55Group0_72 s55Group72_56
theorem s55Blocks : treeBlock 0 128 s55Check = true := s55Group0_128
theorem s55Known : Known s55Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s54Stock) s18Stock) s0Stock) s36Stock) s35Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Stock : Lower s55Mask s55StockWords s55Goal 10 := by
  apply lowerDag _ _ _ _ s55Autos _ _ _ s55Known _ s55Roots s55Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s55Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s56Blob304296 : Nat := (cbits [0x2402090281c0607, 0x40a0d0502c060b04, 0xa1506038140e0603, 0x9088642617088540, 0x986c301a05068301, 0x940a250e078381d0, 0x5029108a44627108, 0x2d118ac502a050a8, 0x118cc2633160b858, 0xe46239188d46233, 0x583c0e0f0703a1c, 0x6070981c02071c0f, 0x9050240a09018244, 0x824300908824180, 0x2c100b0082c50091, 0x100d00834460b098, 0xe04038580d0e034, 0x283c060f1603838, 0x85402150603c140f, 0xc061718854381509, 0x190086422170285, 0x9188643819098641, 0xe068261a04068701, 0x6c141b0186c701a0, 0x181d02874301b088, 0x1e05078301d08874, 0xe07c261f0c07818])
def s56Blob304864 : Nat := (cbits [0xc7ffff0fd9f67cff, 0xee4b9333c7f87fff, 0xf87f81c3f8780711, 0xff8007e2307c1fc3, 0x3f8fe3fcff8001ff, 0xfffffe03fffff8fc, 0xffc00ffc00, 0xfff00000fffffffc, 0xff])
def s56Blob305060 : Nat := (cbits [0xc0ea9f07c8f23c57, 0xca42913142a92bec, 0x4819084940602e00, 0xb6005060301c06c2, 0x370dc3a891821092, 0xbd56d4133f1560f8, 0x122182bf400f7800, 0xbde00000e6677938, 0x46020244604df])
def s56Mask : Nat := 0xffaaffaaffaaffaa
abbrev s56Goal : Nat := sGoal &&& s56Mask
abbrev s56StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcc88cc88cc88cc88, 0xf0a0f0a0f0a0f0a0, 0xff00ff00ff00ff00, 0xffaa0000ffaa0000, 0xffaaffaa00000000]
def s56Fact : Nat × List Nat × Nat × Nat := (s56Mask, s56StockWords, 10, s56Goal)
def s56Cuts : List (Nat × List Nat × Nat × Nat) := [s35Fact, s43Fact, s0Fact, s9Fact]
def s56Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 9, 14, 21, 26, 37, 42, 51, 60, 7, 9, 14, 5, 10, 19, 28, 35, 44, 49, 56, 5, 10, 19, 28], rfl⟩
def s56Witnesses := unpackWitnesses s56StockWords [4616, 265733, 527875, 791041, 1059333, 1329669]
def s56Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x168c33400e0001, 0x8640180860018006, 0xa0c6801a00680190, 0x1b806e01]) else (cbits [0x401d006e31b806e0, 0xc7941d847601d047, 0x98ca602980a60280, 0x2b00ac02])) else (if j < 3 then (cbits [0x32c00b002c00ac2, 0xb802d84b602d80b, 0xf84be02f80b832e0, 0x3004c002]) else (if j < 4 then (cbits [0x3c00f003c00c37, 0xfc03f00f063c00f, 0x2010803f18fc03f0, 0x42810814]) else (cbits [0x204c81320434d0a1, 0x13624d813224c813, 0xed53a04e813a04e8, 0x5a816434])))) else (if j < 7 then (if j < 6 then (cbits [0x5b856e05a896a0, 0x180360018005c217, 0x2818626181860618, 0x6c098b36]) else (cbits [0x417101c406d21b40, 0x9c807185c607181c, 0xb81ee07345cc0720, 0x7c01ee17])) else (if j < 8 then (cbits [0x207c81f207c81f01, 0x5f507d01f407c85f, 0x6021808586160850, 0x86061808]) else (if j < 9 then (cbits [0x8092021b786821a0, 0x2486920248092024, 0xe827a09e82553950, 0x9e827a09]) else (cbits [0xc0a6869a09ec27a0, 0x2ad0ab02ac0a7229, 0x2cc1b30]))))) 14 (i % 16)
def s56Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 11 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0xb80940100400003f, 0x18a85e31485c04c0, 0x3317463e260c6c40, 0x6b50cfc7719b8d43, 0x40310c5e6205dc68, 0x9dcc6f3518ce]) else (cbits [0xa4b377321ed463f, 0x61f912c392058710, 0x45605e884bb10c90, 0x6028c540218a312f, 0xa19981031f01863, 0x42867e058cdc])) else (if j < 3 then (cbits [0x718840c310216343, 0x31f82063703cc660, 0x3904587088190d0f, 0x80b310c1461f826c, 0x3310226f45445e8, 0x411e880230e0]) else (if j < 4 then (cbits [0x4a4f1071a600e340, 0x61c0066204252900, 0x2c010c4086bd100d, 0x80abd30127a201a9, 0x1b31083062005587, 0x7cc560e189c]) else (cbits [0x98fc2231b842633, 0x49684692c488c869, 0x3f0a126e1324cc25, 0x214b0e1284a1a4c9, 0x2e621858c3f0ad87, 0x4ade8a94bd10])))) else (if j < 8 then (if j < 6 then (cbits [0xd3d101a61c03292c, 0x32603c6400740388, 0x2c4818901030f11e, 0x923d102461c0329, 0x2461c03492c09c05, 0xb5e98153d10]) else (if j < 7 then (cbits [0x8806c3000485ac3c, 0x1b8660330c803e1, 0x144d00869980fc34, 0x1118c98181928043, 0x3831986e6210d4c4, 0x4e0c7e1c98dc]) else (cbits [0xd30e20c496272643, 0x62187ac3f0f18721, 0x204f1e8a9d3d103f, 0x90c9898193128066, 0x367a206cc3880d25, 0x68c62021881]))) else (if j < 9 then (cbits [0x6b0e036496448632, 0x61e07cf4c0ede890, 0x3e1080542080983e, 0xca18128440210860, 0x1b19880a31451009, 0x114c4d128cc8]) else (if j < 10 then (cbits [0x519084931f08e62a, 0x49629464e524c942, 0x5012de890730e237, 0x8a31930463202972, 0x600429094812127, 0x70062268048]) else (cbits [0x68cd45018a438032, 0x1a08a834014867d2, 0x4c5486942c8d0857, 0xac8d39571a6aa83, 0x5a3150b4629114c4, 0x81987122a4b2]))))) else (if j < 17 then (if j < 14 then (if j < 12 then (cbits [0x700d15b9280b6f44, 0x1e29e04c13c0802, 0x814c698a8812051, 0x90f00981e01280e0, 0x749648c62011862, 0x159e882ab0e2]) else (if j < 13 then (cbits [0xc0d324f19a09e010, 0x42ac64c1700382, 0x1487c0640f80c408, 0x12d0c685a18c88e3, 0x6049e0bc92c91cc4, 0x19527c31a4f4]) else (cbits [0x1a525604a40cc942, 0x61c2cc94e595294b, 0x405a24a0343d1208, 0x20480215f0260be0, 0x4818a44003208006, 0x185259241880]))) else (if j < 15 then (cbits [0x23120627a2412c38, 0x6240d203019de903, 0x311ac02405002162, 0xc360c52260190420, 0x6f1a50da32a14864, 0x124c40388d38]) else (if j < 16 then (cbits [0xc24b0733210e4641, 0x7a241ec381d127b1, 0x281b92783b494075, 0xa0580206e1940e03, 0x4a18a45002608804, 0x1cc664390cc4]) else (cbits [0xd18f47831ac72620, 0x61c42092c198c823, 0x4e1f5e943e3d107b, 0x3cb0f0809280fcf, 0x820048fe6481e4c8, 0x21003e41806c])))) else (if j < 20 then (if j < 18 then (cbits [0x280fe84015d06027, 0x1988223142180864, 0x210e8c41148cc829, 0xe3418ac5b3138966, 0x3a4963006435d8c7, 0xdd927f25a4b6]) else (if j < 19 then (cbits [0x3bd121161c700943, 0x31e824620221e8a4, 0x380ed2591518f82a, 0xc45006a127a2476c, 0x8b01551402622c03, 0x23409c46012a]) else (cbits [0x58cc82b198826314, 0x3208ea63d0f0c411, 0x419d527b1e24b07b, 0xc473d2a1361c4f69, 0x1400431125023de9, 0x8b004c160094]))) else (if j < 21 then (cbits [0x88cd46f19887a314, 0x31acde6318f4c404, 0x442498710a24b291, 0xc4b3d34947a611cf, 0x937a631d250659e9, 0xb404a0a8020]) else (if j < 22 then (cbits [0xf18803e18a45a026, 0x7a2126c388552591, 0x260b804a0b002095, 0xa4c0d243f18a45c0, 0x98324c7e6201f869, 0x8592593f1936]) else (cbits [0xb30f49461e11ec38, 0x92831ef4465987c4, 0x4abd2099])))))) 23 (i % 16)
def s56Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x8c50080100203f00, 0x862a04c380331001, 0x231f021a0038c6c0, 0x219b810ccc092781, 0x11884098701a6200, 0x3198]) else (cbits [0x3d10498700463702, 0x9e982ac3f0261c81, 0x26201801280b10c0, 0x83108c30e0652583, 0xc1900740383a6271, 0x3158])) else (if j < 3 then (cbits [0x18dc60c6630c3c20, 0x125a30c38244960c, 0x9371801413a4cc6, 0x861c8c3d10a98703, 0xb10c61e985ac3f1, 0x18a0]) else (if j < 4 then (cbits [0x7cc00366000930, 0x8c40600373001998, 0x633303109830e0d, 0x7a21db0e0c0c6e6, 0x83d30f987e60c393, 0x6219]) else (cbits [0x80a90404c8231501, 0x8c4c820424101f20, 0x293c483152099011, 0x17a220990904c7c8, 0x700d1380249a31b0, 0x202])))) else (if j < 7 then (if j < 6 then (cbits [0x8cf934078a23144d, 0x5870aa3404d1a629, 0xa34c581a0a6bd115, 0xc7a22698a5346849, 0xfa4b17863e0201c5, 0x202]) else (cbits [0x3d1185258c293c5e, 0x927cbcc486449eaf, 0x2f445e7a433a5097, 0xb009358ccc04060d, 0x5a4f1b8654d63146, 0x1a53])) else (if j < 8 then (cbits [0x9905ac69cd632870, 0xde88d693d6b32135, 0x26357819b80c941a, 0x861c3c18f5e1878f, 0xfbd39e1e94f0f447, 0x3243]) else (if j < 9 then (cbits [0x26098700325078, 0x807f0401f8200dc1, 0x2f45827a241010e0, 0xa00f45006a298720, 0x53d2a2809d1404a8, 0x7a74]) else (cbits [0xb0e24466b22c3f01, 0x5e892af4c917a649, 0x3499862180bd364, 0x24a13]))))) 21 (i % 16)
def s56Links := pageLinks s56Index s56Codes 5 13 8 6
def s56Data (i : Nat) : Nat × Nat :=
  let e := s56Forest i
  (e &&& 255, e >>> 8)
def s56Sample : Nat × Nat := (s56Blob304296, 96)
def s56Tags := dagTraceTags s56Mask 96 (dagTagBases s56StockWords s56Blob304864 s56Blob305060 96) 9 s56Data
def s56States := dagTrace s56Mask s56StockWords 9 s56Data
def s56MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm3, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 4, 5] 0 i.val))), (pm8, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 5, 4] 0 i.val)))]
def s56Moves := dagMoves s56MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Autos : DagMovesOK s56Mask s56Goal 64 s56Moves := dagMovesOfCheck (by decide +kernel)
def s56Check := dagCheckNode s56Mask s56Goal s56Chart (dagKnownCloses s56Goal s56Cuts) 154 s56States s56Moves s56Links s56Sample s56Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Roots : dagCheckRoots s56Mask s56Goal s56Chart (dagKnownCloses s56Goal s56Cuts) s56Witnesses (dagRef 154 s56States s56Moves s56Links 0) s56StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Block0 : treeBlock 0 24 s56Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Block24 : treeBlock 24 24 s56Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Block48 : treeBlock 48 24 s56Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Block72 : treeBlock 72 24 s56Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Block96 : treeBlock 96 24 s56Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Block120 : treeBlock 120 24 s56Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Block144 : treeBlock 144 10 s56Check = true := by decide +kernel
theorem s56Group24_48 : treeBlock 24 48 s56Check = true := treeBlock_merge (start := 24) (left := 24) (right := 24) (check := s56Check) s56Block24 s56Block48
theorem s56Group0_72 : treeBlock 0 72 s56Check = true := treeBlock_merge (start := 0) (left := 24) (right := 48) (check := s56Check) s56Block0 s56Group24_48
theorem s56Group72_48 : treeBlock 72 48 s56Check = true := treeBlock_merge (start := 72) (left := 24) (right := 24) (check := s56Check) s56Block72 s56Block96
theorem s56Group120_34 : treeBlock 120 34 s56Check = true := treeBlock_merge (start := 120) (left := 24) (right := 10) (check := s56Check) s56Block120 s56Block144
theorem s56Group72_82 : treeBlock 72 82 s56Check = true := treeBlock_merge (start := 72) (left := 48) (right := 34) (check := s56Check) s56Group72_48 s56Group120_34
theorem s56Group0_154 : treeBlock 0 154 s56Check = true := treeBlock_merge (start := 0) (left := 72) (right := 82) (check := s56Check) s56Group0_72 s56Group72_82
theorem s56Blocks : treeBlock 0 154 s56Check = true := s56Group0_154
theorem s56Known : Known s56Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s9Stock) s0Stock) s43Stock) s35Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Stock : Lower s56Mask s56StockWords s56Goal 10 := by
  apply lowerDag _ _ _ _ s56Autos _ _ _ s56Known _ s56Roots s56Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s56Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s57Mask : Nat := 0xfcfcfcfcfcfcfcfc
abbrev s57Goal : Nat := sGoal &&& s57Mask
abbrev s57StockWords : List Nat := [0xa8a8a8a8a8a8a8a8, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xfc00fc00fc00fc00, 0xfcfc0000fcfc0000, 0xfcfcfcfc00000000]
def s57Fact : Nat × List Nat × Nat × Nat := (s57Mask, s57StockWords, 10, s57Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s57Stock : Lower s57Mask s57StockWords s57Goal 10 := dagShiftLower (width := 64) pm4 s56Stock (by decide +kernel)
def s58Mask : Nat := 0xff33ff33ff33ff33
abbrev s58Goal : Nat := sGoal &&& s58Mask
abbrev s58StockWords : List Nat := [0xaa22aa22aa22aa22, 0xcc00cc00cc00cc00, 0xf030f030f030f030, 0xff00ff00ff00ff00, 0xff330000ff330000, 0xff33ff3300000000]
def s58Fact : Nat × List Nat × Nat × Nat := (s58Mask, s58StockWords, 10, s58Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Stock : Lower s58Mask s58StockWords s58Goal 10 := dagShiftLower (width := 64) pm4 s38Stock (by decide +kernel)
def s59Mask : Nat := 0xffccffccffccffcc
abbrev s59Goal : Nat := sGoal &&& s59Mask
abbrev s59StockWords : List Nat := [0xaa88aa88aa88aa88, 0xcccccccccccccccc, 0xf0c0f0c0f0c0f0c0, 0xff00ff00ff00ff00, 0xffcc0000ffcc0000, 0xffccffcc00000000]
def s59Fact : Nat × List Nat × Nat × Nat := (s59Mask, s59StockWords, 10, s59Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59Stock : Lower s59Mask s59StockWords s59Goal 10 := dagShiftLower (width := 64) pm4 s55Stock (by decide +kernel)
def s60Mask : Nat := 0xfff0fff0fff0fff0
abbrev s60Goal : Nat := sGoal &&& s60Mask
abbrev s60StockWords : List Nat := [0xaaa0aaa0aaa0aaa0, 0xccc0ccc0ccc0ccc0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xfff00000fff00000, 0xfff0fff000000000]
def s60Fact : Nat × List Nat × Nat × Nat := (s60Mask, s60StockWords, 10, s60Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Stock : Lower s60Mask s60StockWords s60Goal 10 := dagShiftLower (width := 64) pm5 s51Stock (by decide +kernel)
def s61Mask : Nat := 0xf0f000000000000
abbrev s61Goal : Nat := sGoal &&& s61Mask
abbrev s61StockWords : List Nat := [0xa0a000000000000, 0xc0c000000000000, 0xf00000000000000]
def s61Fact : Nat × List Nat × Nat × Nat := (s61Mask, s61StockWords, 4, s61Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61Stock : Lower s61Mask s61StockWords s61Goal 4 := dagShiftLower (width := 64) pm11 s1Stock (by decide +kernel)
def pm15 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st12]
def s62Mask : Nat := 0x3333000000000000
abbrev s62Goal : Nat := sGoal &&& s62Mask
abbrev s62StockWords : List Nat := [0x2222000000000000, 0x3030000000000000, 0x3300000000000000]
def s62Fact : Nat × List Nat × Nat × Nat := (s62Mask, s62StockWords, 4, s62Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62Stock : Lower s62Mask s62StockWords s62Goal 4 := dagShiftLower (width := 64) pm15 s1Stock (by decide +kernel)
def pm16 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st01, st12]
def s63Mask : Nat := 0x5555000000000000
abbrev s63Goal : Nat := sGoal &&& s63Mask
abbrev s63StockWords : List Nat := [0x4444000000000000, 0x5050000000000000, 0x5500000000000000]
def s63Fact : Nat × List Nat × Nat × Nat := (s63Mask, s63StockWords, 4, s63Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Stock : Lower s63Mask s63StockWords s63Goal 4 := dagShiftLower (width := 64) pm16 s1Stock (by decide +kernel)
def pm17 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12]
def pm18 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12, st13]
def pm19 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01]
def pm20 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st02]
def pm21 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st02, st03]
def pm22 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02, st01]
def pm23 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02, st01, st13]
def s64Blob314455 : Nat := (cbits [0xd46235190cc6233, 0x462391a0d864361a, 0x83c1c0e8643a1c0e, 0x6180d460331c0f06, 0xa0dc6437188dc603, 0xec623b180e860391, 0x623d180f0703b190, 0x3e190f8703d1a0f4, 0x1c0cc68331c0f868, 0xd862361c0d46435, 0x86839190e460371c, 0x23c180ec683a188e, 0xf180f8603d190f06, 0xc0fc683f190fc623, 0xf8643d1a0ec70371, 0x603f188])
def s64Blob314800 : Nat := (cbits [0x99dfd273c777b0cf, 0xfb0f37f1ce7c3de9, 0xff81f81dff07cfe0, 0xf7ffc07])
def s64Blob314907 : Nat := (cbits [0x8920448401108045, 0x810a084410841080, 0x8801500240501480, 0xc00154])
def s64Mask : Nat := 0xffff000000000000
abbrev s64Goal : Nat := sGoal &&& s64Mask
abbrev s64StockWords : List Nat := [0xaaaa000000000000, 0xcccc000000000000, 0xf0f0000000000000, 0xff00000000000000]
def s64Fact : Nat × List Nat × Nat × Nat := (s64Mask, s64StockWords, 7, s64Goal)
def s64Cuts : List (Nat × List Nat × Nat × Nat) := [s1Fact, s61Fact, s62Fact, s63Fact]
def s64Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[51, 53, 54, 57, 58, 60, 51, 53, 54, 57, 58, 60, 49, 50, 52, 56, 49, 50, 52, 56, 49, 50, 52, 56], rfl⟩
def s64Witnesses := unpackWitnesses s64StockWords [26162, 288305, 551473, 815665]
def s64Index (i : Nat) : Nat := unpack 0x4c242e4702cc3401 9 i
def s64Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xf06013020080000f, 0x1f423143602b2601, 0x62b626209632b863, 0x4620043147292ca6, 0x180360802a3492c2]) else 0xa01c583364832a) 20 (i % 16)
def s64Forest (i : Nat) : Nat := unpack (cbits [0x9918a200410078, 0xe50154]) 16 i
def s64Links := pageLinks s64Index s64Codes 4 13 3 5
def s64Data (i : Nat) : Nat × Nat :=
  let e := s64Forest i
  (e &&& 7, e >>> 3)
def s64Sample : Nat × Nat := (s64Blob314455, 55)
def s64Tags := dagTraceTags s64Mask 55 (dagTagBases s64StockWords s64Blob314800 s64Blob314907 55) 6 s64Data
def s64States := dagTrace s64Mask s64StockWords 6 s64Data
def s64MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm11, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val))), (pm17, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val))), (pm18, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val))), (pm19, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 2, 3, 4, 5] 0 i.val))), (pm4, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val))), (pm20, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val))), (pm21, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 0, 1, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 2, 3, 0, 4, 5] 0 i.val))), (pm22, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 2, 0, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 0, 1, 3, 4, 5] 0 i.val))), (pm23, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 3, 0, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 0, 3, 1, 4, 5] 0 i.val))), (pm5, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val)))]
def s64Moves := dagMoves s64MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Autos : DagMovesOK s64Mask s64Goal 64 s64Moves := dagMovesOfCheck (by decide +kernel)
def s64Check := dagCheckNode s64Mask s64Goal s64Chart (dagKnownCloses s64Goal s64Cuts) 6 s64States s64Moves s64Links s64Sample s64Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Roots : dagCheckRoots s64Mask s64Goal s64Chart (dagKnownCloses s64Goal s64Cuts) s64Witnesses (dagRef 6 s64States s64Moves s64Links 0) s64StockWords 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Block0 : treeBlock 0 6 s64Check = true := by decide +kernel
theorem s64Blocks : treeBlock 0 6 s64Check = true := s64Block0
theorem s64Known : Known s64Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s63Stock) s62Stock) s61Stock) s1Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Stock : Lower s64Mask s64StockWords s64Goal 7 := by
  apply lowerDag _ _ _ _ s64Autos _ _ _ s64Known _ s64Roots s64Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s64Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s65Mask : Nat := 0xffff00000000ffff
abbrev s65Goal : Nat := sGoal &&& s65Mask
abbrev s65StockWords : List Nat := [0xaaaa00000000aaaa, 0xcccc00000000cccc, 0xf0f000000000f0f0, 0xff0000000000ff00, 0xffff000000000000]
def s65Fact : Nat × List Nat × Nat × Nat := (s65Mask, s65StockWords, 8, s65Goal)
def s65Witnesses := unpackWitnesses s65StockWords [4616, 265220, 527362, 791041, 1074691]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Stock : Lower s65Mask s65StockWords s65Goal 8 := by
  apply essentialLift (witnesses := s65Witnesses) (cut := s64Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s64StockWords) (by decide +kernel)
  · exact s64Stock
  · decide +kernel
def s66Mask : Nat := 0xffff0000ffff0000
abbrev s66Goal : Nat := sGoal &&& s66Mask
abbrev s66StockWords : List Nat := [0xaaaa0000aaaa0000, 0xcccc0000cccc0000, 0xf0f00000f0f00000, 0xff000000ff000000, 0xffff000000000000]
def s66Fact : Nat × List Nat × Nat × Nat := (s66Mask, s66StockWords, 8, s66Goal)
def s66Witnesses := unpackWitnesses s66StockWords [10772, 273428, 535057, 799249, 1074707]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Stock : Lower s66Mask s66StockWords s66Goal 8 := by
  apply essentialLift (witnesses := s66Witnesses) (cut := s64Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s64StockWords) (by decide +kernel)
  · exact s64Stock
  · decide +kernel
def s67Mask : Nat := 0xffffffff00000000
abbrev s67Goal : Nat := sGoal &&& s67Mask
abbrev s67StockWords : List Nat := [0xaaaaaaaa00000000, 0xcccccccc00000000, 0xf0f0f0f000000000, 0xff00ff0000000000, 0xffff000000000000]
def s67Fact : Nat × List Nat × Nat × Nat := (s67Mask, s67StockWords, 8, s67Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Stock : Lower s67Mask s67StockWords s67Goal 8 := dagShiftLower (width := 64) pm2 s66Stock (by decide +kernel)
def s68Mask : Nat := 0xffff0000ffff
abbrev s68Goal : Nat := sGoal &&& s68Mask
abbrev s68StockWords : List Nat := [0xaaaa0000aaaa, 0xcccc0000cccc, 0xf0f00000f0f0, 0xff000000ff00, 0xffff00000000]
def s68Fact : Nat × List Nat × Nat × Nat := (s68Mask, s68StockWords, 7, s68Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Stock : Lower s68Mask s68StockWords s68Goal 7 := dagShiftLower (width := 64) pm2 s6Stock (by decide +kernel)
def s69Mask : Nat := 0xcc330000cc33
abbrev s69Goal : Nat := sGoal &&& s69Mask
abbrev s69StockWords : List Nat := [0x882200008822, 0xcc000000cc00, 0xc0300000c030, 0xcc3300000000]
def s69Fact : Nat × List Nat × Nat × Nat := (s69Mask, s69StockWords, 6, s69Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Stock : Lower s69Mask s69StockWords s69Goal 6 := dagShiftLower (width := 64) pm10 s7Stock (by decide +kernel)
def s70Mask : Nat := 0x9999999900000000
abbrev s70Goal : Nat := sGoal &&& s70Mask
abbrev s70StockWords : List Nat := [0x8888888800000000, 0x9090909000000000, 0x9900990000000000, 0x9999000000000000]
def s70Fact : Nat × List Nat × Nat × Nat := (s70Mask, s70StockWords, 6, s70Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s70Stock : Lower s70Mask s70StockWords s70Goal 6 := dagShiftLower (width := 64) pm2 s40Stock (by decide +kernel)
def s71Blob329344 : Nat := (cbits [0x81c0607020180406, 0xc060b04024020902, 0x40e060340a0d0502, 0x5108940a25060381, 0x189c482611098482, 0xa8142a140a442291, 0x582d118ac502a110, 0x33188cc4633160b8, 0x190d86835188d464, 0xe87039188e46836, 0x683c160f0703a19, 0xa060181800061c0f, 0x6110181806050180, 0x201c04070081c480, 0x2406090002446070, 0x4209060241409028, 0xb0102c020b14024, 0x2034020d1182c10, 0x38040e16034100d, 0xc060f16038100e02, 0x2250603c140f0283, 0x5118944025020940, 0x1098682518894582, 0x9846261009808260, 0x6271a0986426160, 0x271109c42270289c, 0x100a41029008a448])
def s71Blob329914 : Nat := (cbits [0xffff80067d8e73fc, 0x9ef38ccfff01ffc3, 0x1ffe03fc3c07ff19, 0xc007ffe1e303ff0f, 0x3fc0ff01fffffff, 0xe00003fffff800fe, 0xfffc000000, 0xfffff00000000000, 0xfffffc00000000ff])
def s71Blob330123 : Nat := (cbits [0x653486022c86315c, 0x94b284c52710a4c0, 0x952214428552a08, 0x80a2546143015b0a, 0x3580ea012a54aaa, 0x4020433312c018b4, 0xdff8000000, 0xffefe00000c18000, 0x9cf9f022230460ff])
def s71Mask : Nat := 0xffffffff0000ffff
abbrev s71Goal : Nat := sGoal &&& s71Mask
abbrev s71StockWords : List Nat := [0xaaaaaaaa0000aaaa, 0xcccccccc0000cccc, 0xf0f0f0f00000f0f0, 0xff00ff000000ff00, 0xffff000000000000, 0xffffffff00000000]
def s71Fact : Nat × List Nat × Nat × Nat := (s71Mask, s71StockWords, 10, s71Goal)
def s71Cuts : List (Nat × List Nat × Nat × Nat) := [s65Fact, s67Fact, s64Fact, s68Fact, s37Fact, s69Fact, s70Fact, s3Fact, s28Fact, s20Fact, s11Fact]
def s71Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 9, 37, 42, 51, 60, 6, 9, 37, 42, 51, 60, 5, 10, 35, 44, 49, 50, 52, 56, 5, 10, 35, 44], rfl⟩
def s71Witnesses := unpackWitnesses s71StockWords [4616, 265220, 527362, 791041, 1074723, 1329669]
def s71Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x4804802af034001, 0xe04c14c04c048248, 0x5025005005004e14]) else (cbits [0x562560541540540, 0x816806806615a65a, 0x8a072c7206a46a06])) else (if j < 3 then (cbits [0x9608c58c08a18a0, 0x20a0198498096196, 0xba0ba0ba0b81a2ba]) else (cbits [0xcaaca0ca0c62ba6, 0xc1ec0e06e00de1de, 0xe]))) 12 (i % 16)
def s71Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x8a8024040100003f, 0xc9c0363a0131b007, 0x86602b2f01395007, 0xf6f18daa8c550462, 0x350cad9c64ee631, 0x8131]) else (cbits [0x4e98ae6cc4f2a621, 0xc0801faa92dc1496, 0xa0a3140401381806, 0x70a18f840c6c1c62, 0x871880346561832, 0xf31])) else (if j < 3 then (cbits [0x89a4b044c5620627, 0x1192580c62014496, 0x80c6200b4a4048cd, 0xc463100931221925, 0xb0c0ca85863d0c92, 0x1919]) else (cbits [0x6a30e23d2588e620, 0x87005434c4817324, 0x1a0c38904962e00d, 0x65618a0f00a85801, 0xb1018a87cc40bc33, 0x6031]))) else (if j < 6 then (if j < 5 then (cbits [0xc8a4b090c9244648, 0x85291a2c382549b, 0x8466205718a0b802, 0xe2631e6930e24925, 0xc261882a006c5001, 0xcc61]) else (cbits [0xf00486001052648, 0xac66e403294d18a, 0xc5a92c9e31b4c188, 0xccd61c1724f68126, 0x4190078c00385893, 0xf001])) else (if j < 7 then (cbits [0x4424b120c41e402a, 0x64011126203118a, 0xb146206019aa50c5, 0xd3461c6ca4b280c6, 0x41cb124dd8906ac3, 0x367a]) else (cbits [0x4598812c62834008, 0xd987a70c38da496, 0x1b3d2])))) 21 (i % 16)
def s71Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x8400f08010080fc0, 0x20186281009c200d, 0x866848c6c218a846, 0x610c9c24a41631f0, 0x310846200865]) else (cbits [0x4c4848c561189c2, 0x1e580120a4b42496, 0x866cb0ca963242e3, 0x6080a9c00782c486, 0x3103c02a7802])) else (if j < 3 then (cbits [0x4664879291098a9e, 0x3c9926ef1925e310, 0x4c914807a800d826, 0x95a4f2c19bd601f0, 0x138293dad25]) else (cbits [0x8201ec0629880730, 0x48d987ba30e34015, 0x1893a30e3862468f]))) 19 (i % 16)
def s71Links := pageLinks s71Index s71Codes 5 13 6 6
def s71Data (i : Nat) : Nat × Nat :=
  let e := s71Forest i
  (e &&& 63, e >>> 6)
def s71Sample : Nat × Nat := (s71Blob329344, 96)
def s71Tags := dagTraceTags s71Mask 96 (dagTagBases s71StockWords s71Blob329914 s71Blob330123 96) 9 s71Data
def s71States := dagTrace s71Mask s71StockWords 9 s71Data
def s71MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val))), (pm5, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val))), (pm3, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 4, 5] 0 i.val)))]
def s71Moves := dagMoves s71MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Autos : DagMovesOK s71Mask s71Goal 64 s71Moves := dagMovesOfCheck (by decide +kernel)
def s71Check := dagCheckNode s71Mask s71Goal s71Chart (dagKnownCloses s71Goal s71Cuts) 58 s71States s71Moves s71Links s71Sample s71Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Roots : dagCheckRoots s71Mask s71Goal s71Chart (dagKnownCloses s71Goal s71Cuts) s71Witnesses (dagRef 58 s71States s71Moves s71Links 0) s71StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Block0 : treeBlock 0 24 s71Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Block24 : treeBlock 24 24 s71Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Block48 : treeBlock 48 10 s71Check = true := by decide +kernel
theorem s71Group24_34 : treeBlock 24 34 s71Check = true := treeBlock_merge (start := 24) (left := 24) (right := 10) (check := s71Check) s71Block24 s71Block48
theorem s71Group0_58 : treeBlock 0 58 s71Check = true := treeBlock_merge (start := 0) (left := 24) (right := 34) (check := s71Check) s71Block0 s71Group24_34
theorem s71Blocks : treeBlock 0 58 s71Check = true := s71Group0_58
theorem s71Known : Known s71Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s11Stock) s20Stock) s28Stock) s3Stock) s70Stock) s69Stock) s37Stock) s68Stock) s64Stock) s67Stock) s65Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Stock : Lower s71Mask s71StockWords s71Goal 10 := by
  apply lowerDag _ _ _ _ s71Autos _ _ _ s71Known _ s71Roots s71Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s71Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s72Mask : Nat := 0xffff0000ffffffff
abbrev s72Goal : Nat := sGoal &&& s72Mask
abbrev s72StockWords : List Nat := [0xaaaa0000aaaaaaaa, 0xcccc0000cccccccc, 0xf0f00000f0f0f0f0, 0xff000000ff00ff00, 0xffff0000ffff0000, 0xffff000000000000]
def s72Fact : Nat × List Nat × Nat × Nat := (s72Mask, s72StockWords, 10, s72Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Stock : Lower s72Mask s72StockWords s72Goal 10 := dagShiftLower (width := 64) pm2 s71Stock (by decide +kernel)
def s73Blob334931 : Nat := (cbits [0x85c2215020180406, 0xc263312098442609, 0x406000186235188c, 0x5098540815120184, 0x209804260885c621, 0xd44433088cc40260, 0x6237098dc4835088, 0x1500054400609818, 0x1885c08170105c48, 0xd44033010cc0026, 0xc2237100d4263502, 0x415088184837110d, 0x71105c0017100540, 0xcc622609898481, 0xdc4435000d448330, 0x6206100dc0837010, 0x3308898401711054, 0x37010d408])
def s73Blob335317 : Nat := (cbits [0xf6fe7dfef9f8f1cc, 0xeef3f9e3f3cfc77d, 0x1bfe7ffe7ff9ffcf, 0xf1ff03fe03fe03e])
def s73Blob335432 : Nat := (cbits [0x8901825083a8e1cc, 0x911852491148922c, 0x411104214108608, 0xf2ad3492aa89b6])
def s73Mask : Nat := 0xaa005500aa0055
abbrev s73Goal : Nat := sGoal &&& s73Mask
abbrev s73StockWords : List Nat := [0xaa000000aa0000, 0x88004400880044, 0xa0005000a00050, 0xaa005500000000]
def s73Fact : Nat × List Nat × Nat × Nat := (s73Mask, s73StockWords, 5, s73Goal)
def s73Cuts : List (Nat × List Nat × Nat × Nat) := []
def s73Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 21, 51, 6, 21, 51, 6, 21, 51, 6, 21, 51, 19, 34, 36, 49, 19, 34, 36, 49, 19, 34, 36, 49], rfl⟩
def s73Witnesses := unpackWitnesses s73StockWords [10756, 265220, 527362, 812563]
def s73Index (i : Nat) : Nat := unpack 0x9 2 i
def s73Codes (i : Nat) : Nat := unpack 0xf 15 i
def s73Forest (i : Nat) : Nat := unpack 0x1e 14 i
def s73Links := pageLinks s73Index s73Codes 1 13 1 2
def s73Data (i : Nat) : Nat × Nat :=
  let e := s73Forest i
  (e &&& 1, e >>> 1)
def s73Sample : Nat × Nat := (s73Blob334931, 63)
def s73Tags := dagTraceTags s73Mask 63 (dagTagBases s73StockWords s73Blob335317 s73Blob335432 63) 4 s73Data
def s73States := dagTrace s73Mask s73StockWords 4 s73Data
def s73MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s73Moves := dagMoves s73MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Autos : DagMovesOK s73Mask s73Goal 64 s73Moves := dagMovesOfCheck (by decide +kernel)
def s73Check := dagCheckNode s73Mask s73Goal s73Chart (dagKnownCloses s73Goal s73Cuts) 1 s73States s73Moves s73Links s73Sample s73Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Roots : dagCheckRoots s73Mask s73Goal s73Chart (dagKnownCloses s73Goal s73Cuts) s73Witnesses (dagRef 1 s73States s73Moves s73Links 0) s73StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Block0 : treeBlock 0 1 s73Check = true := by decide +kernel
theorem s73Blocks : treeBlock 0 1 s73Check = true := s73Block0
theorem s73Known : Known s73Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Stock : Lower s73Mask s73StockWords s73Goal 5 := by
  apply lowerDag _ _ _ _ s73Autos _ _ _ s73Known _ s73Roots s73Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s73Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s74Mask : Nat := 0x5500005555000055
abbrev s74Goal : Nat := sGoal &&& s74Mask
abbrev s74StockWords : List Nat := [0x4400004444000044, 0x5000005050000050, 0x5500000055000000, 0x5500005500000000]
def s74Fact : Nat × List Nat × Nat × Nat := (s74Mask, s74StockWords, 5, s74Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Stock : Lower s74Mask s74StockWords s74Goal 5 := dagShiftLower (width := 64) pm3 s73Stock (by decide +kernel)
def s75Blob340099 : Nat := (cbits [0x81c0607020180406, 0x82815088540a1502, 0x2190985c28160905, 0xb0c068241a0c0642, 0x2894381e0e074261, 0x9844261209442250, 0x4633098cc4627120, 0x35188d46433188cc, 0x188e46836190d868, 0xf0703a190e87039, 0x800061c0f0683c0e, 0x806090180a060181, 0x70081c4806110182, 0x181c26070201c040, 0x5420150205402151, 0x6815188543815098, 0x1608058081601058, 0x1a05864160e05826, 0x5c22170285c0617, 0x4201900864281709, 0x191886438190986, 0xa09868201a010687, 0x186c701a19068381, 0x74301b0906c221b0, 0x301d0a074221d028, 0x1f0c078281e09078, 0x209402250e07c26])
def s75Blob340671 : Nat := (cbits [0x1ffe0019fcece7c, 0x67f1738ff1fe07ff, 0x3e1ff81ffe03ffc6, 0xfffffff8787f83ff, 0x8001fc00ffe0001f, 0x3fffffe00000003f, 0xfffc003fff81fff0, 0xfffe00003fffffff, 0xc00000000000003f])
def s75Blob340886 : Nat := (cbits [0x10a721808bc6463c, 0x25d05285506622a7, 0x120aa88952234a82, 0xa5489518502b815a, 0x1a800a4a04112, 0x291145002040002d, 0xf9f1063ffe81ffe0, 0xff7c00003fddf7dc, 0x18600c1821837])
def s75Mask : Nat := 0xffff00ffffff00ff
abbrev s75Goal : Nat := sGoal &&& s75Mask
abbrev s75StockWords : List Nat := [0xaaaa00aaaaaa00aa, 0xcccc00cccccc00cc, 0xf0f000f0f0f000f0, 0xff000000ff000000, 0xffff0000ffff0000, 0xffff00ff00000000]
def s75Fact : Nat × List Nat × Nat × Nat := (s75Mask, s75StockWords, 10, s75Goal)
def s75Cuts : List (Nat × List Nat × Nat × Nat) := [s4Fact, s66Fact, s64Fact, s0Fact, s40Fact, s27Fact, s19Fact, s74Fact, s10Fact]
def s75Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 21, 25, 26, 37, 51, 60, 6, 21, 25, 26, 37, 5, 19, 28, 35, 49, 50, 52, 56, 5, 19, 28, 35], rfl⟩
def s75Witnesses := unpackWitnesses s75StockWords [10772, 265220, 527362, 799249, 1059333, 1329669]
def s75Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x901202222d80d001, 0xa2540a8132260484, 0x340608b11602]) else (cbits [0x2003c4690d01a0, 0xc29452825046480d, 0x5b4ac950a734])) else (if j < 3 then (cbits [0xd0391720e41c8372, 0xf89f03e07c0e91, 0x82504200c008]) else (if j < 4 then (cbits [0x684b29612861bc30, 0x674c298530a25352, 0xc45666c8563a]) else (cbits [0x40e80c8990320640, 0xc1bdf70ee0d2ba43, 0x3b2760e])))) 11 (i % 16)
def s75Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x86003c040100003f, 0x4c06283c0311100d, 0x7a31f3a18d9a8c5, 0x50218a26188524c4, 0x38c7c146360831, 0xa31]) else (cbits [0x30cd00cc4016621, 0x80cc40129480849e, 0x1c93c104960680a, 0xc1501a0900783d29, 0xe0980f074c403633, 0x1431])) else (if j < 3 then (cbits [0xd24b0646282c030, 0x5c6603092c1718a, 0x2c0341300f0c0cc, 0xc1919a0b8cd070c4, 0x591007c7c0103863, 0x2301]) else (cbits [0x94188494c4036326, 0x4b92585862b29313, 0x4292c2031017a4b, 0x62018a1300649189, 0x1500709d2583862, 0x2b32]))) else (if j < 6 then (if j < 5 then (cbits [0x93a4b0846285ac48, 0xc086286401b31007, 0x266620251988e8c6, 0x1033101318f0d0c4, 0x5140cf4106284e63, 0x3631]) else (cbits [0x1c2520dd2787292c, 0xec6685203d05004, 0x7892c2b01883002, 0x3618a1600f41c01, 0xea124f1052587c62, 0x4449])) else (if j < 7 then (cbits [0x1fa4f1212928c948, 0xdc62810008404a4, 0x8ac48434961f988, 0x3818a1680f42401, 0x7a2b1211d2588062, 0x4a00]) else (cbits [0x880c6c286289601b, 0xe4c42666202e198, 0x2686202f19e858c5, 0xf8c5])))) 21 (i % 16)
def s75Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x318a020040101f80, 0x618d8218a823100, 0x40849e0818f8219a, 0x78131082310024a, 0x4a40e49e0e0150d0]) else (cbits [0x300f1200d814960d, 0x1601a1231e1301e1, 0xa164961718a17018, 0x101c19e124961618, 0x41f01881310123])) else (if j < 3 then (cbits [0xf00f9f4962031020, 0xa63101f624240159, 0x39f3109f4962600c, 0x159f3202a00e2a31, 0x4969f4961f6242d3]) else (if j < 4 then (cbits [0x100db1007b118a01, 0x3618a81310b13103, 0x6364a43749e37315, 0x963c19a3b18d8149, 0x49e3f3103e18f814]) else (cbits [0x349e3e4963e4a43f, 0x3e6244549ebe4964, 0x14a4be496474a4, 0x108100dca007ca31, 0x3])))) 20 (i % 16)
def s75Links := pageLinks s75Index s75Codes 4 13 7 5
def s75Data (i : Nat) : Nat × Nat :=
  let e := s75Forest i
  (e &&& 127, e >>> 7)
def s75Sample : Nat × Nat := (s75Blob340099, 96)
def s75Tags := dagTraceTags s75Mask 96 (dagTagBases s75StockWords s75Blob340671 s75Blob340886 96) 9 s75Data
def s75States := dagTrace s75Mask s75StockWords 9 s75Data
def s75MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s75Moves := dagMoves s75MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Autos : DagMovesOK s75Mask s75Goal 64 s75Moves := dagMovesOfCheck (by decide +kernel)
def s75Check := dagCheckNode s75Mask s75Goal s75Chart (dagKnownCloses s75Goal s75Cuts) 77 s75States s75Moves s75Links s75Sample s75Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Roots : dagCheckRoots s75Mask s75Goal s75Chart (dagKnownCloses s75Goal s75Cuts) s75Witnesses (dagRef 77 s75States s75Moves s75Links 0) s75StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Block0 : treeBlock 0 24 s75Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Block24 : treeBlock 24 24 s75Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Block48 : treeBlock 48 24 s75Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Block72 : treeBlock 72 5 s75Check = true := by decide +kernel
theorem s75Group0_48 : treeBlock 0 48 s75Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s75Check) s75Block0 s75Block24
theorem s75Group48_29 : treeBlock 48 29 s75Check = true := treeBlock_merge (start := 48) (left := 24) (right := 5) (check := s75Check) s75Block48 s75Block72
theorem s75Group0_77 : treeBlock 0 77 s75Check = true := treeBlock_merge (start := 0) (left := 48) (right := 29) (check := s75Check) s75Group0_48 s75Group48_29
theorem s75Blocks : treeBlock 0 77 s75Check = true := s75Group0_77
theorem s75Known : Known s75Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s10Stock) s74Stock) s19Stock) s27Stock) s40Stock) s0Stock) s64Stock) s66Stock) s4Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Stock : Lower s75Mask s75StockWords s75Goal 10 := by
  apply lowerDag _ _ _ _ s75Autos _ _ _ s75Known _ s75Roots s75Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s75Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s76Mask : Nat := 0xffff0f0fffff0f0f
abbrev s76Goal : Nat := sGoal &&& s76Mask
abbrev s76StockWords : List Nat := [0xaaaa0a0aaaaa0a0a, 0xcccc0c0ccccc0c0c, 0xf0f00000f0f00000, 0xff000f00ff000f00, 0xffff0000ffff0000, 0xffff0f0f00000000]
def s76Fact : Nat × List Nat × Nat × Nat := (s76Mask, s76StockWords, 10, s76Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Stock : Lower s76Mask s76StockWords s76Goal 10 := dagShiftLower (width := 64) pm4 s75Stock (by decide +kernel)
def s77Mask : Nat := 0xffff3333ffff3333
abbrev s77Goal : Nat := sGoal &&& s77Mask
abbrev s77StockWords : List Nat := [0xaaaa2222aaaa2222, 0xcccc0000cccc0000, 0xf0f03030f0f03030, 0xff003300ff003300, 0xffff0000ffff0000, 0xffff333300000000]
def s77Fact : Nat × List Nat × Nat × Nat := (s77Mask, s77StockWords, 10, s77Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s77Stock : Lower s77Mask s77StockWords s77Goal 10 := dagShiftLower (width := 64) pm5 s75Stock (by decide +kernel)
def s78Mask : Nat := 0xffff5555ffff5555
abbrev s78Goal : Nat := sGoal &&& s78Mask
abbrev s78StockWords : List Nat := [0xaaaa0000aaaa0000, 0xcccc4444cccc4444, 0xf0f05050f0f05050, 0xff005500ff005500, 0xffff0000ffff0000, 0xffff555500000000]
def s78Fact : Nat × List Nat × Nat × Nat := (s78Mask, s78StockWords, 10, s78Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s78Stock : Lower s78Mask s78StockWords s78Goal 10 := dagShiftLower (width := 64) pm3 s75Stock (by decide +kernel)
def s79Blob348397 : Nat := (cbits [0x82c02090281c0607, 0x42215028540a0d01, 0x6170a05824160a05, 0xa090683019088642, 0xe078381d0986c301, 0xa44627108940a250, 0x4633098cc462b108, 0x35188d46433188cc, 0x188e46836190d868, 0xf0703a190e87039, 0xc02071c0f0683c0e, 0xa090182446070981, 0xb108243009088240, 0x834460b0982c020, 0x540a0f0183c380d0, 0x3815098542015008, 0x1608058681518854, 0x1a05864160e05826, 0x5c22170285c0617, 0x4201900864281709, 0x191886438190986, 0xa0e068261a080687, 0x886c061b1c068641, 0x740a1d0c06c241b0, 0x241e0c074281d088, 0x1f0987c301e0a078, 0x1889446250089438])
def s79Blob348969 : Nat := (cbits [0x7ffffc19ffd9cff, 0x67d2e70bf8ff07ff, 0x1f0ff81ff819c1c6, 0xfffe01f8781f07f3, 0x8063f81cfff0001f, 0x1fffffe0001ffe3f, 0xffe0003fff83ffe0, 0xfffc00001fffffff, 0xe00000000000003f])
def s79Blob349184 : Nat := (cbits [0x12bbefc08bfc8c7f, 0x25d0a509e83312a7, 0x4905508950898382, 0xa5140418500702b2, 0x3500012502112, 0x1488a5002104102d, 0xffc498bffe83ffc0, 0xff7800009feeffdc, 0xc000c600c6012137])
def s79Mask : Nat := 0xffffaaaaffffaaaa
abbrev s79Goal : Nat := sGoal &&& s79Mask
abbrev s79StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccc8888cccc8888, 0xf0f0a0a0f0f0a0a0, 0xff00aa00ff00aa00, 0xffff0000ffff0000, 0xffffaaaa00000000]
def s79Fact : Nat × List Nat × Nat × Nat := (s79Mask, s79StockWords, 10, s79Goal)
def s79Cuts : List (Nat × List Nat × Nat × Nat) := [s66Fact, s64Fact, s35Fact, s0Fact, s40Fact, s44Fact, s27Fact, s19Fact, s10Fact]
def s79Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 9, 21, 22, 26, 37, 51, 60, 7, 9, 21, 22, 5, 19, 28, 35, 49, 50, 52, 56, 5, 19, 28, 35], rfl⟩
def s79Witnesses := unpackWitnesses s79StockWords [10772, 265733, 527875, 791041, 1059333, 1329669]
def s79Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x1501410e601d001, 0x8018016216015115, 0x1d01b21921901811]) else (if j < 2 then (cbits [0x2001f11d21d01d0, 0xb02b02b029220920, 0x2f02f02c32c02b12]) else (cbits [0x3113103102f22f0, 0xe03d134934032232, 0x4114104104103e33]))) else (if j < 4 then (cbits [0x4a04a04a0482426, 0x205204f34a54a04a, 0x6006005e252c5205]) else (if j < 5 then (cbits [0x622620620620602, 0xb06b06b064764064, 0x7307306c76c06b16]) else (cbits [0x7b07b0765742731, 0x568418408407b97b, 0x9169108b68b08b08])))) 12 (i % 16)
def s79Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x86003c040100003f, 0x49c6282a0311100d, 0x67631f3618d978c5, 0xb59310aa98814465, 0xa810c5179258b862, 0x418]) else (cbits [0x8518801c63e0a31b, 0x18668066200b310, 0x406620094a40424f, 0x80e49e0824b03405, 0xe0a18804803c1e94, 0x1331])) else (if j < 3 then (cbits [0xd00ac6403e2c008, 0xc80c4e3e6211c310, 0x4c92d254961198a, 0x91b6240c24b05cc4, 0xe0f24b05c6283a01, 0x2100]) else (if j < 4 then (cbits [0xc0c509189044640, 0xa40365000f1e496, 0x383311418d810c5, 0xc2d315961884a8c4, 0x881988074c785c92, 0x1e31]) else (cbits [0x820c50ad2585692c, 0xccc6c6062a1f19e, 0x6293c3561c1a24b, 0x42001e828020c929, 0x41d30e0e466c6e33, 0x600])))) else (if j < 7 then (if j < 6 then (cbits [0x838020e125844031, 0x8f0c40603142301e, 0x886936424961f98d, 0x94c4a42524f51927, 0x41ea4f1418709e94, 0x3e4a]) else (cbits [0x2230f104c908063c, 0xc46281000845624, 0xc8e92c4031b1e988, 0x84b62424b0e12126, 0x190c509007a1200, 0x3e31])) else (if j < 8 then (cbits [0x2730e13525882636, 0x13989092c3c4b624, 0xaa662952310198c5, 0xb56007aa30e10cc6, 0x8880c6c28628ae01, 0x2519]) else (if j < 9 then (cbits [0x2918acd0c4254620, 0x42c6285692c58496, 0xc786292c310130cf, 0xd2d18a2db0e16926, 0x218cd54c6527e31, 0x5a31]) else (cbits [0x9a9884b8c40bac38, 0x561258a062b3a313, 0x2da4b]))))) 21 (i % 16)
def s79Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x318a020040101f80, 0x618d8218a823100, 0x40849e0818f8219a, 0x78131082310024a, 0x4a40e49e0e0150d0]) else (if j < 2 then (cbits [0x300f1200d814960d, 0x16018813101231e1, 0xf964961731017004, 0x10166241b0159600, 0x310964961d00c9d3]) else (cbits [0x63202100e2131396, 0x9649616624243159, 0xda8007a818a01496, 0x10a84962b3102800, 0x18a8149628315a83]))) else (if j < 4 then (cbits [0x4a43149e3131530, 0x8161c304963031b3, 0xb374963819a3718d, 0x103c18f8161c3719, 0x31b3c4a43d49e3d3]) else (if j < 5 then (cbits [0xc4963c3244031e40, 0x3c6244461e4449b3, 0xc4749b474964749e, 0xa43c6244b49ebc61, 0x4a4bc61c4d4964d4]) else (cbits [0x2310521958161c3c, 0xd63100161c52314d, 0x814965600dd6007, 0x158161c5a49b5a31, 0x4960161c5d3])))) 20 (i % 16)
def s79Links := pageLinks s79Index s79Codes 4 13 7 5
def s79Data (i : Nat) : Nat × Nat :=
  let e := s79Forest i
  (e &&& 127, e >>> 7)
def s79Sample : Nat × Nat := (s79Blob348397, 96)
def s79Tags := dagTraceTags s79Mask 96 (dagTagBases s79StockWords s79Blob348969 s79Blob349184 96) 9 s79Data
def s79States := dagTrace s79Mask s79StockWords 9 s79Data
def s79MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s79Moves := dagMoves s79MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Autos : DagMovesOK s79Mask s79Goal 64 s79Moves := dagMovesOfCheck (by decide +kernel)
def s79Check := dagCheckNode s79Mask s79Goal s79Chart (dagKnownCloses s79Goal s79Cuts) 95 s79States s79Moves s79Links s79Sample s79Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Roots : dagCheckRoots s79Mask s79Goal s79Chart (dagKnownCloses s79Goal s79Cuts) s79Witnesses (dagRef 95 s79States s79Moves s79Links 0) s79StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Block0 : treeBlock 0 24 s79Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Block24 : treeBlock 24 24 s79Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Block48 : treeBlock 48 24 s79Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Block72 : treeBlock 72 23 s79Check = true := by decide +kernel
theorem s79Group0_48 : treeBlock 0 48 s79Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s79Check) s79Block0 s79Block24
theorem s79Group48_47 : treeBlock 48 47 s79Check = true := treeBlock_merge (start := 48) (left := 24) (right := 23) (check := s79Check) s79Block48 s79Block72
theorem s79Group0_95 : treeBlock 0 95 s79Check = true := treeBlock_merge (start := 0) (left := 48) (right := 47) (check := s79Check) s79Group0_48 s79Group48_47
theorem s79Blocks : treeBlock 0 95 s79Check = true := s79Group0_95
theorem s79Known : Known s79Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s10Stock) s19Stock) s27Stock) s44Stock) s40Stock) s0Stock) s35Stock) s64Stock) s66Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Stock : Lower s79Mask s79StockWords s79Goal 10 := by
  apply lowerDag _ _ _ _ s79Autos _ _ _ s79Known _ s79Roots s79Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s79Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s80Mask : Nat := 0xffffccccffffcccc
abbrev s80Goal : Nat := sGoal &&& s80Mask
abbrev s80StockWords : List Nat := [0xaaaa8888aaaa8888, 0xcccccccccccccccc, 0xf0f0c0c0f0f0c0c0, 0xff00cc00ff00cc00, 0xffff0000ffff0000, 0xffffcccc00000000]
def s80Fact : Nat × List Nat × Nat × Nat := (s80Mask, s80StockWords, 10, s80Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Stock : Lower s80Mask s80StockWords s80Goal 10 := dagShiftLower (width := 64) pm4 s79Stock (by decide +kernel)
def s81Mask : Nat := 0xfffff0f0fffff0f0
abbrev s81Goal : Nat := sGoal &&& s81Mask
abbrev s81StockWords : List Nat := [0xaaaaa0a0aaaaa0a0, 0xccccc0c0ccccc0c0, 0xf0f0f0f0f0f0f0f0, 0xff00f000ff00f000, 0xffff0000ffff0000, 0xfffff0f000000000]
def s81Fact : Nat × List Nat × Nat × Nat := (s81Mask, s81StockWords, 10, s81Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s81Stock : Lower s81Mask s81StockWords s81Goal 10 := dagShiftLower (width := 64) pm5 s79Stock (by decide +kernel)
def s82Mask : Nat := 0xffffff00ffffff00
abbrev s82Goal : Nat := sGoal &&& s82Mask
abbrev s82StockWords : List Nat := [0xaaaaaa00aaaaaa00, 0xcccccc00cccccc00, 0xf0f0f000f0f0f000, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffff0000000000]
def s82Fact : Nat × List Nat × Nat × Nat := (s82Mask, s82StockWords, 10, s82Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82Stock : Lower s82Mask s82StockWords s82Goal 10 := dagShiftLower (width := 64) pm3 s79Stock (by decide +kernel)
def s83Mask : Nat := 0xffffffff00ff00ff
abbrev s83Goal : Nat := sGoal &&& s83Mask
abbrev s83StockWords : List Nat := [0xaaaaaaaa00aa00aa, 0xcccccccc00cc00cc, 0xf0f0f0f000f000f0, 0xff00ff0000000000, 0xffff000000ff0000, 0xffffffff00000000]
def s83Fact : Nat × List Nat × Nat × Nat := (s83Mask, s83StockWords, 10, s83Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s83Stock : Lower s83Mask s83StockWords s83Goal 10 := dagShiftLower (width := 64) pm2 s75Stock (by decide +kernel)
def s84Mask : Nat := 0xffffffff0f0f0f0f
abbrev s84Goal : Nat := sGoal &&& s84Mask
abbrev s84StockWords : List Nat := [0xaaaaaaaa0a0a0a0a, 0xcccccccc0c0c0c0c, 0xf0f0f0f000000000, 0xff00ff000f000f00, 0xffff00000f0f0000, 0xffffffff00000000]
def s84Fact : Nat × List Nat × Nat × Nat := (s84Mask, s84StockWords, 10, s84Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Stock : Lower s84Mask s84StockWords s84Goal 10 := dagShiftLower (width := 64) pm10 s75Stock (by decide +kernel)
def s85Mask : Nat := 0xffffffff33333333
abbrev s85Goal : Nat := sGoal &&& s85Mask
abbrev s85StockWords : List Nat := [0xaaaaaaaa22222222, 0xcccccccc00000000, 0xf0f0f0f030303030, 0xff00ff0033003300, 0xffff000033330000, 0xffffffff00000000]
def s85Fact : Nat × List Nat × Nat × Nat := (s85Mask, s85StockWords, 10, s85Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Stock : Lower s85Mask s85StockWords s85Goal 10 := dagShiftLower (width := 64) pm9 s75Stock (by decide +kernel)
def s86Mask : Nat := 0xffffffff55555555
abbrev s86Goal : Nat := sGoal &&& s86Mask
abbrev s86StockWords : List Nat := [0xaaaaaaaa00000000, 0xcccccccc44444444, 0xf0f0f0f050505050, 0xff00ff0055005500, 0xffff000055550000, 0xffffffff00000000]
def s86Fact : Nat × List Nat × Nat × Nat := (s86Mask, s86StockWords, 10, s86Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s86Stock : Lower s86Mask s86StockWords s86Goal 10 := dagShiftLower (width := 64) pm8 s75Stock (by decide +kernel)
def s87Mask : Nat := 0xffffffffaaaaaaaa
abbrev s87Goal : Nat := sGoal &&& s87Mask
abbrev s87StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccc88888888, 0xf0f0f0f0a0a0a0a0, 0xff00ff00aa00aa00, 0xffff0000aaaa0000, 0xffffffff00000000]
def s87Fact : Nat × List Nat × Nat × Nat := (s87Mask, s87StockWords, 10, s87Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Stock : Lower s87Mask s87StockWords s87Goal 10 := dagShiftLower (width := 64) pm2 s79Stock (by decide +kernel)
def s88Mask : Nat := 0xffffffffcccccccc
abbrev s88Goal : Nat := sGoal &&& s88Mask
abbrev s88StockWords : List Nat := [0xaaaaaaaa88888888, 0xcccccccccccccccc, 0xf0f0f0f0c0c0c0c0, 0xff00ff00cc00cc00, 0xffff0000cccc0000, 0xffffffff00000000]
def s88Fact : Nat × List Nat × Nat × Nat := (s88Mask, s88StockWords, 10, s88Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Stock : Lower s88Mask s88StockWords s88Goal 10 := dagShiftLower (width := 64) pm10 s79Stock (by decide +kernel)
def s89Mask : Nat := 0xfffffffff0f0f0f0
abbrev s89Goal : Nat := sGoal &&& s89Mask
abbrev s89StockWords : List Nat := [0xaaaaaaaaa0a0a0a0, 0xccccccccc0c0c0c0, 0xf0f0f0f0f0f0f0f0, 0xff00ff00f000f000, 0xffff0000f0f00000, 0xffffffff00000000]
def s89Fact : Nat × List Nat × Nat × Nat := (s89Mask, s89StockWords, 10, s89Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Stock : Lower s89Mask s89StockWords s89Goal 10 := dagShiftLower (width := 64) pm9 s79Stock (by decide +kernel)
def s90Mask : Nat := 0xffffffffff00ff00
abbrev s90Goal : Nat := sGoal &&& s90Mask
abbrev s90StockWords : List Nat := [0xaaaaaaaaaa00aa00, 0xcccccccccc00cc00, 0xf0f0f0f0f000f000, 0xff00ff00ff00ff00, 0xffff0000ff000000, 0xffffffff00000000]
def s90Fact : Nat × List Nat × Nat × Nat := (s90Mask, s90StockWords, 10, s90Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90Stock : Lower s90Mask s90StockWords s90Goal 10 := dagShiftLower (width := 64) pm8 s79Stock (by decide +kernel)
def s91Blob359159 : Nat := (cbits [0x81c0607020180406, 0xc060b04024020902, 0x40e060340a0d0502, 0x5088540a15060381, 0x985c281609058281, 0x68141a0c06422190, 0x381d0986c301a090, 0x27108940a250e078, 0x98cc462b108a446, 0x8e46235188cc4633, 0x80a0601818000618, 0x8060901818060501, 0x70201c04070081c2, 0x182400091181c260, 0x241809050240a090, 0x20b108243009088, 0xb0982c100b0102c, 0x4034080d0083446, 0x38080e01038380d, 0xc0a0f0183c380e04, 0x81500854180f0503, 0x50e0542615080540, 0x8058081601058621, 0x5c06170e05826160, 0x28170905c2217028, 0x1908064101900864, 0x106862190e06426])
def s91Blob359729 : Nat := (cbits [0xfffff80ffd8e73fc, 0xd2f38ccf7ff07fe1, 0x81ff81fe1f00fff3, 0xe000fff41f03ff0f, 0x63fc0ff001ffffff, 0xfe0001ffffff0008, 0xf83fff000, 0xfc000000fffffe00, 0xf])
def s91Blob359923 : Nat := (cbits [0x39a6c86ffc86315c, 0xd0b284c552745260, 0x909490a21a0ad2a1, 0x4014254007015b0a, 0x3580ea021292555, 0x2408219984580180, 0x860460e83efe000, 0x7800000079ce7811, 0x400040001080800f])
def s91Mask : Nat := 0xaaaaaaaaffffffff
abbrev s91Goal : Nat := sGoal &&& s91Mask
abbrev s91StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0x88888888cccccccc, 0xa0a0a0a0f0f0f0f0, 0xaa00aa00ff00ff00, 0xaaaa0000ffff0000, 0xaaaaaaaa00000000]
def s91Fact : Nat × List Nat × Nat × Nat := (s91Mask, s91StockWords, 9, s91Goal)
def s91Cuts : List (Nat × List Nat × Nat × Nat) := [s6Fact, s35Fact, s8Fact, s0Fact]
def s91Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 9, 21, 26, 37, 51, 6, 9, 21, 26, 37, 51, 5, 10, 19, 28, 35, 49, 5, 10, 19, 28, 35, 49], rfl⟩
def s91Witnesses := unpackWitnesses s91StockWords [4616, 265220, 527362, 791041, 1059333, 1329669]
def s91Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x3c9e0f0783483801, 0x2452090482231088, 0xa050]) else 0x642e570b0d82c142) 9 (i % 16)
def s91Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x3620c54118a0003f, 0x8cdca1999031f146, 0xcf3199c62130c405, 0x102ac3951870918d, 0x180801b0e023]) else (cbits [0x7011880901e0e04c, 0x8061102620034358, 0x1a92c0cc409])) 19 (i % 16)
def s91Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xc08c40218a0407e0, 0x8080618d8462a161, 0x66101e2463e10261, 0x161c34c40119b846, 0x31984c42]) else (cbits [0xc4cc6e1026400690, 0x61c85870100])) 18 (i % 16)
def s91Links := pageLinks s91Index s91Codes 4 13 5 5
def s91Data (i : Nat) : Nat × Nat :=
  let e := s91Forest i
  (e &&& 31, e >>> 5)
def s91Sample : Nat × Nat := (s91Blob359159, 96)
def s91Tags := dagTraceTags s91Mask 96 (dagTagBases s91StockWords s91Blob359729 s91Blob359923 96) 8 s91Data
def s91States := dagTrace s91Mask s91StockWords 8 s91Data
def s91MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s91Moves := dagMoves s91MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Autos : DagMovesOK s91Mask s91Goal 64 s91Moves := dagMovesOfCheck (by decide +kernel)
def s91Check := dagCheckNode s91Mask s91Goal s91Chart (dagKnownCloses s91Goal s91Cuts) 22 s91States s91Moves s91Links s91Sample s91Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Roots : dagCheckRoots s91Mask s91Goal s91Chart (dagKnownCloses s91Goal s91Cuts) s91Witnesses (dagRef 22 s91States s91Moves s91Links 0) s91StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Block0 : treeBlock 0 22 s91Check = true := by decide +kernel
theorem s91Blocks : treeBlock 0 22 s91Check = true := s91Block0
theorem s91Known : Known s91Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s0Stock) s8Stock) s35Stock) s6Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Stock : Lower s91Mask s91StockWords s91Goal 9 := by
  apply lowerDag _ _ _ _ s91Autos _ _ _ s91Known _ s91Roots s91Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s91Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s92Mask : Nat := 0xaaaaffffaaaaffff
abbrev s92Goal : Nat := sGoal &&& s92Mask
abbrev s92StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0x8888cccc8888cccc, 0xa0a0f0f0a0a0f0f0, 0xaa00ff00aa00ff00, 0xaaaa0000aaaa0000, 0xaaaaffff00000000]
def s92Fact : Nat × List Nat × Nat × Nat := (s92Mask, s92StockWords, 9, s92Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Stock : Lower s92Mask s92StockWords s92Goal 9 := dagShiftLower (width := 64) pm2 s91Stock (by decide +kernel)
def s93Mask : Nat := 0xaaffaaffaaffaaff
abbrev s93Goal : Nat := sGoal &&& s93Mask
abbrev s93StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0x88cc88cc88cc88cc, 0xa0f0a0f0a0f0a0f0, 0xaa00aa00aa00aa00, 0xaaff0000aaff0000, 0xaaffaaff00000000]
def s93Fact : Nat × List Nat × Nat × Nat := (s93Mask, s93StockWords, 9, s93Goal)
def s93Witnesses := unpackWitnesses s93StockWords [10772, 265220, 527362, 791041, 1059333, 1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Stock : Lower s93Mask s93StockWords s93Goal 9 := by
  apply essentialLift (witnesses := s93Witnesses) (cut := s4Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s4StockWords) (by decide +kernel)
  · exact s4Stock
  · decide +kernel
def s94Mask : Nat := 0xccccccccffffffff
abbrev s94Goal : Nat := sGoal &&& s94Mask
abbrev s94StockWords : List Nat := [0x88888888aaaaaaaa, 0xcccccccccccccccc, 0xc0c0c0c0f0f0f0f0, 0xcc00cc00ff00ff00, 0xcccc0000ffff0000, 0xcccccccc00000000]
def s94Fact : Nat × List Nat × Nat × Nat := (s94Mask, s94StockWords, 9, s94Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Stock : Lower s94Mask s94StockWords s94Goal 9 := dagShiftLower (width := 64) pm4 s91Stock (by decide +kernel)
def s95Mask : Nat := 0xf0f0f0f0ffffffff
abbrev s95Goal : Nat := sGoal &&& s95Mask
abbrev s95StockWords : List Nat := [0xa0a0a0a0aaaaaaaa, 0xc0c0c0c0cccccccc, 0xf0f0f0f0f0f0f0f0, 0xf000f000ff00ff00, 0xf0f00000ffff0000, 0xf0f0f0f000000000]
def s95Fact : Nat × List Nat × Nat × Nat := (s95Mask, s95StockWords, 9, s95Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Stock : Lower s95Mask s95StockWords s95Goal 9 := dagShiftLower (width := 64) pm5 s91Stock (by decide +kernel)
def s96Mask : Nat := 0xff00ff00ffffffff
abbrev s96Goal : Nat := sGoal &&& s96Mask
abbrev s96StockWords : List Nat := [0xaa00aa00aaaaaaaa, 0xcc00cc00cccccccc, 0xf000f000f0f0f0f0, 0xff00ff00ff00ff00, 0xff000000ffff0000, 0xff00ff0000000000]
def s96Fact : Nat × List Nat × Nat × Nat := (s96Mask, s96StockWords, 9, s96Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Stock : Lower s96Mask s96StockWords s96Goal 9 := dagShiftLower (width := 64) pm3 s91Stock (by decide +kernel)
def s97Mask : Nat := 0xffffffffffff0000
abbrev s97Goal : Nat := sGoal &&& s97Mask
abbrev s97StockWords : List Nat := [0xaaaaaaaaaaaa0000, 0xcccccccccccc0000, 0xf0f0f0f0f0f00000, 0xff00ff00ff000000, 0xffff0000ffff0000, 0xffffffff00000000]
def s97Fact : Nat × List Nat × Nat × Nat := (s97Mask, s97StockWords, 9, s97Goal)
def s97Witnesses := unpackWitnesses s97StockWords [10772, 273428, 535057, 799249, 1074723, 1336851]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Stock : Lower s97Mask s97StockWords s97Goal 9 := by
  apply essentialLift (witnesses := s97Witnesses) (cut := s64Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s64StockWords) (by decide +kernel)
  · exact s64Stock
  · decide +kernel
def s98Blob375783 : Nat := (cbits [0x81c0607020180406, 0xc060b04024020902, 0x40e060340a0d0502, 0x5088540a15060381, 0x985c281609058281, 0x68141a0c06422190, 0x381d0986c301a090, 0x25108940a250e078, 0x1189c48261109848, 0xa8142a140a44229, 0x8582d118ac502a11, 0x233118cc2633160b, 0x61a0d46235190cc6, 0xc0e462391a0d8643, 0xf0383c1c0e8643a1, 0x61c0f0683c160, 0x6050180a0601818, 0x1101828060901818, 0x1c04070081c4806, 0x400091181c260702, 0x809050240a090182, 0x9108243009088241, 0x402c040b0082c500, 0x34020d1182c260b0, 0x580d0e034100d020, 0xe04038080e01038, 0x283c060f1603838])
def s98Blob376351 : Nat := (cbits [0x33f639d8e73fc, 0xe2f38ccfc1fffffe, 0xfe0f803fff0ccfbc, 0xfff0f0c0ff03ff0f, 0x3fc0ff0fff0003f, 0xffffffc000ff00ff, 0xffff0003fff000, 0xfc00000000000000, 0xffffff])
def s98Blob376551 : Nat := (cbits [0x60117218c86315c, 0xa0b284c5c01ca9b2, 0x420d02b4aa044b2c, 0x5470a0c057015b0a, 0x3580ea0b5a00509, 0x39c2560018ba00d6, 0x60dffd0003efe000, 0xf800000010841810, 0x2108602180effefb])
def s98Mask : Nat := 0xffffffffffffffff
abbrev s98Goal : Nat := sGoal &&& s98Mask
abbrev s98StockWords : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def s98Fact : Nat × List Nat × Nat × Nat := (s98Mask, s98StockWords, 12, s98Goal)
def s98Cuts : List (Nat × List Nat × Nat × Nat) := [s13Fact, s14Fact, s15Fact, s16Fact, s22Fact, s23Fact, s24Fact, s30Fact, s32Fact, s12Fact, s33Fact, s31Fact, s29Fact, s21Fact, s39Fact, s47Fact, s48Fact, s49Fact, s51Fact, s52Fact, s38Fact, s55Fact, s57Fact, s46Fact, s58Fact, s56Fact, s59Fact, s60Fact, s72Fact, s75Fact, s76Fact, s77Fact, s78Fact, s79Fact, s80Fact, s81Fact, s82Fact, s71Fact, s83Fact, s84Fact, s85Fact, s86Fact, s87Fact, s88Fact, s89Fact, s90Fact, s91Fact, s92Fact, s93Fact, s94Fact, s95Fact, s96Fact, s97Fact, s4Fact, s25Fact, s17Fact, s5Fact, s66Fact, s67Fact, s64Fact, s68Fact, s35Fact, s50Fact, s36Fact, s43Fact, s0Fact, s26Fact, s18Fact, s9Fact]
def s98Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[6, 9, 21, 26, 37, 42, 51, 60, 6, 9, 21, 26, 5, 10, 19, 28, 35, 44, 49, 50, 52, 56, 5, 10], rfl⟩
def s98Witnesses := unpackWitnesses s98StockWords [4616, 265220, 527362, 791041, 1059333, 1329669]
def s98Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x30f281ef00b8001, 0x563158056015805, 0x880620170c5c0170, 0x18806201]) else (cbits [0x401d007401b8c626, 0x7a01e807431d007, 0x8ac8301f887a21e8, 0x2f00b822])) else (if j < 3 then (cbits [0x3000c002f08bc0, 0xc6b3180c033000c, 0xb08e823810dc2370, 0x420cf0c3]) else (cbits [0x444501140438d0e0, 0x11c047011c047011, 0x4895204f2d1d0470, 0x57895645]))) else (if j < 6 then (if j < 5 then (cbits [0x605f917e059b1622, 0x9860618186061818, 0xb09a826a019a761a, 0x6d09b026]) else (cbits [0x207481d20730db8a, 0x9f037a8dd2c7481d, 0x99e1878221fa77d8, 0x929234b8])) else (if j < 7 then (cbits [0xc296a65a09492520, 0xe7639c0e7009c026, 0xba2a26a2368239f0, 0xb3a2be8a]) else 0x2de8))) 14 (i % 16)
def s98Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0xe80240100400003f, 0x3102ba3154046282, 0x2dc052592e988601, 0xe36b0e46a61c6ba9, 0xea7a20dec431b987, 0x804e76bd14]) else (if j < 2 then (cbits [0xd8c508f01f81e033, 0x3108726200b462a0, 0x3813d25a2424b040, 0x62db0fc5a61c8aac, 0xda7a29aaf4417188, 0x18c42019880]) else (cbits [0x53d100949680e92c, 0x7a781af4b031e8a0, 0x2c2324a24549400e, 0x842c940057a20089, 0x88928010f4401125, 0x2187002a4b0]))) else (if j < 4 then (cbits [0xa188410310017250, 0x7a203092d0552580, 0x440452580d494019, 0x808a4b013928024f, 0x1249602f250059e8, 0x4d2580b30e0]) else (if j < 5 then (cbits [0x800cd0300d82ec38, 0x19980632764007e8, 0x21070c40480cfc10, 0x92a4b51c49604a6, 0x2b61f854c3909d87, 0x29de8816310c]) else (cbits [0x898cc04313954f45, 0x49683a92c244c7e0, 0x3f0898721030e01f, 0xa503d1024621846c, 0x9e7a203cc38289e8, 0x85e880f30e0])))) else (if j < 9 then (if j < 7 then (cbits [0x34940267a223ec38, 0x193a500370a00565, 0x3f014c66c98cfd05, 0x1324b4204961266, 0x297a224cc3948187, 0x485e8810b0e0]) else (if j < 8 then (cbits [0x124b01231ea2433d, 0x4960466204898701, 0x3349125812188123, 0x84a0d2c1419f80c3, 0x3261c860c380b925, 0xd9e8a19bd10]) else (cbits [0x9c940387a786ef4b, 0x7a243ec382da4a25, 0x4487d87057c9402f, 0x1a00a4b1928062f, 0x35928062f440bd87, 0x85406703806c]))) else (if j < 10 then (cbits [0xa8ccc07193d2a03f, 0x31083862025467e0, 0x388b925b0e24b02e, 0x61f30fc3d61c874c, 0xbd7a2974f440fd88, 0x8ec06e1d80ac]) else (if j < 11 then (cbits [0x418ce9719fc10327, 0x49684092c25cc7e0, 0x448bd8731030e02f, 0xb10bd102161c078f, 0x2249602c63d85867, 0x8cc411130e0]) else (cbits [0x224b02431044692c, 0x1a583033f0246671, 0x39cc187012988098, 0x622bd14427a2082c, 0xc292808ef4f119e9, 0x10c06a62c944]))))) else (if j < 18 then (if j < 15 then (if j < 13 then (cbits [0x24943317a204c92c, 0x496060621470c402, 0x391258719824b61c, 0x827310c4d61f898c, 0x4a015998f45325e8, 0x481259a500dc]) else (if j < 14 then (cbits [0x8b0e62061c06292d, 0x7a2242c3812de899, 0x208898709124b221, 0x8921882234962466, 0x32310a4a62089125, 0x10525b1724b0]) else (cbits [0x9bd2c527a28a0f44, 0x9289a1250151e9e2, 0x508bd8709324b0d2, 0xe2b80ac5600f8a32, 0x9a19f81433316006, 0xccc42139880]))) else (if j < 16 then (cbits [0x4b0e04249687492c, 0x3100b2f441418722, 0x20129e881db0e034, 0x1a53d10434960506, 0xb31fc7692c4a0c4, 0xd525a14a4b0]) else (if j < 17 then (cbits [0x5bd104461c878c38, 0x19e818333145e8a2, 0x2c0d8c4215188019, 0x22630e04549687a9, 0x2b18a01a02714987, 0xf8c401b8c54]) else (cbits [0x9a4b44d49608c621, 0x18a85831403804e2, 0x2c11cc421f988038, 0x29698805449689c9, 0x60496c8092c178c4, 0x189e89a7b0e0])))) else (if j < 21 then (if j < 19 then (cbits [0x4bd3c687a58cef45, 0x61c1cf25138a4a03, 0x5c17e4a1a0bd1241, 0x1993d11324961bf5, 0x6300e9c355c1864a, 0x19406e3200ac]) else (if j < 20 then (cbits [0x130e05f496a6692c, 0x9286a0f441858732, 0x3890d8709a24b066, 0x9a8c942447a226ac, 0x527a248ac384d925, 0x9192589b9883]) else (cbits [0x3a4b1383106a6c38, 0xf8d6013d518712, 0x14dac06f3580ad6b, 0x2aa98806218a8aa3, 0x62496caa92c588c4, 0xd89873aab0e2]))) else (if j < 22 then (cbits [0xb24b06318a0d8f44, 0x61ccaec3859125aa, 0x21164c41ac3d1265, 0xb324b5594960cc6, 0x597a24ccc3996587, 0x168629b33d17]) else (if j < 23 then (cbits [0x398855a3100ce315, 0x61c4ce92d969258b, 0x916c011b3b0e75a, 0xb40c555b18a0d00, 0x5b4964d062196cc4, 0x170011b424b7]) else (cbits [0x48c555c18a0d2009, 0x4964d2621970c40b, 0x1b4a4b75c])))))) 23 (i % 16)
def s98Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x3013820040101f80, 0x837a204496043100, 0x6837a20849603310, 0xa2839280b7a20349, 0x19827a7837a5837]) else (if j < 2 then (cbits [0x17a2114961131010, 0x1649610310909281, 0x21049690928167a2, 0x101c18a02928107a, 0x4969d61c1e4961d3]) else (cbits [0xd61c9d7a22161c1d, 0x263109c6219d61f9, 0x228015a861c1c7a2, 0x219c61f9c61c9c7a, 0x7a22f4962e18a826]))) else (if j < 5 then (if j < 4 then (cbits [0xe61cae7a23161c2e, 0xae92834014b47a22, 0x27a7ae7a5ae7a2, 0xa23b015bb61c3a31, 0x621ba61fba61cba7]) else (cbits [0x37a24161cc131082, 0xc17a2c19284301ac, 0xc49496027a7c17a5, 0x1cc97a24a015ca61, 0x49682621c961fc96])) else (if j < 6 then (cbits [0x7a2d0928517a250, 0xd661c027a7d07a5d, 0x25601bd6015d600f, 0x218261f8261c827a, 0x9285f310de004816]) else (cbits [0x37a25e92861496de, 0x6301be3015e300ee, 0x7de7a5de7a2de928, 0xa26b009eb61c017a, 0x6218161f8161c817])))) 20 (i % 16)
def s98Links := pageLinks s98Index s98Codes 5 13 7 6
def s98Data (i : Nat) : Nat × Nat :=
  let e := s98Forest i
  (e &&& 127, e >>> 7)
def s98Sample : Nat × Nat := (s98Blob375783, 96)
def s98Tags := dagTraceTags s98Mask 96 (dagTagBases s98StockWords s98Blob376351 s98Blob376551 96) 11 s98Data
def s98States := dagTrace s98Mask s98StockWords 11 s98Data
def s98MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm4, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 4, 5] 0 i.val))), (pm10, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [1, 0, 3, 2, 5, 4] 0 i.val))), (pm5, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 4, 5] 0 i.val))), (pm9, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 3, 0, 1, 5, 4] 0 i.val))), (pm3, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 2, 1, 0, 4, 5] 0 i.val)))]
def s98Moves := dagMoves s98MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Autos : DagMovesOK s98Mask s98Goal 64 s98Moves := dagMovesOfCheck (by decide +kernel)
def s98Check := dagCheckNode s98Mask s98Goal s98Chart (dagKnownCloses s98Goal s98Cuts) 112 s98States s98Moves s98Links s98Sample s98Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Roots : dagCheckRoots s98Mask s98Goal s98Chart (dagKnownCloses s98Goal s98Cuts) s98Witnesses (dagRef 112 s98States s98Moves s98Links 0) s98StockWords 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Block0 : treeBlock 0 24 s98Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Block24 : treeBlock 24 24 s98Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Block48 : treeBlock 48 24 s98Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Block72 : treeBlock 72 24 s98Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Block96 : treeBlock 96 16 s98Check = true := by decide +kernel
theorem s98Group0_48 : treeBlock 0 48 s98Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s98Check) s98Block0 s98Block24
theorem s98Group72_40 : treeBlock 72 40 s98Check = true := treeBlock_merge (start := 72) (left := 24) (right := 16) (check := s98Check) s98Block72 s98Block96
theorem s98Group48_64 : treeBlock 48 64 s98Check = true := treeBlock_merge (start := 48) (left := 24) (right := 40) (check := s98Check) s98Block48 s98Group72_40
theorem s98Group0_112 : treeBlock 0 112 s98Check = true := treeBlock_merge (start := 0) (left := 48) (right := 64) (check := s98Check) s98Group0_48 s98Group48_64
theorem s98Blocks : treeBlock 0 112 s98Check = true := s98Group0_112
theorem s98Known : Known s98Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s9Stock) s18Stock) s26Stock) s0Stock) s43Stock) s36Stock) s50Stock) s35Stock) s68Stock) s64Stock) s67Stock) s66Stock) s5Stock) s17Stock) s25Stock) s4Stock) s97Stock) s96Stock) s95Stock) s94Stock) s93Stock) s92Stock) s91Stock) s90Stock) s89Stock) s88Stock) s87Stock) s86Stock) s85Stock) s84Stock) s83Stock) s71Stock) s82Stock) s81Stock) s80Stock) s79Stock) s78Stock) s77Stock) s76Stock) s75Stock) s72Stock) s60Stock) s59Stock) s56Stock) s58Stock) s46Stock) s57Stock) s55Stock) s38Stock) s52Stock) s51Stock) s49Stock) s48Stock) s47Stock) s39Stock) s21Stock) s29Stock) s31Stock) s33Stock) s12Stock) s32Stock) s30Stock) s24Stock) s23Stock) s22Stock) s16Stock) s15Stock) s14Stock) s13Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Stock : Lower s98Mask s98StockWords s98Goal 12 := by
  apply lowerDag _ _ _ _ s98Autos _ _ _ s98Known _ s98Roots s98Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s98Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
end PEqualNP.Outside.L_meta_43098

open PEqualNP.Outside.L_meta_43098 in
theorem PEqualNP.Outside.L_meta_43098 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678368 * 2 ^ 32 + 4007717568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678368 * 2 ^ 32 + 4007717568) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro t h
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
  let goal : BitVec 64 := 0xfee8eee0eee0eac0
  have root : Lower (fullMask 64) (raw.map BitVec.toNat) goal.toNat 12 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s98Stock
  have size : 12 ≤ t :=
    hcsLower (n := 6) raw goal 12 _ (by decide +kernel) (by decide +kernel) root t h
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 9]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [11, 4]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [15, 5]⟩, ⟨.and, [13, 16]⟩], 17⟩
  refine ⟨circuit, ?_, ?_, by decide +kernel⟩
  · intro gate member
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : circuit.size ≤ 12) size

