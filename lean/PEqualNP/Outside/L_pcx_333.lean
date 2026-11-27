import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_333

section Gauge
variable {G : Type} [Group G] {n : ℕ}

def pref (f : Fin n → G) (k : ℕ) (h : k  ≤  n) : G :=
  (List.ofFn (fun j : Fin k => f ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩)).prod

theorem pref_zero (f : Fin n → G) : pref f 0 (Nat.zero_le n) = 1 := by simp [pref]

theorem pref_full (f : Fin n → G) : pref f n (Nat.le_refl n) = (List.ofFn f).prod := by
  change (List.ofFn (fun j : Fin n => f ⟨j.val, j.isLt⟩)).prod = _
  rfl

theorem pref_succ (f : Fin n → G) (k : ℕ) (h : k+1  ≤  n) :
    pref f (k+1) h = pref f k (by omega) * f ⟨k,by omega⟩ := by
  unfold pref
  rw [List.ofFn_succ_last, List.prod_append]
  simp only [List.prod_cons, List.prod_nil, mul_one]
  rfl

def gauge (f : Fin n → G) (x : Fin n → G) (j : Fin n) : G := x j * (pref f j.val j.isLt.le)⁻¹
def physical (f : Fin n → G) (y : Fin n → G) (j : Fin n) : G := y j * pref f j.val j.isLt.le

theorem physical_gauge (f : Fin n → G) (x : Fin n → G) : physical f (gauge f x) = x := by
  funext j; simp [physical, gauge, mul_assoc]

theorem gauge_physical (f : Fin n → G) (y : Fin n → G) : gauge f (physical f y) = y := by
  funext j; simp [physical, gauge, mul_assoc]

def first (hn : 0 < n) : Fin n := ⟨0,hn⟩
def nxt (hn : 0 < n) (i : Fin n) : Fin n := ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩

theorem nxt_internal (hn : 0 < n) (i : Fin n) (hi : i.val+1 < n) : nxt hn i = ⟨i.val+1,hi⟩ := by
  apply Fin.ext; exact Nat.mod_eq_of_lt hi

theorem nxt_wrap (hn : 0 < n) (i : Fin n) (hi : i.val+1 = n) : nxt hn i = first hn := by
  apply Fin.ext; simp [nxt,first,hi]

theorem edge_internal (hn : 0 < n) (f : Fin n → G) (x : Fin n → G) (i : Fin n)
    (hi : i.val+1 < n) :
    x (nxt hn i) = x i * f i ↔ gauge f x (nxt hn i) = gauge f x i := by
  rw [nxt_internal hn i hi]
  change x ⟨i.val+1,hi⟩ = x i * f i ↔
    x ⟨i.val+1,hi⟩ * (pref f (i.val+1) hi.le)⁻¹ =
      x i * (pref f i.val i.isLt.le)⁻¹
  rw [pref_succ]
  constructor
  · intro h; rw [h,mul_inv_rev]; simp [mul_assoc]
  · intro h
    have q := congrArg (fun z => z * (pref f i.val i.isLt.le * f i)) h
    simpa [mul_assoc] using q

theorem edge_wrap (hn : 0 < n) (f : Fin n → G) (x : Fin n → G) (i : Fin n)
    (hi : i.val+1 = n) :
    x (nxt hn i) = x i * f i ↔
      gauge f x (first hn) = gauge f x i * (List.ofFn f).prod := by
  rw [nxt_wrap hn i hi]
  have hfp : (List.ofFn f).prod = pref f i.val i.isLt.le * f i := by
    rw [← pref_full]
    have hh : pref f n (Nat.le_refl n) = pref f (i.val+1) (by omega) := by
      congr
      exact hi.symm
    rw [hh,pref_succ]
  simp [gauge,first,pref_zero,hfp,mul_assoc]

def switch (P a : G) (e : Fin n) (i : Fin n) : G :=
  if i.val  ≤  e.val then a else a * P⁻¹

theorem switch_first (P a : G) (hn : 0 < n) (e : Fin n) : switch P a e (first hn) = a :=
  if_pos (Nat.zero_le _)

theorem switch_distinct (P a : G) (hP : P ≠ 1) : a ≠ a * P⁻¹ := by
  intro h
  apply hP
  have q := congrArg (fun z => a⁻¹*z) h
  have r : (1 : G) = P⁻¹ := by simpa [← mul_assoc] using q
  have u := congrArg (fun z : G => z⁻¹) r
  simpa using u.symm

theorem switch_edge_internal (P a : G) (hP : P ≠ 1) (hn : 0 < n) (e i : Fin n)
    (hi : i.val+1 < n) :
    switch P a e (nxt hn i) = switch P a e i ↔ i ≠ e := by
  rw [nxt_internal hn i hi]
  change (if i.val+1  ≤  e.val then a else a*P⁻¹) = (if i.val  ≤  e.val then a else a*P⁻¹) ↔ _
  rcases lt_trichotomy i.val e.val with h|h|h
  · have hn' : i ≠ e := fun he => h.ne (congrArg Fin.val he)
    rw [if_pos (by omega), if_pos h.le]; simp [hn']
  · have he : i = e := Fin.ext h
    rw [if_neg (by omega),if_pos h.le]; simp [he, (switch_distinct P a hP).symm]
  · have hn' : i ≠ e := fun he => h.ne' (congrArg Fin.val he)
    rw [if_neg (by omega),if_neg (by omega)]; simp [hn']

theorem switch_edge_wrap (P a : G) (hP : P ≠ 1) (hn : 0 < n) (e i : Fin n)
    (hi : i.val+1 = n) :
    switch P a e (first hn) = switch P a e i * P ↔ i ≠ e := by
  rw [switch_first]
  by_cases h : i = e
  · subst e
    have ha : a ≠ a*P := by
      intro he
      apply hP
      have q := congrArg (fun z => a⁻¹*z) he
      simpa [← mul_assoc] using q.symm
    simp [switch,ha]
  · have hh : ¬i.val  ≤  e.val := by
      have hv : i.val ≠ e.val := fun z => h (Fin.ext z)
      omega
    simp [switch,hh,mul_assoc,h]

end Gauge


section Count
variable {G : Type} [Group G] [Fintype G] [DecidableEq G] {n : ℕ}

def faults (hn : 0 < n) (f : Fin n → G) (x : Fin n → G) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x (nxt hn i) ≠ x i * f i)

def encode (hn : 0 < n) (f : Fin n → G) (e : Fin n) (a : G) : Fin n → G :=
  physical f (switch (List.ofFn f).prod a e)

theorem faults_encode (hn : 0 < n) (f : Fin n → G) (hp : (List.ofFn f).prod ≠ 1)
    (e : Fin n) (a : G) : faults hn f (encode hn f e a) = {e} := by
  ext i
  simp only [faults,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  by_cases hi : i.val+1 < n
  · change (¬ (encode hn f e a (nxt hn i) = encode hn f e a i * f i)) ↔ _
    rw [edge_internal hn f (encode hn f e a) i hi]
    change ¬ (gauge f (physical f _) (nxt hn i) = gauge f (physical f _) i) ↔ _
    rw [gauge_physical,switch_edge_internal _ _ hp hn e i hi]
    simp
  · have hi' : i.val+1 = n := by omega
    change (¬ (encode hn f e a (nxt hn i) = encode hn f e a i * f i)) ↔ _
    rw [edge_wrap hn f (encode hn f e a) i hi']
    change ¬ (gauge f (physical f _) (first hn) =
      gauge f (physical f _) i * (List.ofFn f).prod) ↔ _
    rw [gauge_physical,switch_edge_wrap _ _ hp hn e i hi']
    simp

theorem interval_const (hn : 0 < n) (e : Fin n) (y : Fin n → G)
    (hr : ∀ i : Fin n, i.val+1 < n → i ≠ e → y (nxt hn i) = y i)
    (i j : Fin n) (hij : i.val  ≤  j.val) (hne : ∀ k, i.val  ≤  k → k < j.val → k ≠ e.val) :
    y j = y i := by
  let D := j.val-i.val
  have hD : j.val = i.val+D := by omega
  have iter (d : ℕ) : ∀ hd : i.val+d < n, d  ≤  D → y ⟨i.val+d,hd⟩ = y i := by
    induction d with
    | zero => intro hd hl; rfl
    | succ d ih =>
      intro hd hl
      have hb : i.val+d < n := by omega
      let v : Fin n := ⟨i.val+d,hb⟩
      have hv : v ≠ e := by
        intro q
        have hEq : i.val+d=e.val := congrArg Fin.val q
        exact hne (i.val+d) (by omega) (by omega) hEq
      have hnxt : v.val+1 < n := by change i.val+d+1 < n; omega
      have hnext := hr v hnxt hv
      rw [nxt_internal hn v hnxt] at hnext
      change y ⟨i.val+(d+1),hd⟩ = y ⟨i.val+d,hb⟩ at hnext
      exact hnext.trans (ih hb (by omega))
  have q := iter D (by omega) (Nat.le_refl D)
  have ei : (⟨i.val+D,by omega⟩ : Fin n) = j := Fin.ext hD.symm
  rwa [ei] at q

theorem decode (hn : 0 < n) (f : Fin n → G) (x : Fin n → G) (e : Fin n)
    (he : faults hn f x = {e}) :
    encode hn f e (gauge f x (first hn)) = x := by
  let y := gauge f x
  let a := y (first hn)
  let P := (List.ofFn f).prod
  have clean : ∀ i : Fin n, i ≠ e → x (nxt hn i) = x i * f i := by
    intro i hi
    by_contra bad
    have h : i ∈ faults hn f x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,bad⟩
    rw [he, Finset.mem_singleton] at h
    exact hi h
  have inner : ∀ i : Fin n, i.val+1 < n → i ≠ e → y (nxt hn i) = y i :=
    fun i hj hi => (edge_internal hn f x i hj).mp (clean i hi)
  apply (show Function.Injective (gauge f) from fun u v h => by
    simpa only [physical_gauge] using congrArg (physical f) h)
  change gauge f (physical f (switch P a e)) = y
  rw [gauge_physical]
  funext j
  by_cases hj : j.val  ≤  e.val
  · change (if j.val  ≤  e.val then a else _) = y j
    rw [if_pos hj]
    exact (interval_const hn e y inner (first hn) j (Nat.zero_le _)
      (fun k hk hl h => by omega)).symm
  · let z : Fin n := ⟨n-1, by omega⟩
    have hz : z.val + 1 = n := by dsimp [z]; omega
    have hze : z ≠ e := fun h => hj (by have hv := congrArg Fin.val h; omega)
    have hwrap : a = y z * P := (edge_wrap hn f x z hz).mp (clean z hze)
    have hzval : y z = a * P⁻¹ := by rw [hwrap]; simp [mul_assoc]
    change (if j.val  ≤  e.val then a else _) = y j
    rw [if_neg hj, ← hzval]
    exact interval_const hn e y inner j z (by omega) (fun k hk hl h => by omega)

def privateWords (hn : 0 < n) (f : Fin n → G) : Finset (Fin n → G) :=
  Finset.univ.filter (fun x => (faults hn f x).card = 1)

theorem card_private (hn : 0 < n) (f : Fin n → G) (hp : (List.ofFn f).prod ≠ 1) :
    (privateWords hn f).card = n * Fintype.card G := by
  let W := privateWords hn f
  let enc : Fin n × G → W := fun p => ⟨encode hn f p.1 p.2, by
    simp [W,privateWords,faults_encode hn f hp]⟩
  have hinj : Function.Injective enc := by
    intro a b h
    have he : encode hn f a.1 a.2 = encode hn f b.1 b.2 := congrArg Subtype.val h
    have hset := congrArg (faults hn f) he
    rw [faults_encode hn f hp, faults_encode hn f hp,Finset.singleton_inj] at hset
    have hanchor := congrArg (fun x => gauge f x (first hn)) he
    change gauge f (physical f _) (first hn) = gauge f (physical f _) (first hn) at hanchor
    rw [gauge_physical,gauge_physical,switch_first,switch_first] at hanchor
    exact Prod.ext hset hanchor
  have hsurj : Function.Surjective enc := by
    intro w
    have hs : (faults hn f w.val).card = 1 := (Finset.mem_filter.mp w.property).2
    obtain ⟨e,he⟩ := Finset.card_eq_one.mp hs
    exact ⟨(e,gauge f w.val (first hn)),Subtype.ext (decode hn f w.val e he)⟩
  have hc := Fintype.card_congr (Equiv.ofBijective enc ⟨hinj,hsurj⟩)
  simpa [W,Fintype.card_coe,Fintype.card_prod] using hc.symm

end Count


section Anchor
variable {G : Type} [Group G] {n : Nat}

def rank (r i : Fin n) : Nat :=
  if r.val  ≤  i.val then i.val-r.val else n+i.val-r.val

def anchored (P a : G) (r e i : Fin n) : G :=
  switch P (if r.val  ≤  e.val then a else a*P) e i

theorem anchor_rank (P a : G) (r e i : Fin n) :
    anchored P a r e i =
      (if rank r i  ≤  rank r e then
        (if r.val  ≤  i.val then a else a*P)
      else (if r.val  ≤  i.val then a*P⁻¹ else a)) := by
  have hi := i.isLt; have he := e.isLt; have hr := r.isLt
  by_cases hc : rank r i  ≤  rank r e
  · rw [if_pos hc]
    unfold rank at hc
    unfold anchored switch
    by_cases hre : r.val  ≤  e.val <;> by_cases hri : r.val  ≤  i.val <;>
      by_cases hie : i.val  ≤  e.val <;>
        simp only [hre,hri,if_true,if_false] at hc <;>
        simp [hre,hri,hie,mul_assoc] <;> omega
  · rw [if_neg hc]
    unfold rank at hc
    unfold anchored switch
    by_cases hre : r.val  ≤  e.val <;> by_cases hri : r.val  ≤  i.val <;>
      by_cases hie : i.val  ≤  e.val <;>
        simp only [hre,hri,if_true,if_false] at hc <;>
        simp [hre,hri,hie,mul_assoc] <;> omega

theorem anchor_equality (P a : G) (hP : P ≠ 1) (r e₁ e₂ i : Fin n) :
    anchored P a r e₁ i = anchored P a r e₂ i ↔
      (rank r i  ≤  rank r e₁ ↔ rank r i  ≤  rank r e₂) := by
  rw [anchor_rank,anchor_rank]
  have hpos : a ≠ a*P := by
    have hh : P⁻¹ ≠ (1:G) := by simpa using hP
    simpa using switch_distinct P⁻¹ a hh
  have hneg := switch_distinct P a hP
  by_cases hri : r.val  ≤  i.val <;> by_cases h1 : rank r i  ≤  rank r e₁ <;>
    by_cases h2 : rank r i  ≤  rank r e₂ <;> simp [hri,h1,h2,hpos,hpos.symm,hneg,hneg.symm]

theorem anchor_read (P a : G) (r e : Fin n) : anchored P a r e r = a := by
  rw [anchor_rank]
  have h1 : rank r r = 0 := by simp [rank]
  simp [h1]

end Anchor


section Transcript
variable {X G : Type} [DecidableEq X] [DecidableEq G]

abbrev Strategy (X G : Type) [DecidableEq X] [DecidableEq G] :=
  List (Finset (X × G)) → Finset X

def answers (s : Finset X) (x : X → G) : Finset (X × G) :=
  s.image (fun i => (i,x i))

def history (ask : Strategy X G) (x : X → G) (t : Nat) :=
  (List.range t).foldl (fun hist _ => hist ++ [answers (ask hist) x]) []

theorem history_zero (ask : Strategy X G) (x : X → G) : history ask x 0 = [] := by
  rfl

theorem history_succ (ask : Strategy X G) (x : X → G) (t : Nat) :
    history ask x (t+1) = history ask x t ++ [answers (ask (history ask x t)) x] := by
  unfold history
  rw [List.range_succ,List.foldl_append]
  rfl

def seen (ask : Strategy X G) (x : X → G) (t : Nat) :=
  (Finset.range t).biUnion (fun i => ask (history ask x i))

theorem seen_zero (ask : Strategy X G) (x : X → G) : seen ask x 0 = ∅ := by
  simp [seen]

theorem seen_succ (ask : Strategy X G) (x : X → G) (t : Nat) :
    seen ask x (t+1) = seen ask x t ∪ ask (history ask x t) := by
  ext i
  simp only [seen,Finset.mem_biUnion,Finset.mem_range,Finset.mem_union]
  constructor
  · intro h; obtain ⟨j,hj,hm⟩ := h
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hl | he
    · exact Or.inl ⟨j,hl,hm⟩
    · exact Or.inr (he ▸ hm)
  · intro h; rcases h with ⟨j,hj,hm⟩ | hm
    · exact ⟨j,by omega,hm⟩
    · exact ⟨t,by omega,hm⟩

theorem answers_eq (s : Finset X) (x y : X → G) :
    answers s x = answers s y ↔ ∀ i ∈ s, x i = y i := by
  constructor
  · intro h i hi
    have hx : (i,x i) ∈ answers s x := Finset.mem_image.mpr ⟨i,hi,rfl⟩
    rw [h] at hx
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hx
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    change j=i at h₁; change y j = x i at h₂
    simpa [h₁] using h₂.symm
  · intro h
    ext p
    simp only [answers,Finset.mem_image]
    constructor
    · rintro ⟨i,hi,e⟩
      exact ⟨i,hi,by simpa [← h i hi] using e⟩
    · rintro ⟨i,hi,e⟩
      exact ⟨i,hi,by simpa [h i hi] using e⟩

theorem history_length (ask : Strategy X G) (x : X → G) (t : Nat) :
    (history ask x t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [history_succ,ih]

theorem prefix_last {A : Type} (p q : List A) (hp : p.length = q.length) (a b : A) :
    p ++ [a] = q ++ [b] ↔ p=q ∧ a=b := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => simp
    | cons _ _ => simp at hp
  | cons x p ih =>
    cases q with
    | nil => simp at hp
    | cons y q =>
      simp only [List.cons_append,List.cons.injEq]
      have h : p.length=q.length := by simpa using hp
      rw [ih q h]; tauto

theorem history_eq_seen (ask : Strategy X G) (x y : X → G) (t : Nat) :
    history ask x t = history ask y t ↔ ∀ i ∈ seen ask x t, x i = y i := by
  induction t with
  | zero => simp [history_zero,seen_zero]
  | succ t ih =>
    rw [history_succ,history_succ,prefix_last _ _ (by simp [history_length]),seen_succ]
    constructor
    · rintro ⟨h,e⟩ i hi
      rcases Finset.mem_union.mp hi with hpre|hnow
      · exact ih.mp h i hpre
      · have ee : answers (ask (history ask x t)) x = answers (ask (history ask x t)) y := by
          simpa [← h] using e
        exact (answers_eq _ _ _).mp ee i hnow
    · intro h
      have pre : history ask x t = history ask y t := ih.mpr (fun i hi => h i (Finset.mem_union_left _ hi))
      refine ⟨pre,?_⟩
      rw [← pre]
      exact (answers_eq _ _ _).mpr (fun i hi => h i (Finset.mem_union_right _ hi))

end Transcript


section Ranked
variable {n : Nat}

theorem rank_lt (r i : Fin n) : rank r i < n := by
  have hr := r.isLt; have hi := i.isLt
  unfold rank; split <;> omega

theorem rank_self (r : Fin n) : rank r r = 0 := by simp [rank]

def rotate (r k : Fin n) : Fin n :=
  if h : r.val+k.val<n then ⟨r.val+k.val,h⟩ else ⟨r.val+k.val-n,by have := r.isLt; have := k.isLt; omega⟩

theorem rank_rotate (r k : Fin n) : rank r (rotate r k) = k.val := by
  have hr := r.isLt; have hk := k.isLt
  unfold rotate
  split
  · rename_i h
    change rank r ⟨r.val+k.val,h⟩ = k.val
    unfold rank
    have he : r.val  ≤  r.val+k.val := by omega
    rw [if_pos he]
    change r.val+k.val-r.val=k.val
    omega
  · rename_i h
    unfold rank
    have he : ¬ r.val  ≤  r.val+k.val-n := by omega
    change (if r.val  ≤  r.val+k.val-n then _ else _) = k.val
    rw [if_neg he]
    change n+(r.val+k.val-n)-r.val=k.val
    omega

theorem rank_inj (r : Fin n) : Function.Injective (rank r) := by
  intro a b h
  have hr := r.isLt; have ha := a.isLt; have hb := b.isLt
  apply Fin.ext
  unfold rank at h
  split at h <;> split at h <;> omega

theorem rank_next (hn : 0 < n) (r e : Fin n) :
    rank r (nxt hn e) = (rank r e+1)%n := by
  have hr := r.isLt; have he := e.isLt; have h := rank_lt r e
  by_cases h1 : e.val+1<n
  · rw [nxt_internal hn e h1]
    unfold rank
    by_cases h2 : r.val  ≤  e.val
    · have h3 : r.val  ≤  e.val+1 := by omega
      simp only [Fin.val_mk,if_pos h2,if_pos h3]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · by_cases h3 : r.val  ≤  e.val+1
      · have hh : n+e.val-r.val+1=n := by omega
        simp only [Fin.val_mk,if_neg h2,if_pos h3,hh,Nat.mod_self]
        omega
      · simp only [Fin.val_mk,if_neg h2,if_neg h3]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
  · have h1' : e.val+1=n := by omega
    rw [nxt_wrap hn e h1']
    change rank r ⟨0,hn⟩ = _
    unfold rank
    have h2 : r.val  ≤  e.val := by omega
    simp only [Fin.val_mk,if_pos h2,Nat.add_zero]
    by_cases h0 : r.val ≤ 0
    · have hh : e.val-r.val+1=n := by omega
      rw [if_pos h0,hh,Nat.mod_self,Nat.zero_sub]
    · rw [if_neg h0,Nat.mod_eq_of_lt (by omega)]
      omega

end Ranked

section Physical
variable {G : Type} [Group G] [Fintype G] [DecidableEq G] {n : Nat}

def physicalAnchored (f : Fin n → G) (a : G) (r e : Fin n) : Fin n → G :=
   physical f (anchored (List.ofFn f).prod a r e)

theorem physicalAnchored_eq (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (a : G) (r e₁ e₂ i : Fin n) :
    physicalAnchored f a r e₁ i = physicalAnchored f a r e₂ i ↔
      (rank r i  ≤  rank r e₁ ↔ rank r i  ≤  rank r e₂) := by
  unfold physicalAnchored physical
  simpa only [mul_right_cancel_iff] using anchor_equality _ a hP r e₁ e₂ i

theorem physical_faults (hn : 0<n) (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (a : G) (r e : Fin n) : faults hn f (physicalAnchored f a r e) = {e} := by
  exact faults_encode hn f hP e _

theorem physical_history_eq (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (a : G) (r e₁ e₂ : Fin n) (ask : Strategy (Fin n) G) (t : Nat) :
    history ask (physicalAnchored f a r e₁) t = history ask (physicalAnchored f a r e₂) t ↔
      ∀ i ∈ seen ask (physicalAnchored f a r e₁) t,
          (rank r i  ≤  rank r e₁ ↔ rank r i  ≤  rank r e₂) := by
  rw [history_eq_seen]
  constructor <;> intro h i hi
  · exact (physicalAnchored_eq f hP a r e₁ e₂ i).mp (h i hi)
  · exact (physicalAnchored_eq f hP a r e₁ e₂ i).mpr (h i hi)

theorem thresholds_singleton (hn : 0<n) (r e : Fin n) (S : Finset (Fin n)) (hr : r∈S) :
    (e∈S ∧ nxt hn e ∈ S) ↔
      ∀ v : Fin n, (∀ i ∈ S, (rank r i  ≤  rank r e ↔ rank r i  ≤  rank r v)) → v = e := by
  have he := rank_lt r e
  constructor
  · intro h v hv
    apply rank_inj r
    have hva := (hv e h.1).mp (Nat.le_refl _)
    have hb := hv (nxt hn e) h.2
    rw [rank_next hn] at hb
    by_cases hs : rank r e+1<n
    · rw [Nat.mod_eq_of_lt hs] at hb
      by_contra hne
      exact (by omega : ¬ rank r e+1  ≤  rank r e) (hb.mpr (by omega))
    · have hvn := rank_lt r v; omega
  · intro h
    constructor
    · by_contra hnot
      have hzero : rank r e ≠ 0 := by
        intro hz
        have hh : e = r := rank_inj r (hz.trans (rank_self r).symm)
        exact hnot (hh.symm ▸ hr)
      let v : Fin n := rotate r ⟨rank r e-1, by omega⟩
      have hv : rank r v=rank r e-1 := rank_rotate _ _
      have hneq : v ≠ e := fun h => by
        have hz : rank r v=rank r e := congrArg (rank r) h
        omega
      apply hneq
      apply h
      intro i hi
      rw [hv]
      have hne : rank r i ≠ rank r e := fun he => hnot (rank_inj r he ▸ hi)
      omega
    · by_contra hnot
      have hbound : rank r e+1<n := by
        by_contra hne
        have heq : rank r e+1=n := by omega
        have hnr : rank r (nxt hn e)=rank r r := by rw [rank_next hn,heq,Nat.mod_self,rank_self]
        have hrr : nxt hn e = r := rank_inj r hnr
        exact hnot (hrr.symm ▸ hr)
      let v : Fin n := rotate r ⟨rank r e+1,hbound⟩
      have hv : rank r v=rank r e+1 := rank_rotate _ _
      have hneq : v ≠ e := fun h => by
        have hz : rank r v=rank r e := congrArg (rank r) h
        omega
      apply hneq
      apply h
      intro i hi
      rw [hv]
      have hnrank : rank r (nxt hn e)=rank r e+1 := by rw [rank_next hn,Nat.mod_eq_of_lt hbound]
      have hne : rank r i ≠ rank r e+1 := fun he => hnot (rank_inj r (he.trans hnrank.symm) ▸ hi)
      omega

end Physical



def price (bs : List Nat) := bs.foldr
    (fun k (p : Nat × Nat) => ((k+1)*p.1, max (k*p.1) p.2)) (1,0)

def product (bs : List Nat) := (bs.map (fun k => k+1)).prod

theorem product_zero : product [] = 1 := rfl
theorem product_succ (k : Nat) (ks : List Nat) : product (k::ks) = (k+1)*product ks := rfl

theorem price_fst (bs : List Nat) : (price bs).1 = product bs := by
  induction bs with
  | nil => rfl
  | cons k bs ih =>
    change (k+1)*(price bs).1 = (k+1)*product bs
    rw [ih]

theorem product_pos (bs : List Nat) : 0 < product bs := by
  induction bs with
  | nil => decide
  | cons k bs ih => exact Nat.mul_pos (Nat.succ_pos _) ih

theorem price_snd (k : Nat) (bs : List Nat) :
    (price (k::bs)).2 = max (k*product bs) (price bs).2 := by
  change max (k*(price bs).1) (price bs).2 = _
  rw [price_fst]

theorem attainable_max (bs : List Nat) :
    (price bs).2 = 0 ∨
      ∃ (pref : List Nat) (k : Nat) (tail : List Nat), 0 < k ∧
        bs = pref ++ k::tail ∧ (price bs).2 = k*product tail := by
  induction bs with
  | nil => exact Or.inl rfl
  | cons k bs ih =>
    rw [price_snd]
    by_cases hh : k*product bs ≥ (price bs).2
    · rw [Nat.max_eq_left hh]
      cases k with
      | zero => exact Or.inl (by simp)
      | succ k => exact Or.inr ⟨[],k+1,bs,Nat.succ_pos _,rfl,rfl⟩
    · rw [Nat.max_eq_right (by omega)]
      rcases ih with h|⟨pref,k',tail,hpos,he,hp⟩
      · exact Or.inl h
      · exact Or.inr ⟨k::pref,k',tail,hpos,congrArg (List.cons k) he,hp⟩

theorem split_budget_le (pref : List Nat) (k : Nat) (tail : List Nat) :
    k*product tail  ≤  (price (pref ++ k::tail)).2 := by
  induction pref with
  | nil => rw [List.nil_append,price_snd]; exact Nat.le_max_left _ _
  | cons a l ih =>
    simp only [List.cons_append,price_snd]
    exact Nat.le_trans ih (Nat.le_max_right _ _)

def capped (n B : Nat) := if n  ≤  B then n else B-1

theorem capped_le (n B : Nat) : capped n B  ≤  n := by
  unfold capped; split <;> omega

theorem capped_mono_right {n A B : Nat} (h : A  ≤  B) :
    capped n A  ≤  capped n B := by
  unfold capped; split <;> split <;> omega

theorem loss_at_least_one {n B s : Nat} (hs : s  ≤  n) (hb : s  ≤  B) (h : s=B → n ≤ B) :
    s  ≤  capped n B := by
  unfold capped; split
  · exact hs
  · by_cases hB : B=0
    · omega
    · by_cases hh : s=B
      · have q := h hh; omega
      · omega


def total (l : List Nat) : Nat := l.foldr (· + ·) 0

def weights (t : List (Nat × Nat)) : Nat := total (t.map Prod.fst)

def hits (t : List (Nat × Nat)) : Nat := total (t.map Prod.snd)

theorem total_length_mul_of_le (k : Nat) (l : List Nat) (h : ∀ b ∈ l, b  ≤  k) :
    total l  ≤  l.length*k := by
  induction l with
  | nil => simp [total,weights,hits]
  | cons x xs ih =>
    have hhead := h x (by simp)
    have htail := ih (fun b hb => h b (by simp [hb]))
    change x + total xs  ≤  (xs.length+1)*k
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem total_eq_mul_of_le (k : Nat) (l : List Nat) (h : ∀ b ∈ l, b  ≤  k)
    (he : total l = l.length*k) : ∀ b ∈ l, b = k := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hhead := h x (by simp)
    have htail : ∀ b ∈ xs, b  ≤  k := fun b hb => h b (by simp [hb])
    have hsum := total_length_mul_of_le k xs htail
    change x + total xs = (xs.length+1)*k at he
    rw [Nat.add_mul, Nat.one_mul] at he
    have hx : x=k := by omega
    have hv : total xs=xs.length*k := by omega
    intro b hb
    rcases List.mem_cons.mp hb with h|h
    · exact h.trans hx
    · exact ih htail hv b h

theorem hits_ge_of_weight (t : List (Nat × Nat)) (h : ∀ p ∈ t, p.1  ≤  p.2) :
    weights t  ≤  hits t := by
  induction t with
  | nil => simp [total,weights,hits]
  | cons p ps ih =>
    have h1 := h p (by simp)
    have h2 := ih (fun q hq => h q (by simp [hq]))
    change p.1+weights ps  ≤  p.2+hits ps
    omega

theorem hits_le_of_weight (t : List (Nat × Nat)) (h : ∀ p ∈ t, p.2  ≤  p.1) :
    hits t  ≤  weights t := by
  induction t with
  | nil => simp [total,weights,hits]
  | cons p ps ih =>
    have h1 := h p (by simp)
    have h2 := ih (fun q hq => h q (by simp [hq]))
    change p.2+hits ps  ≤  p.1+weights ps
    omega

inductive IntervalTree : List Nat → Nat → Nat → Prop
  | leaf (n : Nat) : IntervalTree [] n (if n = 1 then 1 else 0)
  | node (k : Nat) (ks : List Nat) (parts : List (Nat × Nat))
      (sizes : parts.length  ≤  k+1) (valid : ∀ p ∈ parts, IntervalTree ks p.1 p.2) :
      IntervalTree (k::ks) (weights parts) (hits parts)

theorem interval_tree_bounds (bs : List Nat) : ∀ n s, IntervalTree bs n s →
    s  ≤  n ∧ s  ≤  product bs ∧ (s = product bs → n  ≤  product bs) := by
  induction bs with
  | nil =>
    intro n s ht
    cases ht with
    | leaf n =>
      by_cases h : n=1 <;> simp [product_zero,h]
  | cons k bs ih =>
    intro n s ht
    cases ht with
    | node _ _ parts hlen hsub =>
      have hb (p : Nat × Nat) (hp : p ∈ parts) :=
        ih p.1 p.2 (hsub p hp)
      have hm : ∀ b ∈ parts.map Prod.snd, b  ≤  product bs := by
        intro b h
        obtain ⟨p,hp,he⟩ := List.mem_map.mp h
        subst b; exact (hb p hp).2.1
      have hsum : hits parts  ≤  parts.length*product bs := by
        simpa [hits] using total_length_mul_of_le (product bs) _ hm
      have hmon := Nat.mul_le_mul_right (product bs) hlen
      refine ⟨hits_le_of_weight parts (fun p hp => (hb p hp).1),?_,?_⟩
      · exact Nat.le_trans hsum hmon
      · intro he
        have hes : hits parts = parts.length*product bs := by
          rw [product_succ] at he
          omega
        have hp := total_eq_mul_of_le (product bs) _ hm (by simpa [hits] using hes)
        have hwp : ∀ p ∈ parts, p.1  ≤  p.2 := by
          intro p hh
          have eq : p.2 = product bs := hp p.2 (List.mem_map.mpr ⟨p,hh,rfl⟩)
          exact eq ▸ (hb p hh).2.2 eq
        exact Nat.le_trans (hits_ge_of_weight parts hwp) (Nat.le_of_eq he)

theorem interval_tree_capped {bs : List Nat} {n s : Nat} (h : IntervalTree bs n s) :
    s  ≤  capped n (product bs) := by
  have u := interval_tree_bounds _ _ _ h
  exact loss_at_least_one u.1 u.2.1 u.2.2

theorem cycle_tree_bounds (k : Nat) (bs : List Nat) (parts : List (Nat × Nat))
    (hlen : parts.length  ≤  k) (hsub : ∀ p ∈ parts, IntervalTree bs p.1 p.2) :
    hits parts  ≤  capped (weights parts) (k*product bs) := by
  have hb p hp := interval_tree_bounds bs p.1 p.2 (hsub p hp)
  have hm : ∀ b ∈ parts.map Prod.snd, b  ≤  product bs := by
    intro b h
    obtain ⟨p,hp,he⟩ := List.mem_map.mp h
    subst b; exact (hb p hp).2.1
  have hsum : hits parts  ≤  parts.length*product bs := by
    simpa [hits] using total_length_mul_of_le (product bs) _ hm
  have hmon := Nat.mul_le_mul_right (product bs) hlen
  apply loss_at_least_one (hits_le_of_weight _ (fun p hp => (hb p hp).1)) (Nat.le_trans hsum hmon)
  intro he
  have hes : hits parts = parts.length*product bs := by omega
  have hp := total_eq_mul_of_le (product bs) _ hm (by simpa [hits] using hes)
  have hwp : ∀ p ∈ parts, p.1  ≤  p.2 := by
    intro p hh
    have eq : p.2 = product bs := hp p.2 (List.mem_map.mpr ⟨p,hh,rfl⟩)
    exact eq ▸ (hb p hh).2.2 eq
  exact Nat.le_trans (hits_ge_of_weight parts hwp) (Nat.le_of_eq he)


theorem capped_zero (B : Nat) : capped 0 B = 0 := by simp [capped]

def greedy (q : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | 1, h => [(h,capped h q)]
  | slots+2, h =>
    (min h q, capped (min h q) q) :: greedy q (slots+1) (h-min h q)

theorem greedy_length (q s n : Nat) (hs : 0<s) : (greedy q s n).length = s := by
  induction s generalizing n with
  | zero => omega
  | succ s ih =>
    cases s with
    | zero => rfl
    | succ s =>
      change (greedy q (s+1) (n-min n q)).length+1 = s+2
      rw [ih _ (Nat.succ_pos _)]

theorem greedy_valid (q s n : Nat) :
    ∀ p ∈ greedy q s n, p.2 = capped p.1 q := by
  induction s generalizing n with
  | zero => simp [greedy]
  | succ s ih =>
    cases s with
    | zero => simp [greedy]
    | succ s =>
      intro a ha
      change a ∈ ((min n q, capped (min n q) q) :: greedy q (s+1) (n-min n q)) at ha
      rcases List.mem_cons.mp ha with he|he
      · subst a; rfl
      · exact ih _ a he

theorem greedy_weights (q s n : Nat) (hs : 0<s) : weights (greedy q s n) = n := by
  induction s generalizing n with
  | zero => omega
  | succ s ih =>
    cases s with
    | zero => simp [greedy,weights,total]
    | succ s =>
      change min n q + weights (greedy q (s+1) (n-min n q)) = n
      rw [ih _ (Nat.succ_pos _)]
      omega

theorem greedy_hits (q s n : Nat) (hq : 0<q) (hs : 0<s) :
    hits (greedy q s n) = capped n (s*q) := by
  induction s generalizing n with
  | zero => omega
  | succ s ih =>
    cases s with
    | zero => simp [greedy,hits,total]
    | succ s =>
      let r := (s+1)*q
      have hr : 0<r := Nat.mul_pos (Nat.succ_pos _) hq
      change capped (min n q) q + hits (greedy q (s+1) (n-min n q)) = capped n ((s+2)*q)
      rw [ih _ (Nat.succ_pos _)]
      rw [show (s+2)*q = (s+1)*q+q from Nat.succ_mul _ _]
      change capped (min n q) q + capped (n - min n q) r = capped n (r+q)
      have hm : capped (min n q) q = min n q := by
        unfold capped
        rw [if_pos (Nat.min_le_right _ _)]
      rw [hm]
      by_cases hn : n  ≤  q
      · rw [Nat.min_eq_left hn, Nat.sub_self, capped_zero]
        unfold capped
        rw [if_pos (by omega),Nat.add_zero]
      · rw [Nat.min_eq_right (by omega)]
        unfold capped
        by_cases h : n - q  ≤  r
        · rw [if_pos h, if_pos (by omega)]; omega
        · rw [if_neg h, if_neg (by omega)]; omega

theorem interval_attainable (bs : List Nat) (n : Nat) :
    IntervalTree bs n (capped n (product bs)) := by
  induction bs generalizing n with
  | nil =>
    suffices h : (if n=1 then 1 else 0) = capped n 1 by
      rw [product_zero,← h]
      exact .leaf n
    unfold capped
    by_cases h1 : n = 1
    · simp [h1]
    · have h0 : (n  ≤  1) → n=0 := by omega
      by_cases h : n ≤ 1
      · rw [if_neg h1, if_pos h]; exact (h0 h).symm
      · rw [if_neg h1, if_neg h]
  | cons k bs ih =>
    let q := product bs
    let parts := greedy q (k+1) n
    have hlen : parts.length  ≤  k+1 := Nat.le_of_eq (greedy_length q _ _ (Nat.succ_pos _))
    have htree : IntervalTree (k::bs) (weights parts) (hits parts) :=
      .node k bs parts hlen (by
        intro p hp
        rw [greedy_valid q _ _ p hp]
        exact ih p.1)
    rw [greedy_weights q _ _ (Nat.succ_pos _),greedy_hits q _ _ (product_pos bs) (Nat.succ_pos _)] at htree
    exact htree

theorem cycle_attainable (k : Nat) (bs : List Nat) (n : Nat) (hk : 0<k) :
    ∃ parts : List (Nat × Nat),
      parts.length = k ∧ weights parts = n ∧ hits parts = capped n (k*product bs) ∧
      ∀ p ∈ parts, IntervalTree bs p.1 p.2 := by
  let q := product bs
  let parts := greedy q k n
  refine ⟨parts,greedy_length q k n hk,greedy_weights q k n hk,
    greedy_hits q k n (product_pos bs) hk,?_⟩
  intro p hp
  rw [greedy_valid q k n p hp]
  exact interval_attainable bs p.1


def floorBy (d p : Nat) : Nat := (d/p)*p

theorem floorBy_le (d p : Nat) : floorBy d p  ≤  d := by
  unfold floorBy
  rw [Nat.mul_comm]
  exact Nat.mul_div_le _ _

theorem floorBy_ge {d p j : Nat} (hp : 0<p) (hj : j*p ≤ d) : j*p  ≤  floorBy d p := by
  exact Nat.mul_le_mul_right p ((Nat.le_div_iff_mul_le hp).mpr hj)

theorem floorBy_splt (d k p : Nat) :
    floorBy d p = floorBy d ((k+1)*p) + (d/p % (k+1))*p := by
  have h := Nat.div_add_mod' (d/p) (k+1)
  have eq : (d/p)/(k+1) = d/((k+1)*p) := by
    rw [Nat.div_div_eq_div_mul,Nat.mul_comm p]
  rw [eq] at h
  unfold floorBy
  rw [← Nat.mul_assoc,← Nat.add_mul,h]

theorem floorBy_lt_next {d p : Nat} (hp : 0<p) : d < floorBy d p+p := by
  have h := Nat.div_add_mod' d p
  have h' := Nat.mod_lt d hp
  unfold floorBy
  omega

theorem floorBy_block_le (d k p : Nat) : floorBy d ((k+1)*p)  ≤  floorBy d p := by
  rw [floorBy_splt d k p]
  omega

theorem product_drop_split (bs : List Nat) (t : Nat) (h : t<bs.length) :
    product (bs.drop t) = (bs.get ⟨t,h⟩+1)*product (bs.drop (t+1)) := by
  rw [List.drop_eq_getElem_cons h]
  rfl

theorem product_drop_end (bs : List Nat) : product (bs.drop bs.length) = 1 := by
  rw [List.drop_length]; rfl

theorem trim_cmp (B x d : Nat) (hx : x<B) :
    (x ≤ d ↔ x ≤ min d (B-1)) := by omega

theorem capped_interval (n B : Nat) (hB : 0<B) :
    (if n ≤ B then n else B-1)  ≤  n := by split <;> omega


section Upper
variable {G : Type} [Group G] [Fintype G] [DecidableEq G] {n : Nat}

def comparisonCount (r e : Fin n) (Q : Finset (Fin n)) : Nat :=
  (Q.filter (fun i => rank r i  ≤  rank r e)).card

theorem comparison_le (r e : Fin n) (Q : Finset (Fin n)) :
    comparisonCount r e Q  ≤  Q.card := Finset.card_filter_le _ _

theorem comparison_pos (r e : Fin n) (Q : Finset (Fin n)) (hr : r∈Q) :
    0 < comparisonCount r e Q := by
  apply Finset.card_pos.mpr
  exact ⟨r,Finset.mem_filter.mpr ⟨hr,by simp [rank_self]⟩⟩

theorem comparison_iff (r e v : Fin n) (Q : Finset (Fin n)) :
    comparisonCount r e Q = comparisonCount r v Q ↔
      ∀ i∈Q, (rank r i  ≤  rank r e ↔ rank r i  ≤  rank r v) := by
  unfold comparisonCount
  constructor
  · intro he
    have h' : Q.filter (fun i => rank r i  ≤  rank r e) = Q.filter (fun i => rank r i  ≤  rank r v) := by
      rcases le_total (rank r e) (rank r v) with h|h
      · exact Finset.eq_of_subset_of_card_le (fun i hi =>
          let H := Finset.mem_filter.mp hi
          Finset.mem_filter.mpr ⟨H.1,Nat.le_trans H.2 h⟩) he.symm.le
      · symm
        exact Finset.eq_of_subset_of_card_le (fun i hi =>
          let H := Finset.mem_filter.mp hi
          Finset.mem_filter.mpr ⟨H.1,Nat.le_trans H.2 h⟩) he.le
    intro i hi
    have eq := congrArg (fun u : Finset (Fin n) => i ∈ u) h'
    simpa [hi] using (Iff.of_eq eq)
  · intro h
    congr 1
    ext i
    simp only [Finset.mem_filter]
    constructor <;> intro p
    · exact ⟨p.1,(h i p.1).mp p.2⟩
    · exact ⟨p.1,(h i p.1).mpr p.2⟩

def discovered (hn : 0<n) (f : Fin n → G) (a : G) (r : Fin n) (ask : Strategy (Fin n) G)
    (t : Nat) (e : Fin n) : Prop :=
  e ∈ seen ask (physicalAnchored f a r e) t ∧
  nxt hn e ∈ seen ask (physicalAnchored f a r e) t

instance discoveredDecidable (hn : 0<n) (f : Fin n → G) (a : G) (r : Fin n)
    (ask : Strategy (Fin n) G) (t : Nat) : DecidablePred (discovered hn f a r ask t) :=
  fun e => inferInstanceAs (Decidable (e ∈ seen ask (physicalAnchored f a r e) t ∧
    nxt hn e ∈ seen ask (physicalAnchored f a r e) t))

def Bounds (M S P : Nat) : Prop :=
  S  ≤  M ∧ S  ≤  P ∧ (S=P → M ≤ P)

theorem bounds_zero (P : Nat) : Bounds 0 0 P := by
  exact ⟨Nat.le_refl _,Nat.zero_le _,fun _ => Nat.zero_le _⟩

theorem bounds_sum {K : Type} (I : Finset K) (M S : K → Nat) (C P : Nat)
    (hI : I.card ≤ C) (h : ∀ i∈I, Bounds (M i) (S i) P) :
    Bounds (∑i ∈ I, M i) (∑i ∈ I, S i) (C*P) := by
  have ha : (∑i∈I,S i)  ≤  ∑i∈I,M i := Finset.sum_le_sum fun i hi => (h i hi).1
  have hb : (∑i∈I,S i)  ≤  ∑_i∈I,P := Finset.sum_le_sum fun i hi => (h i hi).2.1
  have hc : (∑_i∈I,P)  ≤  C*P := by
    simp
    exact Nat.mul_le_mul_right P hI
  refine ⟨ha,Nat.le_trans hb hc,?_⟩
  intro he
  have hs : (∑i∈I,S i) = ∑_i∈I,P := by omega
  have hd : ∀ i∈I, S i = P :=
    (Finset.sum_eq_sum_iff_of_le (fun i hi => (h i hi).2.1)).mp hs
  have hf : (∑i∈I,M i)  ≤  ∑i∈I,S i := Finset.sum_le_sum fun i hi => by
    rw [hd i hi]
    exact (h i hi).2.2 (hd i hi)
  exact Nat.le_trans hf (Nat.le_of_eq he)

theorem bounds_partition {K : Type} [DecidableEq K] (φ : Fin n → K) (I : Finset K)
    (V : Finset (Fin n)) (p : Fin n → Prop) [DecidablePred p]
    (C P : Nat) (hi : I.card ≤ C)
    (maps : ∀ v∈V, φ v∈I)
    (h : ∀ j∈I, Bounds (V.filter (fun v => φ v=j)).card
      ((V.filter (fun v => φ v=j)).filter p).card P) :
    Bounds V.card (V.filter p).card (C*P) := by
  have h₁ := Finset.card_eq_sum_card_fiberwise (f:=φ) (s:=V) (t:=I)
    (fun x hx => maps x hx)
  have h₂ := Finset.card_eq_sum_card_fiberwise (f:=φ) (s:=V.filter p) (t:=I)
    (fun x hx => maps x (Finset.mem_filter.mp hx).1)
  have hcomm (i : K) : ((V.filter p).filter (fun v => φ v=i)) =
      ((V.filter (fun v => φ v=i)).filter p) := by
    ext x
    simp only [Finset.mem_filter]
    tauto
  rw [h₁,h₂]; simp_rw [hcomm]
  exact bounds_sum I _ _ C P hi h

theorem discovered_terminal (hn : 0<n) (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (a : G) (r : Fin n) (ask : Strategy (Fin n) G) (t : Nat) (V : Finset (Fin n))
    (h : ∀ e∈V, ∀ v∈V, history ask (physicalAnchored f a r e) t =
      history ask (physicalAnchored f a r v) t)
    (hr : ∀ e∈V, r∈seen ask (physicalAnchored f a r e) t) :
    Bounds V.card (V.filter (discovered hn f a r ask t)).card 1 := by
  have hs := Finset.card_filter_le (s:=V) (p:=discovered hn f a r ask t)
  refine ⟨hs,?_,?_⟩
  · by_cases hpos : 0 < (V.filter (discovered hn f a r ask t)).card
    · obtain ⟨e,he⟩ := Finset.card_pos.mp hpos
      obtain ⟨heV,heD⟩ := Finset.mem_filter.mp he
      have hsingle : V ⊆ {e} := by
        intro v hv
        apply Finset.mem_singleton.mpr
        apply (thresholds_singleton hn r e _ (hr e heV)).mp heD
        exact (physical_history_eq f hP a r e v ask t).mp (h e heV v hv)
      have hbound := Finset.card_le_card hsingle
      simpa using hs.trans hbound
    · omega
  · intro he
    obtain ⟨e,he'⟩ := Finset.card_pos.mp (by omega : 0 < (V.filter (discovered hn f a r ask t)).card)
    obtain ⟨heV,heD⟩ := Finset.mem_filter.mp he'
    have hsingle : V ⊆ {e} := by
      intro v hv
      apply Finset.mem_singleton.mpr
      apply (thresholds_singleton hn r e _ (hr e heV)).mp heD
      exact (physical_history_eq f hP a r e v ask t).mp (h e heV v hv)
    simpa using Finset.card_le_card hsingle

theorem common_next (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (a : G) (r e v : Fin n) (ask : Strategy (Fin n) G) (t : Nat) (Q : Finset (Fin n))
    (h : history ask (physicalAnchored f a r e) t = history ask (physicalAnchored f a r v) t)
    (hQ : ask (history ask (physicalAnchored f a r e) t)=Q)
    (hc : comparisonCount r e Q = comparisonCount r v Q) :
    history ask (physicalAnchored f a r e) (t+1) = history ask (physicalAnchored f a r v) (t+1) := by
  have ha : answers Q (physicalAnchored f a r e) = answers Q (physicalAnchored f a r v) := by
    apply (answers_eq Q _ _).mpr
    intro i hi
    exact (physicalAnchored_eq f hP a r e v i).mpr ((comparison_iff r e v Q).mp hc i hi)
  simp only [history_succ,← h,hQ,ha]

theorem branch_bound (hn : 0<n) (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (a : G) (r : Fin n) (ask : Strategy (Fin n) G) (bs : List Nat) :
    ∀ (t : Nat) (V : Finset (Fin n)),
    (∀ e∈V, ∀ v∈V, history ask (physicalAnchored f a r e) t =
      history ask (physicalAnchored f a r v) t) →
    (∀ e∈V, r∈seen ask (physicalAnchored f a r e) t) →
    (∀ (j : Fin bs.length) (e : Fin n), (ask (history ask (physicalAnchored f a r e) (t+j.val))).card  ≤  bs.get j) →
    Bounds V.card (V.filter (discovered hn f a r ask (t+bs.length))).card (product bs) := by
  induction bs with
  | nil =>
    intro t V h hr _
    exact discovered_terminal hn f hP a r ask t V h hr
  | cons k ks ih =>
    intro t V h hr legal
    by_cases hV : V.Nonempty
    · obtain ⟨e₀,he₀⟩ := hV
      let Q := ask (history ask (physicalAnchored f a r e₀) t)
      let φ := fun e => comparisonCount r e Q
      let I := Finset.range (k+1)
      have hcQ : Q.card  ≤  k := by
        have hj := legal ⟨0,by simp⟩ e₀
        change (ask (history ask (physicalAnchored f a r e₀) t)).card ≤ k at hj
        exact hj
      have hcard : I.card ≤ k+1 := by simp [I]
      have hmaps : ∀ e∈V, φ e∈I := by
        intro e he
        have q := comparison_le r e Q
        simp only [I,Finset.mem_range,φ]; omega
      rw [product_succ]
      apply bounds_partition φ I V _ (k+1) (product ks) hcard hmaps
      intro i hi
      let W := V.filter (fun e => φ e=i)
      have hsame : ∀ e∈W, ∀ v∈W, history ask (physicalAnchored f a r e) (t+1)=
        history ask (physicalAnchored f a r v) (t+1) := by
        intro e he v hv
        obtain ⟨hev,hφ⟩ := Finset.mem_filter.mp he
        obtain ⟨hvv,hφ'⟩ := Finset.mem_filter.mp hv
        exact common_next f hP a r e v ask t Q (h e hev v hvv)
          (congrArg ask (h e hev e₀ he₀)) (hφ.trans hφ'.symm)
      have hanchor : ∀ e∈W, r∈seen ask (physicalAnchored f a r e) (t+1) := by
        intro e he
        rw [seen_succ]
        exact Finset.mem_union_left _ (hr e (Finset.mem_filter.mp he).1)
      have hleg : ∀ (j : Fin ks.length) (e : Fin n),
          (ask (history ask (physicalAnchored f a r e) ((t+1)+j.val))).card  ≤  ks.get j := by
        intro j e
        have q := legal j.succ e
        rw [List.get_cons_succ'] at q
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using q
      have hb := ih (t+1) W hsame hanchor hleg
      simpa [W,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hb
    · have hz : V=∅ := Finset.not_nonempty_iff_eq_empty.mp hV
      simpa [hz] using bounds_zero (product (k::ks))

end Upper


section Boot
variable {G : Type} [Group G] [Fintype G] [DecidableEq G] {n : Nat}

theorem boot_bound (hn : 0<n) (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (a : G) (r : Fin n) (ask : Strategy (Fin n) G)
    (t k : Nat) (ks : List Nat) (Q : Finset (Fin n))
    (h : ∀ x : Fin n → G, history ask x t = List.replicate t ∅)
    (hQ : ask (List.replicate t ∅)=Q) (hr : r∈Q) (hcQ : Q.card ≤ k)
    (legal : ∀ (j : Fin ks.length) (e : Fin n),
      (ask (history ask (physicalAnchored f a r e) ((t+1)+j.val))).card  ≤  ks.get j) :
    Bounds n ((Finset.univ : Finset (Fin n)).filter
      (discovered hn f a r ask (t+1+ks.length))).card (k*product ks) := by
  let φ := fun e => comparisonCount r e Q
  let I := (Finset.range (k+1)).erase 0
  have hcard : I.card ≤ k := by
    dsimp only [I]
    rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.succ_pos k)),Finset.card_range]
    omega
  have hmaps : ∀ e∈(Finset.univ : Finset (Fin n)), φ e∈I := by
    intro e he
    have qb := comparison_le r e Q
    have qp := comparison_pos r e Q hr
    simp only [I,Finset.mem_erase,Finset.mem_range,φ]
    omega
  have hc :
      Bounds (Finset.univ : Finset (Fin n)).card
        ((Finset.univ : Finset (Fin n)).filter (discovered hn f a r ask (t+1+ks.length))).card
        (k*product ks) := by
    apply bounds_partition φ I _ _ k (product ks) hcard hmaps
    intro i hi
    let W := (Finset.univ : Finset (Fin n)).filter (fun e => φ e=i)
    have hsame : ∀ e∈W, ∀ v∈W, history ask (physicalAnchored f a r e) (t+1)=
        history ask (physicalAnchored f a r v) (t+1) := by
      intro e he v hv
      obtain ⟨_,hφ⟩ := Finset.mem_filter.mp he
      obtain ⟨_,hφ'⟩ := Finset.mem_filter.mp hv
      apply common_next f hP a r e v ask t Q
      · simp only [h]
      · rw [h,hQ]
      · exact hφ.trans hφ'.symm
    have hanchor : ∀ e∈W, r∈seen ask (physicalAnchored f a r e) (t+1) := by
      intro e he
      rw [seen_succ,h,hQ]
      exact Finset.mem_union_right _ hr
    exact branch_bound hn f hP a r ask ks (t+1) W hsame hanchor legal
  simpa using hc

theorem prior_empty (ask : Strategy (Fin n) G) (x : Fin n → G) (t : Nat)
    (h : ∀ j<t, ask (List.replicate j ∅)=∅) :
    history ask x t = List.replicate t ∅ ∧ seen ask x t = ∅ := by
  induction t with
  | zero => simp [history_zero,seen_zero]
  | succ t ih =>
    specialize ih (fun j hj => h j (by omega))
    have z := h t (by omega)
    rw [history_succ,seen_succ,ih.1,ih.2,z]
    have h1 : ([∅] : List (Finset (Fin n × G))) = List.replicate 1 ∅ := rfl
    simp only [answers,Finset.image_empty,Finset.empty_union,h1,List.replicate_append_replicate,and_self]

theorem anchored_card_upper (hn : 0<n) (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (ask : Strategy (Fin n) G) (bs : List Nat)
    (legal : ∀ (j : Fin bs.length) (x : Fin n → G), (ask (history ask x j.val)).card ≤ bs.get j)
    (t : Nat) (ht : t<bs.length)
    (H : ∀ j<t, ask (List.replicate j ∅)=∅)
    (r : Fin n) (hr : r∈ask (List.replicate t ∅)) (a : G) :
    ((Finset.univ : Finset (Fin n)).filter (discovered hn f a r ask bs.length)).card  ≤ 
      capped n (price bs).2 := by
  let ks := bs.drop (t+1)
  let k := bs.get ⟨t,ht⟩
  let Q := ask (List.replicate t ∅)
  have h : ∀ x : Fin n → G, history ask x t = List.replicate t ∅ :=
    fun x => (prior_empty ask x t H).1
  have hc : Q.card ≤ k := by
    have q := legal ⟨t,ht⟩ (physicalAnchored f a r r)
    simpa only [h,Q,k] using q
  have hlength : t+1+ks.length = bs.length := by
    dsimp [ks]; rw [List.length_drop]; omega
  have hleg : ∀ (j : Fin ks.length) (e : Fin n),
      (ask (history ask (physicalAnchored f a r e) ((t+1)+j.val))).card  ≤  ks.get j := by
    intro j e
    have hj := j.isLt
    have q := legal ⟨(t+1)+j.val,by omega⟩ (physicalAnchored f a r e)
    simpa [ks,List.get_eq_getElem,List.getElem_drop,Nat.add_comm,Nat.add_assoc,Nat.add_left_comm] using q
  have b := boot_bound hn f hP a r ask t k ks Q h rfl hr hc hleg
  rw [hlength] at b
  have htake : bs = bs.take t ++ k::ks := by
    exact (List.take_append_drop t bs).symm.trans (by rw [List.drop_eq_getElem_cons ht]; rfl)
  have hk : k*product ks  ≤  (price bs).2 := by
    nth_rw 1 [htake]
    exact split_budget_le _ _ _
  exact Nat.le_trans (loss_at_least_one b.1 b.2.1 b.2.2) (capped_mono_right hk)

end Boot


section Wrap
variable {G : Type} [Group G] [Fintype G] [DecidableEq G] {n : Nat}

noncomputable def anchoredEquiv (hn : 0<n) (f : Fin n → G)
    (hP : (List.ofFn f).prod ≠ 1) (r : Fin n) :
    (Fin n × G) ≃ ↥(privateWords hn f) := by
  let enc : Fin n × G → ↥(privateWords hn f) := fun p =>
    ⟨physicalAnchored f p.2 r p.1, by simp [privateWords,physical_faults hn f hP]⟩
  refine Equiv.ofBijective enc ⟨?_,?_⟩
  · intro p q h
    have he : physicalAnchored f p.2 r p.1 = physicalAnchored f q.2 r q.1 := congrArg Subtype.val h
    have hf := congrArg (faults hn f) he
    rw [physical_faults hn f hP,physical_faults hn f hP,Finset.singleton_inj] at hf
    have ha := congrArg (fun x => gauge f x r) he
    change gauge f (physical f _) r = gauge f (physical f _) r at ha
    rw [gauge_physical,gauge_physical,anchor_read,anchor_read] at ha
    exact Prod.ext hf ha
  · intro w
    have h : (faults hn f w.val).card=1 := (Finset.mem_filter.mp w.property).2
    obtain ⟨e,he⟩ := Finset.card_eq_one.mp h
    let a₀ := gauge f w.val (first hn)
    let a := gauge f w.val r
    let P := (List.ofFn f).prod
    have wd : encode hn f e a₀ = w.val := decode hn f w.val e he
    have ha : a = switch P a₀ e r := by
      change gauge f w.val r = _
      rw [← wd]
      change gauge f (physical f _) r = _
      rw [gauge_physical]
    have haa : (if r.val ≤ e.val then a else a*P)=a₀ := by
      rw [ha]; unfold switch
      by_cases hh : r.val ≤ e.val <;> simp [hh,mul_assoc]
    refine ⟨(e,a),Subtype.ext ?_⟩
    change physical f (switch P (if r.val ≤ e.val then a else a*P) e)=w.val
    rw [haa]
    exact wd

def successful (hn : 0<n) (f : Fin n → G) (ask : Strategy (Fin n) G) (t : Nat)
    (x : Fin n → G) : Prop :=
  ∃ e ∈ faults hn f x, e∈seen ask x t ∧ nxt hn e ∈ seen ask x t

instance successfulDecidable (hn : 0<n) (f : Fin n → G) (ask : Strategy (Fin n) G)
    (t : Nat) : DecidablePred (successful hn f ask t) :=
  fun x => inferInstanceAs (Decidable
    (∃ e ∈ faults hn f x, e ∈ seen ask x t ∧ nxt hn e ∈ seen ask x t))

theorem success_matches (hn : 0<n) (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (ask : Strategy (Fin n) G) (r e : Fin n) (a : G) (t : Nat) :
    successful hn f ask t (physicalAnchored f a r e) ↔ discovered hn f a r ask t e := by
  unfold successful discovered
  rw [physical_faults hn f hP]
  simp

theorem upper_from_strata (hn : 0<n) (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (ask : Strategy (Fin n) G) (t c : Nat) (r : Fin n)
    (h : ∀ a : G, ((Finset.univ : Finset (Fin n)).filter (discovered hn f a r ask t)).card ≤ c) :
    ((privateWords hn f).filter (fun x => decide (successful hn f ask t x))).card  ≤  c*Fintype.card G := by
  classical
  let W := privateWords hn f
  let good := W.filter (fun x => decide (successful hn f ask t x))
  let suc := (Finset.univ : Finset (Fin n × G)).filter
    (fun p => discovered hn f p.2 r ask t p.1)
  let E := anchoredEquiv hn f hP r
  have ecard : good.card = suc.card := by
    symm
    refine Finset.card_bij (fun p _ => (E p).val) ?_ ?_ ?_
    · intro p hp
      refine Finset.mem_filter.mpr ⟨(E p).property,?_⟩
      exact decide_eq_true ((success_matches hn f hP ask r p.1 p.2 t).mpr (Finset.mem_filter.mp hp).2)
    · intro p hp q hq hpq
      exact E.injective (Subtype.ext hpq)
    · intro y hy
      obtain ⟨p,hp⟩ := E.surjective ⟨y,(Finset.mem_filter.mp hy).1⟩
      refine ⟨p,?_ ,congrArg Subtype.val hp⟩
      have hv : (E p).val = y := congrArg Subtype.val hp
      have hg : successful hn f ask t y := of_decide_eq_true (Finset.mem_filter.mp hy).2
      have hpv : successful hn f ask t (physicalAnchored f p.2 r p.1) := by rwa [← hv] at hg
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(success_matches hn f hP ask r p.1 p.2 t).mp hpv⟩
  have fibers (a : G) : (suc.filter (fun p => p.2=a)).card =
      ((Finset.univ : Finset (Fin n)).filter (discovered hn f a r ask t)).card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      have h1 := (Finset.mem_filter.mp hp).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h1 ▸ h2⟩
    · intro p hp q hq he
      exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
    · intro e he
      exact ⟨(e,a),Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩,rfl⟩,rfl⟩
  change good.card  ≤  _
  rw [ecard,Finset.card_eq_sum_card_fiberwise (f:=Prod.snd) (t:=Finset.univ)
    (fun y _ => Finset.mem_univ _)]
  simp_rw [fibers]
  calc
    _  ≤  ∑ _a : G,c := Finset.sum_le_sum fun a _ => h a
    _ = _ := by simp [Nat.mul_comm]

theorem private_card_upper (hn : 0<n) (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (ask : Strategy (Fin n) G) (bs : List Nat)
    (legal : ∀ (j : Fin bs.length) (x : Fin n → G), (ask (history ask x j.val)).card ≤ bs.get j) :
    ((privateWords hn f).filter (fun x => decide (successful hn f ask bs.length x))).card  ≤ 
      capped n (price bs).2*Fintype.card G := by
  classical
  by_cases h : ∃ (t : Nat), t<bs.length ∧ (ask (List.replicate t ∅)).Nonempty
  · let t := Nat.find h
    have ht := Nat.find_spec h
    have H : ∀ j<t, ask (List.replicate j ∅)=∅ := by
      intro j hj
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hh
      exact Nat.find_min h hj ⟨by omega,hh⟩
    obtain ⟨r,hr⟩ := ht.2
    apply upper_from_strata hn f hP ask bs.length _ r
    intro a
    exact anchored_card_upper hn f hP ask bs legal t ht.1 H r hr a
  · have H : ∀ j<bs.length, ask (List.replicate j ∅)=∅ := by
      intro j hj
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hh
      exact h ⟨j,hj,hh⟩
    have z : ∀ x : Fin n → G, ¬successful hn f ask bs.length x := by
      intro x
      unfold successful
      rw [(prior_empty ask x bs.length H).2]
      simp
    simp [z]

end Wrap


section LowerModel
variable {n : Nat}

def indices (n B L p k : Nat) :=
  (Finset.range k).filter (fun j => L+j*p < n ∧ L+j*p < B)

def grid (r : Fin n) (B L p k : Nat) : Finset (Fin n) :=
  (indices n B L p k).attach.image
    (fun j => rotate r ⟨L+j.val*p,(Finset.mem_filter.mp j.property).2.1⟩)

theorem grid_bound (r : Fin n) (B L p k : Nat) : (grid r B L p k).card  ≤  k := by
  unfold grid
  apply Nat.le_trans Finset.card_image_le
  rw [Finset.card_attach]
  exact Nat.le_trans (Finset.card_filter_le _ _) (by simp)

theorem grid_mem (r i : Fin n) (B L p k : Nat) :
    i ∈ grid r B L p k ↔ ∃ j<k, rank r i = L+j*p ∧ rank r i < B := by
  unfold grid
  constructor
  · intro h
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp h
    have hjp := Finset.mem_filter.mp j.property
    have hval : rank r i=L+j.val*p := by rw [← hj,rank_rotate]
    exact ⟨j.val,Finset.mem_range.mp hjp.1,hval,hval.symm ▸ hjp.2.2⟩
  · rintro ⟨j,hj,he,hb⟩
    have hh : j ∈ indices n B L p k := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,he ▸ rank_lt r i,he ▸ hb⟩
    refine Finset.mem_image.mpr ⟨⟨j,hh⟩,Finset.mem_attach _ _,rank_inj r ?_⟩
    rw [rank_rotate]; exact he.symm

def leftOf (r : Fin n) (d : Nat) (S : Finset (Fin n)) :=
  (S.filter (fun i => rank r i ≤ d)).sup (rank r)

theorem leftOf_le (r : Fin n) (d : Nat) (S : Finset (Fin n)) :
    leftOf r d S  ≤  d := by
  apply Finset.sup_le_iff.mpr
  intro i hi
  exact (Finset.mem_filter.mp hi).2

theorem leftOf_trim (r : Fin n) (B d : Nat) (S : Finset (Fin n))
    (hs : ∀ i∈S, rank r i<B) :
    leftOf r d S = leftOf r (min d (B-1)) S := by
  unfold leftOf
  congr 1
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hi,hd⟩
    exact ⟨hi,(trim_cmp B _ _ (hs i hi)).mp hd⟩
  · rintro ⟨hi,hd⟩
    exact ⟨hi,(trim_cmp B _ _ (hs i hi)).mpr hd⟩

theorem leftOf_root (r : Fin n) (B d p k : Nat) (hp : 0<p) (hd : d<n) (hb : d<B)
    (hB : B=k*p) : leftOf r d (grid r B 0 p k) = floorBy d p := by
  apply Nat.le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro i hi
    obtain ⟨hiQ,hiD⟩ := Finset.mem_filter.mp hi
    obtain ⟨j,hj,hx,hxb⟩ := (grid_mem r i _ _ _ _).mp hiQ
    rw [Nat.zero_add] at hx
    rw [hx] at hiD ⊢
    exact floorBy_ge hp hiD
  · let j := d/p
    have hj : j<k := (Nat.div_lt_iff_lt_mul hp).mpr (hB ▸ hb)
    let b := floorBy d p
    have hbd : b ≤ d := floorBy_le d p
    let i := rotate r ⟨b,by omega⟩
    have hi : rank r i=b := rank_rotate _ _
    have he : i∈grid r B 0 p k := (grid_mem r i _ _ _ _).mpr
      ⟨j,hj,by rw [hi,Nat.zero_add];rfl,by omega⟩
    change b ≤ leftOf r d (grid r B 0 p k)
    rw [← hi]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨he,by omega⟩)

theorem leftOf_succ (r : Fin n) (B d p k : Nat) (hp : 0<p) (hd : d<n) (hb : d<B)
    (S : Finset (Fin n))
    (hL : leftOf r d S = floorBy d ((k+1)*p)) :
    leftOf r d (S ∪ grid r B (leftOf r d S+p) p k) = floorBy d p := by
  let L := floorBy d ((k+1)*p)
  let D := floorBy d p
  let j := d/p % (k+1)
  have hj : j<k+1 := Nat.mod_lt _ (Nat.succ_pos _)
  have hD : D=L+j*p := floorBy_splt d k p
  have hDd : D ≤ d := floorBy_le d p
  have hLD : L ≤ D := floorBy_block_le d k p
  rw [hL]
  apply Nat.le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro i hi
    obtain ⟨hu,hd'⟩ := Finset.mem_filter.mp hi
    rcases Finset.mem_union.mp hu with hS|hQ
    · have hOld : rank r i ≤ leftOf r d S := Finset.le_sup (Finset.mem_filter.mpr ⟨hS,hd'⟩)
      rw [hL] at hOld
      exact Nat.le_trans hOld hLD
    · obtain ⟨j',hj',hr',hB'⟩ := (grid_mem r i _ _ _ _).mp hQ
      have hw : j'+1 ≤ j := by
        by_contra H
        have hprod : (j+1)*p ≤ (j'+1)*p := Nat.mul_le_mul_right _ (by omega)
        have hf := floorBy_lt_next (d:=d) hp
        rw [Nat.succ_mul, Nat.succ_mul] at hprod
        omega
      have hpw := Nat.mul_le_mul_right p hw
      rw [Nat.succ_mul] at hpw
      omega
  · change D ≤ leftOf r d (S ∪ grid r B (L+p) p k)
    by_cases h0 : j=0
    · have he : D=L := by rw [hD,h0,Nat.zero_mul,Nat.add_zero]
      rw [he]
      have hold : leftOf r d S ≤ leftOf r d (S ∪ grid r B (L+p) p k) := by
        apply Finset.sup_le_iff.mpr
        intro i hi
        obtain ⟨hi,hd'⟩ := Finset.mem_filter.mp hi
        exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hi,hd'⟩)
      exact Nat.le_trans (Nat.le_of_eq hL.symm) hold
    · let i := rotate r ⟨D,by omega⟩
      have hr : rank r i=D := rank_rotate _ _
      have hgrid : i ∈ grid r B (L+p) p k := by
        apply (grid_mem r i _ _ _ _).mpr
        have he : (j-1)*p+p=j*p := by
          rw [← Nat.succ_mul]; congr 1; omega
        exact ⟨j-1,by omega,by omega,by omega⟩
      rw [← hr]
      exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hgrid,by omega⟩)

end LowerModel


section LowerRule
variable {G : Type} [Group G] [Fintype G] [DecidableEq G] {n : Nat}

def record (h : List (Finset (Fin n × G))) : Finset (Fin n × G) :=
  h.foldr (· ∪ ·) ∅

theorem record_append (h₁ h₂ : List (Finset (Fin n × G))) :
    record (h₁++h₂) = record h₁ ∪ record h₂ := by
  induction h₁ with
  | nil => simp [record]
  | cons a l ih =>
    change a ∪ record (l++h₂)= (a∪record l)∪record h₂
    rw [ih,Finset.union_assoc]

theorem record_history (ask : Strategy (Fin n) G) (x : Fin n → G) (t : Nat) :
    record (history ask x t) = answers (seen ask x t) x := by
  induction t with
  | zero => simp [record,history_zero,seen_zero,answers]
  | succ t ih =>
    rw [history_succ,seen_succ,record_append,ih]
    simp [record,answers,Finset.image_union]

theorem read_mem (S : Finset (Fin n)) (x : Fin n → G) (i : Fin n) (g : G) :
    (i,g) ∈ answers S x ↔ i∈S ∧ g=x i := by
  unfold answers
  constructor
  · intro h
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp h
    have hi : v=i := congrArg Prod.fst he
    have hg : x v=g := congrArg Prod.snd he
    subst v
    exact ⟨hv,hg.symm⟩
  · rintro ⟨hi,he⟩
    exact Finset.mem_image.mpr ⟨i,hi,by rw [he]⟩

def leftLabel (f : Fin n → G) (a : G) (r i : Fin n) : G :=
  if r.val ≤ i.val then a else a*(List.ofFn f).prod

theorem gauge_leftLabel (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (a : G) (r e i : Fin n) :
    gauge f (physicalAnchored f a r e) i = leftLabel f a r i ↔ rank r i ≤ rank r e := by
  unfold physicalAnchored
  rw [gauge_physical,anchor_rank]
  have ha : a≠a*((List.ofFn f).prod)⁻¹ := switch_distinct _ _ hP
  have hb : a≠a*(List.ofFn f).prod := by
    have hPi : ((List.ofFn f).prod)⁻¹ ≠ (1:G) := by simpa using hP
    simpa using switch_distinct _ a hPi
  by_cases hc : rank r i ≤ rank r e <;> by_cases hd : r.val ≤ i.val <;>
    simp [hc,hd,leftLabel,ha,ha.symm,hb,hb.symm]

noncomputable def guessLeft (f : Fin n → G) (r : Fin n)
    (h : List (Finset (Fin n × G))) : Nat := by
  classical
  let R := record h
  exact (R.filter (fun p => ∃ b, (r,b)∈R ∧
    p.2 * (pref f p.1.val p.1.isLt.le)⁻¹ =
      leftLabel f (b * (pref f r.val r.isLt.le)⁻¹) r p.1)).sup (fun p => rank r p.1)

theorem guess_accurate (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (a : G) (r e : Fin n) (ask : Strategy (Fin n) G) (t : Nat)
    (hr : r∈seen ask (physicalAnchored f a r e) t) :
    guessLeft f r (history ask (physicalAnchored f a r e) t) =
      leftOf r (rank r e) (seen ask (physicalAnchored f a r e) t) := by
  classical
  let x := physicalAnchored f a r e
  let S := seen ask x t
  have hA : gauge f x r = a := by
    change gauge f (physical f _) r = _
    rw [gauge_physical,anchor_read]
  have hPred (i : Fin n) :
      (∃ b, (r,b)∈answers S x ∧ (x i) * (pref f i.val i.isLt.le)⁻¹ =
        leftLabel f (b * (pref f r.val r.isLt.le)⁻¹) r i) ↔ rank r i ≤ rank r e := by
    simp only [read_mem,show r∈S from hr,true_and]
    constructor
    · rintro ⟨b,hb,hq⟩
      subst b
      change gauge f x i = leftLabel f (gauge f x r) r i at hq
      rw [hA] at hq
      exact (gauge_leftLabel f hP a r e i).mp hq
    · intro h
      refine ⟨x r,rfl,?_⟩
      change gauge f x i = leftLabel f (gauge f x r) r i
      rw [hA]
      exact (gauge_leftLabel f hP a r e i).mpr h
  unfold guessLeft
  rw [record_history]
  dsimp only
  have heq : ((answers S x).filter (fun p => ∃ b, (r,b)∈answers S x ∧
      p.2 * (pref f p.1.val p.1.isLt.le)⁻¹ =
      leftLabel f (b * (pref f r.val r.isLt.le)⁻¹) r p.1)) =
       answers (S.filter (fun i => rank r i ≤ rank r e)) x := by
    ext ⟨i,y⟩
    simp only [Finset.mem_filter,read_mem,show r∈S from hr,true_and]
    constructor
    · rintro ⟨⟨hi,rfl⟩,hp⟩
      exact ⟨⟨hi,(hPred i).mp (by simpa only [read_mem,show r∈S from hr,true_and] using hp)⟩,rfl⟩
    · rintro ⟨⟨hi,hd⟩,rfl⟩
      exact ⟨⟨hi,rfl⟩,by simpa only [read_mem,show r∈S from hr,true_and] using (hPred i).mpr hd⟩
  change _ = (leftOf r (rank r e) S)
  rw [heq]; unfold leftOf answers
  rw [Finset.sup_image]
  rfl

noncomputable def greedyRule (f : Fin n → G) (r : Fin n) (bs : List Nat) (s B : Nat) :
    Strategy (Fin n) G := by
  intro h
  let j := h.length
  exact if hJ : j<bs.length then
    if j<s then ∅ else
    if j=s then grid r B 0 (product (bs.drop (j+1))) (bs.get ⟨j,hJ⟩) else
      let p := product (bs.drop (j+1))
      grid r B (guessLeft f r h+p) p (bs.get ⟨j,hJ⟩)
  else ∅

theorem greedy_legal (f : Fin n → G) (r : Fin n) (bs : List Nat) (s B : Nat)
    (j : Fin bs.length) (x : Fin n → G) :
    (greedyRule f r bs s B (history (greedyRule f r bs s B) x j.val)).card ≤ bs.get j := by
  generalize hh : history (greedyRule f r bs s B) x j.val = h
  have hj : h.length=j.val := by rw [← hh,history_length]
  unfold greedyRule
  simp only [hj,dif_pos j.isLt]
  split
  · simp
  · split <;> exact grid_bound _ _ _ _ _

theorem greedy_query_bound (f : Fin n → G) (r : Fin n) (bs : List Nat) (s B : Nat)
    (h : List (Finset (Fin n × G))) :
    ∀ i∈greedyRule f r bs s B h, rank r i<B := by
  unfold greedyRule
  dsimp only
  split <;> try simp
  split <;> try simp
  split <;> intro i hi
  · obtain ⟨j,hj,he,hb⟩ := (grid_mem r i _ _ _ _).mp hi
    exact hb
  · obtain ⟨j,hj,he,hb⟩ := (grid_mem r i _ _ _ _).mp hi
    exact hb

theorem greedy_seen_bound (f : Fin n → G) (r : Fin n) (bs : List Nat) (s B : Nat)
    (x : Fin n → G) (t : Nat) :
    ∀ i∈seen (greedyRule f r bs s B) x t, rank r i<B := by
  intro i hi
  obtain ⟨u,hu,he⟩ := Finset.mem_biUnion.mp hi
  exact greedy_query_bound f r bs s B _ i he

theorem greedy_empty (f : Fin n → G) (r : Fin n) (bs : List Nat) (s B : Nat) (t : Nat)
    (ht : t<s) : greedyRule f r bs s B (List.replicate t ∅) = ∅ := by
  unfold greedyRule
  simp [ht]

theorem greedy_root (f : Fin n → G) (r : Fin n) (bs : List Nat) (s B : Nat)
    (hs : s<bs.length) (x : Fin n → G) :
    seen (greedyRule f r bs s B) x (s+1)=
      grid r B 0 (product (bs.drop (s+1))) (bs.get ⟨s,hs⟩) := by
  let ask := greedyRule f r bs s B
  have hh := prior_empty ask x s (fun j hj => greedy_empty f r bs s B j hj)
  rw [seen_succ,hh.1,hh.2]
  change ∅ ∪ greedyRule f r bs s B (List.replicate s ∅)=_
  simp [greedyRule,hs]

theorem greedy_anchor (f : Fin n → G) (r : Fin n) (bs : List Nat) (s B : Nat)
    (hs : s<bs.length) (hk : 0<bs.get ⟨s,hs⟩) (hb : 0<B) (x : Fin n → G) (t : Nat)
    (ht : s+1  ≤  t) : r∈seen (greedyRule f r bs s B) x t := by
  have ha : r∈seen (greedyRule f r bs s B) x (s+1) := by
    rw [greedy_root f r bs s B hs x]
    exact (grid_mem r r _ _ _ _).mpr ⟨0,hk,by simp [rank_self],by simpa [rank_self]⟩
  have hm : ∀ a b, a ≤ b → seen (greedyRule f r bs s B) x a ⊆ seen (greedyRule f r bs s B) x b := by
    intro a b h i hi
    obtain ⟨j,hj,hb⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_range.mpr (Nat.lt_of_lt_of_le (Finset.mem_range.mp hj) h),hb⟩
  exact hm (s+1) t ht ha

end LowerRule


section LowerProof
variable {G : Type} [Group G] [Fintype G] [DecidableEq G] {n : Nat}

theorem greedy_progress (hn : 0<n) (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (a : G) (r e : Fin n) (bs : List Nat) (s B : Nat)
    (hs : s<bs.length) (hk : 0<bs.get ⟨s,hs⟩)
    (hB : B=(bs.get ⟨s,hs⟩)*product (bs.drop (s+1))) :
    ∀ j, s+1 ≤ j → j ≤ bs.length →
      leftOf r (min (rank r e) (B-1))
        (seen (greedyRule f r bs s B) (physicalAnchored f a r e) j) =
      floorBy (min (rank r e) (B-1)) (product (bs.drop j)) := by
  let ask := greedyRule f r bs s B
  let x := physicalAnchored f a r e
  let d := min (rank r e) (B-1)
  have hBpos : 0<B := by rw [hB]; exact Nat.mul_pos hk (product_pos _)
  have hd : d<n := by have h := rank_lt r e; dsimp [d]; omega
  have hb : d<B := by dsimp [d]; omega
  intro j
  induction j with
  | zero => omega
  | succ j ih =>
    intro hj hl
    by_cases hjs : j=s
    · subst j
      rw [greedy_root f r bs s B hs x]
      exact leftOf_root r B d _ _ (product_pos _) hd hb hB
    · have hj₁ : s+1 ≤ j := by omega
      have hj₂ : j<bs.length := by omega
      let S := seen ask x j
      let p := product (bs.drop (j+1))
      let k := bs.get ⟨j,hj₂⟩
      have hC : guessLeft f r (history ask x j) = leftOf r d S := by
        rw [guess_accurate f hP a r e ask j (greedy_anchor f r bs s B hs hk hBpos x j hj₁)]
        exact leftOf_trim r B (rank r e) S (greedy_seen_bound f r bs s B x j)
      have hGrid : ask (history ask x j)=grid r B (leftOf r d S+p) p k := by
        generalize hEq : history ask x j = hist at hC ⊢
        have hlen : hist.length=j := by rw [← hEq,history_length]
        dsimp only [ask]
        unfold greedyRule
        simp only [hlen,dif_pos hj₂,if_neg (show ¬j<s by omega),if_neg hjs,hC]
        rfl
      change leftOf r d (seen ask x (j+1)) = floorBy d p
      rw [seen_succ,hGrid]
      apply leftOf_succ r B d p k (product_pos _) hd hb S
      have hprev := ih hj₁ (by omega)
      rw [product_drop_split bs j hj₂] at hprev
      exact hprev

theorem greedy_final (hn : 0<n) (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (a : G) (r e : Fin n) (bs : List Nat) (s B : Nat)
    (hs : s<bs.length) (hk : 0<bs.get ⟨s,hs⟩)
    (hB : B=(bs.get ⟨s,hs⟩)*product (bs.drop (s+1))) :
    guessLeft f r (history (greedyRule f r bs s B) (physicalAnchored f a r e) bs.length) =
       min (rank r e) (B-1) := by
  let ask := greedyRule f r bs s B
  let x := physicalAnchored f a r e
  have hBpos : 0<B := by rw [hB]; exact Nat.mul_pos hk (product_pos _)
  have hr := greedy_anchor f r bs s B hs hk hBpos x bs.length (by omega)
  rw [guess_accurate f hP a r e ask bs.length hr,
    leftOf_trim r B (rank r e) _ (greedy_seen_bound f r bs s B x bs.length)]
  rw [greedy_progress hn f hP a r e bs s B hs hk hB _ (by omega) (Nat.le_refl _),
    product_drop_end]
  simp [floorBy]

theorem greedy_exact (hn : 0<n) (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (a : G) (r e : Fin n) (bs : List Nat) (s B : Nat)
    (hs : s<bs.length) (hk : 0<bs.get ⟨s,hs⟩)
    (hB : B=(bs.get ⟨s,hs⟩)*product (bs.drop (s+1))) :
    successful hn f (greedyRule f r bs s B) bs.length (physicalAnchored f a r e) ↔
      rank r e < capped n B := by
  let ask := greedyRule f r bs s B
  let x := physicalAnchored f a r e
  let S := seen ask x bs.length
  have hBpos : 0<B := by rw [hB]; exact Nat.mul_pos hk (product_pos _)
  rw [success_matches hn f hP]
  constructor
  · intro h
    have he := rank_lt r e
    by_cases hb : n ≤ B
    · simpa [capped,hb] using he
    · have hb1 := greedy_seen_bound f r bs s B x bs.length e h.1
      have hb2 := greedy_seen_bound f r bs s B x bs.length (nxt hn e) h.2
      unfold capped; rw [if_neg hb]
      by_contra hbad
      have hz : rank r e+1=B := by omega
      rw [rank_next hn,hz,Nat.mod_eq_of_lt (by omega)] at hb2
      omega
  · intro h
    have hr := greedy_anchor f r bs s B hs hk hBpos x bs.length (by omega)
    apply (thresholds_singleton hn r e S hr).mpr
    intro v hv
    apply rank_inj r
    have eqHist := (physical_history_eq f hP a r e v ask bs.length).mpr hv
    have eqLeft := congrArg (guessLeft f r) eqHist
    rw [greedy_final hn f hP a r e bs s B hs hk hB,
      greedy_final hn f hP a r v bs s B hs hk hB] at eqLeft
    have he := rank_lt r e; have hvn := rank_lt r v
    unfold capped at h
    split at h <;> omega

theorem rank_left_inj (e : Fin n) : Function.Injective (fun r => rank r e) := by
  intro a b h
  have he := e.isLt; have ha := a.isLt; have hb := b.isLt
  apply Fin.ext
  change rank a e=rank b e at h
  unfold rank at h
  split at h <;> split at h <;> omega

theorem rotations_count (e : Fin n) (c : Nat) (hc : c ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun r => rank r e<c)).card = c := by
  let F : Fin n → Fin n := fun r => ⟨rank r e,rank_lt r e⟩
  have fi : Function.Injective F := fun x y h => rank_left_inj e (congrArg Fin.val h)
  have fs : Function.Surjective F := Finite.surjective_of_injective fi
  suffices hh : ((Finset.univ : Finset (Fin n)).filter (fun r => rank r e<c)).card =
      (Finset.range c).card by
    exact hh.trans (Finset.card_range c)
  refine Finset.card_bij (fun r _ => rank r e) ?_ ?_ ?_
  · intro r hr
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2
  · intro a ha b hb h
    exact rank_left_inj e h
  · intro j hj
    have hjc := Finset.mem_range.mp hj
    obtain ⟨a,ha⟩ := fs ⟨j,by omega⟩
    have he : rank a e=j := congrArg Fin.val ha
    exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm ▸ hjc⟩,he⟩

theorem family_exact (hn : 0<n) (f : Fin n → G) (hP : (List.ofFn f).prod ≠ 1)
    (bs : List Nat) :
    ∃ family : Fin n → Strategy (Fin n) G,
      (∀ r (x : Fin n → G) (j : Fin bs.length),
        (family r (history (family r) x j.val)).card ≤ bs.get j) ∧
      ∀ w ∈ privateWords hn f,
        ((Finset.univ : Finset (Fin n)).filter
          (fun offset => decide (successful hn f (family offset) bs.length w))).card =
            capped n (price bs).2 := by
  classical
  rcases attainable_max bs with h0 | ⟨pre,k,tail,hk,hbs,hB⟩
  · refine ⟨fun _ _ => ∅,by simp,?_⟩
    intro w hw
    have hh : ¬successful hn f (fun _ => ∅) bs.length w := by
      have hseen : seen (fun _ => ∅) w bs.length = ∅ := by
        ext i; simp [seen,Finset.mem_biUnion]
      simp [successful,hseen]
    have hval : ¬n ≤ 0 := by omega
    simp [hh,h0,capped,hval]
  · let s := pre.length
    have hs : s<bs.length := by rw [hbs]; simp [s]
    let B := (price bs).2
    have dh : bs.drop s = k::tail := by rw [hbs]; exact List.drop_left
    have hk' : bs.get ⟨s,hs⟩=k := by
      have j := List.drop_eq_getElem_cons hs
      change bs.drop s=(bs.get ⟨s,hs⟩)::bs.drop (s+1) at j
      rw [dh] at j
      exact (List.cons.inj j).1.symm
    have ht : bs.drop (s+1)=tail := by
      have j := List.drop_eq_getElem_cons hs
      change bs.drop s=(bs.get ⟨s,hs⟩)::bs.drop (s+1) at j
      rw [dh] at j
      exact (List.cons.inj j).2.symm
    have hB' : B=(bs.get ⟨s,hs⟩)*product (bs.drop (s+1)) := by
      rw [hk',ht]; exact hB
    have hp : 0<bs.get ⟨s,hs⟩ := by rw [hk']; exact hk
    let family := fun r => greedyRule f r bs s B
    refine ⟨family,fun r x j => greedy_legal f r bs s B j x,?_⟩
    intro w hw
    have hf (r : Fin n) : successful hn f (family r) bs.length w ↔
      ∃ e, faults hn f w={e} ∧ rank r e<capped n B := by
      obtain ⟨⟨e,a⟩,h⟩ := (anchoredEquiv hn f hP r).surjective ⟨w,hw⟩
      have he : physicalAnchored f a r e=w := congrArg Subtype.val h
      rw [← he]
      constructor
      · intro H
        exact ⟨e,physical_faults hn f hP a r e,(greedy_exact hn f hP a r e bs s B hs hp hB').mp H⟩
      · rintro ⟨v,hv,hv'⟩
        rw [physical_faults hn f hP,Finset.singleton_inj] at hv
        exact (greedy_exact hn f hP a r e bs s B hs hp hB').mpr (hv.symm ▸ hv')
    obtain ⟨e,he⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hw).2
    have hf' (r : Fin n) : successful hn f (family r) bs.length w ↔ rank r e<capped n B := by
      rw [hf r]
      constructor
      · rintro ⟨v,hv,hp⟩
        rw [he,Finset.singleton_inj] at hv
        exact hv.symm ▸ hp
      · exact fun h => ⟨e,he,h⟩
    have heq : ((Finset.univ : Finset (Fin n)).filter
      (fun offset => decide (successful hn f (family offset) bs.length w))) =
      Finset.univ.filter (fun r => rank r e<capped n B) := by
      ext r; simp [hf' r]
    rw [heq]
    exact rotations_count e (capped n B) (capped_le n B)

end LowerProof

end PEqualNP.Outside.L_pcx_333


theorem PEqualNP.Outside.L_pcx_333 : (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n →
  ∀ (G : Type) [Group G] [Fintype G] [DecidableEq G] (f : Fin n → G),
  (List.ofFn f).prod ≠ 1 →
  let next := fun pos : Fin n => (⟨(pos.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let faults := fun assignment : Fin n → G =>
    Finset.univ.filter (fun site => assignment (next site) ≠ assignment site * f site)
  let Strategy := List (Finset (Fin n × G)) → Finset (Fin n)
  let history := fun (ask : Strategy) (x : Fin n → G) (t : ℕ) =>
    (List.range t).foldl (fun hist _ => hist ++ [(ask hist).image (fun u => (u, x u))]) []
  let batch := fun (ask : Strategy) (x : Fin n → G) (i : ℕ) => ask (history ask x i)
  let price := fun bs : List ℕ => bs.foldr
    (fun k (p : ℕ × ℕ) => ((k+1)*p.1, max (k*p.1) p.2)) (1,0)
  ∀ bs : List ℕ,
    let B := (price bs).2
    let c := if n ≤ B then n else B-1
    let legal := fun rule : Strategy => ∀ (word : Fin n → G) (j : Fin bs.length),
      (batch rule word j.val).card ≤ bs.get j
    let success := fun (search : Strategy) (values : Fin n → G) =>
      let seen := (Finset.range bs.length).biUnion (batch search values)
      ∃ edge ∈ faults values, edge ∈ seen ∧ next edge ∈ seen
    let privateWords := Finset.univ.filter (fun input : Fin n → G => (faults input).card = 1)
    privateWords.card = n * Fintype.card G ∧
    (∀ probe, legal probe →
      (privateWords.filter (fun candidate => decide (success probe candidate))).card ≤ c * Fintype.card G) ∧
    ∃ family : Fin n → Strategy, (∀ rotation, legal (family rotation)) ∧
      ∀ privateWord ∈ privateWords,
        (Finset.univ.filter (fun offset => decide (success (family offset) privateWord))).card = c) := by
  intro n hn hn₂ G _ _ _ f hP next0 faults0 Strategy0 history0 batch0 price0 bs B0 c0 legal0 success0 privateWords0
  constructor
  · exact PEqualNP.Outside.L_pcx_333.card_private hn f hP
  · constructor
    · intro probe hlegal
      apply PEqualNP.Outside.L_pcx_333.private_card_upper hn f hP probe bs
      intro j x
      exact hlegal x j
    · obtain ⟨family,legal,sol⟩ := PEqualNP.Outside.L_pcx_333.family_exact hn f hP bs
      exact ⟨family,fun r x j => legal r x j,sol⟩
