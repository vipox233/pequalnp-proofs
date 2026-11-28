import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40277_aux

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

theorem build_mono_k {ops : α → α → Finset α} {goal : α} {k₁ k₂ : ℕ} {av : Finset α}
    (hle : k₁ ≤ k₂) (h : build ops goal k₁ av) : build ops goal k₂ av := by
  induction hle with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem build_mono_av {ops : α → α → Finset α} {goal : α} {k : ℕ} {av₁ av₂ : Finset α}
    (hsub : av₁ ⊆ av₂) (h : build ops goal k av₁) : build ops goal k av₂ := by
  induction k generalizing av₁ av₂ with
  | zero => exact hsub h
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · exact Or.inl (ih hsub skip)
    · exact Or.inr ⟨a, hsub ha, b, hsub hb, hab, z, hz, ih (Finset.insert_subset_insert z hsub) tail⟩

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn; apply sub; intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := fun hh => sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := fun u hu =>
          (Finset.mem_insert.mp (ht (Finset.mem_erase.mp hu).2)).resolve_left (Finset.mem_erase.mp hu).1
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

theorem live_map {α β : Type} [DecidableEq α] [DecidableEq β]
    {ops1 : α → α → Finset α} {ops2 : β → β → Finset β}
    {g1 : α} {g2 : β} (f : α → β)
    (hinj : Function.Injective f) (hgoal : f g1 = g2)
    (hops : ∀ a b z, z ∈ ops1 a b → f z ∈ ops2 (f a) (f b))
    {k : ℕ} {s : Finset α} (h : live ops1 g1 k s) :
    live ops2 g2 k (s.image f) := by
  induction k generalizing s with
  | zero => change s = {g1} at h; subst h; simp [live, hgoal]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact Or.inl (ih skip)
    · refine Or.inr ⟨f a, Finset.mem_image_of_mem f ha, f b, Finset.mem_image_of_mem f hb,
        fun he => hab (hinj he), f z, hops a b z hz, ?_, rest.image f, ?_, ?_⟩
      · intro hm
        obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hm
        exact hout (hinj he ▸ hu)
      · simp [Finset.image_insert]
      · simpa [Finset.image_insert] using ih tail

end Live

def ops (n : ℕ) (x y : BitVec n) : List (BitVec n) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
abbrev basicOps (n : ℕ) (a b : BitVec n) : Finset (BitVec n) :=
  ((ops n a b).filter (fun z => z != 0 && z != BitVec.allOnes n)).toFinset
def nrm (n : ℕ) (u : BitVec n) : BitVec n := if u.getLsbD 0 then ~~~u else u

theorem ops_swap (n : ℕ) (a b : BitVec n) : basicOps n a b = basicOps n b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

theorem ops_diff_ij {n : ℕ} (i j : ℕ) (hi : i < n) (hj : j < n) (a b z : BitVec n)
    (hz : z ∈ basicOps n a b) (hd : z.getLsbD i ≠ z.getLsbD j) :
    a.getLsbD i ≠ a.getLsbD j ∨ b.getLsbD i ≠ b.getLsbD j := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_filter, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail; obtain ⟨ha, hb⟩ := fail; apply hd
  rcases hz.1 with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
      decide_eq_true hi, decide_eq_true hj, Bool.true_and, ha, hb]

def dif (n : ℕ) (w : BitVec n) (d : ℕ) : BitVec n := (w ^^^ (w >>> d)) &&& (BitVec.allOnes n >>> d)
def unionDif (n : ℕ) (ws : List (BitVec n)) (d : ℕ) : BitVec n := ws.foldr (fun w s => dif n w d ||| s) 0
def cover (n : ℕ) (jumps : List ℕ) (t : BitVec n) (ws : List (BitVec n)) : Bool :=
  jumps.all fun d => (dif n t d &&& unionDif n ws d) == dif n t d

theorem bit_dif {n : ℕ} {w : BitVec n} {d i : ℕ} (_hi : i < n) :
    (dif n w d).getLsbD i = true ↔ i + d < n ∧ w.getLsbD i ≠ w.getLsbD (i + d) := by
  simp only [dif, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, Bool.and_eq_true, decide_eq_true_eq, Nat.add_comm d i]
  cases w.getLsbD i <;> cases w.getLsbD (i + d) <;> simp

theorem bit_union (n : ℕ) (ws : List (BitVec n)) (d i : ℕ) :
    (unionDif n ws d).getLsbD i = true ↔ ∃ w ∈ ws, (dif n w d).getLsbD i = true := by
  induction ws with
  | nil => simp [unionDif]
  | cons w ws ih =>
    change (dif n w d ||| unionDif n ws d).getLsbD i = true ↔ _
    simp [ih]

theorem live_cover {n k : ℕ} {jumps : List ℕ} {goal : BitVec n} {ws : List (BitVec n)}
    (h : live (basicOps n) goal k ws.toFinset) : cover n jumps goal ws = true := by
  apply List.all_eq_true.mpr; intro d _
  apply beq_iff_eq.mpr; apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and]
  cases hd : (dif n goal d).getLsbD i with
  | false => rfl
  | true =>
    obtain ⟨hj, hne⟩ := (bit_dif hi).mp hd
    obtain ⟨w, hw, hdw⟩ := live_separates (fun u : BitVec n => u.getLsbD i ≠ u.getLsbD (i + d))
      hne (ops_diff_ij i (i + d) hi hj) h
    rw [(bit_union n ws d i).mpr ⟨w, List.mem_toFinset.mp hw, (bit_dif hi).mpr ⟨hj, hdw⟩⟩]; rfl

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
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧ ws.Perm (a :: b :: rest) := by
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

def keepChoices {α : Type} (a b : α) (r : List α) : List (List α) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {α : Type} [DecidableEq α] {ws r : List α} {a b : α} {needed : Finset α}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩; ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩; ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

def sameSet {α : Type} [BEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => ys.contains x) && ys.all (fun y => xs.contains y)

theorem sameSet_sound {α : Type} [DecidableEq α] {xs ys : List α} (h : sameSet xs ys = true) :
    xs.toFinset = ys.toFinset := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  ext a; simp only [List.mem_toFinset]; exact ⟨h.1 a, h.2 a⟩

def actN : List ℕ → ℕ → ℕ
  | [], _ => 0
  | p2 :: ps, n => Nat.bit (Nat.beq (Nat.mod (Nat.div n p2) 2) 1) (actN ps n)

def actB (n : ℕ) (ps : List ℕ) (x : BitVec n) : BitVec n := BitVec.ofNat n (actN ps x.toNat)

theorem mod_div_two_pow_eq_testBit (n p : ℕ) :
    Nat.beq (Nat.mod (Nat.div n (2 ^ p)) 2) 1 = n.testBit p := by
  change Nat.beq (n / 2 ^ p % 2) 1 = n.testBit p
  rw [Nat.testBit_eq_decide_div_mod_eq]
  cases h : n / 2 ^ p % 2 with
  | zero => rfl
  | succ k =>
    have hlt : n / 2 ^ p % 2 < 2 := Nat.mod_lt _ (by decide)
    have hk : k = 0 := by omega
    subst hk; rfl

theorem actN_testBit : ∀ (pi ps : List ℕ) (n k : ℕ),
    ps = pi.map (fun p => 2 ^ p) →
    (actN ps n).testBit k = (pi[k]?.map n.testBit).getD false
  | [], _, _, _, rfl => by simp [actN]
  | p :: pi, _, n, 0, rfl => by simp [actN, mod_div_two_pow_eq_testBit]
  | p :: pi, _, n, k + 1, rfl => by
    simp [actN, Nat.testBit_bit_succ, actN_testBit pi (pi.map (fun q => 2 ^ q)) n k rfl]

theorem actB_getLsbD (n : ℕ) (pi : List ℕ) (x : BitVec n) (k : ℕ) (hk : k < n) :
    (actB n (pi.map (fun p => 2 ^ p)) x).getLsbD k = (pi[k]?.map x.getLsbD).getD false := by
  unfold actB
  rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and, actN_testBit pi _ x.toNat k rfl]
  cases pi[k]? <;> rfl

def symValid (n gsize : ℕ) (G_idx G_pow : Array (List ℕ)) (G_inv : Array ℕ) (goal : BitVec n) (g : ℕ) : Bool :=
  let pi := G_idx[g]?.getD []
  let inv := G_idx[G_inv[g]?.getD 0]?.getD []
  let ps := G_pow[g]?.getD []
  Nat.blt (G_inv[g]?.getD 0) gsize &&
  Nat.beq (G_inv[G_inv[g]?.getD 0]?.getD 0) g &&
  Nat.beq pi.length n &&
  Nat.beq inv.length n &&
  (ps == pi.map (fun p => 2 ^ p)) &&
  (actB n ps goal == goal) &&
  (List.range n).all (fun k => match pi[k]? with
    | some p => Nat.blt p n && (inv[p]? == some k)
    | none => false)

theorem actB_spec {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) :
    G_inv[g]?.getD 0 < gsize ∧
    G_inv[G_inv[g]?.getD 0]?.getD 0 = g ∧
    G_pow[g]?.getD [] = (G_idx[g]?.getD []).map (fun p => 2 ^ p) ∧
    actB n (G_pow[g]?.getD []) goal = goal ∧
    (∀ k < n, ∃ p < n, (G_idx[g]?.getD [])[k]? = some p ∧ (G_idx[G_inv[g]?.getD 0]?.getD [])[p]? = some k) := by
  have hv := List.all_eq_true.mp hvalid g (List.mem_range.mpr hg)
  unfold symValid at hv
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, List.all_eq_true, List.mem_range] at hv
  refine ⟨hv.1.1.1.1.1.1, Nat.eq_of_beq_eq_true hv.1.1.1.1.1.2, hv.1.1.2, hv.1.2, fun k hk => ?_⟩
  have h1 := hv.2 k hk
  cases hp : (G_idx[g]?.getD [])[k]? with
  | none => simp [hp] at h1
  | some p =>
    simp only [hp, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h1
    exact ⟨p, h1.1, rfl, h1.2⟩

theorem actB_inv_left {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (x : BitVec n) :
    actB n (G_pow[G_inv[g]?.getD 0]?.getD []) (actB n (G_pow[g]?.getD []) x) = x := by
  obtain ⟨hinv_lt, hinv2, hpow, _, _⟩ := actB_spec hv g hg
  obtain ⟨_, _, hpow', _, hpi'⟩ := actB_spec hv (G_inv[g]?.getD 0) hinv_lt
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow', actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, hpk⟩ := hpi' k hk
  rw [hinv2] at hpk
  rw [hkp]; simp only [Option.map_some, Option.getD_some]
  rw [hpow, actB_getLsbD n _ _ p hp, hpk]; simp

theorem actB_inj {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : Function.Injective (actB n (G_pow[g]?.getD [])) :=
  Function.LeftInverse.injective (actB_inv_left hv g hg)

theorem actB_and {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b : BitVec n) :
    actB n (G_pow[g]?.getD []) (a &&& b) = actB n (G_pow[g]?.getD []) a &&& actB n (G_pow[g]?.getD []) b := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_and, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp, BitVec.getLsbD_and]

theorem actB_or {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b : BitVec n) :
    actB n (G_pow[g]?.getD []) (a ||| b) = actB n (G_pow[g]?.getD []) a ||| actB n (G_pow[g]?.getD []) b := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_or, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp, BitVec.getLsbD_or]

theorem actB_not {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a : BitVec n) :
    actB n (G_pow[g]?.getD []) (~~~a) = ~~~actB n (G_pow[g]?.getD []) a := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_not, hpow, actB_getLsbD n _ _ k hk, actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, _⟩ := hpi k hk
  simp [hkp, hk, hp]

theorem actB_zero {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : actB n (G_pow[g]?.getD []) 0 = 0 := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow, actB_getLsbD n _ _ k hk]
  obtain ⟨p, _, hkp, _⟩ := hpi k hk
  simp [hkp]

theorem actB_allOnes {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) : actB n (G_pow[g]?.getD []) (BitVec.allOnes n) = BitVec.allOnes n := by
  obtain ⟨_, _, hpow, _, hpi⟩ := actB_spec hv g hg
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [hpow, actB_getLsbD n _ _ k hk]
  obtain ⟨p, hp, hkp, _⟩ := hpi k hk
  rw [hkp]
  simp only [Option.map_some, Option.getD_some, BitVec.getLsbD_allOnes, hk, hp, decide_true]

theorem actB_ops {n gsize : ℕ} {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {goal : BitVec n}
    (hv : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (g : ℕ) (hg : g < gsize) (a b z : BitVec n) (hz : z ∈ basicOps n a b) :
    actB n (G_pow[g]?.getD []) z ∈ basicOps n (actB n (G_pow[g]?.getD []) a) (actB n (G_pow[g]?.getD []) b) := by
  simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hz ⊢
  refine ⟨?_, fun e => hz.2.1 (actB_inj hv g hg (e.trans (actB_zero hv g hg).symm)),
               fun e => hz.2.2 (actB_inj hv g hg (e.trans (actB_allOnes hv g hg).symm))⟩
  have hz' := hz.1
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz' ⊢
  rcases hz' with rfl | rfl | rfl | rfl
  · left; exact actB_and hv g hg a b
  · right; left; exact actB_or hv g hg a b
  · right; right; left; rw [actB_and hv g hg, actB_not hv g hg]
  · right; right; right; rw [actB_and hv g hg, actB_not hv g hg]

def checkChildP (n k : ℕ) (targets : List (List (BitVec n))) (nxt : List (BitVec n)) : Bool :=
  decide (nxt.length > k) || targets.any (fun t => sameSet nxt t)

def checkStepP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (k extra : ℕ)
    (targets : List (List (BitVec n))) (a b : BitVec n) (r : List (BitVec n)) : Bool :=
  (ops n a b).all fun w =>
    (w == 0 || w == BitVec.allOnes n || w == a || w == b || r.contains w) ||
    (!cover n jumps goal (w :: r) || checkChildP n k targets (w :: r)) &&
    ((extra == 0) ||
      ((!cover n jumps goal (w :: a :: r) || checkChildP n k targets (w :: a :: r)) &&
       (!cover n jumps goal (w :: b :: r) || checkChildP n k targets (w :: b :: r)))) &&
    ((extra < 2) || !cover n jumps goal (w :: a :: b :: r) || checkChildP n k targets (w :: a :: b :: r))

def checkNodeP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (gsize : ℕ) (G_pow : Array (List ℕ))
    (k : ℕ) (cur prev : Array (List (BitVec n) × List (ℕ × ℕ))) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hs) =>
    decide ws.Nodup && !(ws.contains goal) && decide (ws.length ≤ k + 1) &&
    hs.all (fun p => Nat.blt p.1 gsize && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [])).1.map (actB n (G_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepP n jumps goal k extra targets a b r)

def checkBlockP (n : ℕ) (jumps : List ℕ) (goal : BitVec n) (gsize : ℕ) (G_pow : Array (List ℕ))
    (k : ℕ) (cur prev : Array (List (BitVec n) × List (ℕ × ℕ))) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeP n jumps goal gsize G_pow k cur prev (start + m) &&
      checkBlockP n jumps goal gsize G_pow k cur prev start m

theorem checkBlockP_at {n gsize k start m : ℕ} {jumps : List ℕ} {goal : BitVec n} {G_pow : Array (List ℕ)}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (h : checkBlockP n jumps goal gsize G_pow k cur prev start m = true) (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeP n jumps goal gsize G_pow k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockP, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem node_sound_P {n gsize k i : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (hk : 0 < k) (hi : i < cur.size)
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hprev : ∀ j < prev.size, ¬ live (basicOps n) goal (k - 1) (prev[j]?.getD ([], [])).1.toFinset)
    (hchk : checkNodeP n jumps goal gsize G_pow k cur prev i = true) :
    ¬ live (basicOps n) goal k (cur[i]?.getD ([], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hs⟩
  have hget : cur[i]? = some (ws, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeP at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [])).1.map (actB n (G_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps n) goal (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec hvalid g hg).1
    have hinv_g := (actB_spec hvalid (G_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB n (G_pow[G_inv[g]?.getD 0]?.getD [])) (actB_inj hvalid _ hinv_lt)
      hinv_g (actB_ops hvalid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [])).1.map (actB n (G_pow[g]?.getD []))).toFinset.image
        (actB n (G_pow[G_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left hvalid g hg v]
      · intro hu; exact ⟨actB n (G_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left hvalid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : goal ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
    exact hng (List.mem_toFinset.mp hmem)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec n} (hpair : (a, b, r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps n a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps n) goal (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover n jumps goal (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepP at hstep
      dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes n || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw
      simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq
      simp only [List.length_cons] at plen
      have close (hc : checkChildP n k targets (z :: kept) = true) : False := by
        unfold checkChildP at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with hgt | ⟨t, ht, hss⟩
        · omega
        · rw [sameSet_sound hss] at htail
          exact htargets t ht htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept
        have h1 := hw.1.1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.2
        have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap n a b ▸ hz)

theorem level_sound_P {n gsize k : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ}
    {cur prev : Array (List (BitVec n) × List (ℕ × ℕ))}
    (hk : 0 < k)
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hprev : ∀ j < prev.size, ¬ live (basicOps n) goal (k - 1) (prev[j]?.getD ([], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeP n jumps goal gsize G_pow k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps n) goal k (cur[i]?.getD ([], [])).1.toFinset :=
  fun i hi => node_sound_P hk hi hvalid hprev (hblk i hi)

theorem no_build_of_top {n gsize k rg : ℕ} {jumps : List ℕ} {goal : BitVec n}
    {G_idx G_pow : Array (List ℕ)} {G_inv : Array ℕ} {rows top_ws : List (BitVec n)}
    (hvalid : (List.range gsize).all (symValid n gsize G_idx G_pow G_inv goal) = true)
    (hrg : rg < gsize)
    (hsub : rows.sublists.filter (fun ws => cover n jumps goal ws) = [rows])
    (hmatch : sameSet (rows.map (actB n (G_pow[rg]?.getD []))) top_ws = true)
    (hdead : ¬ live (basicOps n) goal k top_ws.toFinset) :
    ¬ build (basicOps n) goal k rows.toFinset := by
  intro hb
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := rows.filter (· ∈ s)
  have hsubl : ws.Sublist rows := List.filter_sublist
  have heq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hcov : cover n jumps goal ws = true := live_cover (heq.symm ▸ hl)
  have hmem : ws ∈ rows.sublists.filter (fun zs => cover n jumps goal zs) :=
    List.mem_filter.mpr ⟨List.mem_sublists.mpr hsubl, hcov⟩
  rw [hsub, List.mem_singleton] at hmem
  have hs_eq : s = rows.toFinset := by rw [← heq, hmem]
  have hl_rows : live (basicOps n) goal k rows.toFinset := hs_eq ▸ hl
  have hrg_g := (actB_spec hvalid rg hrg).2.2.2.1
  have hrot := live_map (actB n (G_pow[rg]?.getD [])) (actB_inj hvalid rg hrg) hrg_g (actB_ops hvalid rg hrg) hl_rows
  have himg : rows.toFinset.image (actB n (G_pow[rg]?.getD [])) =
      (rows.map (actB n (G_pow[rg]?.getD []))).toFinset := by
    ext u; simp [List.mem_map]
  rw [himg, sameSet_sound hmatch] at hrot
  exact hdead hrot


def jumps4 : List ℕ := [1,2,4,8]

def jumps5 : List ℕ := [1,2,4,8,16]

def jumps6 : List ℕ := [1,2,4,8,16,32]

def rows4 : List (BitVec 16) := [0xaaaa,0xcccc,0xf0f0,0xff00]

def rows5 : List (BitVec 32) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def rows6 : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]

def goal6 : BitVec 64 := 0xfeeaece8eee8e8e8

def projN {m : ℕ} : List ℕ → BitVec m → ℕ
  | [], _ => 0
  | idx :: idxs, w => Nat.bit (w.getLsbD idx) (projN idxs w)

theorem projN_testBit {m : ℕ} : ∀ (idxs : List ℕ) (w : BitVec m) (k : ℕ),
    (projN idxs w).testBit k = (idxs[k]?.map w.getLsbD).getD false
  | [], _, _ => by simp [projN]
  | idx :: idxs, w, 0 => by simp [projN]
  | idx :: idxs, w, k + 1 => by simp [projN, Nat.testBit_bit_succ, projN_testBit idxs w k]

def projB (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) : BitVec n := BitVec.ofNat n (projN idxs w)
def projS (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) : BitVec n := nrm n (projB n idxs w)

theorem projB_getLsbD (n : ℕ) {m : ℕ} (idxs : List ℕ) (w : BitVec m) (k : ℕ) (hk : k < n) :
    (projB n idxs w).getLsbD k = (idxs[k]?.map w.getLsbD).getD false := by
  unfold projB; rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and, projN_testBit]

theorem projB_and (n : ℕ) {m : ℕ} (idxs : List ℕ) (a b : BitVec m) :
    projB n idxs (a &&& b) = projB n idxs a &&& projB n idxs b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_and, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases idxs[k]? <;> simp [BitVec.getLsbD_and]

theorem projB_or (n : ℕ) {m : ℕ} (idxs : List ℕ) (a b : BitVec m) :
    projB n idxs (a ||| b) = projB n idxs a ||| projB n idxs b := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_or, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases idxs[k]? <;> simp [BitVec.getLsbD_or]

theorem projB_not (n : ℕ) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n) (hlt : ∀ idx ∈ idxs, idx < m) (a : BitVec m) :
    projB n idxs (~~~a) = ~~~projB n idxs a := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_not, projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  have hk' : k < idxs.length := by omega
  rw [List.getElem?_eq_getElem hk']
  have hmem := hlt idxs[k] (List.getElem_mem hk')
  simp [hk, hmem]

theorem projB_zero (n : ℕ) {m : ℕ} (idxs : List ℕ) : projB n idxs (0 : BitVec m) = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [projB_getLsbD n _ _ k hk]; cases idxs[k]? <;> simp

theorem projB_mask (n : ℕ) {m : ℕ} (idxs : List ℕ) (mask : BitVec m)
    (hm : ∀ idx ∈ idxs, mask.getLsbD idx = true) (w : BitVec m) :
    projB n idxs (w &&& mask) = projB n idxs w := by
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [projB_getLsbD n _ _ k hk, projB_getLsbD n _ _ k hk]
  cases h : idxs[k]? with
  | none => rfl
  | some idx =>
    have hmem : idx ∈ idxs := List.mem_of_getElem? h
    simp [BitVec.getLsbD_and, hm idx hmem]

theorem nrm_bit0 (n : ℕ) (hn : 0 < n) (u : BitVec n) : (nrm n u).getLsbD 0 = false := by
  unfold nrm
  cases h : u.getLsbD 0
  · simp only [Bool.false_eq_true, ite_false, h]
  · simp only [ite_true, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_true]

theorem projS_ne_allOnes (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (w : BitVec m) :
    projS n idxs w ≠ BitVec.allOnes n := by
  intro h
  have := nrm_bit0 n hn (projB n idxs w)
  change (projS n idxs w).getLsbD 0 = false at this
  rw [h, BitVec.getLsbD_allOnes, decide_eq_true hn] at this
  exact Bool.noConfusion this

theorem nrm_zero (n : ℕ) : nrm n 0 = 0 := by unfold nrm; simp
theorem projS_zero (n : ℕ) {m : ℕ} (idxs : List ℕ) : projS n idxs (0 : BitVec m) = 0 := by
  unfold projS; rw [projB_zero, nrm_zero]
theorem projS_mask (n : ℕ) {m : ℕ} (idxs : List ℕ) (mask : BitVec m)
    (hm : ∀ idx ∈ idxs, mask.getLsbD idx = true) (w : BitVec m) :
    projS n idxs (w &&& mask) = projS n idxs w := by
  unfold projS; rw [projB_mask n idxs mask hm w]

theorem nrm_neg (n : ℕ) (hn : 0 < n) (u : BitVec n) : nrm n (~~~u) = nrm n u := by
  unfold nrm
  cases h : u.getLsbD 0
  · have h1 : (~~~u).getLsbD 0 = true := by
      simp only [BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_false]
    rw [h1]; simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.not_not]
  · have h1 : (~~~u).getLsbD 0 = false := by
      simp only [BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, h, Bool.not_true]
    rw [h1]; simp only [ite_true, ite_false, Bool.false_eq_true]

theorem projS_not (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) (w : BitVec m) :
    projS n idxs (~~~w) = projS n idxs w := by
  unfold projS; rw [projB_not n idxs hlen hlt w, nrm_neg n hn]

theorem nrm_ops (n : ℕ) (hn : 0 < n) (x y z : BitVec n) (hx : x.getLsbD 0 = false) (hy : y.getLsbD 0 = false)
    (hz : z ∈ ops n x y ∨ z ∈ ops n (~~~x) y ∨ z ∈ ops n x (~~~y) ∨ z ∈ ops n (~~~x) (~~~y)) :
    nrm n z ∈ ops n x y := by
  have nrm_f (u : BitVec n) (hu : u.getLsbD 0 = false) : nrm n u = u := by
    unfold nrm; simp only [hu, Bool.false_eq_true, ite_false]
  have nrm_t (u : BitVec n) (hu : u.getLsbD 0 = true) : nrm n u = ~~~u := by
    unfold nrm; simp only [hu, ite_true]
  have b_eq (u v : BitVec n) (h : ∀ i < n, u.getLsbD i = v.getLsbD i) : u = v := BitVec.eq_of_getLsbD_eq h
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · left; exact nrm_f _ (by simp only [BitVec.getLsbD_and, hx, hy, Bool.and_false])
  · right; left; exact nrm_f _ (by simp only [BitVec.getLsbD_or, hx, hy, Bool.or_false])
  · right; right; left; exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right; exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.and_false])]
    exact BitVec.and_comm ..
  · right; right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.true_or])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; left
    exact nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])
  · right; right; right
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.or_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.false_and])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, hx, hy, Bool.not_false, Bool.and_true])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · left
    rw [nrm_t _ (by simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.true_or])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; right
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.not_true, Bool.and_false])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  · right; right; left
    rw [nrm_f _ (by simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, decide_eq_true hn, Bool.true_and, hx, hy, Bool.not_false, Bool.not_true, Bool.and_false])]
    exact b_eq _ _ fun i hi => by simp only [BitVec.getLsbD_not, BitVec.getLsbD_and, decide_eq_true hi, Bool.true_and]; cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

theorem projS_ops (n : ℕ) (hn : 0 < n) {m : ℕ} (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) (a b z : BitVec m) (hz : z ∈ ops m a b) :
    projS n idxs z ∈ ops n (projS n idxs a) (projS n idxs b) := by
  have hrest : projB n idxs z ∈ ops n (projB n idxs a) (projB n idxs b) := by
    simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
    rcases hz with rfl | rfl | rfl | rfl
    · left; exact projB_and n idxs a b
    · right; left; exact projB_or n idxs a b
    · right; right; left; rw [projB_and, projB_not n idxs hlen hlt]
    · right; right; right; rw [projB_and, projB_not n idxs hlen hlt]
  apply nrm_ops n hn (projS n idxs a) (projS n idxs b) (projB n idxs z) (nrm_bit0 n hn _) (nrm_bit0 n hn _)
  unfold projS nrm
  cases ha : (projB n idxs a).getLsbD 0 <;> cases hb : (projB n idxs b).getLsbD 0 <;>
    simp only [ite_true, ite_false, Bool.false_eq_true, BitVec.not_not]
  · exact Or.inl hrest
  · exact Or.inr (Or.inr (Or.inl hrest))
  · exact Or.inr (Or.inl hrest)
  · exact Or.inr (Or.inr (Or.inr hrest))

theorem ops_zero_left (n : ℕ) (y : BitVec n) : ∀ w ∈ ops n 0 y, w = 0 ∨ w = y := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · left; exact BitVec.zero_and
  · right; exact BitVec.zero_or
  · left; exact BitVec.zero_and
  · right; rw [show ~~~(0 : BitVec n) = BitVec.allOnes n from BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi], BitVec.and_allOnes]

theorem ops_zero_right (n : ℕ) (x : BitVec n) : ∀ w ∈ ops n x 0, w = 0 ∨ w = x := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · left; exact BitVec.and_zero
  · right; exact BitVec.or_zero
  · right; rw [show ~~~(0 : BitVec n) = BitVec.allOnes n from BitVec.eq_of_getLsbD_eq fun i hi => by simp [hi], BitVec.and_allOnes]
  · left; exact BitVec.zero_and

theorem ops_self (n : ℕ) (x : BitVec n) : ∀ w ∈ ops n x x, w = 0 ∨ w = x := by
  intro w hw; simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · right; exact BitVec.and_self
  · right; exact BitVec.or_self
  · left; exact BitVec.and_not_self x
  · left; exact BitVec.and_not_self x

def zCount {m n : ℕ} (f : BitVec m → BitVec n) (s : Finset (BitVec m)) : ℕ :=
  (s.filter (fun w => f w = 0)).card
def nonZeroImg {m n : ℕ} (f : BitVec m → BitVec n) (s : Finset (BitVec m)) : Finset (BitVec n) :=
  (s.image f).erase 0

set_option maxRecDepth 100000 in
theorem live_restrict {m n : ℕ} (hn : 0 < n) (idxs : List ℕ) (hlen : idxs.length = n)
    (hlt : ∀ idx ∈ idxs, idx < m) {opsM : BitVec m → BitVec m → Finset (BitVec m)}
    (hopsM : ∀ a b z, z ∈ opsM a b → z ∈ ops m a b)
    {g : BitVec m} {goalN : BitVec n} (hg : projS n idxs g = goalN) (hgnz : goalN ≠ 0)
    {k : ℕ} {s : Finset (BitVec m)} (h : live opsM g k s) :
    build (basicOps n) goalN (k - zCount (projS n idxs) s) (nonZeroImg (projS n idxs) s) := by
  let f : BitVec m → BitVec n := projS n idxs
  change build (basicOps n) goalN (k - zCount f s) (nonZeroImg f s)
  induction k generalizing s with
  | zero =>
    change s = {g} at h; subst h
    have hzc : zCount f {g} = 0 := by
      unfold zCount; rw [Finset.filter_singleton, if_neg (by change projS n idxs g ≠ 0; rw [hg]; exact hgnz)]; rfl
    rw [hzc]; change goalN ∈ nonZeroImg f {g}
    exact Finset.mem_erase.mpr ⟨hgnz, Finset.mem_image.mpr ⟨g, Finset.mem_singleton_self g, hg⟩⟩
  | succ k ih =>
    have hsc := live_card h
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, hs_eq, tail⟩
    · exact build_mono_k (by omega) (ih skip)
    · have htail := ih tail
      have hz_ops : f z ∈ ops n (f a) (f b) := projS_ops n hn idxs hlen hlt a b z (hopsM a b z hz)
      have hsub_rest : nonZeroImg f rest ⊆ nonZeroImg f s := by
        intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hu ⊢
        obtain ⟨hne, v, hv, rfl⟩ := hu; exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
      have hcard_rest : zCount f rest ≤ zCount f (insert z rest) := by
        unfold zCount; exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert z rest))
      by_cases hza : f a = 0
      · have hzb_or := ops_zero_left n (f b) (f z) (hza ▸ hz_ops)
        have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
          intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
          obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
          · rcases hzb_or with h0 | h1; exact (hne h0).elim; exact ⟨hne, b, hb, h1.symm⟩
          · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
        have hm : zCount f s ≤ zCount f (insert z rest) + 1 := by
          by_cases hzb : f b = 0
          · have hzz : f z = 0 := by rcases hzb_or with h0 | h1; exact h0; exact h1.trans hzb
            have hz_nr : z ∉ rest := fun hm => hout (by rw [hs_eq]; simp [hm])
            have h1 : zCount f (insert z rest) = zCount f rest + 1 := by
              unfold zCount; rw [Finset.filter_insert, if_pos hzz, Finset.card_insert_of_notMem (by simp [hz_nr])]
            have h2 : zCount f s ≤ zCount f rest + 2 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_pos hzb, if_pos hza]
              have hc1 := Finset.card_insert_le a (insert b (rest.filter (fun w => f w = 0)))
              have hc2 := Finset.card_insert_le b (rest.filter (fun w => f w = 0))
              omega
            omega
          · have h2 : zCount f s ≤ zCount f rest + 1 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_neg hzb, if_pos hza]
              exact Finset.card_insert_le a (rest.filter (fun w => f w = 0))
            omega
        exact build_mono_k (by omega) (build_mono_av hsub htail)
      · by_cases hzb : f b = 0
        · have hza_or := ops_zero_right n (f a) (f z) (hzb ▸ hz_ops)
          have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
            intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
            obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
            · rcases hza_or with h0 | h1; exact (hne h0).elim; exact ⟨hne, a, ha, h1.symm⟩
            · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
          have hm : zCount f s ≤ zCount f (insert z rest) + 1 := by
            have h2 : zCount f s ≤ zCount f rest + 1 := by
              unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_pos hzb, if_neg hza]
              exact Finset.card_insert_le b (rest.filter (fun w => f w = 0))
            omega
          exact build_mono_k (by omega) (build_mono_av hsub htail)
        · have hzc_eq : zCount f s = zCount f rest := by
            unfold zCount; rw [hs_eq, Finset.filter_insert, Finset.filter_insert, if_neg hzb, if_neg hza]
          have hzc_le : zCount f s ≤ k := by
            have hsubf : insert a (insert b (s.filter (fun w => f w = 0))) ⊆ s := by
              intro u hu
              rcases Finset.mem_insert.mp hu with rfl | hu
              · exact ha
              · rcases Finset.mem_insert.mp hu with rfl | hu
                · exact hb
                · exact (Finset.mem_filter.mp hu).1
            have han : a ∉ insert b (s.filter (fun w => f w = 0)) := by
              simp only [Finset.mem_insert, Finset.mem_filter, not_or]; exact ⟨hab, fun h => hza h.2⟩
            have hbn : b ∉ s.filter (fun w => f w = 0) := by
              simp only [Finset.mem_filter]; exact fun h => hzb h.2
            have hle := Finset.card_le_card hsubf
            rw [Finset.card_insert_of_notMem han, Finset.card_insert_of_notMem hbn] at hle
            unfold zCount; omega
          by_cases hzz : f z = 0
          · have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
              intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
              obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
              · exact (hne hzz).elim
              · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
            exact build_mono_k (by omega) (build_mono_av hsub htail)
          · by_cases heqab : f a = f b
            · have hsame := ops_self n (f a) (f z) (heqab ▸ hz_ops)
              have hsub : nonZeroImg f (insert z rest) ⊆ nonZeroImg f s := by
                intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu ⊢
                obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
                · rcases hsame with h0 | h1; exact (hne h0).elim; exact ⟨hne, a, ha, h1.symm⟩
                · exact ⟨hne, v, by rw [hs_eq]; simp [hv], rfl⟩
              exact build_mono_k (by omega) (build_mono_av hsub htail)
            · have hstep : build (basicOps n) goalN ((k - zCount f (insert z rest)) + 1) (nonZeroImg f s) := by
                refine Or.inr ⟨f a, ?_, f b, ?_, heqab, f z, ?_, ?_⟩
                · exact Finset.mem_erase.mpr ⟨hza, Finset.mem_image_of_mem f ha⟩
                · exact Finset.mem_erase.mpr ⟨hzb, Finset.mem_image_of_mem f hb⟩
                · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
                  exact ⟨hz_ops, hzz, projS_ne_allOnes n hn idxs z⟩
                · apply build_mono_av _ htail
                  intro u hu; simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, Finset.mem_insert] at hu
                  obtain ⟨hne, v, rfl | hv, rfl⟩ := hu
                  · exact Finset.mem_insert_self _ _
                  · exact Finset.mem_insert_of_mem (hsub_rest (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f hv⟩))
              exact build_mono_k (by omega) hstep

def b4_0_goal : BitVec 16 := 0xeaa8
def b4_0_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_0_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_0_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_0_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_0_s2 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_0_p2 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_0_s3 : List ℕ := [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15]
def b4_0_p3 : List ℕ := [1,2,16,32,256,512,4096,8192,4,8,64,128,1024,2048,16384,32768]
def b4_0_s4 : List ℕ := [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15]
def b4_0_p4 : List ℕ := [1,2,256,512,4,8,1024,2048,16,32,4096,8192,64,128,16384,32768]
def b4_0_s5 : List ℕ := [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15]
def b4_0_p5 : List ℕ := [1,2,256,512,16,32,4096,8192,4,8,1024,2048,64,128,16384,32768]
def b4_0_idx : Array (List ℕ) := Array.mk [b4_0_s0,b4_0_s1,b4_0_s2,b4_0_s3,b4_0_s4,b4_0_s5]
def b4_0_pow : Array (List ℕ) := Array.mk [b4_0_p0,b4_0_p1,b4_0_p2,b4_0_p3,b4_0_p4,b4_0_p5]
def b4_0_inv : Array ℕ := Array.mk [0,1,2,4,3,5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_G_valid : (List.range 6).all (symValid 16 6 b4_0_idx b4_0_pow b4_0_inv b4_0_goal) = true := by decide +kernel
def b4_0_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x55aa,0xcccc,0xf0f0],[]),
([0xff0,0xaaaa,0xcccc],[])
]
def b4_0_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff88],[]),
([0x44cc,0xaaaa,0xf0f0,0xff00],[]),
([0xaaaa,0xc8c8,0xf0f0,0xff00],[]),
([0xee,0xaaaa,0xcccc,0xf0f0],[]),
([0xaa,0x5500,0xcccc,0xf0f0],[(0,0)]),
([0xaaaa,0xc0c0,0xfcfc,0xff00],[(3,1)]),
([0xaaaa,0xcccc,0xf0f0,0xff0c],[]),
([0xaaaa,0xc0cc,0xf0f0,0xff00],[]),
([0xcc,0x3300,0xaaaa,0xf0f0],[(2,1)])
]
def b4_0_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(1,0),(4,1),(5,1)]),
([0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00],[(0,3),(1,3),(2,2),(3,2)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,4)]),
([0x4444,0xaaaa,0xcccc,0xf0f0,0xff00],[(4,4)]),
([0xaaaa,0xc0c0,0xcccc,0xf0f0,0xff00],[(0,5)]),
([0xaaaa,0xcccc,0xf0f0,0xfcfc,0xff00],[(0,5)]),
([0xcc,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,8),(1,6),(4,7)])
]
def b4_0_L5 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(1,5),(1,6),(2,0),(2,1),(2,3),(2,6),(3,0),(3,1),(3,3),(3,6),(4,2),(4,4),(4,5),(4,6),(5,6)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_2_0 : checkBlockP 16 jumps4 b4_0_goal 6 b4_0_pow 2 b4_0_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_2 : ∀ i < b4_0_L2.size, checkNodeP 16 jumps4 b4_0_goal 6 b4_0_pow 2 b4_0_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_0_L2.size = 2 := by decide +kernel
  exact checkBlockP_at b4_0_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_3_0 : checkBlockP 16 jumps4 b4_0_goal 6 b4_0_pow 3 b4_0_L3 b4_0_L2 0 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_3 : ∀ i < b4_0_L3.size, checkNodeP 16 jumps4 b4_0_goal 6 b4_0_pow 3 b4_0_L3 b4_0_L2 i = true := by
  intro i hi
  have hsz : b4_0_L3.size = 9 := by decide +kernel
  exact checkBlockP_at b4_0_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_4_0 : checkBlockP 16 jumps4 b4_0_goal 6 b4_0_pow 4 b4_0_L4 b4_0_L3 0 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_4 : ∀ i < b4_0_L4.size, checkNodeP 16 jumps4 b4_0_goal 6 b4_0_pow 4 b4_0_L4 b4_0_L3 i = true := by
  intro i hi
  have hsz : b4_0_L4.size = 7 := by decide +kernel
  exact checkBlockP_at b4_0_chk_4_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_5_0 : checkBlockP 16 jumps4 b4_0_goal 6 b4_0_pow 5 b4_0_L5 b4_0_L4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_5 : ∀ i < b4_0_L5.size, checkNodeP 16 jumps4 b4_0_goal 6 b4_0_pow 5 b4_0_L5 b4_0_L4 i = true := by
  intro i hi
  have hsz : b4_0_L5.size = 1 := by decide +kernel
  exact checkBlockP_at b4_0_chk_5_0 i (Nat.zero_le _) (by omega)
theorem b4_0_L2_sound : ∀ i < b4_0_L2.size, ¬ live (basicOps 16) b4_0_goal 2 (b4_0_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid (fun j hj => by simp at hj) b4_0_chk_2
theorem b4_0_L3_sound : ∀ i < b4_0_L3.size, ¬ live (basicOps 16) b4_0_goal 3 (b4_0_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L2_sound b4_0_chk_3
theorem b4_0_L4_sound : ∀ i < b4_0_L4.size, ¬ live (basicOps 16) b4_0_goal 4 (b4_0_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L3_sound b4_0_chk_4
theorem b4_0_L5_sound : ∀ i < b4_0_L5.size, ¬ live (basicOps 16) b4_0_goal 5 (b4_0_L5[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L4_sound b4_0_chk_5
set_option maxRecDepth 100000 in
theorem b4_0_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_0_goal ws) = [rows4] := by decide +kernel
theorem b4_0_top_match : sameSet (rows4.map (actB 16 (b4_0_pow[0]?.getD []))) (b4_0_L5[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_0_no_build : ¬ build (basicOps 16) b4_0_goal 5 rows4.toFinset :=
  no_build_of_top b4_0_G_valid (by decide) b4_0_sublists b4_0_top_match (b4_0_L5_sound 0 (by decide))

def b4_1_goal : BitVec 16 := 0xe8a8
def b4_1_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_1_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_1_s1 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_1_p1 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_1_idx : Array (List ℕ) := Array.mk [b4_1_s0,b4_1_s1]
def b4_1_pow : Array (List ℕ) := Array.mk [b4_1_p0,b4_1_p1]
def b4_1_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_G_valid : (List.range 2).all (symValid 16 2 b4_1_idx b4_1_pow b4_1_inv b4_1_goal) = true := by decide +kernel
def b4_1_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcc88,0xf0f0],[]),
([0xaaaa,0xcc0c,0xf0f0],[])
]
def b4_1_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(1,0)]),
([0x5500,0xaaaa,0xcccc,0xf0f0],[]),
([0xaaaa,0xcc00,0xcccc,0xf0f0],[]),
([0xcc,0xaaaa,0xcccc,0xf0f0],[(1,1)])
]
def b4_1_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_2_0 : checkBlockP 16 jumps4 b4_1_goal 2 b4_1_pow 2 b4_1_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_2 : ∀ i < b4_1_L2.size, checkNodeP 16 jumps4 b4_1_goal 2 b4_1_pow 2 b4_1_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_1_L2.size = 2 := by decide +kernel
  exact checkBlockP_at b4_1_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_3_0 : checkBlockP 16 jumps4 b4_1_goal 2 b4_1_pow 3 b4_1_L3 b4_1_L2 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_3 : ∀ i < b4_1_L3.size, checkNodeP 16 jumps4 b4_1_goal 2 b4_1_pow 3 b4_1_L3 b4_1_L2 i = true := by
  intro i hi
  have hsz : b4_1_L3.size = 4 := by decide +kernel
  exact checkBlockP_at b4_1_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_4_0 : checkBlockP 16 jumps4 b4_1_goal 2 b4_1_pow 4 b4_1_L4 b4_1_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_4 : ∀ i < b4_1_L4.size, checkNodeP 16 jumps4 b4_1_goal 2 b4_1_pow 4 b4_1_L4 b4_1_L3 i = true := by
  intro i hi
  have hsz : b4_1_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_1_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_1_L2_sound : ∀ i < b4_1_L2.size, ¬ live (basicOps 16) b4_1_goal 2 (b4_1_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid (fun j hj => by simp at hj) b4_1_chk_2
theorem b4_1_L3_sound : ∀ i < b4_1_L3.size, ¬ live (basicOps 16) b4_1_goal 3 (b4_1_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L2_sound b4_1_chk_3
theorem b4_1_L4_sound : ∀ i < b4_1_L4.size, ¬ live (basicOps 16) b4_1_goal 4 (b4_1_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L3_sound b4_1_chk_4
set_option maxRecDepth 100000 in
theorem b4_1_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_1_goal ws) = [rows4] := by decide +kernel
theorem b4_1_top_match : sameSet (rows4.map (actB 16 (b4_1_pow[0]?.getD []))) (b4_1_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_1_no_build : ¬ build (basicOps 16) b4_1_goal 4 rows4.toFinset :=
  no_build_of_top b4_1_G_valid (by decide) b4_1_sublists b4_1_top_match (b4_1_L4_sound 0 (by decide))

def b4_2_goal : BitVec 16 := 0xeae8
def b4_2_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_2_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_2_s1 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_2_p1 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_2_idx : Array (List ℕ) := Array.mk [b4_2_s0,b4_2_s1]
def b4_2_pow : Array (List ℕ) := Array.mk [b4_2_p0,b4_2_p1]
def b4_2_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_G_valid : (List.range 2).all (symValid 16 2 b4_2_idx b4_2_pow b4_2_inv b4_2_goal) = true := by decide +kernel
def b4_2_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfaf0],[]),
([0xaaaa,0xcccc,0xf3f0],[])
]
def b4_2_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaa00,0xaaaa,0xcccc,0xf0f0],[(0,0),(1,0)]),
([0xaa,0xaaaa,0xcccc,0xf0f0],[]),
([0xaaaa,0xcccc,0xf0f0,0xffcc],[]),
([0xf00,0xaaaa,0xcccc,0xf0f0],[(1,1)])
]
def b4_2_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_2_0 : checkBlockP 16 jumps4 b4_2_goal 2 b4_2_pow 2 b4_2_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_2 : ∀ i < b4_2_L2.size, checkNodeP 16 jumps4 b4_2_goal 2 b4_2_pow 2 b4_2_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_2_L2.size = 2 := by decide +kernel
  exact checkBlockP_at b4_2_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_3_0 : checkBlockP 16 jumps4 b4_2_goal 2 b4_2_pow 3 b4_2_L3 b4_2_L2 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_3 : ∀ i < b4_2_L3.size, checkNodeP 16 jumps4 b4_2_goal 2 b4_2_pow 3 b4_2_L3 b4_2_L2 i = true := by
  intro i hi
  have hsz : b4_2_L3.size = 4 := by decide +kernel
  exact checkBlockP_at b4_2_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_4_0 : checkBlockP 16 jumps4 b4_2_goal 2 b4_2_pow 4 b4_2_L4 b4_2_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_4 : ∀ i < b4_2_L4.size, checkNodeP 16 jumps4 b4_2_goal 2 b4_2_pow 4 b4_2_L4 b4_2_L3 i = true := by
  intro i hi
  have hsz : b4_2_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_2_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_2_L2_sound : ∀ i < b4_2_L2.size, ¬ live (basicOps 16) b4_2_goal 2 (b4_2_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_2_G_valid (fun j hj => by simp at hj) b4_2_chk_2
theorem b4_2_L3_sound : ∀ i < b4_2_L3.size, ¬ live (basicOps 16) b4_2_goal 3 (b4_2_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_2_G_valid b4_2_L2_sound b4_2_chk_3
theorem b4_2_L4_sound : ∀ i < b4_2_L4.size, ¬ live (basicOps 16) b4_2_goal 4 (b4_2_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_2_G_valid b4_2_L3_sound b4_2_chk_4
set_option maxRecDepth 100000 in
theorem b4_2_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_2_goal ws) = [rows4] := by decide +kernel
theorem b4_2_top_match : sameSet (rows4.map (actB 16 (b4_2_pow[0]?.getD []))) (b4_2_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_2_no_build : ¬ build (basicOps 16) b4_2_goal 4 rows4.toFinset :=
  no_build_of_top b4_2_G_valid (by decide) b4_2_sublists b4_2_top_match (b4_2_L4_sound 0 (by decide))

def b4_3_goal : BitVec 16 := 0xfeea
def b4_3_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_3_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_3_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_3_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_3_s2 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_3_p2 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_3_s3 : List ℕ := [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15]
def b4_3_p3 : List ℕ := [1,2,16,32,256,512,4096,8192,4,8,64,128,1024,2048,16384,32768]
def b4_3_s4 : List ℕ := [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15]
def b4_3_p4 : List ℕ := [1,2,256,512,4,8,1024,2048,16,32,4096,8192,64,128,16384,32768]
def b4_3_s5 : List ℕ := [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15]
def b4_3_p5 : List ℕ := [1,2,256,512,16,32,4096,8192,4,8,1024,2048,64,128,16384,32768]
def b4_3_idx : Array (List ℕ) := Array.mk [b4_3_s0,b4_3_s1,b4_3_s2,b4_3_s3,b4_3_s4,b4_3_s5]
def b4_3_pow : Array (List ℕ) := Array.mk [b4_3_p0,b4_3_p1,b4_3_p2,b4_3_p3,b4_3_p4,b4_3_p5]
def b4_3_inv : Array ℕ := Array.mk [0,1,2,4,3,5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_G_valid : (List.range 6).all (symValid 16 6 b4_3_idx b4_3_pow b4_3_inv b4_3_goal) = true := by decide +kernel
def b4_3_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xcccc,0xfafa,0xffaa],[])
]
def b4_3_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(2,0)]),
([0x4444,0xaaaa,0xf0f0,0xff00],[])
]
def b4_3_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(1,0),(2,1),(3,1),(4,0)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_2_0 : checkBlockP 16 jumps4 b4_3_goal 6 b4_3_pow 2 b4_3_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_2 : ∀ i < b4_3_L2.size, checkNodeP 16 jumps4 b4_3_goal 6 b4_3_pow 2 b4_3_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_3_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_3_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_3_0 : checkBlockP 16 jumps4 b4_3_goal 6 b4_3_pow 3 b4_3_L3 b4_3_L2 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_3 : ∀ i < b4_3_L3.size, checkNodeP 16 jumps4 b4_3_goal 6 b4_3_pow 3 b4_3_L3 b4_3_L2 i = true := by
  intro i hi
  have hsz : b4_3_L3.size = 2 := by decide +kernel
  exact checkBlockP_at b4_3_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_4_0 : checkBlockP 16 jumps4 b4_3_goal 6 b4_3_pow 4 b4_3_L4 b4_3_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_4 : ∀ i < b4_3_L4.size, checkNodeP 16 jumps4 b4_3_goal 6 b4_3_pow 4 b4_3_L4 b4_3_L3 i = true := by
  intro i hi
  have hsz : b4_3_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_3_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_3_L2_sound : ∀ i < b4_3_L2.size, ¬ live (basicOps 16) b4_3_goal 2 (b4_3_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_3_G_valid (fun j hj => by simp at hj) b4_3_chk_2
theorem b4_3_L3_sound : ∀ i < b4_3_L3.size, ¬ live (basicOps 16) b4_3_goal 3 (b4_3_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_3_G_valid b4_3_L2_sound b4_3_chk_3
theorem b4_3_L4_sound : ∀ i < b4_3_L4.size, ¬ live (basicOps 16) b4_3_goal 4 (b4_3_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_3_G_valid b4_3_L3_sound b4_3_chk_4
set_option maxRecDepth 100000 in
theorem b4_3_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_3_goal ws) = [rows4] := by decide +kernel
theorem b4_3_top_match : sameSet (rows4.map (actB 16 (b4_3_pow[0]?.getD []))) (b4_3_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_3_no_build : ¬ build (basicOps 16) b4_3_goal 4 rows4.toFinset :=
  no_build_of_top b4_3_G_valid (by decide) b4_3_sublists b4_3_top_match (b4_3_L4_sound 0 (by decide))

def b4_4_goal : BitVec 16 := 0xeee8
def b4_4_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_4_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_4_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_4_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_4_s2 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_4_p2 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_4_s3 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_4_p3 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_4_idx : Array (List ℕ) := Array.mk [b4_4_s0,b4_4_s1,b4_4_s2,b4_4_s3]
def b4_4_pow : Array (List ℕ) := Array.mk [b4_4_p0,b4_4_p1,b4_4_p2,b4_4_p3]
def b4_4_inv : Array ℕ := Array.mk [0,1,2,3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_G_valid : (List.range 4).all (symValid 16 4 b4_4_idx b4_4_pow b4_4_inv b4_4_goal) = true := by decide +kernel
def b4_4_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfff0],[])
]
def b4_4_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfff0],[]),
([0xaaaa,0xcccc,0xf0f0,0xfff0],[]),
([0xf0,0xaaaa,0xcccc,0xff00],[(0,0)])
]
def b4_4_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,1),(1,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_2_0 : checkBlockP 16 jumps4 b4_4_goal 4 b4_4_pow 2 b4_4_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_2 : ∀ i < b4_4_L2.size, checkNodeP 16 jumps4 b4_4_goal 4 b4_4_pow 2 b4_4_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_4_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_4_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_3_0 : checkBlockP 16 jumps4 b4_4_goal 4 b4_4_pow 3 b4_4_L3 b4_4_L2 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_3 : ∀ i < b4_4_L3.size, checkNodeP 16 jumps4 b4_4_goal 4 b4_4_pow 3 b4_4_L3 b4_4_L2 i = true := by
  intro i hi
  have hsz : b4_4_L3.size = 3 := by decide +kernel
  exact checkBlockP_at b4_4_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_4_0 : checkBlockP 16 jumps4 b4_4_goal 4 b4_4_pow 4 b4_4_L4 b4_4_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_4 : ∀ i < b4_4_L4.size, checkNodeP 16 jumps4 b4_4_goal 4 b4_4_pow 4 b4_4_L4 b4_4_L3 i = true := by
  intro i hi
  have hsz : b4_4_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_4_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_4_L2_sound : ∀ i < b4_4_L2.size, ¬ live (basicOps 16) b4_4_goal 2 (b4_4_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_4_G_valid (fun j hj => by simp at hj) b4_4_chk_2
theorem b4_4_L3_sound : ∀ i < b4_4_L3.size, ¬ live (basicOps 16) b4_4_goal 3 (b4_4_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_4_G_valid b4_4_L2_sound b4_4_chk_3
theorem b4_4_L4_sound : ∀ i < b4_4_L4.size, ¬ live (basicOps 16) b4_4_goal 4 (b4_4_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_4_G_valid b4_4_L3_sound b4_4_chk_4
set_option maxRecDepth 100000 in
theorem b4_4_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_4_goal ws) = [rows4] := by decide +kernel
theorem b4_4_top_match : sameSet (rows4.map (actB 16 (b4_4_pow[0]?.getD []))) (b4_4_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_4_no_build : ¬ build (basicOps 16) b4_4_goal 4 rows4.toFinset :=
  no_build_of_top b4_4_G_valid (by decide) b4_4_sublists b4_4_top_match (b4_4_L4_sound 0 (by decide))

def b4_5_goal : BitVec 16 := 0xe888
def b4_5_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_5_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_5_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_5_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_5_s2 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_5_p2 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_5_s3 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_5_p3 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_5_idx : Array (List ℕ) := Array.mk [b4_5_s0,b4_5_s1,b4_5_s2,b4_5_s3]
def b4_5_pow : Array (List ℕ) := Array.mk [b4_5_p0,b4_5_p1,b4_5_p2,b4_5_p3]
def b4_5_inv : Array ℕ := Array.mk [0,1,2,3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_5_G_valid : (List.range 4).all (symValid 16 4 b4_5_idx b4_5_pow b4_5_inv b4_5_goal) = true := by decide +kernel
def b4_5_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf000],[])
]
def b4_5_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf000],[]),
([0xaaaa,0xcccc,0xf000,0xf0f0],[]),
([0xf0,0xaaaa,0xcccc,0xf0f0],[(0,0)])
]
def b4_5_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,1),(1,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_5_chk_2_0 : checkBlockP 16 jumps4 b4_5_goal 4 b4_5_pow 2 b4_5_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_5_chk_2 : ∀ i < b4_5_L2.size, checkNodeP 16 jumps4 b4_5_goal 4 b4_5_pow 2 b4_5_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_5_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_5_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_5_chk_3_0 : checkBlockP 16 jumps4 b4_5_goal 4 b4_5_pow 3 b4_5_L3 b4_5_L2 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_5_chk_3 : ∀ i < b4_5_L3.size, checkNodeP 16 jumps4 b4_5_goal 4 b4_5_pow 3 b4_5_L3 b4_5_L2 i = true := by
  intro i hi
  have hsz : b4_5_L3.size = 3 := by decide +kernel
  exact checkBlockP_at b4_5_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_5_chk_4_0 : checkBlockP 16 jumps4 b4_5_goal 4 b4_5_pow 4 b4_5_L4 b4_5_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_5_chk_4 : ∀ i < b4_5_L4.size, checkNodeP 16 jumps4 b4_5_goal 4 b4_5_pow 4 b4_5_L4 b4_5_L3 i = true := by
  intro i hi
  have hsz : b4_5_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_5_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_5_L2_sound : ∀ i < b4_5_L2.size, ¬ live (basicOps 16) b4_5_goal 2 (b4_5_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_5_G_valid (fun j hj => by simp at hj) b4_5_chk_2
theorem b4_5_L3_sound : ∀ i < b4_5_L3.size, ¬ live (basicOps 16) b4_5_goal 3 (b4_5_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_5_G_valid b4_5_L2_sound b4_5_chk_3
theorem b4_5_L4_sound : ∀ i < b4_5_L4.size, ¬ live (basicOps 16) b4_5_goal 4 (b4_5_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_5_G_valid b4_5_L3_sound b4_5_chk_4
set_option maxRecDepth 100000 in
theorem b4_5_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_5_goal ws) = [rows4] := by decide +kernel
theorem b4_5_top_match : sameSet (rows4.map (actB 16 (b4_5_pow[0]?.getD []))) (b4_5_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_5_no_build : ¬ build (basicOps 16) b4_5_goal 4 rows4.toFinset :=
  no_build_of_top b4_5_G_valid (by decide) b4_5_sublists b4_5_top_match (b4_5_L4_sound 0 (by decide))

def b4_6_goal : BitVec 16 := 0xeac8
def b4_6_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_6_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_6_s1 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_6_p1 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_6_idx : Array (List ℕ) := Array.mk [b4_6_s0,b4_6_s1]
def b4_6_pow : Array (List ℕ) := Array.mk [b4_6_p0,b4_6_p1]
def b4_6_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_6_G_valid : (List.range 2).all (symValid 16 2 b4_6_idx b4_6_pow b4_6_inv b4_6_goal) = true := by decide +kernel
def b4_6_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_6_chk_3_0 : checkBlockP 16 jumps4 b4_6_goal 2 b4_6_pow 3 b4_6_L3 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_6_chk_3 : ∀ i < b4_6_L3.size, checkNodeP 16 jumps4 b4_6_goal 2 b4_6_pow 3 b4_6_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_6_L3.size = 1 := by decide +kernel
  exact checkBlockP_at b4_6_chk_3_0 i (Nat.zero_le _) (by omega)
theorem b4_6_L3_sound : ∀ i < b4_6_L3.size, ¬ live (basicOps 16) b4_6_goal 3 (b4_6_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_6_G_valid (fun j hj => by simp at hj) b4_6_chk_3
set_option maxRecDepth 100000 in
theorem b4_6_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_6_goal ws) = [rows4] := by decide +kernel
theorem b4_6_top_match : sameSet (rows4.map (actB 16 (b4_6_pow[0]?.getD []))) (b4_6_L3[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_6_no_build : ¬ build (basicOps 16) b4_6_goal 3 rows4.toFinset :=
  no_build_of_top b4_6_G_valid (by decide) b4_6_sublists b4_6_top_match (b4_6_L3_sound 0 (by decide))

theorem no_build5_of_proj4 (k4 : ℕ) (base_goal : BitVec 16) (hbnz : base_goal ≠ 0)
    (hbase : ¬ build (basicOps 16) base_goal k4 rows4.toFinset)
    (goal5 : BitVec 32) (idxs4 : List ℕ) (u p0 p1 : ℕ)
    (hp0 : p0 < 32) (hp1 : p1 < 32) (hlen : idxs4.length = 16) (hlt : ∀ idx ∈ idxs4, idx < 32)
    (hpg : projS 16 idxs4 goal5 = base_goal)
    (hxu : projS 16 idxs4 (rows5.getD u 0) = 0)
    (hsub : rows5.all (fun w => projS 16 idxs4 w == 0 || rows4.contains (projS 16 idxs4 w)) = true)
    (hess : rows5.all (fun w => w == rows5.getD u 0 || w.getLsbD p0 == w.getLsbD p1) = true)
    (hdiff : goal5.getLsbD p0 ≠ goal5.getLsbD p1) :
    ¬ build (basicOps 32) goal5 (k4 + 1) rows5.toFinset := by
  intro hb
  obtain ⟨s, hs, hl⟩ := compress hb
  obtain ⟨w, hw, hdw⟩ := live_separates (fun v : BitVec 32 => v.getLsbD p0 ≠ v.getLsbD p1)
    hdiff (ops_diff_ij p0 p1 hp0 hp1) hl
  have hw_eq : w = rows5.getD u 0 := by
    have h1 := List.all_eq_true.mp hess w (List.mem_toFinset.mp (hs hw))
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    exact h1.resolve_right hdw
  have hmem_z : rows5.getD u 0 ∈ s.filter (fun v => projS 16 idxs4 v = 0) :=
    Finset.mem_filter.mpr ⟨hw_eq ▸ hw, hxu⟩
  have hzc_pos : 1 ≤ zCount (projS 16 idxs4) s := Finset.one_le_card.mpr ⟨_, hmem_z⟩
  have hops32 : ∀ a b z : BitVec 32, z ∈ basicOps 32 a b → z ∈ ops 32 a b := fun a b z hz =>
    (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
  have hb16 := live_restrict (by decide : 0 < 16) idxs4 hlen hlt hops32 hpg hbnz hl
  have hsub16 : nonZeroImg (projS 16 idxs4) s ⊆ rows4.toFinset := by
    intro v hv
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hv
    obtain ⟨hne, y, hy, rfl⟩ := hv
    have h1 := List.all_eq_true.mp hsub y (List.mem_toFinset.mp (hs hy))
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h1
    exact List.mem_toFinset.mpr (h1.resolve_left hne)
  exact hbase (build_mono_k (by omega) (build_mono_av hsub16 hb16))

def nrmM32 (m : BitVec 32) (b0 : ℕ) (u : BitVec 32) : BitVec 32 :=
  if u.getLsbD b0 then (~~~u) &&& m else u &&& m

theorem projS_nrmM32 (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 32)
    (m : BitVec 32) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (u : BitVec 32) :
    projS 16 idxs (nrmM32 m b0 u) = projS 16 idxs u := by
  unfold nrmM32
  cases u.getLsbD b0
  · simp only [Bool.false_eq_true, ite_false]
    exact projS_mask 16 idxs m hm u
  · simp only [ite_true]
    rw [projS_mask 16 idxs m hm (~~~u), projS_not 16 (by decide) idxs hlen hlt u]

abbrev W5Node := List (BitVec 32) × List (BitVec 32 × BitVec 32 × BitVec 32) × List ℕ × List (ℕ × ℕ)

def checkReplay32 (m : BitVec 32) (b0 : ℕ) (bank : List (BitVec 32)) :
    List (BitVec 32 × BitVec 32 × BitVec 32) → List (BitVec 32) → Bool
  | [], targets => targets.all (fun t => nrmM32 m b0 t == 0 || bank.contains (nrmM32 m b0 t))
  | (v, a, b) :: rest, targets =>
    bank.contains a && bank.contains b && (ops 32 a b).contains v &&
    checkReplay32 m b0 (v :: bank) rest targets

theorem checkReplay32_sound (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 32)
    (m : BitVec 32) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (g : BitVec 16)
    (steps : List (BitVec 32 × BitVec 32 × BitVec 32)) (targets : List (BitVec 32)) :
    ∀ (bank : List (BitVec 32)) (k : ℕ),
      checkReplay32 m b0 bank steps targets = true →
      build (basicOps 16) g k (nonZeroImg (projS 16 idxs) targets.toFinset) →
      build (basicOps 16) g (k + steps.length) (nonZeroImg (projS 16 idxs) bank.toFinset) := by
  let f : BitVec 32 → BitVec 16 := projS 16 idxs
  have hn : 0 < 16 := by decide
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [checkReplay32, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne
      rw [← projS_nrmM32 idxs hlen hlt m hm b0 t, h0, projS_zero]
    · exact ⟨hne, nrmM32 m b0 t, hmem, projS_nrmM32 idxs hlen hlt m hm b0 t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [checkReplay32, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ha, hb_mem⟩, hv⟩, hrest⟩ := hchk
    have hb' := ih (v :: bank) k hrest hb
    simp only [List.length_cons, show k + (rest.length + 1) = (k + rest.length) + 1 by omega]
    have hfv : f v ∈ ops 16 (f a) (f b) := projS_ops 16 hn idxs hlen hlt a b v hv
    have hsub_ins (hmem_v : f v = 0 ∨ f v ∈ nonZeroImg f bank.toFinset) :
        nonZeroImg f (v :: bank).toFinset ⊆ nonZeroImg f bank.toFinset := by
      intro u hu
      simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
      · rcases hmem_v with h0 | hm'
        · exact (hne h0).elim
        · exact Finset.mem_erase.mp hm' |>.imp_right (fun hi => by simpa [List.mem_toFinset] using hi)
      · exact ⟨hne, w, hw, rfl⟩
    by_cases hv0 : f v = 0
    · exact Or.inl (build_mono_av (hsub_ins (Or.inl hv0)) hb')
    · by_cases ha0 : f a = 0
      · rcases ops_zero_left 16 (f b) (f v) (ha0 ▸ hfv) with h0 | h1
        · exact (hv0 h0).elim
        · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb_mem, h1.symm⟩⟩))) hb')
      · by_cases hb0 : f b = 0
        · rcases ops_zero_right 16 (f a) (f v) (hb0 ▸ hfv) with h0 | h1
          · exact (hv0 h0).elim
          · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
        · by_cases hab : f a = f b
          · rcases ops_self 16 (f a) (f v) (hab ▸ hfv) with h0 | h1
            · exact (hv0 h0).elim
            · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
          · refine Or.inr ⟨f a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr ha)⟩,
              f b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hb_mem)⟩,
              hab, f v, ?_, ?_⟩
            · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
              exact ⟨hfv, hv0, projS_ne_allOnes 16 hn idxs v⟩
            · apply build_mono_av _ hb'
              intro u hu
              simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu
              obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hw)⟩)

def addNeed32 (stock needed : List (BitVec 32)) (u : BitVec 32) : List (BitVec 32) :=
  if u == 0 || stock.contains u || needed.contains u then needed else u :: needed

def buildNeeded32 (m : BitVec 32) (b0 : ℕ) (stock : List (BitVec 32)) :
    List (BitVec 32 × BitVec 32 × BitVec 32) → List (BitVec 32) → List (BitVec 32)
  | [], needed => needed
  | (w, a, b) :: rest, needed =>
    let pw := nrmM32 m b0 w
    let needed' := if needed.contains pw then addNeed32 stock (addNeed32 stock needed (nrmM32 m b0 a)) (nrmM32 m b0 b) else needed
    buildNeeded32 m b0 stock rest needed'

def buildSteps32 (m : BitVec 32) (b0 : ℕ) (needed : List (BitVec 32)) :
    List (BitVec 32 × BitVec 32 × BitVec 32) → List (BitVec 32) → List (BitVec 32 × BitVec 32 × BitVec 32)
  | [], _ => []
  | (w, a, b) :: rest, bank =>
    let pw := nrmM32 m b0 w
    let pa := nrmM32 m b0 a
    let pb := nrmM32 m b0 b
    if needed.contains pw && pw != 0 && !bank.contains pw &&
       bank.contains pa && bank.contains pb && (ops 32 pa pb).contains pw then
      (pw, pa, pb) :: buildSteps32 m b0 needed rest (pw :: bank)
    else
      buildSteps32 m b0 needed rest bank

def checkCofClose32 (lb fuel : ℕ) (m : BitVec 32) (b0 : ℕ) (stock : List (BitVec 32))
    (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) : Bool :=
  let flat := (nxt.filter (fun u => nrmM32 m b0 u == 0)).length
  let rem := fuel - flat
  if Nat.blt rem lb then
    let start := nxt.foldl (fun acc u => addNeed32 stock acc (nrmM32 m b0 u)) []
    if Nat.blt (start.length + rem) lb then
      let needed := buildNeeded32 m b0 stock hist.reverse start
      if Nat.blt (needed.length + rem) lb then
        let steps := buildSteps32 m b0 needed hist stock
        Nat.blt (steps.length + rem) lb && checkReplay32 m b0 stock steps nxt
      else false
    else false
  else false

theorem checkCofClose32_sound_aux (goal5 : BitVec 32) (lb : ℕ) (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 32)
    (m : BitVec 32) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ)
    (stock : List (BitVec 32)) (g : BitVec 16) (hgnz : g ≠ 0)
    (hg : projS 16 idxs goal5 = g)
    (hstock : stock.all (fun w => rows4.contains (projS 16 idxs w)) = true)
    (hnobuild : ¬ build (basicOps 16) g (lb - 1) rows4.toFinset)
    (fuel : ℕ) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32))
    (hnd : nxt.Nodup) (hchk : checkCofClose32 lb fuel m b0 stock hist nxt = true) :
    ¬ live (basicOps 32) goal5 fuel nxt.toFinset := by
  intro hlive
  unfold checkCofClose32 at hchk
  dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops32 : ∀ a b z : BitVec 32, z ∈ basicOps 32 a b → z ∈ ops 32 a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict (by decide : 0 < 16) idxs hlen hlt hops32 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => nrmM32 m b0 u == 0)).length ≤ zCount (projS 16 idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => nrmM32 m b0 u == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]
          apply Finset.card_le_card
          intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_nrmM32 idxs hlen hlt m hm b0 u, hu.2, projS_zero]
        have hrep := checkReplay32_sound idxs hlen hlt m hm b0 g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS 16 idxs) stock.toFinset ⊆ rows4.toFinset := by
          intro u hu
          simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu
          obtain ⟨_, v, hv, rfl⟩ := hu
          have h1 := List.all_eq_true.mp hstock v hv
          simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
          exact List.mem_toFinset.mpr h1
        exact hnobuild (build_mono_k (by omega) (build_mono_av hsub hrep))
      · cases hchk
    · cases hchk
  · cases hchk

def checkChildW5 (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 32)))
    (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) : Bool :=
  decide (nxt.length > k) ||
  cfs.any (fun c => checkCofClose32 (cfLBs[c]?.getD 0) (k - 1) (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt) ||
  targets.any (fun t => sameSet nxt t)

def checkStepW5 (goal5 : BitVec 32) (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k extra : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 32)))
    (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (a b : BitVec 32) (r : List (BitVec 32)) : Bool :=
  (ops 32 a b).all fun w =>
    (w == 0 || w == BitVec.allOnes 32 || w == a || w == b || r.contains w) ||
    let h' := hist ++ [(w, a, b)]
    (!cover 32 jumps5 goal5 (w :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: r)) &&
    ((extra == 0) ||
      ((!cover 32 jumps5 goal5 (w :: a :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: r)) &&
       (!cover 32 jumps5 goal5 (w :: b :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: b :: r)))) &&
    ((extra < 2) || !cover 32 jumps5 goal5 (w :: a :: b :: r) || checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: b :: r))

def checkNodeW5 (goal5 : BitVec 32) (gsize : ℕ) (g5_pow : Array (List ℕ)) (ncf : ℕ)
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k : ℕ) (cur prev : Array W5Node) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hist, cfs, hs) =>
    decide ws.Nodup && !(ws.contains goal5) && decide (ws.length ≤ k + 1) &&
    cfs.all (fun c => Nat.blt c ncf) &&
    hs.all (fun p => Nat.blt p.1 gsize && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 32 (g5_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepW5 goal5 cfLBs cfMasks cfB0s cfStocks k extra cfs targets hist a b r)

def checkBlockW5 (goal5 : BitVec 32) (gsize : ℕ) (g5_pow : Array (List ℕ)) (ncf : ℕ)
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 32)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 32)))
    (k : ℕ) (cur prev : Array W5Node) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev (start + m) &&
      checkBlockW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev start m

theorem checkBlockW5_at {goal5 : BitVec 32} {gsize ncf k start m : ℕ} {g5_pow : Array (List ℕ)}
    {cfLBs cfB0s : Array ℕ} {cfMasks : Array (BitVec 32)} {cfStocks : Array (List (BitVec 32))}
    {cur prev : Array W5Node}
    (h : checkBlockW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev start m = true)
    (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockW5, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem node_sound_W5 {goal5 : BitVec 32} {gsize ncf k i : ℕ}
    {g5_idx g5_pow : Array (List ℕ)} {g5_inv cfLBs cfB0s : Array ℕ}
    {cfMasks : Array (BitVec 32)} {cfStocks : Array (List (BitVec 32))}
    {cur prev : Array W5Node}
    (hk : 0 < k) (hi : i < cur.size)
    (hvalid : (List.range gsize).all (symValid 32 gsize g5_idx g5_pow g5_inv goal5) = true)
    (hcof : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose32 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 32) goal5 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 32) goal5 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hchk : checkNodeW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ¬ live (basicOps 32) goal5 k (cur[i]?.getD ([], [], [], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hist, cfs, hs⟩
  have hget : cur[i]? = some (ws, hist, cfs, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeW5 at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hcfs⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 32 (g5_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps 32) goal5 (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec hvalid g hg).1
    have hinv_g := (actB_spec hvalid (g5_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB 32 (g5_pow[g5_inv[g]?.getD 0]?.getD [])) (actB_inj hvalid _ hinv_lt)
      hinv_g (actB_ops hvalid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [], [], [])).1.map (actB 32 (g5_pow[g]?.getD []))).toFinset.image
        (actB 32 (g5_pow[g5_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [], [], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left hvalid g hg v]
      · intro hu; exact ⟨actB 32 (g5_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left hvalid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : goal5 ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
    exact hng (List.mem_toFinset.mp hmem)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec 32} (hpair : (a, b, r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps 32 a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps 32) goal5 (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover 32 jumps5 goal5 (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepW5 at hstep
      dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes 32 || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw
      simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq
      simp only [List.length_cons] at plen
      have close (hc : checkChildW5 cfLBs cfMasks cfB0s cfStocks k cfs targets (hist ++ [(z, a, b)]) (z :: kept) = true) : False := by
        unfold checkChildW5 at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with (hgt | ⟨c, hcm, hcf⟩) | ⟨t, ht, hss⟩
        · omega
        · exact hcof c (k - 1) (hcfs c hcm) (hist ++ [(z, a, b)]) (z :: kept) hndc hcf htail
        · rw [sameSet_sound hss] at htail
          exact htargets t ht htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept
        have h1 := hw.1.1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.2
        have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap 32 a b ▸ hz)

theorem level_sound_W5 {goal5 : BitVec 32} {gsize ncf k : ℕ}
    {g5_idx g5_pow : Array (List ℕ)} {g5_inv cfLBs cfB0s : Array ℕ}
    {cfMasks : Array (BitVec 32)} {cfStocks : Array (List (BitVec 32))}
    {cur prev : Array W5Node}
    (hk : 0 < k)
    (hvalid : (List.range gsize).all (symValid 32 gsize g5_idx g5_pow g5_inv goal5) = true)
    (hcof : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose32 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 32) goal5 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 32) goal5 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeW5 goal5 gsize g5_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps 32) goal5 k (cur[i]?.getD ([], [], [], [])).1.toFinset :=
  fun i hi => node_sound_W5 hk hi hvalid hcof hprev (hblk i hi)

def u0 : BitVec 32 := 0xaaaaaaaa
def u1 : BitVec 32 := 0xcccccccc
def u2 : BitVec 32 := 0xffff0000
def u3 : BitVec 32 := 0xf0f0f0f0
def u4 : BitVec 32 := 0xff00ff00
def u5 : BitVec 32 := 0xeeeeeeee
def u6 : BitVec 32 := 0x88888888
def u7 : BitVec 32 := 0x22222222
def u8 : BitVec 32 := 0x33003300
def u9 : BitVec 32 := 0xe0e0e0e0
def u10 : BitVec 32 := 0xaa00aa00
def u11 : BitVec 32 := 0xfafafafa
def u12 : BitVec 32 := 0x30303030
def u13 : BitVec 32 := 0x44444444
def u14 : BitVec 32 := 0x70707070
def u15 : BitVec 32 := 0xcc00cc00
def u16 : BitVec 32 := 0xffffcccc
def u17 : BitVec 32 := 0xee00ee00
def u18 : BitVec 32 := 0x55005500
def u19 : BitVec 32 := 0x77007700
def u20 : BitVec 32 := 0x33330000
def u21 : BitVec 32 := 0xffaaffaa
def u22 : BitVec 32 := 0xffff8888
def u23 : BitVec 32 := 0xff000000
def u24 : BitVec 32 := 0xf000f000
def u25 : BitVec 32 := 0xffaaaaaa
def u26 : BitVec 32 := 0xff88ff88
def u27 : BitVec 32 := 0x66666666
def u28 : BitVec 32 := 0xa0a0a0a0
def u29 : BitVec 32 := 0xcc00ff00
def u30 : BitVec 32 := 0x5500ff00

def c5_0_goal : BitVec 32 := 0xeac8e888
def c5_0_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_0_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_0_s1 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15,16,18,17,19,24,26,25,27,20,22,21,23,28,30,29,31]
def c5_0_p1 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768,65536,262144,131072,524288,16777216,67108864,33554432,134217728,1048576,4194304,2097152,8388608,268435456,1073741824,536870912,2147483648]
def c5_0_idx : Array (List ℕ) := Array.mk [c5_0_s0,c5_0_s1]
def c5_0_pow : Array (List ℕ) := Array.mk [c5_0_p0,c5_0_p1]
def c5_0_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_G_valid : (List.range 2).all (symValid 32 2 c5_0_idx c5_0_pow c5_0_inv c5_0_goal) = true := by decide +kernel
def c5_0_m0 : BitVec 32 := 0xf0f0f0f0
def c5_0_st0 : List (BitVec 32) := [0xa0a0a0a0,0xc0c0c0c0,0xf000f000,0xf0f00000]
def c5_0_ix0 : List ℕ := [4,6,5,7,12,14,13,15,20,22,21,23,28,30,29,31]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_0 : c5_0_ix0.length = 16 ∧ (∀ idx ∈ c5_0_ix0, idx < 32) ∧ (∀ idx ∈ c5_0_ix0, c5_0_m0.getLsbD idx = true) ∧ projS 16 c5_0_ix0 c5_0_goal = b4_2_goal ∧ c5_0_st0.all (fun w => rows4.contains (projS 16 c5_0_ix0 w)) = true := by decide +kernel
def c5_0_m1 : BitVec 32 := 0xff00ff00
def c5_0_st1 : List (BitVec 32) := [0xaa00aa00,0xcc00cc00,0xf000f000,0xff000000]
def c5_0_ix1 : List ℕ := [8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_1 : c5_0_ix1.length = 16 ∧ (∀ idx ∈ c5_0_ix1, idx < 32) ∧ (∀ idx ∈ c5_0_ix1, c5_0_m1.getLsbD idx = true) ∧ projS 16 c5_0_ix1 c5_0_goal = b4_2_goal ∧ c5_0_st1.all (fun w => rows4.contains (projS 16 c5_0_ix1 w)) = true := by decide +kernel
def c5_0_m2 : BitVec 32 := 0xffff
def c5_0_st2 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def c5_0_ix2 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_2 : c5_0_ix2.length = 16 ∧ (∀ idx ∈ c5_0_ix2, idx < 32) ∧ (∀ idx ∈ c5_0_ix2, c5_0_m2.getLsbD idx = true) ∧ projS 16 c5_0_ix2 c5_0_goal = b4_5_goal ∧ c5_0_st2.all (fun w => rows4.contains (projS 16 c5_0_ix2 w)) = true := by decide +kernel
def c5_0_m3 : BitVec 32 := 0xffff0000
def c5_0_st3 : List (BitVec 32) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def c5_0_ix3 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_3 : c5_0_ix3.length = 16 ∧ (∀ idx ∈ c5_0_ix3, idx < 32) ∧ (∀ idx ∈ c5_0_ix3, c5_0_m3.getLsbD idx = true) ∧ projS 16 c5_0_ix3 c5_0_goal = b4_6_goal ∧ c5_0_st3.all (fun w => rows4.contains (projS 16 c5_0_ix3 w)) = true := by decide +kernel
def c5_0_cfMasks : Array (BitVec 32) := Array.mk [c5_0_m0,c5_0_m1,c5_0_m2,c5_0_m3]
def c5_0_cfB0s : Array ℕ := Array.mk [4,8,0,16]
def c5_0_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_0_st0,c5_0_st1,c5_0_st2,c5_0_st3]
def c5_0_cfLBs : Array ℕ := Array.mk [5,5,5,4]
theorem c5_0_cof_sound (c fuel : ℕ) (hc : c < 4) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_0_cfLBs[c]?.getD 0) fuel (c5_0_cfMasks[c]?.getD 0) (c5_0_cfB0s[c]?.getD 0) (c5_0_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_0_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix0 c5_0_cspec_0.1 c5_0_cspec_0.2.1 c5_0_m0 c5_0_cspec_0.2.2.1 4 c5_0_st0 b4_2_goal (by decide) c5_0_cspec_0.2.2.2.1 c5_0_cspec_0.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix1 c5_0_cspec_1.1 c5_0_cspec_1.2.1 c5_0_m1 c5_0_cspec_1.2.2.1 8 c5_0_st1 b4_2_goal (by decide) c5_0_cspec_1.2.2.2.1 c5_0_cspec_1.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix2 c5_0_cspec_2.1 c5_0_cspec_2.2.1 c5_0_m2 c5_0_cspec_2.2.2.1 0 c5_0_st2 b4_5_goal (by decide) c5_0_cspec_2.2.2.2.1 c5_0_cspec_2.2.2.2.2 b4_5_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_0_goal 4 c5_0_ix3 c5_0_cspec_3.1 c5_0_cspec_3.2.1 c5_0_m3 c5_0_cspec_3.2.2.1 16 c5_0_st3 b4_6_goal (by decide) c5_0_cspec_3.2.2.2.1 c5_0_cspec_3.2.2.2.2 b4_6_no_build fuel hist nxt hnd hchk
  | c + 4 => omega
def c5_0_L3 : Array W5Node := Array.mk [
([u0,0xeecceecc,u3,0xffffcc00],[],[],[])
]
def c5_0_L4 : Array W5Node := Array.mk [
([u7,u13,u3,u4,u2],[],[],[]),
([u14,u0,u1,u4,u2],[],[],[]),
([0x70f070f0,u0,u1,u4,u2],[],[],[]),
([u0,u1,0xf8f8f8f8,u26,u2],[],[],[]),
([u14,u0,u1,u26,u2],[],[],[]),
([u0,u1,u3,u26,u22],[],[],[]),
([0x77770000,u0,u1,u3,u26],[],[],[]),
([u14,u19,u0,u1,u2],[],[],[]),
([u14,u0,u1,u4,u22],[],[],[]),
([u14,0x77770000,u0,u1,u4],[],[],[]),
([u27,u0,u3,u4,u2],[],[],[]),
([u6,u0,u9,u4,u2],[],[],[]),
([u7,u0,u9,u4,u2],[],[],[]),
([u0,u1,u9,u17,u2],[],[],[]),
([0xee00ee,u0,u1,u9,u2],[],[],[]),
([u0,u1,u9,0xeeee0000,u4],[],[],[]),
([0xeeee,u0,u1,u9,u4],[],[],[]),
([u0,u1,u9,u4,u2],[],[],[]),
([0xee00ee,0xe0e0e0e,u0,u1,u2],[],[],[]),
([0xee00ee,u0,u1,0xeeee0000,u3],[],[],[]),
([0xeeee,0xee00ee,u0,u1,u3],[],[],[]),
([u0,u1,0xe0f0e0f0,u4,u2],[],[],[]),
([u7,u27,u3,u4,u2],[],[],[]),
([u7,0xbabababa,u3,u4,u2],[],[],[]),
([u8,u0,u1,u3,0xffffcc00],[],[],[]),
([u0,0xeccceccc,u3,u4,u2],[],[],[]),
([0x2aaa2aaa,u1,u3,u4,u2],[],[],[]),
([u10,u0,u1,u3,0xffffcc00],[],[],[(0,0)]),
([u28,u1,0xeaeaeaea,u4,u2],[],[],[(1,0)]),
([0x70507050,u0,u1,u4,u2],[],[],[]),
([u12,0x8c8c8c8c,u0,u4,u2],[],[],[]),
([u8,0x88cc88cc,u0,u3,u2],[],[],[]),
([u8,u0,u1,u3,0xffff5500],[],[],[]),
([0xaaa0aaa,0x50505050,u1,u4,u2],[],[],[]),
([u8,u0,u1,u3,0xfffff000],[],[],[]),
([u8,u0,0xcccc00cc,u3,u2],[],[],[]),
([u0,u1,0xe0c0e0c0,u4,u2],[],[],[]),
([u10,u0,u1,u3,0xffff5500],[],[],[]),
([u10,u1,u3,0xfaaafaaa,u2],[],[],[]),
([u10,u0,u1,u3,0xfffff000],[],[],[]),
([0x33007700,u0,u1,u3,u2],[],[],[]),
([0xaa00ee00,u0,u1,u3,u2],[],[],[]),
([0xaa00fa00,u0,u1,u3,u2],[],[],[]),
([u10,0xaaaaffaa,u1,u3,u2],[],[],[]),
([0x3300f300,u0,u1,u3,u2],[],[],[])
]
def c5_0_L5 : Array W5Node := Array.mk [
([u7,u6,u1,u3,u4,u2],[],[0],[(0,0)]),
([u7,u0,u1,u3,u4,u2],[],[],[(0,0)]),
([0x80808080,u0,u1,u3,u4,u2],[],[1,2,3],[(0,1),(1,2)]),
([u6,u0,u1,u3,u26,u2],[],[],[(0,3),(0,4),(0,5),(0,6),(1,1)]),
([u14,u0,u1,u4,u2],[],[],[]),
([u14,u6,u0,u1,u4,u2],[],[0],[(0,4),(0,7),(0,8),(0,9)]),
([u14,u0,u1,u3,u4,u2],[],[],[]),
([u0,u1,u3,u4,u22],[],[],[]),
([u6,u0,u1,u3,u4,u22],[],[2],[(0,5),(0,8),(1,5),(1,8)]),
([0x77770000,u6,u0,u1,u3,u4],[],[3],[(0,6),(0,9),(1,6),(1,9)]),
([u6,u0,u5,u3,u4,u2],[],[],[(0,10),(0,11)]),
([u6,u10,u1,u3,u4,u2],[],[1],[]),
([u12,u6,u0,u3,u4,u2],[],[0],[]),
([u7,u0,u5,u3,u4,u2],[],[0],[(0,0),(0,12)]),
([u0,u1,u9,u4,u2],[],[],[(0,11),(0,12)]),
([u0,u1,u9,u5,u4,u2],[],[0],[(0,12),(0,13),(0,14),(0,15),(0,16)]),
([u0,u1,u9,u3,u4,u2],[],[],[]),
([0xee00ee,u0,u1,u5,u3,u2],[],[],[(0,14),(0,18),(0,19),(0,20),(1,17)]),
([0x10101010,u0,u1,u3,u4,u2],[],[1,2,3],[(0,17),(1,21)]),
([u0,u1,0xeeee0000,u5,u3,u4],[],[3],[(0,15),(0,19),(1,15),(1,19)]),
([0xeeee,u0,u1,u3,u4],[],[],[]),
([0xeeee,u0,u1,u5,u3,u4],[],[2],[(0,16),(0,20),(1,16),(1,20)]),
([u6,u0,u1,u3,u4,u2],[],[0,1,2,3],[(0,1),(1,1)]),
([u0,u1,u5,u3,u4,u2],[],[0,1,2,3],[(0,17),(1,17)]),
([0x20202020,u0,u1,u3,u4,u2],[],[2,3],[]),
([u0,0xbb00bb00,u1,u3,u4,u2],[],[],[]),
([0x22002200,u0,u1,u3,u4,u2],[],[],[]),
([u0,0xb0b0b0b0,u1,u3,u4,u2],[],[2,3],[]),
([u7,u13,u3,u4,u2],[],[],[(0,22),(1,22)]),
([u7,u13,u0,u3,u4,u2],[],[],[(0,10)]),
([u7,u0,0xc0c0c0c0,u3,u4,u2],[],[],[]),
([u7,u12,u0,u3,u4,u2],[],[0],[(0,23)]),
([u0,u1,0xecececec,u3,u4,u2],[],[],[(0,17)]),
([0x22aa22aa,u0,u1,u3,u4,u2],[],[],[]),
([u8,u0,u15,u1,u3,u2],[],[0,1],[(0,24)]),
([0xa000a000,u0,u1,u3,u4,u2],[],[2,3],[(0,25),(1,26)]),
([0x30f030f0,u0,u1,u3,u4,u2],[],[],[]),
([u0,u1,u3,u4,0xffffa0a0],[(0xffffa0a0,u28,u2)],[0],[(1,24),(1,27)]),
([u28,u0,u1,u3,u4,0xffffa0a0],[(0xffffa0a0,u28,u2)],[0,2],[(1,24)]),
([0x33ff0000,u0,u15,u1,u3,u4],[(0x33ff0000,u15,u2)],[1,3],[]),
([u28,u0,0xc0c0c0c0,u1,u4,u2],[],[],[(0,17),(0,28),(1,27)]),
([u0,0xbbaabbaa,u1,u3,u4,u2],[],[],[]),
([0x88aa88aa,u0,u1,u3,u4,u2],[],[0,2,3],[(0,29),(1,1),(1,30)]),
([0x30003000,u0,u1,u3,u4,u2],[],[2,3],[]),
([u0,0xaf00af00,u1,u3,u4,u2],[],[],[]),
([u12,0x50505050,u0,u1,u4,u2],[],[],[(0,1),(0,30),(1,31),(1,32)]),
([u8,u0,u1,u24,u3,u2],[],[0],[(0,34),(1,33)]),
([0xf0f0,0x50505050,u0,u1,u4,u2],[],[2],[(1,35)]),
([u0,u1,0xeaeaeaea,u3,u4,u2],[],[0,1,2,3],[(0,17),(0,28),(1,36)]),
([0x2a2a2a2a,u0,u1,u3,u4,u2],[],[],[]),
([0x3f003f00,u0,u1,u3,u4,u2],[],[],[]),
([u12,u0,0xc0c0c0c0,u1,u4,u2],[],[0],[(1,37)]),
([u10,u0,u1,u24,u3,u2],[],[0],[(0,38),(0,39)]),
([0xf0f0,u0,0xc0c0c0c0,u1,u4,u2],[],[2],[]),
([u0,0xbabababa,u1,u3,u4,u2],[],[0],[(0,23)]),
([0x88cc88cc,u0,u1,u3,u4,u2],[],[],[(0,31),(1,1)]),
([0xa0f0a0f0,u0,u1,u3,u4,u2],[],[],[]),
([u0,u1,u3,u4,0xffff3030],[(0xffff3030,u12,u2)],[0],[(1,32),(1,37)]),
([u12,u0,u1,u3,u4,0xffff3030],[(0xffff3030,u12,u2)],[0,2],[(1,37)]),
([u12,u0,u1,0xcfcf0000,u3,u4],[(0xcfcf0000,u12,u2)],[0,3],[]),
([0xaaaa8888,u0,u1,u3,u4,u2],[],[0,3],[(1,40)]),
([0x33332222,u0,u1,u3,u4,u2],[],[],[]),
([u0,u1,0xf0f0a0a0,u3,u4,u2],[(0xffffaaaa,u0,u2)],[0],[]),
([u0,u1,0xf0f0c0c0,u3,u4,u2],[],[],[]),
([u0,0xaaaaeeee,u1,u3,u4,u2],[],[1,3],[(0,41)]),
([0xaaaa2222,u0,u1,u3,u4,u2],[],[],[]),
([u0,u1,0xf0f05050,u3,u4,u2],[],[],[]),
([u0,u1,0xf0f03030,u3,u4,u2],[(0xcccc,u1,u2)],[0],[]),
([u0,u1,u3,0xfaaafaaa,u4,u2],[],[0],[(0,38)]),
([0xaaa0aaa,u0,u1,u3,u4,u2],[],[1],[(0,33)]),
([u0,u1,u3,u4,0xfffff000],[(0xfffff000,u24,u2)],[0,1],[(0,34),(0,39),(1,34),(1,39)]),
([u0,u1,u24,u3,u4,0xfffff000],[],[2],[]),
([0xfff0000,u0,u1,u24,u3,u4],[],[3],[]),
([u0,0xaaaafafa,u1,u3,u4,u2],[],[0,1,3],[(0,42)]),
([0xaaaa0a0a,u0,u1,u3,u4,u2],[],[2],[(1,35)]),
([u0,0xaaaaffaa,u1,u3,u4,u2],[],[2],[(0,43)]),
([0xaaaa00aa,u0,u1,u3,u4,u2],[],[0,1,3],[(1,44)]),
([u0,u1,0xf0f000f0,u3,u4,u2],[],[],[])
]
def c5_0_L6 : Array W5Node := Array.mk [
([u6,u0,u1,u3,u4,u2],[],[0,1,2,3],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,10),(1,11),(1,12)]),
([u0,u1,u5,u3,u4,u2],[],[0,1,2,3],[(0,1),(0,10),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(1,1),(1,10),(1,13),(1,14),(1,15),(1,16),(1,17),(1,18)]),
([u7,u0,u1,u3,u4,u2],[],[0,1,2,3],[(0,0),(0,13),(0,22),(0,23),(0,24),(0,26),(0,28),(0,29),(0,30),(0,31),(1,25),(1,27),(1,29)]),
([u28,u0,u1,u3,u4,u2],[],[0,1,2,3],[(0,2),(0,24),(0,32),(0,35),(0,37),(0,38),(0,40),(1,33),(1,34),(1,36),(1,39)]),
([u8,u0,u1,u3,u4,u2],[],[0,1,2,3],[(0,26),(0,34),(0,41),(0,42),(0,43),(0,46),(1,18),(1,44),(1,45),(1,47)]),
([u10,u0,u1,u3,u4,u2],[],[0,1,2,3],[(0,11),(0,26),(0,35),(0,52),(1,2),(1,30),(1,40),(1,48),(1,49),(1,50),(1,51),(1,53)]),
([u12,u0,u1,u3,u4,u2],[],[0,1,2,3],[(0,12),(0,18),(0,24),(0,31),(0,43),(0,45),(0,51),(0,54),(0,57),(0,58),(0,59),(1,55),(1,56)]),
([u0,u1,u3,u4,u2,0xffffaaaa],[],[0,1,2,3],[(0,61),(0,62),(1,60),(1,63)]),
([0xaaaa,u0,u1,u3,u4,u2],[],[0,1,2,3],[(0,66),(1,64),(1,65),(1,67)]),
([u0,u1,u24,u3,u4,u2],[(u24,u3,u4)],[0,1,2,3],[(0,35),(0,43),(0,46),(0,52),(0,68),(0,69),(0,70),(0,71),(0,72),(1,35),(1,43),(1,46),(1,52),(1,68),(1,69)]),
([0xf0f0,u0,u1,u3,u4,u2],[],[0,1,2,3],[(0,47),(0,53),(0,73),(0,74),(1,75),(1,76),(1,77)])
]
def c5_0_L7 : Array W5Node := Array.mk [
([u0,u1,u3,u4,u2],[],[0,1,2],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,10)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_3_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 3 c5_0_L3 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_3 : ∀ i < c5_0_L3.size, checkNodeW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 3 c5_0_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_0_L3.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_1 : checkBlockW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_2 : checkBlockW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 32 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_4 : ∀ i < c5_0_L4.size, checkNodeW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 i = true := by
  intro i hi
  have hsz : c5_0_L4.size = 45 := by decide +kernel
  have hi' : i < 45 := hsz ▸ hi
  by_cases h : i < 32
  ·
    by_cases h : i < 16
    ·
      exact checkBlockW5_at c5_0_chk_4_0 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_0_chk_4_1 i (by omega) (by omega)
  ·
    exact checkBlockW5_at c5_0_chk_4_2 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_1 : checkBlockW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_2 : checkBlockW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_3 : checkBlockW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_4 : checkBlockW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 64 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_5 : ∀ i < c5_0_L5.size, checkNodeW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 i = true := by
  intro i hi
  have hsz : c5_0_L5.size = 78 := by decide +kernel
  have hi' : i < 78 := hsz ▸ hi
  by_cases h : i < 48
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW5_at c5_0_chk_5_0 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_5_1 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_0_chk_5_2 i (by omega) (by omega)
  ·
    by_cases h : i < 64
    ·
      exact checkBlockW5_at c5_0_chk_5_3 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_0_chk_5_4 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 0 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_6 : ∀ i < c5_0_L6.size, checkNodeW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 i = true := by
  intro i hi
  have hsz : c5_0_L6.size = 11 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_6_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_7_0 : checkBlockW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_7 : ∀ i < c5_0_L7.size, checkNodeW5 c5_0_goal 2 c5_0_pow 4 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 i = true := by
  intro i hi
  have hsz : c5_0_L7.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_7_0 i (Nat.zero_le _) (by omega)
theorem c5_0_L3_sound : ∀ i < c5_0_L3.size, ¬ live (basicOps 32) c5_0_goal 3 (c5_0_L3[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound (fun j hj => by simp at hj) c5_0_chk_3
theorem c5_0_L4_sound : ∀ i < c5_0_L4.size, ¬ live (basicOps 32) c5_0_goal 4 (c5_0_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L3_sound c5_0_chk_4
theorem c5_0_L5_sound : ∀ i < c5_0_L5.size, ¬ live (basicOps 32) c5_0_goal 5 (c5_0_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L4_sound c5_0_chk_5
theorem c5_0_L6_sound : ∀ i < c5_0_L6.size, ¬ live (basicOps 32) c5_0_goal 6 (c5_0_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L5_sound c5_0_chk_6
theorem c5_0_L7_sound : ∀ i < c5_0_L7.size, ¬ live (basicOps 32) c5_0_goal 7 (c5_0_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L6_sound c5_0_chk_7
set_option maxRecDepth 100000 in
theorem c5_0_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_0_goal ws) = [rows5] := by decide +kernel
theorem c5_0_top_match : sameSet (rows5.map (actB 32 (c5_0_pow[0]?.getD []))) (c5_0_L7[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_0_no_build : ¬ build (basicOps 32) c5_0_goal 7 rows5.toFinset :=
  no_build_of_top c5_0_G_valid (by decide) c5_0_sublists c5_0_top_match (c5_0_L7_sound 0 (by decide))

def c5_1_goal : BitVec 32 := 0xe8a8a888
def c5_1_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_1_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_1_s1 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
def c5_1_p1 : List ℕ := [1,2,4,8,16,32,64,128,65536,131072,262144,524288,1048576,2097152,4194304,8388608,256,512,1024,2048,4096,8192,16384,32768,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_1_idx : Array (List ℕ) := Array.mk [c5_1_s0,c5_1_s1]
def c5_1_pow : Array (List ℕ) := Array.mk [c5_1_p0,c5_1_p1]
def c5_1_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_G_valid : (List.range 2).all (symValid 32 2 c5_1_idx c5_1_pow c5_1_inv c5_1_goal) = true := by decide +kernel
def c5_1_m0 : BitVec 32 := 0xff00ff00
def c5_1_st0 : List (BitVec 32) := [0xaa00aa00,0xcc00cc00,0xf000f000,0xff000000]
def c5_1_ix0 : List ℕ := [8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_0 : c5_1_ix0.length = 16 ∧ (∀ idx ∈ c5_1_ix0, idx < 32) ∧ (∀ idx ∈ c5_1_ix0, c5_1_m0.getLsbD idx = true) ∧ projS 16 c5_1_ix0 c5_1_goal = b4_1_goal ∧ c5_1_st0.all (fun w => rows4.contains (projS 16 c5_1_ix0 w)) = true := by decide +kernel
def c5_1_m1 : BitVec 32 := 0xf0f0f0f0
def c5_1_st1 : List (BitVec 32) := [0xa0a0a0a0,0xc0c0c0c0,0xf000f000,0xf0f00000]
def c5_1_ix1 : List ℕ := [4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_1 : c5_1_ix1.length = 16 ∧ (∀ idx ∈ c5_1_ix1, idx < 32) ∧ (∀ idx ∈ c5_1_ix1, c5_1_m1.getLsbD idx = true) ∧ projS 16 c5_1_ix1 c5_1_goal = b4_0_goal ∧ c5_1_st1.all (fun w => rows4.contains (projS 16 c5_1_ix1 w)) = true := by decide +kernel
def c5_1_m2 : BitVec 32 := 0xffff0000
def c5_1_st2 : List (BitVec 32) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def c5_1_ix2 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_2 : c5_1_ix2.length = 16 ∧ (∀ idx ∈ c5_1_ix2, idx < 32) ∧ (∀ idx ∈ c5_1_ix2, c5_1_m2.getLsbD idx = true) ∧ projS 16 c5_1_ix2 c5_1_goal = b4_1_goal ∧ c5_1_st2.all (fun w => rows4.contains (projS 16 c5_1_ix2 w)) = true := by decide +kernel
def c5_1_cfMasks : Array (BitVec 32) := Array.mk [c5_1_m0,c5_1_m1,c5_1_m2]
def c5_1_cfB0s : Array ℕ := Array.mk [8,4,16]
def c5_1_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_1_st0,c5_1_st1,c5_1_st2]
def c5_1_cfLBs : Array ℕ := Array.mk [5,6,5]
theorem c5_1_cof_sound (c fuel : ℕ) (hc : c < 3) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_1_cfLBs[c]?.getD 0) fuel (c5_1_cfMasks[c]?.getD 0) (c5_1_cfB0s[c]?.getD 0) (c5_1_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_1_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_1_goal 5 c5_1_ix0 c5_1_cspec_0.1 c5_1_cspec_0.2.1 c5_1_m0 c5_1_cspec_0.2.2.1 8 c5_1_st0 b4_1_goal (by decide) c5_1_cspec_0.2.2.2.1 c5_1_cspec_0.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_1_goal 6 c5_1_ix1 c5_1_cspec_1.1 c5_1_cspec_1.2.1 c5_1_m1 c5_1_cspec_1.2.2.1 4 c5_1_st1 b4_0_goal (by decide) c5_1_cspec_1.2.2.2.1 c5_1_cspec_1.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_1_goal 5 c5_1_ix2 c5_1_cspec_2.1 c5_1_cspec_2.2.1 c5_1_m2 c5_1_cspec_2.2.2.1 16 c5_1_st2 b4_1_goal (by decide) c5_1_cspec_2.2.2.2.1 c5_1_cspec_2.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | c + 3 => omega
def c5_1_L3 : Array W5Node := Array.mk [
([0x70007000,0x70700000,u0,u1],[],[],[]),
([u0,u1,0xe000e000,0xe0e00000],[],[],[]),
([u18,u0,u1,0xf0f0a000],[],[],[]),
([u0,u15,u1,0xf0f03000],[],[],[])
]
def c5_1_L4 : Array W5Node := Array.mk [
([u7,u13,u3,u4,u2],[],[],[]),
([0x70007000,u14,u0,u1,u2],[],[],[(0,0)]),
([0x7070,u14,u0,u1,u4],[],[],[]),
([u14,u0,u1,u4,u22],[],[],[]),
([u14,u19,u0,u1,u2],[],[],[]),
([0x7070f0f0,u0,u1,u4,u2],[],[],[]),
([u19,u0,u1,u3,u2],[],[],[]),
([0x7700ff00,u0,u1,u3,u2],[],[],[]),
([u0,u1,u3,u26,u22],[],[],[]),
([u19,u0,u1,u3,u22],[],[],[]),
([u19,0x77770000,u0,u1,u3],[],[],[]),
([u27,u0,u3,u4,u2],[],[],[]),
([u6,u0,u9,u4,u2],[],[],[]),
([u6,u0,u17,u3,u2],[],[],[]),
([u27,u1,u3,u4,u2],[],[],[]),
([u6,u1,u9,u4,u2],[],[],[]),
([u6,u0,u29,u3,u2],[],[],[]),
([u7,u0,u9,u4,u2],[],[],[]),
([u7,u0,u17,u3,u2],[],[],[]),
([u13,u1,u9,u4,u2],[],[],[]),
([u0,u1,0xe000e000,u9,u2],[],[],[(0,1)]),
([0xe0e0,u0,u1,u9,u4],[],[],[]),
([u0,u1,u9,u17,u2],[],[],[]),
([0xeeee,u0,u1,u9,u4],[],[],[]),
([u0,u1,u17,0xeeee0000,u3],[],[],[]),
([0xeeee,u0,u1,u17,u3],[],[],[]),
([u0,u1,u17,u3,u2],[],[],[]),
([0xeeee,0xee00ee,u0,u1,u3],[],[],[]),
([u0,u1,0xe0e0f0f0,u4,u2],[],[],[]),
([u0,u1,0xee00ff00,u3,u2],[],[],[]),
([u14,u0,u1,u4,u2],[],[],[]),
([u0,u1,u9,u4,u2],[],[],[]),
([u0,u1,0xdd00ff00,u3,u2],[],[],[]),
([u7,u27,u3,u4,u2],[],[],[]),
([u13,u27,u3,u4,u2],[],[],[]),
([u7,0xbbaabbaa,u3,u4,u2],[],[],[]),
([u7,u0,u29,u3,u2],[],[],[]),
([0x4400ff00,u0,u1,u3,u2],[],[],[]),
([u0,u15,0xeecceecc,u3,u2],[],[],[]),
([u18,u0,u1,u3,0xffffaa00],[],[],[(0,2)]),
([u30,u0,u1,u3,u2],[],[],[]),
([u10,u0,u1,0xf0f0a000,u4],[(0xffffaa00,u10,u2),(0xf0f0a000,u3,0xffffaa00)],[0],[(0,2)]),
([u10,u1,0xeeaaeeaa,u3,u2],[],[],[]),
([u10,u1,u3,u25,u2],[],[],[]),
([0x70307030,u0,u1,u4,u2],[],[],[]),
([0x77003300,u0,u1,u3,u2],[],[],[]),
([u8,0x88cc88cc,u0,u3,u2],[],[],[]),
([u18,0x88aa88aa,u1,u3,u2],[],[],[]),
([u0,u1,0xe0a0e0a0,u4,u2],[],[],[]),
([u0,u1,0xee00aa00,u3,u2],[],[],[]),
([u0,u29,u1,u3,u2],[],[],[]),
([u0,u15,u1,u3,0xffff3300],[],[],[(0,3)]),
([u8,u0,u1,0xf0f03000,u4],[],[],[(0,3)]),
([0xcccccc,u8,u0,u3,u2],[],[],[]),
([u0,0xcc888888,u3,u4,u2],[(u25,u0,u23),(0xcc888888,u1,u25)],[0],[]),
([0x33222222,u0,u3,u4,u2],[],[],[]),
([u0,u1,0xf0a0a0a0,u4,u2],[(u25,u0,u23),(0xf0a0a0a0,u3,u25)],[0],[]),
([u0,u1,0xf0303030,u4,u2],[(0xcccccc,u1,u23),(0xf0303030,0xcccccc,u3)],[0],[])
]
def c5_1_L5 : Array W5Node := Array.mk [
([u7,u6,u1,u3,u4,u2],[],[1],[(0,0)]),
([u7,u0,u1,u3,u4,u2],[],[],[(0,0)]),
([u13,u6,u0,u3,u4,u2],[],[1],[(0,0)]),
([u13,u0,u1,u3,u4,u2],[],[],[(0,0)]),
([u14,u0,u1,u4,u2],[],[],[(0,1),(0,2),(1,1),(1,2)]),
([u14,u6,u0,u1,u4,u2],[],[1],[(0,3),(0,4),(1,3),(1,4)]),
([0x88008800,u0,u1,u3,u4,u2],[],[1,2],[(0,6),(1,5),(1,7)]),
([u6,u0,u1,u3,u4,u22],[(u6,u0,u1),(u22,u6,u2)],[1],[(0,3),(0,8),(0,9),(1,6)]),
([u19,u0,u1,u3,u2],[(u6,u0,u1),(u19,u6,u4)],[1],[]),
([u19,u6,u0,u1,u3,u2],[(u6,u0,u1),(u19,u6,u4)],[0,1],[(0,4),(0,9),(0,10)]),
([u19,u0,u1,u3,u4,u2],[],[],[]),
([u6,u0,u5,u3,u4,u2],[],[],[(0,11),(0,12),(0,13),(1,13)]),
([u6,u1,u5,u3,u4,u2],[],[],[(0,14),(0,15)]),
([u6,u0,u15,u3,u4,u2],[],[0],[]),
([u8,u6,u0,u3,u4,u2],[],[0],[(1,16)]),
([u7,u0,u5,u3,u4,u2],[],[1],[(0,0),(0,17),(0,18),(1,18)]),
([u13,u1,u5,u3,u4,u2],[],[1],[(0,0),(0,19)]),
([u0,u1,u9,u4,u2],[],[],[(0,12),(0,15),(0,17),(0,19),(0,20),(0,21),(1,20),(1,21)]),
([u0,u1,u9,u5,u4,u2],[],[1],[(0,17),(0,19),(0,22),(0,23),(1,22),(1,23)]),
([u0,u1,u17,u3,u2],[(u5,u0,u1),(u17,u5,u4)],[1],[(0,13),(0,18)]),
([u0,u1,u17,u5,u3,u2],[(u5,u0,u1),(u17,u5,u4)],[0,1],[(0,18),(0,22),(0,24),(0,25)]),
([u0,u1,u17,u3,u4,u2],[],[],[]),
([0xeeee,u0,u1,u5,u3,u4],[(u5,u0,u1),(0xeeee,u5,u2)],[1],[(0,23),(0,25),(0,27),(1,26)]),
([0x11001100,u0,u1,u3,u4,u2],[],[1,2],[(0,26),(1,28),(1,29)]),
([u6,u0,u1,u3,u4,u2],[],[0,1,2],[(0,6),(0,30),(1,6)]),
([u0,u1,u5,u3,u4,u2],[],[0,1,2],[(0,26),(0,31),(1,26)]),
([0x22002200,u0,u1,u3,u4,u2],[],[2],[(1,32)]),
([u0,u1,0xdd00dd00,u3,u4,u2],[],[],[]),
([u7,u13,u3,u4,u2],[(u7,u0,u1),(u13,u0,u1)],[1],[(0,33),(0,34)]),
([u7,u13,u0,u3,u4,u2],[],[],[(0,11)]),
([u7,u13,u1,u3,u4,u2],[],[],[(0,14)]),
([u7,u0,u15,u3,u4,u2],[],[0],[]),
([u7,u8,u0,u3,u4,u2],[],[0],[(0,35),(1,36)]),
([0x44004400,u0,u1,u3,u4,u2],[],[],[]),
([u0,0xbb00bb00,u1,u3,u4,u2],[],[2],[(1,37)]),
([u0,u1,0xeecceecc,u3,u4,u2],[],[],[(0,26),(0,38)]),
([0x4444cccc,u0,u1,u3,u4,u2],[],[],[]),
([u18,u10,u0,u1,u3,u2],[],[0,1],[(0,39)]),
([0xaa000000,u0,u1,u3,u4,u2],[],[],[(0,40),(1,40)]),
([u10,u0,u1,u3,u4,0xffffaa00],[(0xffffaa00,u10,u2)],[0],[(0,39),(0,41),(1,40)]),
([u30,u0,u1,u3,u2],[(0xaaaa0000,u0,u2),(u30,0xaaaa0000,u4)],[1],[]),
([u30,0xaaaa0000,u0,u1,u3,u2],[(u30,0xaaaa0000,u4)],[0,2],[]),
([u30,u0,u1,u3,u4,u2],[],[],[]),
([u10,u0,u15,u1,u3,u2],[(u15,u1,u4)],[2],[(0,26),(0,38),(0,42)]),
([u10,u0,u1,u3,u23,u2],[],[2],[(0,43)]),
([u0,u1,0xddccddcc,u3,u4,u2],[],[],[]),
([0x8888cccc,u0,u1,u3,u4,u2],[],[0,1],[(0,45),(1,6),(1,44),(1,46)]),
([0x55000000,u0,u1,u3,u4,u2],[(0x55000000,u18,u2)],[0],[]),
([0xaa00ff00,u0,u1,u3,u4,u2],[(0x55550000,u0,u2)],[0],[]),
([u8,u18,u0,u1,u3,u2],[(u18,u0,u4)],[2],[(0,6),(0,46),(0,47)]),
([u0,u1,0xeeaaeeaa,u3,u4,u2],[],[0,1,2],[(0,26),(0,42),(0,48),(1,49)]),
([0x2222aaaa,u0,u1,u3,u4,u2],[],[],[]),
([u8,u0,u15,u1,u3,u2],[(u15,u1,u4)],[0,1,2],[]),
([u0,0xcc000000,u1,u3,u4,u2],[(0xcc000000,u15,u2)],[0],[]),
([0x3300ff00,u0,u1,u3,u4,u2],[(0xcccc0000,u1,u2)],[0],[]),
([u0,0xbbaabbaa,u1,u3,u4,u2],[],[0],[(0,35)]),
([0x8888aaaa,u0,u1,u3,u4,u2],[],[],[(1,6),(1,47)]),
([0x33000000,u0,u1,u3,u4,u2],[],[],[(0,50),(1,50)]),
([u8,u0,u1,u3,u4,0xffff3300],[(0xffff3300,u8,u2)],[0],[(0,51),(0,52),(1,50)]),
([u0,u29,u1,u3,u2],[(u20,u1,u2),(u29,u20,u4)],[1],[(0,16),(0,36)]),
([u8,u0,u1,0xccff0000,u3,u4],[(0xccff0000,u8,u2)],[0,2],[]),
([u0,u29,u1,u3,u4,u2],[],[],[]),
([u8,u0,u1,u3,u23,u2],[],[2],[(0,53)]),
([u0,u1,u3,u4,u25,u2],[(u25,u0,u23)],[0,1,2],[(0,43),(0,54),(0,55),(0,56),(1,43)]),
([0xaaaaaa,u0,u1,u3,u4,u2],[],[],[]),
([u0,u1,u3,u4,0xffcccccc,u2],[],[],[]),
([0xcccccc,u0,u1,u3,u4,u2],[(0xcccccc,u1,u23)],[0,1,2],[(0,53),(0,57),(1,53)])
]
def c5_1_L6 : Array W5Node := Array.mk [
([u6,u0,u1,u3,u4,u2],[(u6,u0,u1)],[0,1,2],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(1,6),(1,7),(1,8),(1,9),(1,10),(1,13),(1,14)]),
([u0,u1,u5,u3,u4,u2],[(u5,u0,u1)],[0,1,2],[(0,1),(0,3),(0,11),(0,12),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(0,22),(0,23),(1,19),(1,20),(1,21),(1,22),(1,23)]),
([u7,u0,u1,u3,u4,u2],[(u7,u0,u1)],[0,1,2],[(0,0),(0,15),(0,24),(0,25),(0,26),(0,27),(0,28),(0,29),(0,30),(0,31),(0,32),(1,26),(1,27),(1,31),(1,32)]),
([u13,u0,u1,u3,u4,u2],[(u13,u0,u1)],[0,1,2],[(0,2),(0,16),(0,24),(0,25),(0,28),(0,29),(0,30),(0,33),(0,34),(1,33),(1,34)]),
([u10,u0,u1,u3,u4,u2],[(u10,u0,u4)],[0,1,2],[(0,6),(0,26),(0,35),(0,37),(0,38),(0,39),(0,43),(0,44),(1,36),(1,40),(1,41),(1,42)]),
([u18,u0,u1,u3,u4,u2],[(u18,u0,u4)],[0,1,2],[(0,23),(0,33),(0,37),(0,45),(0,47),(0,49),(1,46),(1,48)]),
([u0,u15,u1,u3,u4,u2],[(u15,u1,u4)],[0,1,2],[(0,6),(0,13),(0,31),(0,33),(0,43),(0,50),(0,52),(0,53),(1,51),(1,54)]),
([u8,u0,u1,u3,u4,u2],[(u8,u1,u4)],[0,1,2],[(0,14),(0,23),(0,26),(0,32),(0,49),(0,52),(0,55),(0,57),(0,58),(0,60),(0,62),(1,56),(1,59),(1,61)]),
([u0,u1,u3,u23,u4,u2],[(u23,u4,u2)],[0,1,2],[(0,38),(0,44),(0,47),(0,53),(0,57),(0,62),(0,63),(0,64),(0,65),(0,66),(1,44),(1,62)])
]
def c5_1_L7 : Array W5Node := Array.mk [
([u0,u1,u3,u4,u2],[],[0,1,2],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,4),(1,5),(1,6),(1,7)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_3_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 3 c5_1_L3 (Array.mk []) 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_3 : ∀ i < c5_1_L3.size, checkNodeW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 3 c5_1_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_1_L3.size = 4 := by decide +kernel
  exact checkBlockW5_at c5_1_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_4_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 c5_1_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_4_1 : checkBlockW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 c5_1_L3 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_4_2 : checkBlockW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 c5_1_L3 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_4_3 : checkBlockW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 c5_1_L3 48 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_4 : ∀ i < c5_1_L4.size, checkNodeW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 c5_1_L3 i = true := by
  intro i hi
  have hsz : c5_1_L4.size = 58 := by decide +kernel
  have hi' : i < 58 := hsz ▸ hi
  by_cases h : i < 32
  ·
    by_cases h : i < 16
    ·
      exact checkBlockW5_at c5_1_chk_4_0 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_1_chk_4_1 i (by omega) (by omega)
  ·
    by_cases h : i < 48
    ·
      exact checkBlockW5_at c5_1_chk_4_2 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_1_chk_4_3 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_1 : checkBlockW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_2 : checkBlockW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_3 : checkBlockW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_4 : checkBlockW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 64 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_5 : ∀ i < c5_1_L5.size, checkNodeW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 i = true := by
  intro i hi
  have hsz : c5_1_L5.size = 67 := by decide +kernel
  have hi' : i < 67 := hsz ▸ hi
  by_cases h : i < 48
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW5_at c5_1_chk_5_0 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_1_chk_5_1 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_1_chk_5_2 i (by omega) (by omega)
  ·
    by_cases h : i < 64
    ·
      exact checkBlockW5_at c5_1_chk_5_3 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_1_chk_5_4 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_6_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 6 c5_1_L6 c5_1_L5 0 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_6 : ∀ i < c5_1_L6.size, checkNodeW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 6 c5_1_L6 c5_1_L5 i = true := by
  intro i hi
  have hsz : c5_1_L6.size = 9 := by decide +kernel
  exact checkBlockW5_at c5_1_chk_6_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_7_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 7 c5_1_L7 c5_1_L6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_7 : ∀ i < c5_1_L7.size, checkNodeW5 c5_1_goal 2 c5_1_pow 3 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 7 c5_1_L7 c5_1_L6 i = true := by
  intro i hi
  have hsz : c5_1_L7.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_1_chk_7_0 i (Nat.zero_le _) (by omega)
theorem c5_1_L3_sound : ∀ i < c5_1_L3.size, ¬ live (basicOps 32) c5_1_goal 3 (c5_1_L3[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound (fun j hj => by simp at hj) c5_1_chk_3
theorem c5_1_L4_sound : ∀ i < c5_1_L4.size, ¬ live (basicOps 32) c5_1_goal 4 (c5_1_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L3_sound c5_1_chk_4
theorem c5_1_L5_sound : ∀ i < c5_1_L5.size, ¬ live (basicOps 32) c5_1_goal 5 (c5_1_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L4_sound c5_1_chk_5
theorem c5_1_L6_sound : ∀ i < c5_1_L6.size, ¬ live (basicOps 32) c5_1_goal 6 (c5_1_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L5_sound c5_1_chk_6
theorem c5_1_L7_sound : ∀ i < c5_1_L7.size, ¬ live (basicOps 32) c5_1_goal 7 (c5_1_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L6_sound c5_1_chk_7
set_option maxRecDepth 100000 in
theorem c5_1_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_1_goal ws) = [rows5] := by decide +kernel
theorem c5_1_top_match : sameSet (rows5.map (actB 32 (c5_1_pow[0]?.getD []))) (c5_1_L7[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_1_no_build : ¬ build (basicOps 32) c5_1_goal 7 rows5.toFinset :=
  no_build_of_top c5_1_G_valid (by decide) c5_1_sublists c5_1_top_match (c5_1_L7_sound 0 (by decide))

def c5_2_goal : BitVec 32 := 0xeee8e8e8
def c5_2_idxs4 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27]
set_option maxRecDepth 100000 in
theorem c5_2_no_build : ¬ build (basicOps 32) c5_2_goal 5 rows5.toFinset :=
  no_build5_of_proj4 4 b4_5_goal (by decide) b4_5_no_build c5_2_goal c5_2_idxs4 2 1 5 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

def c5_3_goal : BitVec 32 := 0xfeeaeee8
def c5_3_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_3_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_3_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31]
def c5_3_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768,65536,131072,262144,524288,16777216,33554432,67108864,134217728,1048576,2097152,4194304,8388608,268435456,536870912,1073741824,2147483648]
def c5_3_idx : Array (List ℕ) := Array.mk [c5_3_s0,c5_3_s1]
def c5_3_pow : Array (List ℕ) := Array.mk [c5_3_p0,c5_3_p1]
def c5_3_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_G_valid : (List.range 2).all (symValid 32 2 c5_3_idx c5_3_pow c5_3_inv c5_3_goal) = true := by decide +kernel
def c5_3_m0 : BitVec 32 := 0x55555555
def c5_3_st0 : List (BitVec 32) := [0x44444444,0x50505050,0x55005500,0x55550000]
def c5_3_ix0 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_0 : c5_3_ix0.length = 16 ∧ (∀ idx ∈ c5_3_ix0, idx < 32) ∧ (∀ idx ∈ c5_3_ix0, c5_3_m0.getLsbD idx = true) ∧ projS 16 c5_3_ix0 c5_3_goal = b4_1_goal ∧ c5_3_st0.all (fun w => rows4.contains (projS 16 c5_3_ix0 w)) = true := by decide +kernel
def c5_3_m1 : BitVec 32 := 0xf0f0f0f
def c5_3_st1 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def c5_3_ix1 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_1 : c5_3_ix1.length = 16 ∧ (∀ idx ∈ c5_3_ix1, idx < 32) ∧ (∀ idx ∈ c5_3_ix1, c5_3_m1.getLsbD idx = true) ∧ projS 16 c5_3_ix1 c5_3_goal = b4_2_goal ∧ c5_3_st1.all (fun w => rows4.contains (projS 16 c5_3_ix1 w)) = true := by decide +kernel
def c5_3_m2 : BitVec 32 := 0xffff
def c5_3_st2 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def c5_3_ix2 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_2 : c5_3_ix2.length = 16 ∧ (∀ idx ∈ c5_3_ix2, idx < 32) ∧ (∀ idx ∈ c5_3_ix2, c5_3_m2.getLsbD idx = true) ∧ projS 16 c5_3_ix2 c5_3_goal = b4_4_goal ∧ c5_3_st2.all (fun w => rows4.contains (projS 16 c5_3_ix2 w)) = true := by decide +kernel
def c5_3_m3 : BitVec 32 := 0x33333333
def c5_3_st3 : List (BitVec 32) := [0x22222222,0x30303030,0x33003300,0x33330000]
def c5_3_ix3 : List ℕ := [0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_3 : c5_3_ix3.length = 16 ∧ (∀ idx ∈ c5_3_ix3, idx < 32) ∧ (∀ idx ∈ c5_3_ix3, c5_3_m3.getLsbD idx = true) ∧ projS 16 c5_3_ix3 c5_3_goal = b4_0_goal ∧ c5_3_st3.all (fun w => rows4.contains (projS 16 c5_3_ix3 w)) = true := by decide +kernel
def c5_3_m4 : BitVec 32 := 0xffff0000
def c5_3_st4 : List (BitVec 32) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def c5_3_ix4 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_4 : c5_3_ix4.length = 16 ∧ (∀ idx ∈ c5_3_ix4, idx < 32) ∧ (∀ idx ∈ c5_3_ix4, c5_3_m4.getLsbD idx = true) ∧ projS 16 c5_3_ix4 c5_3_goal = b4_3_goal ∧ c5_3_st4.all (fun w => rows4.contains (projS 16 c5_3_ix4 w)) = true := by decide +kernel
def c5_3_m5 : BitVec 32 := 0xff00ff
def c5_3_st5 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def c5_3_ix5 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23]
set_option maxRecDepth 100000 in
theorem c5_3_cspec_5 : c5_3_ix5.length = 16 ∧ (∀ idx ∈ c5_3_ix5, idx < 32) ∧ (∀ idx ∈ c5_3_ix5, c5_3_m5.getLsbD idx = true) ∧ projS 16 c5_3_ix5 c5_3_goal = b4_2_goal ∧ c5_3_st5.all (fun w => rows4.contains (projS 16 c5_3_ix5 w)) = true := by decide +kernel
def c5_3_cfMasks : Array (BitVec 32) := Array.mk [c5_3_m0,c5_3_m1,c5_3_m2,c5_3_m3,c5_3_m4,c5_3_m5]
def c5_3_cfB0s : Array ℕ := Array.mk [0,0,0,0,16,0]
def c5_3_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_3_st0,c5_3_st1,c5_3_st2,c5_3_st3,c5_3_st4,c5_3_st5]
def c5_3_cfLBs : Array ℕ := Array.mk [5,5,5,6,5,5]
theorem c5_3_cof_sound (c fuel : ℕ) (hc : c < 6) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_3_cfLBs[c]?.getD 0) fuel (c5_3_cfMasks[c]?.getD 0) (c5_3_cfB0s[c]?.getD 0) (c5_3_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_3_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_3_goal 5 c5_3_ix0 c5_3_cspec_0.1 c5_3_cspec_0.2.1 c5_3_m0 c5_3_cspec_0.2.2.1 0 c5_3_st0 b4_1_goal (by decide) c5_3_cspec_0.2.2.2.1 c5_3_cspec_0.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_3_goal 5 c5_3_ix1 c5_3_cspec_1.1 c5_3_cspec_1.2.1 c5_3_m1 c5_3_cspec_1.2.2.1 0 c5_3_st1 b4_2_goal (by decide) c5_3_cspec_1.2.2.2.1 c5_3_cspec_1.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_3_goal 5 c5_3_ix2 c5_3_cspec_2.1 c5_3_cspec_2.2.1 c5_3_m2 c5_3_cspec_2.2.2.1 0 c5_3_st2 b4_4_goal (by decide) c5_3_cspec_2.2.2.2.1 c5_3_cspec_2.2.2.2.2 b4_4_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_3_goal 6 c5_3_ix3 c5_3_cspec_3.1 c5_3_cspec_3.2.1 c5_3_m3 c5_3_cspec_3.2.2.1 0 c5_3_st3 b4_0_goal (by decide) c5_3_cspec_3.2.2.2.1 c5_3_cspec_3.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose32_sound_aux c5_3_goal 5 c5_3_ix4 c5_3_cspec_4.1 c5_3_cspec_4.2.1 c5_3_m4 c5_3_cspec_4.2.2.1 16 c5_3_st4 b4_3_goal (by decide) c5_3_cspec_4.2.2.2.1 c5_3_cspec_4.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose32_sound_aux c5_3_goal 5 c5_3_ix5 c5_3_cspec_5.1 c5_3_cspec_5.2.1 c5_3_m5 c5_3_cspec_5.2.2.1 0 c5_3_st5 b4_2_goal (by decide) c5_3_cspec_5.2.2.2.1 c5_3_cspec_5.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | c + 6 => omega
def c5_3_L4 : Array W5Node := Array.mk [
([0x33323332,u0,u3,u4,u2],[],[],[])
]
def c5_3_L5 : Array W5Node := Array.mk [
([u0,u1,u3,u21,0xfff0fff0,u2],[(0xfff0fff0,u4,u3)],[0,1,2],[]),
([u0,u1,u3,u4,0xfffafffa,u2],[],[2,3,4],[(0,0)]),
([0xfa00fa,u0,u1,u3,u4,u2],[],[],[]),
([u0,u1,u3,0xfafa0000,u11,u4],[(0xfafa0000,u11,u2)],[0,4],[]),
([0xfafa,u0,u1,u3,u11,u4],[(0xfafa,u11,u2)],[0,2],[]),
([0x55505550,u0,u1,u3,u4,u2],[],[],[])
]
def c5_3_L6 : Array W5Node := Array.mk [
([u0,u1,u3,u11,u4,u2],[(u11,u0,u3)],[0,1,2,3,4,5],[(0,1),(0,2),(0,3),(0,4),(1,0)]),
([u0,u1,u3,u4,0xfff0fff0,u2],[(0xfff0fff0,u3,u4)],[0,1,2,3,4,5],[(0,0),(0,1),(0,5),(1,0)])
]
def c5_3_L7 : Array W5Node := Array.mk [
([u0,u1,u3,u4,u2],[],[0,1,2,3,4,5],[(0,0),(0,1),(1,0)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_4_0 : checkBlockW5 c5_3_goal 2 c5_3_pow 6 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_3_chk_4 : ∀ i < c5_3_L4.size, checkNodeW5 c5_3_goal 2 c5_3_pow 6 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 4 c5_3_L4 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_3_L4.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_3_chk_4_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_5_0 : checkBlockW5 c5_3_goal 2 c5_3_pow 6 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_3_chk_5 : ∀ i < c5_3_L5.size, checkNodeW5 c5_3_goal 2 c5_3_pow 6 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 5 c5_3_L5 c5_3_L4 i = true := by
  intro i hi
  have hsz : c5_3_L5.size = 6 := by decide +kernel
  exact checkBlockW5_at c5_3_chk_5_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_6_0 : checkBlockW5 c5_3_goal 2 c5_3_pow 6 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_3_chk_6 : ∀ i < c5_3_L6.size, checkNodeW5 c5_3_goal 2 c5_3_pow 6 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 6 c5_3_L6 c5_3_L5 i = true := by
  intro i hi
  have hsz : c5_3_L6.size = 2 := by decide +kernel
  exact checkBlockW5_at c5_3_chk_6_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_3_chk_7_0 : checkBlockW5 c5_3_goal 2 c5_3_pow 6 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 7 c5_3_L7 c5_3_L6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_3_chk_7 : ∀ i < c5_3_L7.size, checkNodeW5 c5_3_goal 2 c5_3_pow 6 c5_3_cfLBs c5_3_cfMasks c5_3_cfB0s c5_3_cfStocks 7 c5_3_L7 c5_3_L6 i = true := by
  intro i hi
  have hsz : c5_3_L7.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_3_chk_7_0 i (Nat.zero_le _) (by omega)
theorem c5_3_L4_sound : ∀ i < c5_3_L4.size, ¬ live (basicOps 32) c5_3_goal 4 (c5_3_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_3_G_valid c5_3_cof_sound (fun j hj => by simp at hj) c5_3_chk_4
theorem c5_3_L5_sound : ∀ i < c5_3_L5.size, ¬ live (basicOps 32) c5_3_goal 5 (c5_3_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_3_G_valid c5_3_cof_sound c5_3_L4_sound c5_3_chk_5
theorem c5_3_L6_sound : ∀ i < c5_3_L6.size, ¬ live (basicOps 32) c5_3_goal 6 (c5_3_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_3_G_valid c5_3_cof_sound c5_3_L5_sound c5_3_chk_6
theorem c5_3_L7_sound : ∀ i < c5_3_L7.size, ¬ live (basicOps 32) c5_3_goal 7 (c5_3_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_3_G_valid c5_3_cof_sound c5_3_L6_sound c5_3_chk_7
set_option maxRecDepth 100000 in
theorem c5_3_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_3_goal ws) = [rows5] := by decide +kernel
theorem c5_3_top_match : sameSet (rows5.map (actB 32 (c5_3_pow[0]?.getD []))) (c5_3_L7[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_3_no_build : ¬ build (basicOps 32) c5_3_goal 7 rows5.toFinset :=
  no_build_of_top c5_3_G_valid (by decide) c5_3_sublists c5_3_top_match (c5_3_L7_sound 0 (by decide))

def c5_4_goal : BitVec 32 := 0xfeeaece8
def c5_4_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_4_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_4_s1 : List ℕ := [0,2,1,3,4,6,5,7,16,18,17,19,20,22,21,23,8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31]
def c5_4_p1 : List ℕ := [1,4,2,8,16,64,32,128,65536,262144,131072,524288,1048576,4194304,2097152,8388608,256,1024,512,2048,4096,16384,8192,32768,16777216,67108864,33554432,134217728,268435456,1073741824,536870912,2147483648]
def c5_4_idx : Array (List ℕ) := Array.mk [c5_4_s0,c5_4_s1]
def c5_4_pow : Array (List ℕ) := Array.mk [c5_4_p0,c5_4_p1]
def c5_4_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_4_G_valid : (List.range 2).all (symValid 32 2 c5_4_idx c5_4_pow c5_4_inv c5_4_goal) = true := by decide +kernel
def c5_4_m0 : BitVec 32 := 0x55555555
def c5_4_st0 : List (BitVec 32) := [0x44444444,0x50505050,0x55005500,0x55550000]
def c5_4_ix0 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]
set_option maxRecDepth 100000 in
theorem c5_4_cspec_0 : c5_4_ix0.length = 16 ∧ (∀ idx ∈ c5_4_ix0, idx < 32) ∧ (∀ idx ∈ c5_4_ix0, c5_4_m0.getLsbD idx = true) ∧ projS 16 c5_4_ix0 c5_4_goal = b4_1_goal ∧ c5_4_st0.all (fun w => rows4.contains (projS 16 c5_4_ix0 w)) = true := by decide +kernel
def c5_4_m1 : BitVec 32 := 0xff00ff00
def c5_4_st1 : List (BitVec 32) := [0xaa00aa00,0xcc00cc00,0xf000f000,0xff000000]
def c5_4_ix1 : List ℕ := [8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31]
set_option maxRecDepth 100000 in
theorem c5_4_cspec_1 : c5_4_ix1.length = 16 ∧ (∀ idx ∈ c5_4_ix1, idx < 32) ∧ (∀ idx ∈ c5_4_ix1, c5_4_m1.getLsbD idx = true) ∧ projS 16 c5_4_ix1 c5_4_goal = b4_3_goal ∧ c5_4_st1.all (fun w => rows4.contains (projS 16 c5_4_ix1 w)) = true := by decide +kernel
def c5_4_m2 : BitVec 32 := 0xffff0000
def c5_4_st2 : List (BitVec 32) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def c5_4_ix2 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_4_cspec_2 : c5_4_ix2.length = 16 ∧ (∀ idx ∈ c5_4_ix2, idx < 32) ∧ (∀ idx ∈ c5_4_ix2, c5_4_m2.getLsbD idx = true) ∧ projS 16 c5_4_ix2 c5_4_goal = b4_3_goal ∧ c5_4_st2.all (fun w => rows4.contains (projS 16 c5_4_ix2 w)) = true := by decide +kernel
def c5_4_m3 : BitVec 32 := 0x33333333
def c5_4_st3 : List (BitVec 32) := [0x22222222,0x30303030,0x33003300,0x33330000]
def c5_4_ix3 : List ℕ := [0,1,4,5,16,17,20,21,8,9,12,13,24,25,28,29]
set_option maxRecDepth 100000 in
theorem c5_4_cspec_3 : c5_4_ix3.length = 16 ∧ (∀ idx ∈ c5_4_ix3, idx < 32) ∧ (∀ idx ∈ c5_4_ix3, c5_4_m3.getLsbD idx = true) ∧ projS 16 c5_4_ix3 c5_4_goal = b4_1_goal ∧ c5_4_st3.all (fun w => rows4.contains (projS 16 c5_4_ix3 w)) = true := by decide +kernel
def c5_4_m4 : BitVec 32 := 0xffff
def c5_4_st4 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def c5_4_ix4 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
set_option maxRecDepth 100000 in
theorem c5_4_cspec_4 : c5_4_ix4.length = 16 ∧ (∀ idx ∈ c5_4_ix4, idx < 32) ∧ (∀ idx ∈ c5_4_ix4, c5_4_m4.getLsbD idx = true) ∧ projS 16 c5_4_ix4 c5_4_goal = b4_2_goal ∧ c5_4_st4.all (fun w => rows4.contains (projS 16 c5_4_ix4 w)) = true := by decide +kernel
def c5_4_m5 : BitVec 32 := 0xff00ff
def c5_4_st5 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def c5_4_ix5 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23]
set_option maxRecDepth 100000 in
theorem c5_4_cspec_5 : c5_4_ix5.length = 16 ∧ (∀ idx ∈ c5_4_ix5, idx < 32) ∧ (∀ idx ∈ c5_4_ix5, c5_4_m5.getLsbD idx = true) ∧ projS 16 c5_4_ix5 c5_4_goal = b4_2_goal ∧ c5_4_st5.all (fun w => rows4.contains (projS 16 c5_4_ix5 w)) = true := by decide +kernel
def c5_4_m6 : BitVec 32 := 0xf0f0f0f
def c5_4_st6 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def c5_4_ix6 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27]
set_option maxRecDepth 100000 in
theorem c5_4_cspec_6 : c5_4_ix6.length = 16 ∧ (∀ idx ∈ c5_4_ix6, idx < 32) ∧ (∀ idx ∈ c5_4_ix6, c5_4_m6.getLsbD idx = true) ∧ projS 16 c5_4_ix6 c5_4_goal = b4_6_goal ∧ c5_4_st6.all (fun w => rows4.contains (projS 16 c5_4_ix6 w)) = true := by decide +kernel
def c5_4_cfMasks : Array (BitVec 32) := Array.mk [c5_4_m0,c5_4_m1,c5_4_m2,c5_4_m3,c5_4_m4,c5_4_m5,c5_4_m6]
def c5_4_cfB0s : Array ℕ := Array.mk [0,8,16,0,0,0,0]
def c5_4_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_4_st0,c5_4_st1,c5_4_st2,c5_4_st3,c5_4_st4,c5_4_st5,c5_4_st6]
def c5_4_cfLBs : Array ℕ := Array.mk [5,5,5,5,5,5,4]
theorem c5_4_cof_sound (c fuel : ℕ) (hc : c < 7) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_4_cfLBs[c]?.getD 0) fuel (c5_4_cfMasks[c]?.getD 0) (c5_4_cfB0s[c]?.getD 0) (c5_4_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_4_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_4_goal 5 c5_4_ix0 c5_4_cspec_0.1 c5_4_cspec_0.2.1 c5_4_m0 c5_4_cspec_0.2.2.1 0 c5_4_st0 b4_1_goal (by decide) c5_4_cspec_0.2.2.2.1 c5_4_cspec_0.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_4_goal 5 c5_4_ix1 c5_4_cspec_1.1 c5_4_cspec_1.2.1 c5_4_m1 c5_4_cspec_1.2.2.1 8 c5_4_st1 b4_3_goal (by decide) c5_4_cspec_1.2.2.2.1 c5_4_cspec_1.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_4_goal 5 c5_4_ix2 c5_4_cspec_2.1 c5_4_cspec_2.2.1 c5_4_m2 c5_4_cspec_2.2.2.1 16 c5_4_st2 b4_3_goal (by decide) c5_4_cspec_2.2.2.2.1 c5_4_cspec_2.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_4_goal 5 c5_4_ix3 c5_4_cspec_3.1 c5_4_cspec_3.2.1 c5_4_m3 c5_4_cspec_3.2.2.1 0 c5_4_st3 b4_1_goal (by decide) c5_4_cspec_3.2.2.2.1 c5_4_cspec_3.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose32_sound_aux c5_4_goal 5 c5_4_ix4 c5_4_cspec_4.1 c5_4_cspec_4.2.1 c5_4_m4 c5_4_cspec_4.2.2.1 0 c5_4_st4 b4_2_goal (by decide) c5_4_cspec_4.2.2.2.1 c5_4_cspec_4.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose32_sound_aux c5_4_goal 5 c5_4_ix5 c5_4_cspec_5.1 c5_4_cspec_5.2.1 c5_4_m5 c5_4_cspec_5.2.2.1 0 c5_4_st5 b4_2_goal (by decide) c5_4_cspec_5.2.2.2.1 c5_4_cspec_5.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 6 => exact checkCofClose32_sound_aux c5_4_goal 4 c5_4_ix6 c5_4_cspec_6.1 c5_4_cspec_6.2.1 c5_4_m6 c5_4_cspec_6.2.2.1 0 c5_4_st6 b4_6_goal (by decide) c5_4_cspec_6.2.2.2.1 c5_4_cspec_6.2.2.2.2 b4_6_no_build fuel hist nxt hnd hchk
  | c + 7 => omega
def c5_4_L3 : Array W5Node := Array.mk [
([u5,u3,0xffaacc88],[],[],[])
]
def c5_4_L4 : Array W5Node := Array.mk [
([u5,u11,0xfcfcfcfc,u4,u2],[],[0],[]),
([u5,u3,u11,u4,u16],[],[],[]),
([u5,u3,u21,u16],[(u5,u1,u0),(u16,u1,u2),(u21,u0,u4)],[1,2],[(0,0)]),
([u0,u1,u3,0xfafac8c8,u4],[(u16,u1,u2),(0xfafac8c8,u11,u16)],[0],[]),
([0xa8fca8fc,u0,u1,u3,u2],[],[],[]),
([u0,u1,u3,0xffaacc88],[(u16,u1,u2),(u21,u0,u4),(0xffaacc88,u21,u16)],[0,3],[(0,0)])
]
def c5_4_L5 : Array W5Node := Array.mk [
([u0,u5,u3,0xfcfcfcfc,u4,u2],[],[0],[(0,0),(1,1)]),
([u0,u5,u3,u4,u16],[(u5,u1,u0),(u16,u1,u2)],[0,1,2,3,4],[(0,1),(0,2)]),
([u0,u1,u3,0xfefefefe,u4,u2],[],[1,2,4,5],[]),
([0xe0e0e0e,u0,u1,u3,u4,u2],[],[],[]),
([u0,u1,u11,0xfcfcfcfc,u4,u2],[],[0],[(0,0)]),
([u12,u0,u1,u11,u4,u2],[],[0],[]),
([0x32323232,u0,u1,u3,u4,u2],[],[2,4],[]),
([u0,u1,u3,u11,u4,u16],[(u16,u1,u2)],[0,2],[(0,1),(0,3)]),
([u20,u0,u1,u3,u11,u4],[(u20,u1,u2)],[0,4],[(1,4)]),
([u0,u1,u3,0xfafa0000,u11,u4],[(0xfafa0000,u11,u2)],[0,2],[]),
([0xfafa,u0,u1,u3,u11,u4],[(0xfafa,u11,u2)],[0,4],[]),
([u0,0xbabababa,u1,u3,u4,u2],[],[2,4],[]),
([u12,u0,u1,u3,u21,u2],[],[],[]),
([u12,u18,u0,u1,u3,u2],[],[],[]),
([u0,u1,u3,u21,u16],[(u16,u1,u2),(u21,u0,u4)],[0,1,2,3,4,5],[(0,2),(0,5)]),
([u20,u0,u1,u3,u21],[(u21,u0,u4),(u20,u1,u2)],[0,1,3,4,5],[]),
([u20,u18,u0,u1,u3],[(u20,u1,u2),(u18,u0,u4)],[0,3,4,5],[])
]
def c5_4_L6 : Array W5Node := Array.mk [
([u0,u1,u5,u3,u4,u2],[(u5,u0,u1)],[0,1,2,3,4,5,6],[(0,0),(0,1),(0,2),(0,3),(1,0),(1,1)]),
([u0,u1,u3,u11,u4,u2],[(u11,u0,u3)],[0,1,2,3,4,5,6],[(0,2),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(1,0)]),
([u12,u0,u1,u3,u4,u2],[(u12,u1,u3)],[0,1,2,3,4,5,6],[(0,5),(0,11),(0,12),(0,13)]),
([u0,u1,u3,u4,u16],[(u16,u1,u2)],[0,1,2,3,4,5],[(0,1),(0,7),(0,14),(1,12),(1,15)]),
([u20,u0,u1,u3,u4],[(u20,u1,u2)],[0,1,3,4,5],[(0,8),(0,15),(0,16),(1,13)])
]
def c5_4_L7 : Array W5Node := Array.mk [
([u0,u1,u3,u4,u2],[],[0,1,2,3,4,5],[(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_4_chk_3_0 : checkBlockW5 c5_4_goal 2 c5_4_pow 7 c5_4_cfLBs c5_4_cfMasks c5_4_cfB0s c5_4_cfStocks 3 c5_4_L3 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_4_chk_3 : ∀ i < c5_4_L3.size, checkNodeW5 c5_4_goal 2 c5_4_pow 7 c5_4_cfLBs c5_4_cfMasks c5_4_cfB0s c5_4_cfStocks 3 c5_4_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_4_L3.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_4_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_4_chk_4_0 : checkBlockW5 c5_4_goal 2 c5_4_pow 7 c5_4_cfLBs c5_4_cfMasks c5_4_cfB0s c5_4_cfStocks 4 c5_4_L4 c5_4_L3 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_4_chk_4 : ∀ i < c5_4_L4.size, checkNodeW5 c5_4_goal 2 c5_4_pow 7 c5_4_cfLBs c5_4_cfMasks c5_4_cfB0s c5_4_cfStocks 4 c5_4_L4 c5_4_L3 i = true := by
  intro i hi
  have hsz : c5_4_L4.size = 6 := by decide +kernel
  exact checkBlockW5_at c5_4_chk_4_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_4_chk_5_0 : checkBlockW5 c5_4_goal 2 c5_4_pow 7 c5_4_cfLBs c5_4_cfMasks c5_4_cfB0s c5_4_cfStocks 5 c5_4_L5 c5_4_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_4_chk_5_1 : checkBlockW5 c5_4_goal 2 c5_4_pow 7 c5_4_cfLBs c5_4_cfMasks c5_4_cfB0s c5_4_cfStocks 5 c5_4_L5 c5_4_L4 16 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_4_chk_5 : ∀ i < c5_4_L5.size, checkNodeW5 c5_4_goal 2 c5_4_pow 7 c5_4_cfLBs c5_4_cfMasks c5_4_cfB0s c5_4_cfStocks 5 c5_4_L5 c5_4_L4 i = true := by
  intro i hi
  have hsz : c5_4_L5.size = 17 := by decide +kernel
  have hi' : i < 17 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockW5_at c5_4_chk_5_0 i (by omega) (by omega)
  ·
    exact checkBlockW5_at c5_4_chk_5_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_4_chk_6_0 : checkBlockW5 c5_4_goal 2 c5_4_pow 7 c5_4_cfLBs c5_4_cfMasks c5_4_cfB0s c5_4_cfStocks 6 c5_4_L6 c5_4_L5 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_4_chk_6 : ∀ i < c5_4_L6.size, checkNodeW5 c5_4_goal 2 c5_4_pow 7 c5_4_cfLBs c5_4_cfMasks c5_4_cfB0s c5_4_cfStocks 6 c5_4_L6 c5_4_L5 i = true := by
  intro i hi
  have hsz : c5_4_L6.size = 5 := by decide +kernel
  exact checkBlockW5_at c5_4_chk_6_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_4_chk_7_0 : checkBlockW5 c5_4_goal 2 c5_4_pow 7 c5_4_cfLBs c5_4_cfMasks c5_4_cfB0s c5_4_cfStocks 7 c5_4_L7 c5_4_L6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_4_chk_7 : ∀ i < c5_4_L7.size, checkNodeW5 c5_4_goal 2 c5_4_pow 7 c5_4_cfLBs c5_4_cfMasks c5_4_cfB0s c5_4_cfStocks 7 c5_4_L7 c5_4_L6 i = true := by
  intro i hi
  have hsz : c5_4_L7.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_4_chk_7_0 i (Nat.zero_le _) (by omega)
theorem c5_4_L3_sound : ∀ i < c5_4_L3.size, ¬ live (basicOps 32) c5_4_goal 3 (c5_4_L3[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_4_G_valid c5_4_cof_sound (fun j hj => by simp at hj) c5_4_chk_3
theorem c5_4_L4_sound : ∀ i < c5_4_L4.size, ¬ live (basicOps 32) c5_4_goal 4 (c5_4_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_4_G_valid c5_4_cof_sound c5_4_L3_sound c5_4_chk_4
theorem c5_4_L5_sound : ∀ i < c5_4_L5.size, ¬ live (basicOps 32) c5_4_goal 5 (c5_4_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_4_G_valid c5_4_cof_sound c5_4_L4_sound c5_4_chk_5
theorem c5_4_L6_sound : ∀ i < c5_4_L6.size, ¬ live (basicOps 32) c5_4_goal 6 (c5_4_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_4_G_valid c5_4_cof_sound c5_4_L5_sound c5_4_chk_6
theorem c5_4_L7_sound : ∀ i < c5_4_L7.size, ¬ live (basicOps 32) c5_4_goal 7 (c5_4_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_4_G_valid c5_4_cof_sound c5_4_L6_sound c5_4_chk_7
set_option maxRecDepth 100000 in
theorem c5_4_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_4_goal ws) = [rows5] := by decide +kernel
theorem c5_4_top_match : sameSet (rows5.map (actB 32 (c5_4_pow[0]?.getD []))) (c5_4_L7[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_4_no_build : ¬ build (basicOps 32) c5_4_goal 7 rows5.toFinset :=
  no_build_of_top c5_4_G_valid (by decide) c5_4_sublists c5_4_top_match (c5_4_L7_sound 0 (by decide))

def c5_5_goal : BitVec 32 := 0xeae8e8e8
def c5_5_idxs4 : List ℕ := [8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_5_no_build : ¬ build (basicOps 32) c5_5_goal 5 rows5.toFinset :=
  no_build5_of_proj4 4 b4_2_goal (by decide) b4_2_no_build c5_5_goal c5_5_idxs4 3 17 25 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

def nrmM64 (m : BitVec 64) (b0 : ℕ) (u : BitVec 64) : BitVec 64 :=
  if u.getLsbD b0 then (~~~u) &&& m else u &&& m

theorem projS_nrmM64 (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (u : BitVec 64) :
    projS 32 idxs (nrmM64 m b0 u) = projS 32 idxs u := by
  unfold nrmM64
  cases u.getLsbD b0
  · simp only [Bool.false_eq_true, ite_false]
    exact projS_mask 32 idxs m hm u
  · simp only [ite_true]
    rw [projS_mask 32 idxs m hm (~~~u), projS_not 32 (by decide) idxs hlen hlt u]

abbrev W6Node := List (BitVec 64) × List (BitVec 64 × BitVec 64 × BitVec 64) × List ℕ × List (ℕ × ℕ)

def checkReplay64 (m : BitVec 64) (b0 : ℕ) (bank : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → Bool
  | [], targets => targets.all (fun t => nrmM64 m b0 t == 0 || bank.contains (nrmM64 m b0 t))
  | (v, a, b) :: rest, targets =>
    bank.contains a && bank.contains b && (ops 64 a b).contains v &&
    checkReplay64 m b0 (v :: bank) rest targets

theorem checkReplay64_sound (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (g : BitVec 32)
    (steps : List (BitVec 64 × BitVec 64 × BitVec 64)) (targets : List (BitVec 64)) :
    ∀ (bank : List (BitVec 64)) (k : ℕ),
      checkReplay64 m b0 bank steps targets = true →
      build (basicOps 32) g k (nonZeroImg (projS 32 idxs) targets.toFinset) →
      build (basicOps 32) g (k + steps.length) (nonZeroImg (projS 32 idxs) bank.toFinset) := by
  let f : BitVec 64 → BitVec 32 := projS 32 idxs
  have hn : 0 < 32 := by decide
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [checkReplay64, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne
      rw [← projS_nrmM64 idxs hlen hlt m hm b0 t, h0, projS_zero]
    · exact ⟨hne, nrmM64 m b0 t, hmem, projS_nrmM64 idxs hlen hlt m hm b0 t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [checkReplay64, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ha, hb_mem⟩, hv⟩, hrest⟩ := hchk
    have hb' := ih (v :: bank) k hrest hb
    simp only [List.length_cons, show k + (rest.length + 1) = (k + rest.length) + 1 by omega]
    have hfv : f v ∈ ops 32 (f a) (f b) := projS_ops 32 hn idxs hlen hlt a b v hv
    have hsub_ins (hmem_v : f v = 0 ∨ f v ∈ nonZeroImg f bank.toFinset) :
        nonZeroImg f (v :: bank).toFinset ⊆ nonZeroImg f bank.toFinset := by
      intro u hu
      simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
      · rcases hmem_v with h0 | hm'
        · exact (hne h0).elim
        · exact Finset.mem_erase.mp hm' |>.imp_right (fun hi => by simpa [List.mem_toFinset] using hi)
      · exact ⟨hne, w, hw, rfl⟩
    by_cases hv0 : f v = 0
    · exact Or.inl (build_mono_av (hsub_ins (Or.inl hv0)) hb')
    · by_cases ha0 : f a = 0
      · rcases ops_zero_left 32 (f b) (f v) (ha0 ▸ hfv) with h0 | h1
        · exact (hv0 h0).elim
        · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb_mem, h1.symm⟩⟩))) hb')
      · by_cases hb0 : f b = 0
        · rcases ops_zero_right 32 (f a) (f v) (hb0 ▸ hfv) with h0 | h1
          · exact (hv0 h0).elim
          · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
        · by_cases hab : f a = f b
          · rcases ops_self 32 (f a) (f v) (hab ▸ hfv) with h0 | h1
            · exact (hv0 h0).elim
            · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
          · refine Or.inr ⟨f a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr ha)⟩,
              f b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hb_mem)⟩,
              hab, f v, ?_, ?_⟩
            · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
              exact ⟨hfv, hv0, projS_ne_allOnes 32 hn idxs v⟩
            · apply build_mono_av _ hb'
              intro u hu
              simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu
              obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hw)⟩)

def addNeed64 (stock needed : List (BitVec 64)) (u : BitVec 64) : List (BitVec 64) :=
  if u == 0 || stock.contains u || needed.contains u then needed else u :: needed

def buildNeeded64 (m : BitVec 64) (b0 : ℕ) (stock : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → List (BitVec 64)
  | [], needed => needed
  | (w, a, b) :: rest, needed =>
    let pw := nrmM64 m b0 w
    let needed' := if needed.contains pw then addNeed64 stock (addNeed64 stock needed (nrmM64 m b0 a)) (nrmM64 m b0 b) else needed
    buildNeeded64 m b0 stock rest needed'

def buildSteps64 (m : BitVec 64) (b0 : ℕ) (needed : List (BitVec 64)) :
    List (BitVec 64 × BitVec 64 × BitVec 64) → List (BitVec 64) → List (BitVec 64 × BitVec 64 × BitVec 64)
  | [], _ => []
  | (w, a, b) :: rest, bank =>
    let pw := nrmM64 m b0 w
    let pa := nrmM64 m b0 a
    let pb := nrmM64 m b0 b
    if needed.contains pw && pw != 0 && !bank.contains pw &&
       bank.contains pa && bank.contains pb && (ops 64 pa pb).contains pw then
      (pw, pa, pb) :: buildSteps64 m b0 needed rest (pw :: bank)
    else
      buildSteps64 m b0 needed rest bank

def checkCofClose64 (lb fuel : ℕ) (m : BitVec 64) (b0 : ℕ) (stock : List (BitVec 64))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) : Bool :=
  let flat := (nxt.filter (fun u => nrmM64 m b0 u == 0)).length
  let rem := fuel - flat
  if Nat.blt rem lb then
    let start := nxt.foldl (fun acc u => addNeed64 stock acc (nrmM64 m b0 u)) []
    if Nat.blt (start.length + rem) lb then
      let needed := buildNeeded64 m b0 stock hist.reverse start
      if Nat.blt (needed.length + rem) lb then
        let steps := buildSteps64 m b0 needed hist stock
        Nat.blt (steps.length + rem) lb && checkReplay64 m b0 stock steps nxt
      else false
    else false
  else false

theorem checkCofClose64_sound_aux (goal6 : BitVec 64) (lb : ℕ) (idxs : List ℕ) (hlen : idxs.length = 32) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ)
    (stock : List (BitVec 64)) (g : BitVec 32) (hgnz : g ≠ 0)
    (hg : projS 32 idxs goal6 = g)
    (hstock : stock.all (fun w => rows5.contains (projS 32 idxs w)) = true)
    (hnobuild : ¬ build (basicOps 32) g (lb - 1) rows5.toFinset)
    (fuel : ℕ) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64))
    (hnd : nxt.Nodup) (hchk : checkCofClose64 lb fuel m b0 stock hist nxt = true) :
    ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  intro hlive
  unfold checkCofClose64 at hchk
  dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops64 : ∀ a b z : BitVec 64, z ∈ basicOps 64 a b → z ∈ ops 64 a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict (by decide : 0 < 32) idxs hlen hlt hops64 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => nrmM64 m b0 u == 0)).length ≤ zCount (projS 32 idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => nrmM64 m b0 u == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]
          apply Finset.card_le_card
          intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_nrmM64 idxs hlen hlt m hm b0 u, hu.2, projS_zero]
        have hrep := checkReplay64_sound idxs hlen hlt m hm b0 g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS 32 idxs) stock.toFinset ⊆ rows5.toFinset := by
          intro u hu
          simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu
          obtain ⟨_, v, hv, rfl⟩ := hu
          have h1 := List.all_eq_true.mp hstock v hv
          simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
          exact List.mem_toFinset.mpr h1
        exact hnobuild (build_mono_k (by omega) (build_mono_av hsub hrep))
      · cases hchk
    · cases hchk
  · cases hchk

def checkChildW6 (cfLBs : Array ℕ) (cfMasks : Array (BitVec 64)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 64)))
    (k : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 64)))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) : Bool :=
  decide (nxt.length > k) ||
  cfs.any (fun c => checkCofClose64 (cfLBs[c]?.getD 0) (k - 1) (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt) ||
  targets.any (fun t => sameSet nxt t)

def checkStepW6 (goal6 : BitVec 64) (cfLBs : Array ℕ) (cfMasks : Array (BitVec 64)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 64)))
    (k extra : ℕ) (cfs : List ℕ) (targets : List (List (BitVec 64)))
    (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (a b : BitVec 64) (r : List (BitVec 64)) : Bool :=
  (ops 64 a b).all fun w =>
    (w == 0 || w == BitVec.allOnes 64 || w == a || w == b || r.contains w) ||
    let h' := hist ++ [(w, a, b)]
    (!cover 64 jumps6 goal6 (w :: r) || checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: r)) &&
    ((extra == 0) ||
      ((!cover 64 jumps6 goal6 (w :: a :: r) || checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: r)) &&
       (!cover 64 jumps6 goal6 (w :: b :: r) || checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: b :: r)))) &&
    ((extra < 2) || !cover 64 jumps6 goal6 (w :: a :: b :: r) || checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets h' (w :: a :: b :: r))

def checkNodeW6 (goal6 : BitVec 64) (gsize : ℕ) (g6_pow : Array (List ℕ)) (ncf : ℕ)
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 64)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 64)))
    (k : ℕ) (cur prev : Array W6Node) (i : ℕ) : Bool :=
  match cur[i]? with
  | none => false
  | some (ws, hist, cfs, hs) =>
    decide ws.Nodup && !(ws.contains goal6) && decide (ws.length ≤ k + 1) &&
    cfs.all (fun c => Nat.blt c ncf) &&
    hs.all (fun p => Nat.blt p.1 gsize && Nat.blt p.2 prev.size) &&
    let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 64 (g6_pow[p.1]?.getD [])))
    let extra := k + 1 - ws.length
    (pairs ws).all (fun (a, b, r) => checkStepW6 goal6 cfLBs cfMasks cfB0s cfStocks k extra cfs targets hist a b r)

def checkBlockW6 (goal6 : BitVec 64) (gsize : ℕ) (g6_pow : Array (List ℕ)) (ncf : ℕ)
    (cfLBs : Array ℕ) (cfMasks : Array (BitVec 64)) (cfB0s : Array ℕ) (cfStocks : Array (List (BitVec 64)))
    (k : ℕ) (cur prev : Array W6Node) (start : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => checkNodeW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev (start + m) &&
      checkBlockW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev start m

theorem checkBlockW6_at {goal6 : BitVec 64} {gsize ncf k start m : ℕ} {g6_pow : Array (List ℕ)}
    {cfLBs cfB0s : Array ℕ} {cfMasks : Array (BitVec 64)} {cfStocks : Array (List (BitVec 64))}
    {cur prev : Array W6Node}
    (h : checkBlockW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev start m = true)
    (j : ℕ) (lo : start ≤ j) (hi : j < start + m) :
    checkNodeW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev j = true := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [checkBlockW6, Bool.and_eq_true] at h
    by_cases eq : j = start + m
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem node_sound_W6 {goal6 : BitVec 64} {gsize ncf k i : ℕ}
    {g6_idx g6_pow : Array (List ℕ)} {g6_inv cfLBs cfB0s : Array ℕ}
    {cfMasks : Array (BitVec 64)} {cfStocks : Array (List (BitVec 64))}
    {cur prev : Array W6Node}
    (hk : 0 < k) (hi : i < cur.size)
    (hvalid : (List.range gsize).all (symValid 64 gsize g6_idx g6_pow g6_inv goal6) = true)
    (hcof : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose64 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 64) goal6 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 64) goal6 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hchk : checkNodeW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ¬ live (basicOps 64) goal6 k (cur[i]?.getD ([], [], [], [])).1.toFinset := by
  rcases hci : cur[i] with ⟨ws, hist, cfs, hs⟩
  have hget : cur[i]? = some (ws, hist, cfs, hs) := by rw [Array.getElem?_eq_getElem hi, hci]
  unfold checkNodeW6 at hchk
  rw [hget] at hchk ⊢
  dsimp only at hchk ⊢
  simp only [Option.getD_some]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, List.all_eq_true, Nat.blt_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hnd, hng⟩, hlen⟩, hcfs⟩, hhs⟩, hall⟩ := hchk
  let targets := hs.map (fun p => (prev[p.2]?.getD ([], [], [], [])).1.map (actB 64 (g6_pow[p.1]?.getD [])))
  have htargets : ∀ t ∈ targets, ¬ live (basicOps 64) goal6 (k - 1) t.toFinset := by
    intro t ht
    obtain ⟨⟨g, c⟩, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨hg, hc⟩ := hhs (g, c) hmem
    intro hlive
    have hinv_lt := (actB_spec hvalid g hg).1
    have hinv_g := (actB_spec hvalid (g6_inv[g]?.getD 0) hinv_lt).2.2.2.1
    have himg := live_map (actB 64 (g6_pow[g6_inv[g]?.getD 0]?.getD [])) (actB_inj hvalid _ hinv_lt)
      hinv_g (actB_ops hvalid _ hinv_lt) hlive
    have hset : (((prev[c]?.getD ([], [], [], [])).1.map (actB 64 (g6_pow[g]?.getD []))).toFinset.image
        (actB 64 (g6_pow[g6_inv[g]?.getD 0]?.getD []))) = (prev[c]?.getD ([], [], [], [])).1.toFinset := by
      ext u; simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
      constructor
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩; rwa [actB_inv_left hvalid g hg v]
      · intro hu; exact ⟨actB 64 (g6_pow[g]?.getD []) u, ⟨u, hu, rfl⟩, actB_inv_left hvalid g hg u⟩
    rw [hset] at himg
    exact hprev c hc himg
  intro hlive
  have hk_eq : k = (k - 1) + 1 := by omega
  rw [hk_eq] at hlive
  rcases first_live hlive with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs_eq, tail⟩
  · have hmem : goal6 ∈ ws.toFinset := done.symm ▸ Finset.mem_singleton_self _
    exact hng (List.mem_toFinset.mp hmem)
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have check_pair {a b : BitVec 64} (hpair : (a, b, r) ∈ pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed))
        (hop : z ∈ basicOps 64 a b) : False := by
      obtain ⟨kept, hkept, hnk, hfin⟩ := recover_kept perm hnd hset
      have hznot : z ≠ a ∧ z ≠ b ∧ z ∉ r := by
        refine ⟨fun e => hout (by rw [hset, e]; simp), fun e => hout (by rw [hset, e]; simp), ?_⟩
        intro hr
        exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
      have hznew : z ∉ kept := by
        intro hu; apply hout; rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hndc : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have htail : live (basicOps 64) goal6 (k - 1) (z :: kept).toFinset := by simpa [hfin] using tail
      have hcard := live_card htail
      rw [List.toFinset_card_of_nodup hndc] at hcard
      have hcov : cover 64 jumps6 goal6 (z :: kept) = true := live_cover htail
      have hstep := hall (a, b, r) hpair
      unfold checkStepW6 at hstep
      dsimp only at hstep
      simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne] at hop
      have hw := List.all_eq_true.mp hstep z hop.1
      have hskip : (z == 0 || z == BitVec.allOnes 64 || z == a || z == b || r.contains z) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.contains_eq_mem, decide_eq_false_iff_not]
        exact ⟨⟨⟨⟨hop.2.1, hop.2.2⟩, hznot.1⟩, hznot.2.1⟩, hznot.2.2⟩
      rw [hskip, Bool.false_or] at hw
      simp only [Bool.and_eq_true] at hw
      have plen := perm.length_eq
      simp only [List.length_cons] at plen
      have close (hc : checkChildW6 cfLBs cfMasks cfB0s cfStocks k cfs targets (hist ++ [(z, a, b)]) (z :: kept) = true) : False := by
        unfold checkChildW6 at hc
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hc
        rcases hc with (hgt | ⟨c, hcm, hcf⟩) | ⟨t, ht, hss⟩
        · omega
        · exact hcof c (k - 1) (hcfs c hcm) (hist ++ [(z, a, b)]) (z :: kept) hndc hcf htail
        · rw [sameSet_sound hss] at htail
          exact htargets t ht htail
      simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hkept
      rcases hkept with hkr | rfl | rfl | rfl
      · subst kept
        have h1 := hw.1.1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.1
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.1.2
        have hex : k + 1 - ws.length ≠ 0 := by simp only [List.length_cons] at hcard; omega
        simp only [beq_eq_false_iff_ne.mpr hex, Bool.false_or, Bool.and_eq_true] at h1
        have h2 := h1.2
        rw [hcov] at h2; simp only [Bool.not_true, Bool.false_or] at h2
        exact close h2
      · have h1 := hw.2
        have hex : ¬ (k + 1 - ws.length < 2) := by simp only [List.length_cons] at hcard; omega
        simp only [decide_eq_false hex, Bool.false_or] at h1
        rw [hcov] at h1; simp only [Bool.not_true, Bool.false_or] at h1
        exact close h1
    rcases hm with direct | swap
    · exact check_pair direct hp hs_eq hz
    · exact check_pair swap (hp.trans (.swap _ _ _)) (by rw [hs_eq, Finset.insert_comm]) (ops_swap 64 a b ▸ hz)

theorem level_sound_W6 {goal6 : BitVec 64} {gsize ncf k : ℕ}
    {g6_idx g6_pow : Array (List ℕ)} {g6_inv cfLBs cfB0s : Array ℕ}
    {cfMasks : Array (BitVec 64)} {cfStocks : Array (List (BitVec 64))}
    {cur prev : Array W6Node}
    (hk : 0 < k)
    (hvalid : (List.range gsize).all (symValid 64 gsize g6_idx g6_pow g6_inv goal6) = true)
    (hcof : ∀ c fuel, c < ncf → ∀ hist nxt, nxt.Nodup →
      checkCofClose64 (cfLBs[c]?.getD 0) fuel (cfMasks[c]?.getD 0) (cfB0s[c]?.getD 0) (cfStocks[c]?.getD []) hist nxt = true →
      ¬ live (basicOps 64) goal6 fuel nxt.toFinset)
    (hprev : ∀ j < prev.size, ¬ live (basicOps 64) goal6 (k - 1) (prev[j]?.getD ([], [], [], [])).1.toFinset)
    (hblk : ∀ i < cur.size, checkNodeW6 goal6 gsize g6_pow ncf cfLBs cfMasks cfB0s cfStocks k cur prev i = true) :
    ∀ i < cur.size, ¬ live (basicOps 64) goal6 k (cur[i]?.getD ([], [], [], [])).1.toFinset :=
  fun i hi => node_sound_W6 hk hi hvalid hcof hprev (hblk i hi)

theorem projS_nrmM64_16 (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (u : BitVec 64) :
    projS 16 idxs (nrmM64 m b0 u) = projS 16 idxs u := by
  unfold nrmM64
  cases u.getLsbD b0
  · simp only [Bool.false_eq_true, ite_false]
    exact projS_mask 16 idxs m hm u
  · simp only [ite_true]
    rw [projS_mask 16 idxs m hm (~~~u), projS_not 16 (by decide) idxs hlen hlt u]

theorem checkReplay64_16_sound (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ) (g : BitVec 16)
    (steps : List (BitVec 64 × BitVec 64 × BitVec 64)) (targets : List (BitVec 64)) :
    ∀ (bank : List (BitVec 64)) (k : ℕ),
      checkReplay64 m b0 bank steps targets = true →
      build (basicOps 16) g k (nonZeroImg (projS 16 idxs) targets.toFinset) →
      build (basicOps 16) g (k + steps.length) (nonZeroImg (projS 16 idxs) bank.toFinset) := by
  let f : BitVec 64 → BitVec 16 := projS 16 idxs
  have hn : 0 < 16 := by decide
  induction steps with
  | nil =>
    intro bank k hchk hb
    simp only [checkReplay64, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at hchk
    simp only [List.length_nil, Nat.add_zero]
    apply build_mono_av _ hb
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu ⊢
    obtain ⟨hne, t, ht, rfl⟩ := hu
    rcases hchk t ht with h0 | hmem
    · exfalso; apply hne
      rw [← projS_nrmM64_16 idxs hlen hlt m hm b0 t, h0, projS_zero]
    · exact ⟨hne, nrmM64 m b0 t, hmem, projS_nrmM64_16 idxs hlen hlt m hm b0 t⟩
  | cons s rest ih =>
    obtain ⟨v, a, b⟩ := s
    intro bank k hchk hb
    simp only [checkReplay64, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨ha, hb_mem⟩, hv⟩, hrest⟩ := hchk
    have hb' := ih (v :: bank) k hrest hb
    simp only [List.length_cons, show k + (rest.length + 1) = (k + rest.length) + 1 by omega]
    have hfv : f v ∈ ops 16 (f a) (f b) := projS_ops 16 hn idxs hlen hlt a b v hv
    have hsub_ins (hmem_v : f v = 0 ∨ f v ∈ nonZeroImg f bank.toFinset) :
        nonZeroImg f (v :: bank).toFinset ⊆ nonZeroImg f bank.toFinset := by
      intro u hu
      simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
      · rcases hmem_v with h0 | hm'
        · exact (hne h0).elim
        · exact Finset.mem_erase.mp hm' |>.imp_right (fun hi => by simpa [List.mem_toFinset] using hi)
      · exact ⟨hne, w, hw, rfl⟩
    by_cases hv0 : f v = 0
    · exact Or.inl (build_mono_av (hsub_ins (Or.inl hv0)) hb')
    · by_cases ha0 : f a = 0
      · rcases ops_zero_left 16 (f b) (f v) (ha0 ▸ hfv) with h0 | h1
        · exact (hv0 h0).elim
        · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨b, List.mem_toFinset.mpr hb_mem, h1.symm⟩⟩))) hb')
      · by_cases hb0 : f b = 0
        · rcases ops_zero_right 16 (f a) (f v) (hb0 ▸ hfv) with h0 | h1
          · exact (hv0 h0).elim
          · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
        · by_cases hab : f a = f b
          · rcases ops_self 16 (f a) (f v) (hab ▸ hfv) with h0 | h1
            · exact (hv0 h0).elim
            · exact Or.inl (build_mono_av (hsub_ins (Or.inr (Finset.mem_erase.mpr ⟨hv0, Finset.mem_image.mpr ⟨a, List.mem_toFinset.mpr ha, h1.symm⟩⟩))) hb')
          · refine Or.inr ⟨f a, Finset.mem_erase.mpr ⟨ha0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr ha)⟩,
              f b, Finset.mem_erase.mpr ⟨hb0, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hb_mem)⟩,
              hab, f v, ?_, ?_⟩
            · simp only [basicOps, List.mem_toFinset, List.mem_filter, Bool.and_eq_true, bne_iff_ne]
              exact ⟨hfv, hv0, projS_ne_allOnes 16 hn idxs v⟩
            · apply build_mono_av _ hb'
              intro u hu
              simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu
              obtain ⟨hne, w, rfl | hw, rfl⟩ := hu
              · exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem f (List.mem_toFinset.mpr hw)⟩)

theorem checkCofClose64_16_sound_aux (goal6 : BitVec 64) (lb : ℕ) (idxs : List ℕ) (hlen : idxs.length = 16) (hlt : ∀ idx ∈ idxs, idx < 64)
    (m : BitVec 64) (hm : ∀ idx ∈ idxs, m.getLsbD idx = true) (b0 : ℕ)
    (stock : List (BitVec 64)) (g : BitVec 16) (hgnz : g ≠ 0)
    (hg : projS 16 idxs goal6 = g)
    (hstock : stock.all (fun w => rows4.contains (projS 16 idxs w)) = true)
    (hnobuild : ¬ build (basicOps 16) g (lb - 1) rows4.toFinset)
    (fuel : ℕ) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64))
    (hnd : nxt.Nodup) (hchk : checkCofClose64 lb fuel m b0 stock hist nxt = true) :
    ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  intro hlive
  unfold checkCofClose64 at hchk
  dsimp only at hchk
  split at hchk
  · split at hchk
    · split at hchk
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hchk
        have hops64 : ∀ a b z : BitVec 64, z ∈ basicOps 64 a b → z ∈ ops 64 a b := fun a b z hz =>
          (List.mem_filter.mp (List.mem_toFinset.mp hz)).1
        have hres := live_restrict (by decide : 0 < 16) idxs hlen hlt hops64 hg hgnz hlive
        have hflat_le : (nxt.filter (fun u => nrmM64 m b0 u == 0)).length ≤ zCount (projS 16 idxs) nxt.toFinset := by
          have hndf : (nxt.filter (fun u => nrmM64 m b0 u == 0)).Nodup := hnd.filter _
          rw [← List.toFinset_card_of_nodup hndf]
          apply Finset.card_le_card
          intro u hu
          simp only [List.mem_toFinset, List.mem_filter, beq_iff_eq] at hu
          refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu.1, ?_⟩
          rw [← projS_nrmM64_16 idxs hlen hlt m hm b0 u, hu.2, projS_zero]
        have hrep := checkReplay64_16_sound idxs hlen hlt m hm b0 g _ nxt stock _ hchk.2 hres
        have hsub : nonZeroImg (projS 16 idxs) stock.toFinset ⊆ rows4.toFinset := by
          intro u hu
          simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image, List.mem_toFinset] at hu
          obtain ⟨_, v, hv, rfl⟩ := hu
          have h1 := List.all_eq_true.mp hstock v hv
          simp only [List.contains_eq_mem, decide_eq_true_eq] at h1
          exact List.mem_toFinset.mpr h1
        exact hnobuild (build_mono_k (by omega) (build_mono_av hsub hrep))
      · cases hchk
    · cases hchk
  · cases hchk

def v0 : BitVec 64 := 0xaaaaaaaaaaaaaaaa
def v1 : BitVec 64 := 0xcccccccccccccccc
def v2 : BitVec 64 := 0xf0f0f0f0f0f0f0f0
def v3 : BitVec 64 := 0xff00ff00ff00ff00
def v4 : BitVec 64 := 0xffff0000ffff0000
def v5 : BitVec 64 := 0xffffffff00000000
def v6 : BitVec 64 := 0xeeeeeeeeeeeeeeee
def v7 : BitVec 64 := 0xfafafafafafafafa
def v8 : BitVec 64 := 0xfefefefefefefefe
def v9 : BitVec 64 := 0xfcfcfcfcfcfcfcfc
def v10 : BitVec 64 := 0xff000000ff000000
def v11 : BitVec 64 := 0x3232323232323232
def v12 : BitVec 64 := 0xe0e0e0e0e0e0e0e
def v13 : BitVec 64 := 0xfe00fe00fe00fe00
def v14 : BitVec 64 := 0xff00ff0000000000
def v15 : BitVec 64 := 0xf000f000f000f00
def v16 : BitVec 64 := 0xf0f0f0f00000000
def v17 : BitVec 64 := 0xfefefefe00000000
def v18 : BitVec 64 := 0xfefe0000fefe
def v19 : BitVec 64 := 0xffff000000000000
def v20 : BitVec 64 := 0x3333000033330000
def v21 : BitVec 64 := 0xffaaaaaaffaaaaaa
def v22 : BitVec 64 := 0xfefe0000fefe0000
def v23 : BitVec 64 := 0xfff0f0f0fff0f0f0
def v24 : BitVec 64 := 0x3300330033003300
def v25 : BitVec 64 := 0xfefefefe
def v26 : BitVec 64 := 0xee00ee00ee00ee00
def v27 : BitVec 64 := 0x303000003030000
def v28 : BitVec 64 := 0x1100110011001100
def v29 : BitVec 64 := 0x3333333300000000
def v30 : BitVec 64 := 0x300030003000300
def v31 : BitVec 64 := 0xafafafafaaaaaaaa
def v32 : BitVec 64 := 0xffffcccccccccccc
def v33 : BitVec 64 := 0xfafa0000fafa0000
def v34 : BitVec 64 := 0xffeeeeeeffeeeeee
def v35 : BitVec 64 := 0xeeeeeeee00000000
def v36 : BitVec 64 := 0x303030300000000
def v37 : BitVec 64 := 0xffccccccffcccccc
def v38 : BitVec 64 := 0xfa00fa00fa00fa00
def v39 : BitVec 64 := 0x5454545454545454
def v40 : BitVec 64 := 0xffaaffaaaaaaaaaa
def v41 : BitVec 64 := 0x1111111100000000
def v42 : BitVec 64 := 0x5555555500000000
def v43 : BitVec 64 := 0x5555000055550000
def v44 : BitVec 64 := 0xf0f00000f0f0000
def v45 : BitVec 64 := 0xfafafafa00000000
def v46 : BitVec 64 := 0xfafa0000ffff0000
def v47 : BitVec 64 := 0x505000005050000
def v48 : BitVec 64 := 0xfafaffff00000000
def v49 : BitVec 64 := 0x505050500000000
def v50 : BitVec 64 := 0xafaaafaaafaaafaa
def v51 : BitVec 64 := 0xeeee0000eeee0000
def v52 : BitVec 64 := 0xf0a0a0a0f0a0a0a
def v53 : BitVec 64 := 0xfc00fc00fc00fc00
def v54 : BitVec 64 := 0xfffafafafffafafa
def v55 : BitVec 64 := 0xefefefefeeeeeeee
def v56 : BitVec 64 := 0x3322222233222222
def v57 : BitVec 64 := 0x100010001000100
def v58 : BitVec 64 := 0x5500550055005500
def v59 : BitVec 64 := 0xffccffcccccccccc
def v60 : BitVec 64 := 0xfafafa00fafafa
def v61 : BitVec 64 := 0xfe00fe00fe00fe
def v62 : BitVec 64 := 0xf0e0e0e0f0e0e0e
def v63 : BitVec 64 := 0xf0000000f000000
def v64 : BitVec 64 := 0xafafaaaaafafaaaa
def v65 : BitVec 64 := 0xf1f0f1f0f1f0f1f0
def v66 : BitVec 64 := 0x2323232322222222
def v67 : BitVec 64 := 0x3330303033303030
def v68 : BitVec 64 := 0xe0e0e0e0eeeeeeee
def v69 : BitVec 64 := 0xfcfc0000fcfc0000
def v70 : BitVec 64 := 0xfcfcfcfc00000000
def v71 : BitVec 64 := 0xfe00ff00fe00ff00
def v72 : BitVec 64 := 0xffeeeeee00000000
def v73 : BitVec 64 := 0x101010100000000
def v74 : BitVec 64 := 0x101000001010000
def v75 : BitVec 64 := 0xcfcfcfcfcccccccc
def v76 : BitVec 64 := 0x3300000033000000
def v77 : BitVec 64 := 0xbbaabbaabbaabbaa
def v78 : BitVec 64 := 0xbbbbbbbbaaaaaaaa
def v79 : BitVec 64 := 0xeeeeee00eeeeee
def v80 : BitVec 64 := 0xf000f0000000000
def v81 : BitVec 64 := 0xfefeccccfefecccc
def v82 : BitVec 64 := 0xfffff0f0f0f0f0f0
def v83 : BitVec 64 := 0xff00ff00ff00
def v84 : BitVec 64 := 0xf5f5f0f0f5f5f0f0
def v85 : BitVec 64 := 0xcdcdcccccdcdcccc
def v86 : BitVec 64 := 0xfefeffff00000000
def v87 : BitVec 64 := 0xfe00cc00fe00cc00
def v88 : BitVec 64 := 0xfff0fff0f0f0f0f0
def v89 : BitVec 64 := 0xf0a0f0a0a0a0a0a
def v90 : BitVec 64 := 0xabaaabaaabaaabaa
def v91 : BitVec 64 := 0xcdcccdcccdcccdcc
def v92 : BitVec 64 := 0xcdcdcdcdcccccccc
def v93 : BitVec 64 := 0xfe00fe00ff00ff00
def v94 : BitVec 64 := 0xf0ffffff00000000
def v95 : BitVec 64 := 0xfcfffcff00000000
def v96 : BitVec 64 := 0xfef0fef0fef0fef0
def v97 : BitVec 64 := 0xf000ff00f000ff00
def v98 : BitVec 64 := 0xf0f0ffff00000000
def v99 : BitVec 64 := 0xf000f000ff00ff00
def v100 : BitVec 64 := 0x3322332222222222
def v101 : BitVec 64 := 0xfeccfeccfeccfecc
def v102 : BitVec 64 := 0x3200320032003200
def v103 : BitVec 64 := 0x1111000011110000
def v104 : BitVec 64 := 0xff00000000000000
def v105 : BitVec 64 := 0xffffaaaaaaaaaaaa
def v106 : BitVec 64 := 0xffaacc8888888888
def v107 : BitVec 64 := 0xfffcfcfcfffcfcfc
def v108 : BitVec 64 := 0xf1f1f1f1f0f0f0f0
def v109 : BitVec 64 := 0xababaaaaababaaaa
def v110 : BitVec 64 := 0xababababaaaaaaaa
def v111 : BitVec 64 := 0xe000e000e000e00
def v112 : BitVec 64 := 0xe0e0e0e00000000
def v113 : BitVec 64 := 0xffeeffeeeeeeeeee
def v114 : BitVec 64 := 0x3333222222222222
def v115 : BitVec 64 := 0xfbfafbfafbfafbfa
def v116 : BitVec 64 := 0xf3f0f0f0f3f0f0f0
def v117 : BitVec 64 := 0x500050005000500
def v118 : BitVec 64 := 0xfeaafeaafeaafeaa
def v119 : BitVec 64 := 0xf0c0f0c0c0c0c0c
def v120 : BitVec 64 := 0xffffff00000000
def v121 : BitVec 64 := 0xaa00ff00aa00ff00
def v122 : BitVec 64 := 0xaa00aa00ff00ff00
def v123 : BitVec 64 := 0x3333000000000000
def v124 : BitVec 64 := 0xf5f5f5f5f0f0f0f0
def v125 : BitVec 64 := 0x3300330000000000

def g6_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def g6_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648,4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808]
def g6_s1 : List ℕ := [0,2,1,3,4,6,5,7,16,18,17,19,20,22,21,23,8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31,32,34,33,35,36,38,37,39,48,50,49,51,52,54,53,55,40,42,41,43,44,46,45,47,56,58,57,59,60,62,61,63]
def g6_p1 : List ℕ := [1,4,2,8,16,64,32,128,65536,262144,131072,524288,1048576,4194304,2097152,8388608,256,1024,512,2048,4096,16384,8192,32768,16777216,67108864,33554432,134217728,268435456,1073741824,536870912,2147483648,4294967296,17179869184,8589934592,34359738368,68719476736,274877906944,137438953472,549755813888,281474976710656,1125899906842624,562949953421312,2251799813685248,4503599627370496,18014398509481984,9007199254740992,36028797018963968,1099511627776,4398046511104,2199023255552,8796093022208,17592186044416,70368744177664,35184372088832,140737488355328,72057594037927936,288230376151711744,144115188075855872,576460752303423488,1152921504606846976,4611686018427387904,2305843009213693952,9223372036854775808]
def g6_idx : Array (List ℕ) := Array.mk [g6_s0,g6_s1]
def g6_pow : Array (List ℕ) := Array.mk [g6_p0,g6_p1]
def g6_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_G_valid : (List.range 2).all (symValid 64 2 g6_idx g6_pow g6_inv goal6) = true := by decide +kernel

def g6_m0 : BitVec 64 := 0xf0f0f0f0f0f0f0f

def g6_st0 : List (BitVec 64) := [0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]

def g6_ix0 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,32,33,34,35,40,41,42,43,48,49,50,51,56,57,58,59]

set_option maxRecDepth 100000 in

theorem g6_cspec_0 : g6_ix0.length = 32 ∧ (∀ idx ∈ g6_ix0, idx < 64) ∧ (∀ idx ∈ g6_ix0, g6_m0.getLsbD idx = true) ∧ projS 32 g6_ix0 goal6 = c5_0_goal ∧ g6_st0.all (fun w => rows5.contains (projS 32 g6_ix0 w)) = true := by decide +kernel

def g6_m1 : BitVec 64 := 0x5555555555555555

def g6_st1 : List (BitVec 64) := [0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]

def g6_ix1 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_1 : g6_ix1.length = 32 ∧ (∀ idx ∈ g6_ix1, idx < 64) ∧ (∀ idx ∈ g6_ix1, g6_m1.getLsbD idx = true) ∧ projS 32 g6_ix1 goal6 = c5_1_goal ∧ g6_st1.all (fun w => rows5.contains (projS 32 g6_ix1 w)) = true := by decide +kernel

def g6_m2 : BitVec 64 := 0xffffffff

def g6_st2 : List (BitVec 64) := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]

def g6_ix2 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]

set_option maxRecDepth 100000 in

theorem g6_cspec_2 : g6_ix2.length = 32 ∧ (∀ idx ∈ g6_ix2, idx < 64) ∧ (∀ idx ∈ g6_ix2, g6_m2.getLsbD idx = true) ∧ projS 32 g6_ix2 goal6 = c5_2_goal ∧ g6_st2.all (fun w => rows5.contains (projS 32 g6_ix2 w)) = true := by decide +kernel

def g6_m3 : BitVec 64 := 0xff00ff00ff00ff00

def g6_st3 : List (BitVec 64) := [0xaa00aa00aa00aa00,0xcc00cc00cc00cc00,0xf000f000f000f000,0xff000000ff000000,0xff00ff0000000000]

def g6_ix3 : List ℕ := [8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31,40,42,41,43,44,46,45,47,56,58,57,59,60,62,61,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_3 : g6_ix3.length = 32 ∧ (∀ idx ∈ g6_ix3, idx < 64) ∧ (∀ idx ∈ g6_ix3, g6_m3.getLsbD idx = true) ∧ projS 32 g6_ix3 goal6 = c5_3_goal ∧ g6_st3.all (fun w => rows5.contains (projS 32 g6_ix3 w)) = true := by decide +kernel

def g6_m4 : BitVec 64 := 0x5500550055005500

def g6_st4 : List (BitVec 64) := [0x4400440044004400,0x5000500050005000,0x5500000055000000,0x5500550000000000]

def g6_ix4 : List ℕ := [8,10,12,14,24,26,28,30,40,42,44,46,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_4 : g6_ix4.length = 16 ∧ (∀ idx ∈ g6_ix4, idx < 64) ∧ (∀ idx ∈ g6_ix4, g6_m4.getLsbD idx = true) ∧ projS 16 g6_ix4 goal6 = b4_0_goal ∧ g6_st4.all (fun w => rows4.contains (projS 16 g6_ix4 w)) = true := by decide +kernel

def g6_m5 : BitVec 64 := 0x3300330033003300

def g6_st5 : List (BitVec 64) := [0x2200220022002200,0x3000300030003000,0x3300000033000000,0x3300330000000000]

def g6_ix5 : List ℕ := [8,9,12,13,24,25,28,29,40,41,44,45,56,57,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_5 : g6_ix5.length = 16 ∧ (∀ idx ∈ g6_ix5, idx < 64) ∧ (∀ idx ∈ g6_ix5, g6_m5.getLsbD idx = true) ∧ projS 16 g6_ix5 goal6 = b4_1_goal ∧ g6_st5.all (fun w => rows4.contains (projS 16 g6_ix5 w)) = true := by decide +kernel

def g6_m6 : BitVec 64 := 0xffffffff00000000

def g6_st6 : List (BitVec 64) := [0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000]

def g6_ix6 : List ℕ := [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_6 : g6_ix6.length = 32 ∧ (∀ idx ∈ g6_ix6, idx < 64) ∧ (∀ idx ∈ g6_ix6, g6_m6.getLsbD idx = true) ∧ projS 32 g6_ix6 goal6 = c5_4_goal ∧ g6_st6.all (fun w => rows5.contains (projS 32 g6_ix6 w)) = true := by decide +kernel

def g6_m7 : BitVec 64 := 0x5555555500000000

def g6_st7 : List (BitVec 64) := [0x4444444400000000,0x5050505000000000,0x5500550000000000,0x5555000000000000]

def g6_ix7 : List ℕ := [32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_7 : g6_ix7.length = 16 ∧ (∀ idx ∈ g6_ix7, idx < 64) ∧ (∀ idx ∈ g6_ix7, g6_m7.getLsbD idx = true) ∧ projS 16 g6_ix7 goal6 = b4_1_goal ∧ g6_st7.all (fun w => rows4.contains (projS 16 g6_ix7 w)) = true := by decide +kernel

def g6_m8 : BitVec 64 := 0x3333333300000000

def g6_st8 : List (BitVec 64) := [0x2222222200000000,0x3030303000000000,0x3300330000000000,0x3333000000000000]

def g6_ix8 : List ℕ := [32,33,36,37,48,49,52,53,40,41,44,45,56,57,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_8 : g6_ix8.length = 16 ∧ (∀ idx ∈ g6_ix8, idx < 64) ∧ (∀ idx ∈ g6_ix8, g6_m8.getLsbD idx = true) ∧ projS 16 g6_ix8 goal6 = b4_1_goal ∧ g6_st8.all (fun w => rows4.contains (projS 16 g6_ix8 w)) = true := by decide +kernel

def g6_m9 : BitVec 64 := 0xffff0000ffff0000

def g6_st9 : List (BitVec 64) := [0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff000000000000]

def g6_ix9 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_9 : g6_ix9.length = 32 ∧ (∀ idx ∈ g6_ix9, idx < 64) ∧ (∀ idx ∈ g6_ix9, g6_m9.getLsbD idx = true) ∧ projS 32 g6_ix9 goal6 = c5_3_goal ∧ g6_st9.all (fun w => rows5.contains (projS 32 g6_ix9 w)) = true := by decide +kernel

def g6_m10 : BitVec 64 := 0x3333000033330000

def g6_st10 : List (BitVec 64) := [0x2222000022220000,0x3030000030300000,0x3300000033000000,0x3333000000000000]

def g6_ix10 : List ℕ := [16,17,20,21,24,25,28,29,48,49,52,53,56,57,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_10 : g6_ix10.length = 16 ∧ (∀ idx ∈ g6_ix10, idx < 64) ∧ (∀ idx ∈ g6_ix10, g6_m10.getLsbD idx = true) ∧ projS 16 g6_ix10 goal6 = b4_0_goal ∧ g6_st10.all (fun w => rows4.contains (projS 16 g6_ix10 w)) = true := by decide +kernel

def g6_m11 : BitVec 64 := 0xf0f00000f0f0000

def g6_st11 : List (BitVec 64) := [0xa0a00000a0a0000,0xc0c00000c0c0000,0xf0000000f000000,0xf0f000000000000]

def g6_ix11 : List ℕ := [16,17,18,19,24,25,26,27,48,49,50,51,56,57,58,59]

set_option maxRecDepth 100000 in

theorem g6_cspec_11 : g6_ix11.length = 16 ∧ (∀ idx ∈ g6_ix11, idx < 64) ∧ (∀ idx ∈ g6_ix11, g6_m11.getLsbD idx = true) ∧ projS 16 g6_ix11 goal6 = b4_2_goal ∧ g6_st11.all (fun w => rows4.contains (projS 16 g6_ix11 w)) = true := by decide +kernel

def g6_m12 : BitVec 64 := 0xf000f000f000f00

def g6_st12 : List (BitVec 64) := [0xa000a000a000a00,0xc000c000c000c00,0xf0000000f000000,0xf000f0000000000]

def g6_ix12 : List ℕ := [8,10,9,11,24,26,25,27,40,42,41,43,56,58,57,59]

set_option maxRecDepth 100000 in

theorem g6_cspec_12 : g6_ix12.length = 16 ∧ (∀ idx ∈ g6_ix12, idx < 64) ∧ (∀ idx ∈ g6_ix12, g6_m12.getLsbD idx = true) ∧ projS 16 g6_ix12 goal6 = b4_2_goal ∧ g6_st12.all (fun w => rows4.contains (projS 16 g6_ix12 w)) = true := by decide +kernel

def g6_m13 : BitVec 64 := 0x3333333333333333

def g6_st13 : List (BitVec 64) := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]

def g6_ix13 : List ℕ := [0,1,4,5,16,17,20,21,8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,40,41,44,45,56,57,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_13 : g6_ix13.length = 32 ∧ (∀ idx ∈ g6_ix13, idx < 64) ∧ (∀ idx ∈ g6_ix13, g6_m13.getLsbD idx = true) ∧ projS 32 g6_ix13 goal6 = c5_1_goal ∧ g6_st13.all (fun w => rows5.contains (projS 32 g6_ix13 w)) = true := by decide +kernel

def g6_m14 : BitVec 64 := 0xff00ff0000000000

def g6_st14 : List (BitVec 64) := [0xaa00aa0000000000,0xcc00cc0000000000,0xf000f00000000000,0xff00000000000000]

def g6_ix14 : List ℕ := [40,42,41,43,44,46,45,47,56,58,57,59,60,62,61,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_14 : g6_ix14.length = 16 ∧ (∀ idx ∈ g6_ix14, idx < 64) ∧ (∀ idx ∈ g6_ix14, g6_m14.getLsbD idx = true) ∧ projS 16 g6_ix14 goal6 = b4_3_goal ∧ g6_st14.all (fun w => rows4.contains (projS 16 g6_ix14 w)) = true := by decide +kernel

def g6_m15 : BitVec 64 := 0xffff000000000000

def g6_st15 : List (BitVec 64) := [0xaaaa000000000000,0xcccc000000000000,0xf0f0000000000000,0xff00000000000000]

def g6_ix15 : List ℕ := [48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_15 : g6_ix15.length = 16 ∧ (∀ idx ∈ g6_ix15, idx < 64) ∧ (∀ idx ∈ g6_ix15, g6_m15.getLsbD idx = true) ∧ projS 16 g6_ix15 goal6 = b4_3_goal ∧ g6_st15.all (fun w => rows4.contains (projS 16 g6_ix15 w)) = true := by decide +kernel

def g6_m16 : BitVec 64 := 0xff000000ff0000

def g6_st16 : List (BitVec 64) := [0xaa000000aa0000,0xcc000000cc0000,0xf0000000f00000,0xff000000000000]

def g6_ix16 : List ℕ := [16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55]

set_option maxRecDepth 100000 in

theorem g6_cspec_16 : g6_ix16.length = 16 ∧ (∀ idx ∈ g6_ix16, idx < 64) ∧ (∀ idx ∈ g6_ix16, g6_m16.getLsbD idx = true) ∧ projS 16 g6_ix16 goal6 = b4_2_goal ∧ g6_st16.all (fun w => rows4.contains (projS 16 g6_ix16 w)) = true := by decide +kernel

def g6_m17 : BitVec 64 := 0xff00ff00000000

def g6_st17 : List (BitVec 64) := [0xaa00aa00000000,0xcc00cc00000000,0xf000f000000000,0xff000000000000]

def g6_ix17 : List ℕ := [32,33,34,35,36,37,38,39,48,49,50,51,52,53,54,55]

set_option maxRecDepth 100000 in

theorem g6_cspec_17 : g6_ix17.length = 16 ∧ (∀ idx ∈ g6_ix17, idx < 64) ∧ (∀ idx ∈ g6_ix17, g6_m17.getLsbD idx = true) ∧ projS 16 g6_ix17 goal6 = b4_2_goal ∧ g6_st17.all (fun w => rows4.contains (projS 16 g6_ix17 w)) = true := by decide +kernel

def g6_m18 : BitVec 64 := 0xff000000ff00

def g6_st18 : List (BitVec 64) := [0xaa000000aa00,0xcc000000cc00,0xf0000000f000,0xff0000000000]

def g6_ix18 : List ℕ := [8,10,9,11,12,14,13,15,40,42,41,43,44,46,45,47]

set_option maxRecDepth 100000 in

theorem g6_cspec_18 : g6_ix18.length = 16 ∧ (∀ idx ∈ g6_ix18, idx < 64) ∧ (∀ idx ∈ g6_ix18, g6_m18.getLsbD idx = true) ∧ projS 16 g6_ix18 goal6 = b4_2_goal ∧ g6_st18.all (fun w => rows4.contains (projS 16 g6_ix18 w)) = true := by decide +kernel

def g6_m19 : BitVec 64 := 0xffff0000

def g6_st19 : List (BitVec 64) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]

def g6_ix19 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]

set_option maxRecDepth 100000 in

theorem g6_cspec_19 : g6_ix19.length = 16 ∧ (∀ idx ∈ g6_ix19, idx < 64) ∧ (∀ idx ∈ g6_ix19, g6_m19.getLsbD idx = true) ∧ projS 16 g6_ix19 goal6 = b4_4_goal ∧ g6_st19.all (fun w => rows4.contains (projS 16 g6_ix19 w)) = true := by decide +kernel

def g6_m20 : BitVec 64 := 0xffff00000000

def g6_st20 : List (BitVec 64) := [0xaaaa00000000,0xcccc00000000,0xf0f000000000,0xff0000000000]

def g6_ix20 : List ℕ := [32,34,33,35,36,38,37,39,40,42,41,43,44,46,45,47]

set_option maxRecDepth 100000 in

theorem g6_cspec_20 : g6_ix20.length = 16 ∧ (∀ idx ∈ g6_ix20, idx < 64) ∧ (∀ idx ∈ g6_ix20, g6_m20.getLsbD idx = true) ∧ projS 16 g6_ix20 goal6 = b4_2_goal ∧ g6_st20.all (fun w => rows4.contains (projS 16 g6_ix20 w)) = true := by decide +kernel

def g6_m21 : BitVec 64 := 0xffff0000ffff

def g6_st21 : List (BitVec 64) := [0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]

def g6_ix21 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,32,34,33,35,36,38,37,39,40,42,41,43,44,46,45,47]

set_option maxRecDepth 100000 in

theorem g6_cspec_21 : g6_ix21.length = 32 ∧ (∀ idx ∈ g6_ix21, idx < 64) ∧ (∀ idx ∈ g6_ix21, g6_m21.getLsbD idx = true) ∧ projS 32 g6_ix21 goal6 = c5_5_goal ∧ g6_st21.all (fun w => rows5.contains (projS 32 g6_ix21 w)) = true := by decide +kernel

def g6_m22 : BitVec 64 := 0xff00ff00ff00ff

def g6_st22 : List (BitVec 64) := [0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]

def g6_ix22 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,32,33,34,35,36,37,38,39,48,49,50,51,52,53,54,55]

set_option maxRecDepth 100000 in

theorem g6_cspec_22 : g6_ix22.length = 32 ∧ (∀ idx ∈ g6_ix22, idx < 64) ∧ (∀ idx ∈ g6_ix22, g6_m22.getLsbD idx = true) ∧ projS 32 g6_ix22 goal6 = c5_5_goal ∧ g6_st22.all (fun w => rows5.contains (projS 32 g6_ix22 w)) = true := by decide +kernel

def g6_m23 : BitVec 64 := 0xff00ff00

def g6_st23 : List (BitVec 64) := [0xaa00aa00,0xcc00cc00,0xf000f000,0xff000000]

def g6_ix23 : List ℕ := [8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]

set_option maxRecDepth 100000 in

theorem g6_cspec_23 : g6_ix23.length = 16 ∧ (∀ idx ∈ g6_ix23, idx < 64) ∧ (∀ idx ∈ g6_ix23, g6_m23.getLsbD idx = true) ∧ projS 16 g6_ix23 goal6 = b4_4_goal ∧ g6_st23.all (fun w => rows4.contains (projS 16 g6_ix23 w)) = true := by decide +kernel

def g6_m24 : BitVec 64 := 0xf0f0f0f

def g6_st24 : List (BitVec 64) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]

def g6_ix24 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27]

set_option maxRecDepth 100000 in

theorem g6_cspec_24 : g6_ix24.length = 16 ∧ (∀ idx ∈ g6_ix24, idx < 64) ∧ (∀ idx ∈ g6_ix24, g6_m24.getLsbD idx = true) ∧ projS 16 g6_ix24 goal6 = b4_5_goal ∧ g6_st24.all (fun w => rows4.contains (projS 16 g6_ix24 w)) = true := by decide +kernel

def g6_m25 : BitVec 64 := 0x5555000055550000

def g6_st25 : List (BitVec 64) := [0x4444000044440000,0x5050000050500000,0x5500000055000000,0x5555000000000000]

def g6_ix25 : List ℕ := [16,18,20,22,24,26,28,30,48,50,52,54,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_25 : g6_ix25.length = 16 ∧ (∀ idx ∈ g6_ix25, idx < 64) ∧ (∀ idx ∈ g6_ix25, g6_m25.getLsbD idx = true) ∧ projS 16 g6_ix25 goal6 = b4_1_goal ∧ g6_st25.all (fun w => rows4.contains (projS 16 g6_ix25 w)) = true := by decide +kernel

def g6_cfMasks : Array (BitVec 64) := Array.mk [g6_m0,g6_m1,g6_m2,g6_m3,g6_m4,g6_m5,g6_m6,g6_m7,g6_m8,g6_m9,g6_m10,g6_m11,g6_m12,g6_m13,g6_m14,g6_m15,g6_m16,g6_m17,g6_m18,g6_m19,g6_m20,g6_m21,g6_m22,g6_m23,g6_m24,g6_m25]

def g6_cfB0s : Array ℕ := Array.mk [0,0,0,8,8,8,32,32,32,16,16,16,8,0,40,48,16,32,8,16,32,0,0,8,0,16]

def g6_cfStocks : Array (List (BitVec 64)) := Array.mk [g6_st0,g6_st1,g6_st2,g6_st3,g6_st4,g6_st5,g6_st6,g6_st7,g6_st8,g6_st9,g6_st10,g6_st11,g6_st12,g6_st13,g6_st14,g6_st15,g6_st16,g6_st17,g6_st18,g6_st19,g6_st20,g6_st21,g6_st22,g6_st23,g6_st24,g6_st25]

def g6_cfLBs : Array ℕ := Array.mk [8,8,6,8,6,5,8,5,5,8,6,5,5,8,5,5,5,5,5,5,5,6,6,5,5,5]

theorem g6_cof_sound (c fuel : ℕ) (hc : c < 26) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) (hnd : nxt.Nodup) (hchk : checkCofClose64 (g6_cfLBs[c]?.getD 0) fuel (g6_cfMasks[c]?.getD 0) (g6_cfB0s[c]?.getD 0) (g6_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose64_sound_aux goal6 8 g6_ix0 g6_cspec_0.1 g6_cspec_0.2.1 g6_m0 g6_cspec_0.2.2.1 0 g6_st0 c5_0_goal (by decide) g6_cspec_0.2.2.2.1 g6_cspec_0.2.2.2.2 c5_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose64_sound_aux goal6 8 g6_ix1 g6_cspec_1.1 g6_cspec_1.2.1 g6_m1 g6_cspec_1.2.2.1 0 g6_st1 c5_1_goal (by decide) g6_cspec_1.2.2.2.1 g6_cspec_1.2.2.2.2 c5_1_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose64_sound_aux goal6 6 g6_ix2 g6_cspec_2.1 g6_cspec_2.2.1 g6_m2 g6_cspec_2.2.2.1 0 g6_st2 c5_2_goal (by decide) g6_cspec_2.2.2.2.1 g6_cspec_2.2.2.2.2 c5_2_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose64_sound_aux goal6 8 g6_ix3 g6_cspec_3.1 g6_cspec_3.2.1 g6_m3 g6_cspec_3.2.2.1 8 g6_st3 c5_3_goal (by decide) g6_cspec_3.2.2.2.1 g6_cspec_3.2.2.2.2 c5_3_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose64_16_sound_aux goal6 6 g6_ix4 g6_cspec_4.1 g6_cspec_4.2.1 g6_m4 g6_cspec_4.2.2.1 8 g6_st4 b4_0_goal (by decide) g6_cspec_4.2.2.2.1 g6_cspec_4.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix5 g6_cspec_5.1 g6_cspec_5.2.1 g6_m5 g6_cspec_5.2.2.1 8 g6_st5 b4_1_goal (by decide) g6_cspec_5.2.2.2.1 g6_cspec_5.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 6 => exact checkCofClose64_sound_aux goal6 8 g6_ix6 g6_cspec_6.1 g6_cspec_6.2.1 g6_m6 g6_cspec_6.2.2.1 32 g6_st6 c5_4_goal (by decide) g6_cspec_6.2.2.2.1 g6_cspec_6.2.2.2.2 c5_4_no_build fuel hist nxt hnd hchk
  | 7 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix7 g6_cspec_7.1 g6_cspec_7.2.1 g6_m7 g6_cspec_7.2.2.1 32 g6_st7 b4_1_goal (by decide) g6_cspec_7.2.2.2.1 g6_cspec_7.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 8 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix8 g6_cspec_8.1 g6_cspec_8.2.1 g6_m8 g6_cspec_8.2.2.1 32 g6_st8 b4_1_goal (by decide) g6_cspec_8.2.2.2.1 g6_cspec_8.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 9 => exact checkCofClose64_sound_aux goal6 8 g6_ix9 g6_cspec_9.1 g6_cspec_9.2.1 g6_m9 g6_cspec_9.2.2.1 16 g6_st9 c5_3_goal (by decide) g6_cspec_9.2.2.2.1 g6_cspec_9.2.2.2.2 c5_3_no_build fuel hist nxt hnd hchk
  | 10 => exact checkCofClose64_16_sound_aux goal6 6 g6_ix10 g6_cspec_10.1 g6_cspec_10.2.1 g6_m10 g6_cspec_10.2.2.1 16 g6_st10 b4_0_goal (by decide) g6_cspec_10.2.2.2.1 g6_cspec_10.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 11 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix11 g6_cspec_11.1 g6_cspec_11.2.1 g6_m11 g6_cspec_11.2.2.1 16 g6_st11 b4_2_goal (by decide) g6_cspec_11.2.2.2.1 g6_cspec_11.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 12 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix12 g6_cspec_12.1 g6_cspec_12.2.1 g6_m12 g6_cspec_12.2.2.1 8 g6_st12 b4_2_goal (by decide) g6_cspec_12.2.2.2.1 g6_cspec_12.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 13 => exact checkCofClose64_sound_aux goal6 8 g6_ix13 g6_cspec_13.1 g6_cspec_13.2.1 g6_m13 g6_cspec_13.2.2.1 0 g6_st13 c5_1_goal (by decide) g6_cspec_13.2.2.2.1 g6_cspec_13.2.2.2.2 c5_1_no_build fuel hist nxt hnd hchk
  | 14 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix14 g6_cspec_14.1 g6_cspec_14.2.1 g6_m14 g6_cspec_14.2.2.1 40 g6_st14 b4_3_goal (by decide) g6_cspec_14.2.2.2.1 g6_cspec_14.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 15 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix15 g6_cspec_15.1 g6_cspec_15.2.1 g6_m15 g6_cspec_15.2.2.1 48 g6_st15 b4_3_goal (by decide) g6_cspec_15.2.2.2.1 g6_cspec_15.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 16 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix16 g6_cspec_16.1 g6_cspec_16.2.1 g6_m16 g6_cspec_16.2.2.1 16 g6_st16 b4_2_goal (by decide) g6_cspec_16.2.2.2.1 g6_cspec_16.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 17 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix17 g6_cspec_17.1 g6_cspec_17.2.1 g6_m17 g6_cspec_17.2.2.1 32 g6_st17 b4_2_goal (by decide) g6_cspec_17.2.2.2.1 g6_cspec_17.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 18 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix18 g6_cspec_18.1 g6_cspec_18.2.1 g6_m18 g6_cspec_18.2.2.1 8 g6_st18 b4_2_goal (by decide) g6_cspec_18.2.2.2.1 g6_cspec_18.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 19 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix19 g6_cspec_19.1 g6_cspec_19.2.1 g6_m19 g6_cspec_19.2.2.1 16 g6_st19 b4_4_goal (by decide) g6_cspec_19.2.2.2.1 g6_cspec_19.2.2.2.2 b4_4_no_build fuel hist nxt hnd hchk
  | 20 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix20 g6_cspec_20.1 g6_cspec_20.2.1 g6_m20 g6_cspec_20.2.2.1 32 g6_st20 b4_2_goal (by decide) g6_cspec_20.2.2.2.1 g6_cspec_20.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 21 => exact checkCofClose64_sound_aux goal6 6 g6_ix21 g6_cspec_21.1 g6_cspec_21.2.1 g6_m21 g6_cspec_21.2.2.1 0 g6_st21 c5_5_goal (by decide) g6_cspec_21.2.2.2.1 g6_cspec_21.2.2.2.2 c5_5_no_build fuel hist nxt hnd hchk
  | 22 => exact checkCofClose64_sound_aux goal6 6 g6_ix22 g6_cspec_22.1 g6_cspec_22.2.1 g6_m22 g6_cspec_22.2.2.1 0 g6_st22 c5_5_goal (by decide) g6_cspec_22.2.2.2.1 g6_cspec_22.2.2.2.2 c5_5_no_build fuel hist nxt hnd hchk
  | 23 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix23 g6_cspec_23.1 g6_cspec_23.2.1 g6_m23 g6_cspec_23.2.2.1 8 g6_st23 b4_4_goal (by decide) g6_cspec_23.2.2.2.1 g6_cspec_23.2.2.2.2 b4_4_no_build fuel hist nxt hnd hchk
  | 24 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix24 g6_cspec_24.1 g6_cspec_24.2.1 g6_m24 g6_cspec_24.2.2.1 0 g6_st24 b4_5_goal (by decide) g6_cspec_24.2.2.2.1 g6_cspec_24.2.2.2.2 b4_5_no_build fuel hist nxt hnd hchk
  | 25 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix25 g6_cspec_25.1 g6_cspec_25.2.1 g6_m25 g6_cspec_25.2.2.1 16 g6_st25 b4_1_goal (by decide) g6_cspec_25.2.2.2.1 g6_cspec_25.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | c + 26 => omega

def g6_L3 : Array W6Node := Array.mk [
([v6,v2,v10,v106],[],[],[])
]

def g6_L4 : Array W6Node := Array.mk [
([v6,v2,v10,v40,v32],[],[],[(0,0)]),
([v6,v2,v3,v106,v4],[],[],[(0,0)]),
([v0,v1,v2,v10,v106],[],[],[(0,0)])
]

def g6_L5 : Array W6Node := Array.mk [
([v6,v7,v48,v9,v3,v4],[(v47,v7,v4),(v48,v47,v5)],[0],[]),
([v55,v7,v9,v3,v4,v5],[],[0],[]),
([v6,v46,v7,v9,v3,v5],[(v49,v7,v5),(v46,v49,v4)],[0],[]),
([v6,v7,v3,v107,v4,v5],[],[1],[]),
([v60,v6,v9,v3,v4,v5],[],[],[]),
([v12,v11,v39,v3,v4,v5],[],[],[]),
([v11,v39,v2,v13,v4,v5],[],[],[]),
([v18,v11,v39,v2,v3,v5],[],[],[]),
([v11,v39,v2,v17,v3,v4],[],[],[]),
([v25,v11,v39,v2,v3,v4],[],[],[]),
([v18,v12,v39,v1,v3,v5],[],[],[]),
([v12,v11,v0,v22,v3,v5],[],[],[]),
([v18,v12,v11,v0,v3,v5],[],[],[]),
([v12,v11,v0,v17,v3,v4],[],[],[]),
([v25,v12,v11,v0,v3,v4],[],[],[]),
([v11,v0,v2,v13,v22,v5],[],[],[]),
([v18,v11,v0,v2,v13,v5],[],[],[]),
([v11,v0,v2,v13,v17,v4],[],[],[]),
([v25,v11,v0,v2,v13,v4],[],[],[]),
([v11,v0,v2,v13,v4,v5],[],[],[]),
([v11,v90,v2,v3,v4,v5],[],[],[]),
([v11,v0,v65,v3,v4,v5],[],[],[]),
([v11,v0,v2,v22,v17,v3],[],[],[]),
([v12,v0,v1,v13,v22,v5],[],[],[]),
([v18,v12,v0,v1,v13,v5],[],[],[]),
([v12,v0,v1,v13,v17,v4],[],[],[]),
([v25,v12,v0,v1,v13,v4],[],[],[]),
([v12,v0,v1,v13,v4,v5],[],[],[]),
([v18,v12,v0,v1,v17,v3],[],[],[]),
([v12,v0,v85,v3,v4,v5],[],[],[]),
([v12,v0,v91,v3,v4,v5],[],[],[]),
([v12,v0,v1,v71,v4,v5],[],[],[]),
([v12,v0,v1,v86,v3,v4],[],[],[]),
([v12,v0,v1,v17,v3,v4],[],[],[]),
([v12,v0,v92,v3,v4,v5],[],[],[]),
([v12,v0,v1,v93,v4,v5],[],[],[]),
([v0,v1,v2,v13,v22,v17],[],[],[]),
([v25,v0,v1,v2,v13,v22],[],[],[]),
([v0,v1,v2,v13,v22,v5],[],[],[]),
([v18,v0,v1,v2,v13,v17],[],[],[]),
([v25,v18,v0,v1,v2,v13],[],[],[]),
([v0,v85,v2,v13,v4,v5],[],[],[]),
([v0,v1,v65,v22,v3,v5],[],[],[]),
([v0,v1,v2,v3,0xfffe0100fffe0100,v5],[],[],[]),
([v0,v1,v2,v13,v86,v4],[],[],[]),
([v0,v1,v2,v13,v17,v4],[],[],[]),
([v0,v92,v2,v13,v4,v5],[],[],[]),
([v0,v1,v108,v13,v4,v5],[],[],[]),
([v0,v1,v2,v13,0xfefe0000ffff0000,v5],[],[],[]),
([v18,v61,v0,v1,v2,v17],[],[],[]),
([v25,v18,v61,v0,v1,v2],[],[],[]),
([v0,v1,v65,v17,v3,v4],[],[],[]),
([v0,v1,v2,v71,v17,v4],[],[],[]),
([v62,v0,v1,v3,v4,v5],[],[],[]),
([v12,v0,0xcfcccccccfcccccc,v3,v4,v5],[],[],[]),
([v12,v0,v1,v94,v3,v4],[],[],[]),
([v12,v0,0xcfcfcccccccccccc,v3,v4,v5],[],[],[]),
([v15,v0,v1,0xff0e0e0eff0e0e0e,v4,v5],[],[],[]),
([v16,0x1f1f1f1f0e0e0e0e,v0,v1,v3,v4],[],[],[]),
([v0,v1,0xe1e0e1e0e1e0e1e0,v3,v4,v5],[],[],[]),
([v0,v26,v51,v2,v37,v5],[],[],[]),
([v0,v51,v35,v2,v3,v32],[],[],[]),
([v0,v1,v26,v2,v72,v4],[],[],[]),
([v0,v1,v26,v2,0xffee0000eeee0000,v5],[],[],[]),
([v0,v1,v2,0xf1eef1eef1eef1ee,v4,v5],[],[],[]),
([v0,v1,v35,v2,0xff00ee00ee00ee00,v4],[],[],[]),
([v0,v1,v2,0xf1f1f1f1eeeeeeee,v3,v4],[],[],[]),
([v66,0x4545454544444444,v2,v3,v4,v5],[],[],[]),
([v56,0x5544444455444444,v2,v3,v4,v5],[],[],[]),
([0xffeeeeee,v0,v1,0xf0e0e0e0f0e0e0e0,v3,v4],[],[],[]),
([v62,v0,v1,v3,v72,v4],[],[],[]),
([0xffeeeeee,v62,v0,v1,v3,v4],[],[],[]),
([v79,v0,v1,v2,v14,v19],[],[],[]),
([v0,0xeee0e0e0eee0e0e0,v9,v3,v4,v5],[],[],[]),
([0xf0e0e0e0e0e0e0e,v0,v1,v3,v4,v5],[],[],[]),
([v0,v6,v2,v10,v14,v32],[(v10,v4,v3),(v14,v3,v5)],[1],[(0,0)]),
([v6,v2,v3,v40,v4,v32],[],[],[(0,0),(0,1)]),
([v12,v0,v1,v48,v3,v4],[],[],[]),
([v12,v0,v1,v46,v3,v5],[],[],[]),
([v0,v1,v2,v48,v13,v4],[],[],[]),
([v0,v1,v2,v46,v13,v5],[],[],[]),
([v11,v0,v2,v87,v4,v5],[],[],[]),
([0xa9a9a8a8a9a9a8a8,v1,v2,v3,v4,v5],[],[],[]),
([v0,0xababfcfcababfcfc,v1,v2,v3,v5],[],[],[]),
([v0,v1,v2,v10,0xff03fc00ff03fc00,v5],[(v10,v3,v4)],[2],[]),
([v0,v1,v2,v87,0xfefecccc00000000,v4],[],[],[]),
([v52,0x5550505055505050,v1,v3,v4,v5],[],[],[]),
([v0,v1,v2,v10,v40,v32],[],[],[(0,0),(0,2)]),
([v0,v1,v2,v3,v106,v4],[],[],[(0,1),(0,2)])
]

set_option maxRecDepth 100000 in

def g6_L6 : Array W6Node := Array.mk [
([v26,v6,v7,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v7,v0,v2),(v26,v6,v3)],[0,3],[]),
([v28,v6,v7,v9,v3,v4,v5],[(v9,v1,v2)],[0,3,4,5],[]),
([v35,v6,v7,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v7,v0,v2),(v35,v6,v5)],[0,6],[]),
([v41,v6,v7,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v7,v0,v2)],[0,6,7,8],[]),
([v6,v38,v7,v9,v3,v4,v5],[(v38,v7,v3)],[0],[]),
([v27,v6,v7,v9,v3,v4,v5],[(v7,v0,v2)],[0,1,9,10,11],[]),
([v6,v33,v7,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v7,v0,v2),(v33,v7,v4)],[0,9],[]),
([v30,v6,v7,v9,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v9,v1,v2)],[0,1,3,5,6,12],[(1,0)]),
([v6,v45,v7,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v7,v0,v2),(v45,v7,v5)],[0,6,13],[]),
([v36,v6,v7,v9,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v9,v1,v2),(v36,v9,v5)],[0,1,3,6,8,13],[(0,1),(1,2)]),
([v6,v7,v9,v10,v3,v4,v5],[(v10,v3,v4)],[0],[(0,3),(0,4),(1,3),(1,4)]),
([v6,v7,v9,v14,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v7,v0,v2),(v14,v3,v5)],[0,3,14],[]),
([v12,v11,v6,v7,v3,v4,v5],[(v6,v0,v1),(v11,v1,v7)],[0],[]),
([v0,v6,v65,v9,v3,v4,v5],[],[5],[]),
([v0,v6,0xf1f1f0f0f1f1f0f0,v9,v3,v4,v5],[],[10],[]),
([v0,v6,v108,v9,v3,v4,v5],[],[8],[]),
([v90,v6,v2,v9,v3,v4,v5],[],[5],[]),
([v0,v6,v2,v9,v95,v3,v4],[(v30,v9,v3),(v95,v30,v5)],[0],[(1,0)]),
([v109,v6,v2,v9,v3,v4,v5],[],[10],[]),
([v110,v6,v2,v9,v3,v4,v5],[],[8],[]),
([v0,v55,v2,v9,v3,v4,v5],[],[0],[(0,1)]),
([v0,v6,v2,0xfc00fc00ff00ff00,v9,v4,v5],[(v36,v9,v5),(0xfc00fc00ff00ff00,v36,v3)],[0],[(1,2)]),
([v6,v2,v7,v3,v37,v4,v5],[],[],[(0,3)]),
([v0,v6,v9,v3,v23,v4,v5],[],[],[(1,3)]),
([v0,v6,v2,v3,v107,v4,v5],[],[1],[(0,3)]),
([v60,v1,v6,v2,v3,v4,v5],[],[],[(0,4)]),
([v6,v2,v7,v3,v4,v32,v5],[(v6,v0,v1),(v7,v0,v2)],[15],[]),
([v0,v6,v9,v3,v88,v4,v5],[(v6,v1,v0),(v9,v1,v2)],[14],[]),
([v11,v39,v2,v3,v4,v5],[],[],[]),
([v11,v39,v2,v8,v3,v4,v5],[],[],[(0,5),(0,6),(0,7),(0,8),(0,9),(1,6),(1,7)]),
([v12,v11,v0,v3,v4,v5],[],[],[]),
([v12,v11,v0,v8,v3,v4,v5],[],[],[(0,5),(0,11),(0,12),(0,13),(0,14),(1,10)]),
([v11,v0,v2,v13,v4,v5],[],[],[]),
([v11,v0,v2,v13,v8,v4,v5],[(v6,v1,v0),(v8,v6,v2)],[3],[(0,6),(0,15),(0,16),(0,17),(0,18)]),
([v11,v0,v2,v13,v3,v4,v5],[],[],[]),
([v18,v39,v1,v2,v8,v3,v5],[(v6,v0,v1),(v8,v6,v2),(v18,v8,v4)],[3],[(0,7),(0,10),(1,19)]),
([v57,v11,v0,v2,v3,v4,v5],[],[3],[(0,19),(0,20),(0,21)]),
([v11,v0,v2,v22,v8,v3,v5],[(v6,v1,v0),(v8,v6,v2),(v22,v8,v4)],[3],[(0,11),(0,15),(0,22),(1,6)]),
([v18,v11,v0,v2,v8,v3,v5],[(v6,v1,v0),(v8,v6,v2),(v18,v8,v4)],[3],[(0,7),(0,12),(0,16)]),
([v11,v0,v2,v17,v8,v3,v4],[(v6,v1,v0),(v8,v6,v2),(v17,v8,v5)],[3],[(0,8),(0,13),(0,17),(0,22)]),
([v25,v11,v0,v2,v8,v3,v4],[(v6,v1,v0),(v8,v6,v2),(v25,v8,v5)],[3],[(0,9),(0,14),(0,18)]),
([v12,v0,v1,v13,v4,v5],[],[],[]),
([v12,v0,v1,v13,v8,v4,v5],[(v6,v0,v1),(v8,v6,v2)],[3],[(0,23),(0,24),(0,25),(0,26),(1,11)]),
([v12,v0,v1,v13,v3,v4,v5],[],[],[]),
([v18,v12,v0,v1,v8,v3,v5],[(v6,v1,v0),(v8,v6,v2),(v18,v8,v4)],[3],[(0,10),(0,12),(0,24),(0,28),(1,27)]),
([v57,v12,v0,v1,v3,v4,v5],[],[3],[(0,27),(0,30),(1,29),(1,31),(1,32)]),
([v12,v0,v1,v17,v3,v4],[],[],[]),
([v12,v0,v1,v17,v8,v3,v4],[(v6,v0,v1),(v8,v6,v2),(v17,v8,v5)],[3],[(0,13),(0,25),(0,28),(1,13),(1,25),(1,28)]),
([v12,v0,v1,v17,v3,v4,v5],[],[],[]),
([v25,v12,v0,v1,v8,v3,v4],[(v6,v0,v1),(v8,v6,v2),(v25,v8,v5)],[3],[(0,14),(0,26),(0,33),(1,14),(1,26)]),
([v73,v12,v0,v1,v3,v4,v5],[],[6],[(0,33),(0,34),(0,35),(1,34),(1,35)]),
([v0,v1,v2,v13,v22,v5],[],[],[]),
([v0,v1,v2,v13,v22,v8,v5],[(v6,v0,v1),(v8,v6,v2),(v13,v8,v3),(v22,v8,v4)],[3,9],[(0,15),(0,23),(0,36),(0,37),(1,15)]),
([v0,v1,v2,v13,v22,v3,v5],[],[],[]),
([v18,v0,v1,v2,v13,v8,v5],[(v6,v0,v1),(v8,v6,v2),(v18,v8,v4)],[3],[(0,16),(0,24),(0,38),(0,39),(0,40)]),
([v57,v0,v1,v2,v22,v3,v5],[(v6,v1,v0),(v8,v6,v2),(v22,v8,v4)],[6],[(0,38),(0,42),(0,43),(1,41),(1,44)]),
([v0,v1,v2,v13,v17,v4],[],[],[]),
([v0,v1,v2,v13,v17,v8,v4],[(v6,v0,v1),(v8,v6,v2),(v13,v8,v3),(v17,v8,v5)],[3,6],[(0,17),(0,25),(0,36),(0,39),(1,22)]),
([v0,v1,v2,v13,v17,v4,v5],[],[],[]),
([v25,v0,v1,v2,v13,v8,v4],[(v6,v0,v1),(v8,v6,v2),(v25,v8,v5)],[3],[(0,18),(0,26),(0,37),(0,40),(0,45)]),
([v73,v0,v1,v2,v13,v4,v5],[(v6,v0,v1),(v8,v6,v2),(v13,v8,v3)],[9,14],[(0,45),(0,46),(0,47),(0,48)]),
([v0,v1,v2,v13,v17,v3,v4],[],[],[]),
([v0,v1,v2,v13,v8,v4,v5],[],[3,16,17],[(0,19),(0,27),(0,38),(0,45)]),
([v18,v61,v0,v1,v2,v5],[],[],[]),
([v18,v61,v0,v1,v2,v8,v5],[],[16,18],[(0,49),(0,50)]),
([v18,v0,v1,v2,v17,v8,v3],[(v6,v1,v0),(v8,v6,v2),(v18,v8,v4)],[6],[(0,28),(0,39),(0,49),(1,45)]),
([v25,v18,v0,v1,v2,v8,v3],[],[19,20],[(0,40),(0,50)]),
([v0,v85,v2,v8,v3,v4,v5],[],[3,21],[(0,29),(0,41),(1,20)]),
([v0,v91,v2,v8,v3,v4,v5],[],[3,22],[(0,30)]),
([v0,v1,v65,v8,v3,v4,v5],[],[3,22],[(0,21),(0,42),(0,51)]),
([v0,v1,v2,v71,v8,v4,v5],[(v6,v1,v0),(v8,v6,v2),(v71,v74,v3)],[3,9,17,21],[(0,31),(0,52)]),
([v0,v1,v2,v8,v86,v3,v4],[(v6,v1,v0),(v8,v6,v2),(v86,v74,v5)],[6,9,21,23],[(0,32),(0,44)]),
([v57,v0,v1,v2,v17,v3,v4],[(v6,v0,v1),(v8,v6,v2),(v17,v8,v5)],[9,14],[(0,45),(0,51),(1,52)]),
([v0,v1,v2,v17,v8,v3,v4],[],[6,19,23],[(0,33),(0,45),(1,45)]),
([v0,v92,v2,v8,v3,v4,v5],[],[2,3],[(0,34),(0,46)]),
([v0,v1,v108,v8,v3,v4,v5],[],[2,3],[(0,47),(1,47)]),
([v0,v1,v2,v93,v8,v4,v5],[(v6,v0,v1),(v8,v6,v2),(v93,v73,v3)],[2,3,6,19],[(0,35),(1,48)]),
([v0,v1,v8,v3,v23,v4,v5],[(v23,v2,v10)],[21,22,23],[]),
([v0,v1,v2,v3,0xfffefefefffefefe,v4,v5],[],[2,3,6,9],[(0,53)]),
([0xfefefe00fefefe,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v8,v6,v2),(0xfefefe00fefefe,v8,v10)],[3],[]),
([v12,v11,v0,v6,v3,v4,v5],[],[],[]),
([v11,v0,v26,v2,v3,v4,v5],[],[],[]),
([v28,v11,v0,v2,v3,v4,v5],[],[3],[(0,21)]),
([v11,v39,v6,v2,v3,v4,v5],[(v6,v1,v0),(v11,v1,v8),(v39,v0,v8)],[0],[(0,5)]),
([v11,v0,v6,v2,v13,v4,v5],[(v6,v1,v0),(v11,v1,v8),(v13,v8,v3)],[0,3],[]),
([v18,v39,v1,v6,v2,v3,v5],[(v6,v0,v1),(v8,v6,v2),(v18,v8,v4)],[3],[(0,10)]),
([v11,v0,v6,v2,v22,v3,v5],[(v6,v1,v0),(v8,v6,v2),(v22,v8,v4)],[3],[(0,11)]),
([v18,v11,v0,v6,v2,v3,v5],[(v6,v1,v0),(v8,v6,v2),(v18,v8,v4)],[3],[(0,12)]),
([v11,v0,v6,v2,v17,v3,v4],[(v6,v1,v0),(v8,v6,v2),(v17,v8,v5)],[3],[(0,13)]),
([v25,v11,v0,v6,v2,v3,v4],[(v6,v1,v0),(v8,v6,v2),(v25,v8,v5)],[3],[(0,14)]),
([v12,v0,v1,v6,v13,v4,v5],[(v6,v0,v1),(v13,v8,v3)],[0],[]),
([v12,v0,v1,v6,v17,v3,v4],[(v6,v0,v1),(v17,v8,v5)],[0],[]),
([v0,v1,v26,v2,v22,v3,v5],[],[],[]),
([v0,v1,v26,v2,v17,v3,v4],[],[],[]),
([v28,v0,v1,v2,v22,v3,v5],[(v6,v0,v1),(v22,v8,v4)],[0],[(0,42)]),
([v28,v0,v1,v2,v17,v3,v4],[(v6,v0,v1),(v17,v8,v5)],[0],[(0,51)]),
([0x10101010fefefefe,v0,v1,v2,v3,v4,v5],[],[6],[]),
([v0,v1,v35,v2,v13,v4,v5],[],[],[]),
([v41,v0,v1,v2,v13,v4,v5],[(v6,v0,v1),(v13,v8,v3)],[0],[(0,47)]),
([v0,v1,v6,v2,v13,v22,v5],[(v6,v0,v1),(v13,v8,v3),(v22,v8,v4)],[0],[(0,23)]),
([v18,v0,v1,v6,v2,v13,v5],[(v6,v0,v1),(v13,v8,v3),(v18,v8,v4)],[0],[(0,24)]),
([v0,v1,v6,v2,v13,v17,v4],[(v6,v0,v1),(v13,v8,v3),(v17,v8,v5)],[0],[(0,25)]),
([v25,v0,v1,v6,v2,v13,v4],[(v6,v0,v1),(v13,v8,v3),(v25,v8,v5)],[0],[(0,26)]),
([v0,v1,v6,v2,v13,v4,v5],[(v6,v0,v1),(v61,v8,v3),(v13,v61,v8)],[0],[(0,27)]),
([v18,v61,v0,v1,v6,v2,v5],[],[],[]),
([v18,v0,v1,v6,v2,v17,v3],[(v6,v1,v0),(v18,v8,v4),(v17,v8,v5)],[0],[(0,28)]),
([v25,v18,v0,v1,v6,v2,v3],[],[],[]),
([v0,v85,v6,v2,v3,v4,v5],[],[3],[(0,29)]),
([v0,v91,v6,v2,v3,v4,v5],[],[3],[(0,30)]),
([v0,v1,v6,v2,v71,v4,v5],[(v6,v1,v0),(v74,v8,v4),(v71,v74,v3)],[0],[(0,31)]),
([v0,v1,v6,v2,v86,v3,v4],[(v6,v1,v0),(v74,v8,v4),(v86,v74,v5)],[0],[(0,32)]),
([v0,v1,v6,v2,v17,v3,v4],[(v6,v0,v1),(v25,v8,v5),(v17,v25,v8)],[0],[(0,33)]),
([v0,v92,v6,v2,v3,v4,v5],[],[3],[(0,34)]),
([v0,v1,v55,v2,v3,v4,v5],[],[6],[]),
([v0,v1,v6,v2,v93,v4,v5],[(v6,v0,v1),(v73,v8,v5),(v93,v73,v3)],[0],[(0,35)]),
([v12,v0,v1,v96,v3,v4,v5],[(v6,v0,v1),(v111,v12,v3)],[0,3],[]),
([v12,v15,v0,v1,0xf100f100f100f100,v4,v5],[],[3],[]),
([v12,v0,v1,0xfefefefef0f0f0f0,v3,v4,v5],[(v6,v0,v1),(v112,v12,v5)],[0,2,3],[]),
([v12,v16,v0,v1,0xf1f1f1f100000000,v3,v4],[],[6],[]),
([v12,v63,v0,v1,v3,v4,v5],[],[],[(0,53),(0,54),(0,55),(1,54)]),
([v12,v0,v1,v97,v3,v4,v5],[],[],[]),
([v12,v80,v0,v1,v3,v4,v5],[],[14],[(1,56)]),
([v12,v0,v1,v98,v3,v4,v5],[],[],[]),
([v12,v15,v0,v1,v10,v4,v5],[],[],[(0,57)]),
([v12,v15,v0,v1,v14,v4,v5],[],[14],[]),
([v12,v0,v1,v99,v3,v4,v5],[],[],[]),
([v12,v16,v0,v1,v14,v3,v4],[],[14],[]),
([v0,v1,v2,v3,0xff0e0e0eff0e0e0e,v4,v5],[],[2,3,6,9],[(0,53),(0,57),(1,57)]),
([0xe0e0e000e0e0e,v0,v1,v2,v3,v4,v5],[],[],[]),
([v0,v1,v68,v2,v3,v4,v5],[],[0],[]),
([v12,v15,v28,v0,v1,v4,v5],[],[12],[]),
([0x1f1f1f1f0e0e0e0e,v0,v1,v2,v3,v4,v5],[],[0,3,6,9,21,22],[(0,58)]),
([v12,v16,v41,v0,v1,v3,v4],[],[],[(0,58)]),
([v12,v0,v1,0xefeeefeeefeeefee,v3,v4,v5],[],[],[(0,59)]),
([v12,v0,v1,v55,v3,v4,v5],[],[24],[]),
([v79,v0,v1,v2,v3,v4,v5],[],[],[]),
([v0,v1,v6,0xfef0f0f0fef0f0f0,v3,v4,v5],[],[],[]),
([0x11ffffff00000000,v0,v1,v6,v2,v3,v4],[],[],[]),
([v0,v1,v26,v51,v2,v10,v5],[(v6,v0,v1)],[3,9],[(0,60),(1,60)]),
([v0,v1,v2,v3,0xff11ee00ff11ee00,v4,v5],[],[9],[]),
([v0,v1,v26,v35,v2,v14,v4],[(v6,v0,v1)],[3,6],[(1,61)]),
([v0,v51,v6,v2,v3,v37,v5],[(v6,v1,v0),(v51,v6,v4),(v37,v1,v10)],[3],[(0,60)]),
([v0,v26,v6,v2,v37,v4,v5],[(v6,v0,v1),(v26,v6,v3),(v37,v1,v10)],[9],[(0,60)]),
([v0,v1,v26,v2,v34,v4,v5],[(v6,v0,v1),(v26,v6,v3)],[0,3,18],[(0,62)]),
([v0,v51,v6,v2,v3,v32,v5],[(v6,v1,v0),(v51,v6,v4),(v32,v1,v19)],[6],[(0,61)]),
([v0,v1,v26,v2,v113,v4,v5],[(v6,v0,v1),(v26,v6,v3)],[0,3,23],[(0,63)]),
([v0,0xddccccccddcccccc,v6,v2,v3,v4,v5],[],[3,21,22],[]),
([v0,v1,v2,v3,v34,v4,v5],[],[0,2,3,6,9],[(0,53)]),
([v0,0xddddcccccccccccc,v6,v2,v3,v4,v5],[],[2,3,21],[]),
([v0,0xddccddcccccccccc,v6,v2,v3,v4,v5],[],[2,3,22],[]),
([v28,v0,v1,0xe0eee0eee0eee0ee,v2,v4,v5],[],[],[(0,64)]),
([v0,v35,v6,v2,v3,v4,v32],[(v6,v1,v0),(v35,v6,v5),(v32,v1,v19)],[9],[(0,61)]),
([v0,v1,v35,v2,v3,v113,v4],[(v6,v0,v1),(v35,v6,v5)],[0,6,17],[(1,65)]),
([v41,v0,v1,v68,v2,v3,v4],[],[],[(0,66)]),
([0x2323222223232222,v0,v6,v2,v3,v4,v5],[],[3],[]),
([0x2322232223222322,v0,v6,v2,v3,v4,v5],[],[3],[]),
([v0,0xcfcccccccfcccccc,v6,v2,v3,v4,v5],[],[1],[(0,54)]),
([v0,v1,0xefeeeeeeefeeeeee,v2,v3,v4,v5],[],[],[(0,53)]),
([v0,v1,0xe0eeeeeee0eeeeee,v2,v3,v4,v5],[],[],[]),
([v0,v1,v6,v2,v94,v3,v4],[(v63,v15,v4),(v94,v63,v5)],[0],[(0,55)]),
([v0,0xcfcfcccccccccccc,v6,v2,v3,v4,v5],[],[1],[(0,56)]),
([v0,v1,0xefeeefeeeeeeeeee,v2,v3,v4,v5],[],[14],[]),
([v0,v1,0xe0e0eeeeeeeeeeee,v2,v3,v4,v5],[],[],[]),
([v15,v1,v6,v2,v21,v4,v5],[(v15,v2,v3)],[21],[]),
([v15,v0,v6,v2,v37,v4,v5],[(v15,v2,v3)],[21],[]),
([v15,v0,v1,v2,v34,v4,v5],[(v15,v2,v3)],[0,2,3,12],[]),
([v15,v1,v6,v2,v40,v4,v5],[(v6,v0,v1),(v15,v2,v3),(v40,v0,v14)],[2,6],[]),
([v66,v0,v55,v2,v3,v4,v5],[],[3],[(0,67)]),
([v66,v0,v6,v2,v3,v4,v5],[],[3],[]),
([v0,v1,v68,v2,v14,v3,v4],[],[3],[]),
([v16,v0,v6,v2,v3,v4,v32],[(v16,v2,v5)],[21],[]),
([v56,v6,v2,v3,v21,v4,v5],[],[],[]),
([v52,v1,v6,v2,v3,v4,v5],[(v10,v3,v4),(v21,v0,v10),(v52,v2,v21)],[13],[]),
([v6,v2,v3,v21,v37,v4,v5],[],[1,13,21,22],[]),
([v56,v0,v2,v3,v34,v4,v5],[],[3],[(0,68)]),
([v0,v1,0xf0e0e0e0f0e0e0e0,v3,v34,v4,v5],[(v6,v0,v1),(v34,v6,v10),(0xf0e0e0e0f0e0e0e0,v2,v34)],[3,9,24],[(0,53),(0,69)]),
([v62,v0,v1,v3,v4,v5],[],[],[]),
([v62,v0,v1,v2,v3,v4,v5],[],[],[]),
([v62,v0,v1,v3,v34,v4,v5],[(v6,v0,v1),(v34,v6,v10),(v62,v2,v34)],[0,3,9],[(0,70),(0,71)]),
([v0,v1,v2,v3,v72,v34,v4],[(v6,v0,v1),(v34,v6,v10),(v72,v34,v5)],[3,6,9,24],[(0,70)]),
([0xffeeeeee,v0,v1,v2,v3,v34,v4],[(v6,v0,v1),(v34,v6,v10),(0xffeeeeee,v34,v5)],[2,3,9],[(0,69),(0,71)]),
([v56,v0,v6,v2,v3,v4,v5],[],[3],[]),
([v62,v0,v1,v6,v3,v4,v5],[],[],[]),
([v0,v1,v6,v2,v3,v72,v4],[(v6,v0,v1),(v34,v6,v10),(v72,v34,v5)],[3,9],[(0,62),(1,62)]),
([v62,v0,v1,v10,v3,v4,v5],[],[],[]),
([v0,v1,v2,0xf0fefefef0fefefe,v3,v4,v5],[],[2,3,6,9],[]),
([v79,v0,v1,v2,v14,v4,v5],[],[6],[(0,72)]),
([v0,v1,0xeee0e0e0eee0e0e0,v2,v3,v4,v5],[],[1,2,3,6,9,13,22],[(1,73)]),
([0x1110101011101010,v0,v1,v2,v3,v4,v5],[],[],[]),
([v0,v6,v2,v3,0xffcccccccccccccc,v4,v5],[],[1,2,21,22],[]),
([v0,v1,v2,v3,0xffeeeeeeeeeeeeee,v4,v5],[],[0,2,21,22],[(0,74)]),
([0xeeeeeeeeeeeeee,v0,v1,v2,v3,v4,v5],[],[],[]),
([v0,v6,v2,v10,v3,v32,v5],[(v10,v4,v3)],[1,2],[(0,75)]),
([v0,v1,v6,v2,v10,v14,v19],[(v6,v0,v1),(v14,v3,v5),(v19,v4,v5)],[3,14,15,21,22],[(0,72),(0,75),(1,75)]),
([v89,v1,v6,v2,v3,v4,v5],[(v14,v3,v5),(v40,v0,v14),(v89,v2,v40)],[13],[]),
([v0,v6,v2,v14,v3,v4,v32],[(v14,v3,v5)],[1,21],[(0,75),(0,76)]),
([v114,v0,v6,v2,v3,v4,v5],[],[3],[]),
([v100,v0,v6,v2,v3,v4,v5],[],[3],[]),
([0xf0e0f0e0e0e0e0e,v0,v1,v6,v3,v4,v5],[],[],[]),
([v0,v1,v6,v2,0xff00ee00ee00ee00,v4,v5],[(v6,v1,v0),(0xffffeeeeeeeeeeee,v6,v19),(0xff00ee00ee00ee00,0xffffeeeeeeeeeeee,v3)],[6,9],[(0,65),(1,63)]),
([v11,v39,v7,v9,v3,v4,v5],[(v7,v0,v2),(v39,v0,v9)],[0,13],[]),
([v0,v91,v7,v9,v3,v4,v5],[],[12],[]),
([v0,v85,v7,v9,v3,v4,v5],[],[11],[]),
([v0,v1,v7,v48,v9,v3,v4],[(v47,v7,v4),(v48,v47,v5)],[1,13],[(0,0)]),
([v0,v92,v7,v9,v3,v4,v5],[],[],[(0,1)]),
([v0,v75,v7,v9,v3,v4,v5],[],[],[(0,1)]),
([v0,v1,v46,v7,v9,v3,v5],[(v49,v7,v5),(v46,v49,v4)],[1,13],[(0,2)]),
([v0,v1,v7,v3,v107,v4,v5],[],[1],[(0,3)]),
([v60,v0,v1,v9,v3,v4,v5],[],[],[(0,4)]),
([v11,v39,v2,v7,v3,v4,v5],[],[],[]),
([v11,v0,v2,v53,v3,v4,v5],[],[],[]),
([v30,v11,v0,v2,v3,v4,v5],[],[3],[(0,20)]),
([v12,v11,v0,v9,v3,v4,v5],[(v9,v1,v2),(v11,v1,v8),(v12,v2,v8)],[1],[(0,5)]),
([v11,v0,v2,v9,v13,v4,v5],[(v9,v1,v2),(v11,v1,v8),(v13,v8,v3)],[1,3],[(0,6)]),
([v18,v39,v1,v2,v7,v3,v5],[(v8,v1,v7),(v18,v8,v4)],[0,3],[(0,7)]),
([v11,v0,v2,v9,v22,v3,v5],[(v9,v1,v2),(v8,v0,v9),(v22,v8,v4)],[3],[(1,6)]),
([v18,v11,v0,v2,v9,v3,v5],[(v9,v1,v2),(v8,v0,v9),(v18,v8,v4)],[3],[(0,7)]),
([v11,v0,v2,v9,v17,v3,v4],[(v9,v1,v2),(v8,v0,v9),(v17,v8,v5)],[3],[(0,8)]),
([v25,v11,v0,v2,v9,v3,v4],[(v9,v1,v2),(v8,v0,v9),(v25,v8,v5)],[3],[(0,9)]),
([v12,v11,v0,v7,v3,v4,v5],[],[],[]),
([v11,v0,v2,v7,v13,v4,v5],[(v7,v0,v2),(v8,v1,v7),(v11,v1,v7),(v13,v8,v3)],[0,13],[]),
([v12,v0,v1,v38,v3,v4,v5],[],[],[]),
([v27,v12,v0,v1,v3,v4,v5],[],[9],[(1,30)]),
([v12,v0,v1,v33,v3,v4,v5],[],[],[]),
([v30,v12,v0,v1,v3,v4,v5],[],[3],[(1,29),(1,77)]),
([v12,v0,v1,v45,v3,v4,v5],[],[],[]),
([v36,v12,v0,v1,v3,v4,v5],[],[6],[(1,34),(1,78)]),
([v12,v0,v1,v7,v13,v4,v5],[(v7,v0,v2),(v8,v1,v7),(v12,v2,v8),(v13,v8,v3)],[0,3,13],[]),
([v18,v12,v0,v1,v9,v3,v5],[(v9,v1,v2),(v8,v0,v9),(v18,v8,v4)],[3],[(0,10)]),
([v12,v0,v1,v7,v22,v3,v5],[(v7,v0,v2),(v8,v1,v7),(v12,v2,v8),(v22,v8,v4)],[0,3,13],[(0,11)]),
([v18,v12,v0,v1,v7,v3,v5],[(v8,v1,v7),(v18,v8,v4)],[0,3],[(0,12)]),
([v12,v0,v1,v7,v17,v3,v4],[(v7,v0,v2),(v8,v1,v7),(v12,v2,v8),(v17,v8,v5)],[0,3,13],[(0,13)]),
([v25,v12,v0,v1,v7,v3,v4],[(v8,v1,v7),(v25,v8,v5)],[0,3],[(0,14)]),
([v0,v1,v2,v38,v22,v3,v5],[],[],[]),
([v0,v1,v2,v38,v17,v3,v4],[],[],[]),
([v27,v0,v1,v2,v13,v4,v5],[],[],[]),
([v27,v0,v1,v2,v17,v3,v4],[],[],[]),
([v0,v1,v2,v33,v13,v4,v5],[],[],[]),
([v0,v1,v2,v33,v17,v3,v4],[],[],[]),
([v0,v1,v2,v48,v8,v3,v4],[(v7,v0,v2),(v47,v7,v4),(v48,v47,v5)],[3,8,9,21],[(0,77),(0,79)]),
([v30,v0,v1,v2,v22,v3,v5],[(v9,v1,v2),(v8,v0,v9),(v22,v8,v4)],[1,6],[(1,41),(1,79)]),
([v30,v0,v1,v2,v17,v3,v4],[(v9,v1,v2),(v17,v8,v5)],[1,14],[]),
([v0,v1,v2,v45,v13,v4,v5],[],[],[]),
([v0,v1,v2,v45,v22,v3,v5],[],[],[]),
([v0,v1,v2,v46,v8,v3,v5],[(v7,v0,v2),(v49,v7,v5),(v46,v49,v4)],[2,3,6,10],[(0,78),(0,80)]),
([v36,v0,v1,v2,v13,v4,v5],[(v9,v1,v2),(v13,v8,v3)],[1,14],[]),
([v36,v0,v1,v2,v22,v3,v5],[(v9,v1,v2),(v8,v0,v9),(v22,v8,v4)],[1,3],[(1,46),(1,80)]),
([v0,v1,v2,v7,v13,v22,v5],[(v7,v0,v2),(v8,v1,v7),(v13,v8,v3),(v22,v8,v4)],[0,13],[(0,15)]),
([v18,v0,v1,v2,v7,v13,v5],[(v7,v0,v2),(v8,v1,v7),(v13,v8,v3),(v18,v8,v4)],[0,13],[(0,16)]),
([v0,v1,v2,v7,v13,v17,v4],[(v7,v0,v2),(v8,v1,v7),(v13,v8,v3),(v17,v8,v5)],[0,13],[(0,17)]),
([v25,v0,v1,v2,v7,v13,v4],[(v7,v0,v2),(v8,v1,v7),(v13,v8,v3),(v25,v8,v5)],[0,13],[(0,18)]),
([v0,v1,v2,v7,v13,v4,v5],[(v7,v0,v2),(v8,v1,v7),(v61,v8,v3),(v13,v61,v8)],[0,13],[(0,19)]),
([v18,v0,v1,v2,v9,v13,v5],[],[],[]),
([v18,v61,v0,v1,v2,v7,v5],[(v8,v1,v7),(v61,v8,v3),(v18,v8,v4)],[0],[]),
([v18,v0,v1,v2,v9,v17,v3],[],[],[]),
([v25,v18,v0,v1,v2,v9,v3],[],[],[]),
([v0,v85,v2,v9,v3,v4,v5],[],[3],[(1,20)]),
([v0,v1,v65,v7,v3,v4,v5],[],[0,3],[(0,21)]),
([v0,v1,v2,v7,0xfeff0000feff0000,v3,v5],[(v8,v1,v7),(v57,v8,v3),(0xfeff0000feff0000,v57,v4)],[0],[]),
([v0,v1,v2,v7,v22,v17,v3],[(v7,v0,v2),(v8,v1,v7),(v22,v8,v4),(v17,v8,v5)],[0,13],[(0,22)]),
([v25,v0,v1,v2,v7,v22,v3],[(v8,v1,v7),(v22,v8,v4),(v25,v8,v5)],[0],[]),
([v0,v1,v2,v7,v22,v3,v5],[(v8,v1,v7),(v18,v8,v4),(v22,v18,v8)],[0],[]),
([v18,v0,v1,v2,v7,v17,v3],[(v8,v1,v7),(v18,v8,v4),(v17,v8,v5)],[0],[]),
([v25,v18,v0,v1,v2,v7,v3],[(v8,v1,v7),(v18,v8,v4),(v25,v8,v5)],[0],[]),
([v0,v91,v2,v9,v3,v4,v5],[],[3],[]),
([v0,v1,v65,v9,v3,v4,v5],[],[3],[]),
([v0,v1,v2,v7,v71,v4,v5],[(v8,v1,v7),(v74,v8,v4),(v71,v74,v3)],[0],[]),
([v11,v0,v2,v101,v3,v4,v5],[(v7,v0,v2),(v102,v11,v3)],[3,13,22],[]),
([v11,v24,v0,0xcd00cd00cd00cd00,v2,v4,v5],[],[3],[]),
([v11,v0,v2,v81,v3,v4,v5],[],[3,21],[(0,81)]),
([v11,0x3232ffff00000000,v0,v1,v2,v3,v4],[],[],[]),
([v11,v0,v2,0xfefefefecccccccc,v3,v4,v5],[],[2,3],[]),
([0x32320000ffff0000,v11,v0,v1,v2,v3,v5],[],[],[]),
([v0,v1,v2,v3,0xff323232ff323232,v4,v5],[],[3],[]),
([0x32323200323232,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v10,v3,v4),(0x32323200323232,v11,v10)],[9,13],[]),
([v11,v0,v1,v3,v23,v4,v5],[],[21],[]),
([v11,v0,v2,v115,v3,v4,v5],[(v11,v1,v7),(v24,v1,v3),(v115,v24,v7)],[0],[(1,82)]),
([v27,v39,v43,v1,v2,v3,v5],[],[25],[]),
([v11,v0,v1,v2,v48,v3,v4],[],[],[]),
([v11,v0,v1,v2,v46,v3,v5],[],[],[]),
([0x3131303031313030,v0,v2,v9,v3,v4,v5],[],[3],[]),
([0xb0a0b0a0b0a0b0a,v0,v1,v7,v3,v4,v5],[],[0,3],[]),
([v27,0xa8a8fcfca8a8fcfc,v0,v1,v2,v3,v5],[],[],[(0,83)]),
([v0,v1,v116,v7,v3,v4,v5],[],[1],[]),
([v0,v1,v2,0xfbfafafafbfafafa,v3,v4,v5],[],[],[]),
([0xa8fcfcfca8fcfcfc,v0,v1,v2,v3,v4,v5],[],[21],[]),
([v20,v0,v1,v7,v3,v23,v5],[],[21],[]),
([v20,v0,v1,v2,v3,v54,v5],[],[10],[]),
([0xb0b0b0b0a0a0a0a,v0,v1,v7,v3,v4,v5],[],[0,3],[]),
([v60,v0,v1,v2,v3,v4,v5],[],[9],[]),
([v0,v1,v2,v3,0xff05fa00ff05fa00,v4,v5],[],[],[]),
([v0,v1,v2,v38,v48,v3,v4],[],[],[]),
([v0,v1,v2,v38,v46,v3,v5],[],[],[]),
([v0,0xcfcccccccfcccccc,v2,v9,v3,v4,v5],[],[3,22],[]),
([v0,v1,v116,v9,v3,v4,v5],[],[3,22],[]),
([v0,v1,v2,v3,v54,v4,v5],[],[3],[]),
([v0,v1,v2,v3,0xff03fc00ff03fc00,v4,v5],[],[2,3,6,9],[(0,84)]),
([v27,v0,v1,v2,v53,v10,v5],[],[],[(0,84)]),
([v27,v0,v1,v2,v95,v3,v4],[],[],[]),
([v27,v0,v1,v2,0xfc00fc00ff00ff00,v4,v5],[],[],[]),
([v60,v117,v0,v1,v2,v4,v5],[(v117,v7,v3),(v10,v4,v3),(v60,v7,v10)],[0,18],[]),
([v0,v1,v2,v87,v81,v4,v5],[(v7,v0,v2),(v33,v7,v4),(v87,v81,v3)],[3,13,17],[(0,85)]),
([v0,v1,v2,0xfeaafeaa00000000,v118,v3,v4],[(v9,v1,v2),(v53,v9,v3),(0xfeaafeaa00000000,v118,v5)],[1,6,19],[(1,85)]),
([v0,v1,v2,v7,v87,v4,v5],[(v7,v0,v2),(v33,v7,v4),(v81,v1,v33),(v87,v81,v3)],[0,13],[(0,81)]),
([v0,v1,v33,v7,v3,v23,v5],[],[],[]),
([v0,v1,v2,v33,v3,v54,v5],[(v33,v7,v4),(v10,v3,v4),(v54,v7,v10)],[0,16],[]),
([v0,v1,v2,v33,v7,v3,0xffffffff05050000],[(v7,v0,v2),(v47,v7,v4),(0xffffffff05050000,v47,v5),(v33,v47,v4)],[0,9],[]),
([v66,v1,v2,v7,v3,v4,v5],[],[0],[]),
([v0,v1,v2,0xfac8c8c8fac8c8c8,v3,v4,v5],[(v7,v0,v2),(v10,v3,v4),(0xfac8c8c8fac8c8c8,v7,v37)],[1,3,9,13],[]),
([0x302020203020202,v0,v1,v2,v3,v4,v5],[],[],[]),
([v67,v0,v9,v3,v23,v4,v5],[],[],[]),
([v67,v0,v1,v7,v3,v4,v5],[],[1],[]),
([v0,v1,v7,v14,v23,v4,v5],[(v10,v3,v4),(v14,v3,v5)],[2,21,24],[]),
([v0,v1,v7,v3,v23,v19,v5],[(v10,v3,v4)],[2,21,24],[]),
([v67,v0,v2,v3,v107,v4,v5],[],[3],[(1,86)]),
([0x3332323233323232,v0,v1,v2,v3,v4,v5],[],[],[]),
([v52,v0,v1,v3,v54,v4,v5],[],[3],[(0,86)]),
([v67,v0,v2,v9,v3,v4,v5],[],[3],[]),
([v52,v0,v1,v7,v3,v4,v5],[],[0,3],[]),
([v0,0xaafefefeaafefefe,v1,v2,v3,v4,v5],[],[3,9],[]),
([v0,v1,v7,v10,v3,v82,v5],[(v10,v3,v4)],[1,24],[]),
([v0,v1,v2,0xfac8fac8c8c8c8c8,v3,v4,v5],[],[3,6],[]),
([0x303020202020202,v0,v1,v2,v3,v4,v5],[],[],[]),
([v89,v0,v1,v7,v3,v4,v5],[],[0,3],[]),
([v0,v1,v2,0xfafac8c8c8c8c8c8,v3,v4,v5],[],[1,6,9],[]),
([0x302030202020202,v0,v1,v2,v3,v4,v5],[],[],[]),
([v119,v0,v1,v9,v3,v4,v5],[],[3],[]),
([0xb0a0a0a0b0a0a0a,v0,v1,v2,v3,v4,v5],[],[],[]),
([0x3130303031303030,v0,v1,v2,v3,v4,v5],[],[],[]),
([v20,v58,v0,v1,v2,v23,v5],[],[],[]),
([v20,v0,v50,v1,v2,v10,v5],[],[10],[]),
([v15,v20,v0,v1,v2,v21,v5],[(v15,v2,v3),(v10,v3,v4)],[1],[]),
([v52,v20,v0,v1,v2,v3,v5],[],[],[]),
([v67,v58,v0,v1,v2,v4,v5],[],[],[]),
([v0,0xb0a0b0a0bbaabbaa,v1,v2,v3,v4,v5],[],[],[]),
([0xbbbbbb00aaaaaa,v0,v1,v2,v3,v4,v5],[],[9],[]),
([v0,v50,v1,v2,v37,v4,v5],[],[],[]),
([0x2322222223222222,v0,v1,v2,v3,v4,v5],[],[],[]),
([0x2322232222222222,v0,v1,v2,v3,v4,v5],[],[],[]),
([0x2323222222222222,v0,v1,v2,v3,v4,v5],[],[],[]),
([v15,v56,v0,v1,v2,v4,v5],[],[],[]),
([v0,v1,0xf0a0aaaaf0a0aaaa,v2,v3,v21,v5],[],[],[]),
([v15,0x5544444455444444,v0,v1,v2,v4,v5],[],[],[]),
([v15,v100,v0,v1,v2,v4,v5],[],[],[]),
([v15,0x5544554444444444,v0,v1,v2,v4,v5],[],[],[]),
([v66,v0,v75,v2,v3,v4,v5],[],[2,3],[(0,67)]),
([v0,v1,v2,v3,0xffafafafffaaaaaa,v4,v5],[],[0,3,9],[]),
([0xafafaf00aaaaaa,v0,v1,v2,v3,v4,v5],[],[],[]),
([v0,v31,v1,v3,v23,v4,v5],[(v23,v2,v10)],[23],[]),
([v0,v31,v1,v2,v3,v4,v32],[],[],[]),
([0x3303030333000000,v0,v1,v2,v3,v4,v5],[],[3],[]),
([v0,v1,0xf0a0a0a0ffaaaaaa,v2,v3,v4,v5],[],[],[]),
([v16,v100,v0,v1,v2,v3,v4],[],[],[]),
([v16,v114,v0,v1,v2,v3,v4],[],[],[]),
([v56,v0,v2,v3,v37,v4,v5],[],[3,22],[(0,68)]),
([v62,v0,v1,v3,v21,v4,v5],[(v10,v3,v4),(v34,v1,v21),(v62,v2,v34)],[1,3],[]),
([v0,v1,v2,v3,v21,v72,v4],[(v10,v3,v4),(v34,v1,v21),(v72,v34,v5)],[1,3],[]),
([v0,v1,v2,0xf3f2f2f2f3f2f2f2,v3,v4,v5],[],[],[]),
([v67,v0,v2,v3,v37,v4,v5],[],[3,21,22],[(1,86)]),
([v0,0xafaeaeaeafaeaeae,v1,v2,v3,v4,v5],[(v10,v4,v3),(v37,v1,v10),(0xf0c0c0c0f0c0c0c,v2,v37)],[1],[]),
([v52,v0,v1,v3,v23,v4,v5],[],[3,22],[(0,86)]),
([v0,0xbbbabababbbababa,v1,v2,v3,v4,v5],[],[],[]),
([v0,v1,v2,v3,v23,v32,v5],[(v10,v4,v3),(v23,v2,v10)],[9,13,23,24],[]),
([0x3322222222222222,v0,v1,v2,v3,v4,v5],[],[],[]),
([v89,v0,v1,v2,v10,v4,v5],[(v10,v3,v4)],[9,24],[]),
([v0,v1,v2,v10,v14,v32],[(v10,v4,v3),(v19,v4,v5),(v14,v3,v5)],[1,6,9,13,15,21,22,24],[(0,75),(0,87)]),
([v0,v1,v2,0xf3f2f3f2f2f2f2f2,v3,v4,v5],[],[],[]),
([v0,0xafafaeaeaeaeaeae,v1,v2,v3,v4,v5],[(v19,v4,v5),(v32,v1,v19),(0xf0f0c0c0c0c0c0c,v2,v32)],[1],[]),
([v0,v1,v2,v3,v40,v4,v32],[],[],[(0,76),(0,87),(0,88)]),
([v0,v1,v2,0xf3f3f2f2f2f2f2f2,v3,v4,v5],[],[],[]),
([v0,0xafaeafaeaeaeaeae,v1,v2,v3,v4,v5],[(v14,v3,v5),(v59,v1,v14),(v119,v2,v59)],[1],[])
]

set_option maxRecDepth 100000 in

def g6_L7 : Array W6Node := Array.mk [
([v6,v7,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v7,v0,v2)],[0,1,3,6,9,13],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(1,0),(1,1),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,11)]),
([v11,v6,v2,v7,v3,v4,v5],[(v6,v0,v1),(v7,v0,v2),(v11,v1,v7)],[0,1,3,13],[(0,12)]),
([v12,v0,v6,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v12,v6,v2)],[0,1,3,13],[(1,12)]),
([v0,v26,v6,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v26,v6,v3)],[0,3],[(0,0)]),
([v28,v0,v6,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v28,v6,v3)],[0,3,4,5],[(0,1),(0,13)]),
([v0,v51,v6,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v51,v6,v4)],[0,9],[(1,0)]),
([v28,v1,v6,v2,v7,v3,v4,v5],[(v6,v0,v1),(v28,v6,v3)],[0,3,4,5],[(0,1),(1,14)]),
([v0,v35,v6,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v35,v6,v5)],[0,6],[(0,2)]),
([v41,v0,v6,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2)],[0,6,7,8],[(0,3),(0,15)]),
([v0,v6,v2,v53,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v53,v9,v3)],[0,3],[(1,6)]),
([v30,v0,v6,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2)],[0,1,3,5,6,12],[(0,7),(0,16),(0,17)]),
([v0,v6,v2,v69,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v69,v9,v4)],[0,9],[(1,4)]),
([v27,v0,v6,v2,v9,v3,v4,v5],[(v9,v1,v2)],[0,1,9,10,11],[(0,5),(0,18)]),
([v0,v6,v2,v70,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v70,v9,v5)],[0,1,6],[(1,8)]),
([v36,v0,v6,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v36,v9,v5)],[0,1,3,6,8],[(0,9),(0,19),(0,20),(0,21)]),
([v0,v6,v2,v9,v10,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v10,v3,v4)],[0,1],[(0,10),(0,23),(0,24),(1,22),(1,25)]),
([v0,v6,v2,v9,v14,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2),(v14,v3,v5)],[0,1,3],[(0,11),(0,27),(1,26)]),
([v0,v6,v2,v9,v3,v19,v4,v5],[(v6,v1,v0),(v19,v4,v5)],[0,15],[(1,11)]),
([v11,v0,v2,v8,v3,v4,v5],[(v6,v1,v0),(v8,v6,v2),(v11,v1,v8)],[0,1,3],[(0,28),(0,29),(0,30),(0,31),(0,32),(0,33),(0,34),(0,36),(0,37),(0,38),(0,39),(0,40),(1,35)]),
([v12,v0,v1,v8,v3,v4,v5],[(v8,v6,v2),(v12,v2,v8)],[0,1,3,13],[(0,30),(0,31),(0,41),(0,42),(0,43),(0,44),(0,45),(0,46),(0,47),(0,48),(0,49),(0,50),(1,30),(1,31),(1,41),(1,42),(1,43),(1,44),(1,45)]),
([v0,v1,v2,v13,v4,v5],[(v6,v0,v1),(v8,v6,v2),(v13,v8,v3)],[0,1,3,6,9,13,16,22],[]),
([v0,v1,v2,v13,v8,v4,v5],[(v6,v0,v1),(v8,v6,v2),(v13,v8,v3)],[0,1,3,6,9,13,16,17],[(0,32),(0,33),(0,41),(0,42),(0,51),(0,52),(0,54),(0,56),(0,57),(0,58),(0,59),(0,60),(1,37),(1,53),(1,55)]),
([v0,v1,v2,v13,v8,v3,v4,v5],[(v6,v0,v1),(v8,v6,v2)],[3,16,17,22],[(0,34),(0,43),(0,53),(0,61)]),
([v18,v0,v1,v2,v8,v3,v5],[(v6,v1,v0),(v8,v6,v2),(v18,v8,v4)],[0,1,3,6,9,13,15,16,19,21],[(0,35),(0,38),(0,44),(0,54),(0,63),(0,64),(0,65),(0,66),(1,62)]),
([v57,v0,v1,v2,v8,v3,v4,v5],[(v6,v0,v1),(v8,v6,v2)],[3,6,9,16,17,22],[(0,36),(0,45),(0,55),(0,62),(0,68),(0,69),(0,72),(1,67),(1,70),(1,71)]),
([v0,v1,v2,v17,v3,v4],[(v6,v0,v1),(v8,v6,v2),(v17,v8,v5)],[0,1,2,3,6,9,13,23],[]),
([v0,v1,v2,v17,v8,v3,v4],[(v6,v0,v1),(v8,v6,v2),(v17,v8,v5)],[0,1,3,6,9,13,19,23],[(0,39),(0,46),(0,47),(0,56),(0,57),(0,61),(0,65),(0,72),(1,39),(1,56),(1,57),(1,61),(1,65),(1,72)]),
([v0,v1,v2,v17,v8,v3,v4,v5],[(v6,v0,v1),(v8,v6,v2)],[2,6,19,23],[(0,48),(0,58),(1,58)]),
([v25,v0,v1,v2,v8,v3,v4],[(v6,v0,v1),(v8,v6,v2),(v25,v8,v5)],[0,1,2,3,6,9,13,14,15,17,20],[(0,40),(0,49),(0,59),(0,66),(0,73),(1,40),(1,59),(1,66)]),
([v73,v0,v1,v2,v8,v3,v4,v5],[(v6,v0,v1),(v8,v6,v2)],[2,3,6,9,19,23],[(0,50),(0,60),(0,73),(0,74),(0,75),(0,76),(1,60),(1,74),(1,76)]),
([v0,v1,v2,v8,v10,v3,v4,v5],[(v6,v0,v1),(v10,v3,v4)],[0,3,6,9,21,22,23],[(0,77),(0,78),(0,79)]),
([v0,v1,v2,v8,v14,v3,v4,v5],[(v6,v0,v1),(v8,v6,v2),(v14,v3,v5)],[2,3,6,9,14,18,22],[]),
([v11,v0,v6,v2,v3,v4,v5],[(v6,v1,v0),(v8,v6,v2),(v11,v1,v8)],[0,3,13],[(0,30),(0,80),(0,81),(0,82)]),
([v11,v0,v6,v2,v8,v3,v4,v5],[(v6,v1,v0),(v11,v1,v8)],[0,3],[(0,31),(0,80),(0,83),(0,84),(0,86),(0,87),(0,88),(0,89),(1,85)]),
([v12,v0,v1,v6,v8,v3,v4,v5],[(v6,v0,v1)],[0,3],[(0,80),(0,90),(0,91),(1,80),(1,90)]),
([v0,v1,v26,v2,v8,v3,v4,v5],[(v6,v0,v1),(v26,v6,v3)],[0,3,6,9,12],[(0,81),(0,92),(0,93)]),
([v28,v0,v1,v2,v8,v3,v4,v5],[(v6,v0,v1),(v28,v6,v3)],[0,3,6,9,22],[(0,69),(0,82),(0,94),(0,95)]),
([v0,v1,v35,v2,v8,v3,v4,v5],[(v6,v0,v1),(v35,v6,v5)],[0,3,6,9],[(0,96),(0,97),(1,97)]),
([v41,v0,v1,v2,v8,v3,v4,v5],[(v6,v0,v1),(v41,v6,v5)],[0,2,3,6,9],[(0,75),(0,98),(1,98)]),
([v0,v1,v6,v2,v13,v4,v5],[(v6,v0,v1),(v8,v6,v2),(v13,v8,v3)],[0,1,3,6,9,13],[(0,41),(0,90),(0,97),(0,98),(1,92),(1,94)]),
([v0,v1,v6,v2,v13,v8,v4,v5],[(v6,v0,v1),(v13,v8,v3)],[0,3],[(0,42),(0,84),(0,90),(0,99),(0,100),(0,101),(0,102),(1,86)]),
([v0,v1,v6,v2,v13,v3,v4,v5],[(v6,v0,v1),(v8,v6,v2),(v13,v8,v3)],[0,3,22],[(0,43)]),
([v18,v0,v1,v6,v2,v8,v3,v5],[(v6,v1,v0),(v18,v8,v4)],[0],[(0,44),(0,85),(0,87),(0,100),(0,104),(0,105),(0,106),(1,103)]),
([v57,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v57,v8,v3)],[0,6,9,12],[(0,45),(0,103),(0,108),(1,107),(1,109),(1,110)]),
([v0,v1,v6,v2,v17,v3,v4],[(v6,v0,v1),(v8,v6,v2),(v17,v8,v5)],[0,1,3,6,9,13],[(0,46),(0,91),(0,93),(0,95),(1,93),(1,95)]),
([v0,v1,v6,v2,v17,v8,v3,v4],[(v6,v0,v1),(v17,v8,v5)],[0,6],[(0,47),(0,88),(0,91),(0,101),(0,105),(1,88),(1,101),(1,105)]),
([v0,v1,v6,v2,v17,v3,v4,v5],[(v6,v0,v1),(v8,v6,v2),(v17,v8,v5)],[0,2,6],[(0,48)]),
([v25,v0,v1,v6,v2,v8,v3,v4],[(v6,v0,v1),(v25,v8,v5)],[0],[(0,49),(0,89),(0,102),(0,106),(0,111),(1,89),(1,102),(1,106)]),
([v73,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v73,v8,v5)],[0,3,9],[(0,50),(0,111),(0,112),(0,113),(0,114),(1,112),(1,114)]),
([v111,v12,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2),(v111,v12,v3)],[0,3,22],[(0,115)]),
([v12,v0,v1,v2,0xf100f100f100f100,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2)],[3,22],[(0,45),(0,116)]),
([v112,v12,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2),(v112,v12,v5)],[0,2,6],[(0,117)]),
([v12,v0,v1,v2,0xf1f1f1f100000000,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2)],[2,6],[(0,50),(0,118)]),
([v12,v15,v0,v1,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2),(v15,v2,v3)],[0,1,3,13],[(0,45),(0,116),(0,119),(0,121),(0,123),(0,124),(1,120),(1,122)]),
([v12,v16,v0,v1,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2),(v16,v2,v5)],[0,1,6,13],[(0,50),(0,118),(0,121),(0,125),(0,126),(1,121),(1,125),(1,126)]),
([v12,v0,v1,v2,v10,v3,v4,v5],[(v6,v0,v1)],[0,3,9,21,22],[(0,119),(0,123),(0,127),(0,128),(1,123)]),
([v12,v0,v1,v2,v14,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2)],[0,2,3,6,14,22],[(0,121),(0,124),(0,126)]),
([v111,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2)],[3,12,22],[]),
([v0,v1,v6,v2,0xf100f100f100f100,v3,v4,v5],[(v12,v6,v2)],[0,3,4,5,22],[]),
([v112,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2)],[2,6],[(0,129)]),
([v0,v1,v6,v2,0xf1f1f1f100000000,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2)],[0,2,6,7,8],[]),
([v12,v0,v1,v26,v2,v3,v4,v5],[(v6,v0,v1),(v26,v6,v3)],[0,3,22],[(0,115)]),
([v12,v28,v0,v1,v2,v3,v4,v5],[(v6,v0,v1)],[0,3,12,22],[(0,45),(0,130)]),
([v12,v0,v1,v35,v2,v3,v4,v5],[(v6,v0,v1),(v35,v6,v5)],[0,2,6],[(0,117)]),
([v12,v41,v0,v1,v2,v3,v4,v5],[(v6,v0,v1)],[0,2,6],[(0,50),(0,131),(0,132)]),
([v12,v15,v0,v1,v6,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2)],[0,3],[(0,45),(0,130),(0,133)]),
([v12,v16,v0,v1,v6,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2)],[0,6],[(0,50),(0,132),(0,134)]),
([v0,v1,v2,v96,v3,v4,v5],[(v6,v0,v1),(v26,v6,v3),(v96,v26,v2)],[0,1,2,3,6,9,13,21,22],[]),
([v0,v1,v6,v2,v96,v3,v4,v5],[(v6,v0,v1),(v26,v6,v3),(v96,v26,v2)],[0,3,22],[(0,115)]),
([v28,v0,v1,v26,v6,v2,v4,v5],[],[3,4,5],[]),
([v0,v1,0xee000000ee000000,v6,v2,v3,v4,v5],[(v6,v0,v1)],[0,1,6,13],[(0,135),(0,136),(0,137)]),
([0x1100ff001100ff00,v0,v1,v6,v2,v3,v4,v5],[(v6,v1,v0),(v51,v6,v4)],[3,9,22],[]),
([v0,v1,0xee00ee0000000000,v6,v2,v3,v4,v5],[],[1,13,14],[]),
([0x1111ffff00000000,v0,v1,v6,v2,v3,v4,v5],[(v6,v1,v0),(v51,v6,v4)],[2,6,9],[]),
([v0,v1,v26,v51,v2,v3,v4,v5],[(v6,v0,v1)],[3,9,21,22],[(0,138)]),
([v28,v0,v1,v51,v2,v3,v4,v5],[(v6,v1,v0)],[9,21],[(1,139)]),
([v0,v1,v26,v35,v2,v3,v4,v5],[(v6,v0,v1)],[2,3,6,22],[(0,140)]),
([v41,v0,v1,v26,v2,v3,v4,v5],[(v6,v0,v1)],[3,14,22],[]),
([v0,v1,v26,v6,v2,v10,v4,v5],[(v6,v0,v1),(v26,v6,v3)],[3,9,22],[(0,138),(0,142),(0,143),(1,141)]),
([v0,v1,v26,v6,v2,v14,v4,v5],[(v6,v0,v1),(v26,v6,v3)],[3,6,22],[(0,140),(0,145),(1,144)]),
([v0,v1,v2,v65,v3,v4,v5],[(v28,v6,v3),(v65,v28,v2)],[0,1,2,3,6,9,13,16,17,21,22],[]),
([v0,v1,v6,v2,v65,v3,v4,v5],[(v6,v0,v1),(v28,v6,v3)],[0,3,4,5],[(0,13),(0,69),(1,14)]),
([0x1100000011000000,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v28,v6,v3),(0x1100000011000000,v28,v4)],[3,9,21,22],[(0,146),(0,147),(1,146)]),
([v0,v1,0xee00ff00ee00ff00,v6,v2,v3,v4,v5],[(v6,v1,v0),(v103,v6,v4),(0xee00ff00ee00ff00,v103,v3)],[3,9,21,22],[]),
([0x1100110000000000,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v28,v6,v3),(0x1100110000000000,v28,v5)],[2,3,6,14,22],[(0,149),(1,148)]),
([v0,v1,v6,0xeeeeffff00000000,v2,v3,v4,v5],[(v6,v1,v0),(v103,v6,v4),(0xeeeeffff00000000,v103,v5)],[2,6,9,21],[]),
([v28,v103,v0,v1,v2,v3,v4,v5],[(v6,v0,v1)],[3,9,21,22],[]),
([v28,v0,v1,v35,v2,v3,v4,v5],[(v6,v0,v1)],[2,6,14],[]),
([v28,v41,v0,v1,v2,v3,v4,v5],[(v6,v0,v1)],[2,3,6,22],[]),
([v15,v28,v0,v1,v6,v2,v4,v5],[(v6,v0,v1),(v28,v6,v3)],[0,3,4,5,22],[(0,130),(0,150)]),
([v0,v1,v6,v2,0xfefefefef0f0f0f0,v3,v4,v5],[(v6,v0,v1),(v35,v6,v5),(0xfefefefef0f0f0f0,v35,v2)],[0,2,6],[(0,117)]),
([0x11001100ff00ff00,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v35,v6,v5)],[3,6,22],[]),
([v41,v0,v1,v35,v6,v2,v3,v4],[],[3,6,7,8],[]),
([v0,v1,v35,v6,v2,v14,v3,v4],[(v6,v0,v1),(v35,v6,v5)],[2,3,6],[(0,140),(0,152),(1,151)]),
([v0,v1,v6,v2,v108,v3,v4,v5],[(v6,v0,v1),(v41,v6,v5)],[0,6,7,8],[(0,15),(0,75),(1,15)]),
([v0,v1,0xee00ee00ff00ff00,v6,v2,v3,v4,v5],[(v6,v0,v1),(v41,v6,v5),(0xee00ee00ff00ff00,v41,v3)],[2,3,6,22],[]),
([v16,v41,v0,v1,v6,v2,v3,v4],[(v6,v0,v1),(v41,v6,v5)],[0,2,6,7,8],[(0,132),(0,153)]),
([v0,v1,v6,0xefeeefeeefeeefee,v2,v3,v4,v5],[(v6,v0,v1),(0xefeeefeeefeeefee,v15,v6)],[0,3,22],[(0,133),(0,155),(1,154)]),
([v0,v1,0xe0e0eeeee0e0eeee,v6,v2,v3,v4,v5],[(v6,v1,v0),(0xe0e0eeeee0e0eeee,v44,v6)],[0,9,21],[(1,150)]),
([v63,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v63,v15,v4)],[0,1,6,13,22],[(0,119),(0,156),(0,157),(0,158),(0,159),(1,156)]),
([v0,v1,v6,v97,v2,v3,v4,v5],[(v97,v44,v3)],[0,3,18,22],[(0,120)]),
([v80,v0,v1,v6,v2,v3,v4,v5],[(v80,v15,v5)],[0,1,22],[(0,121),(0,161),(1,160),(1,162)]),
([v0,v1,v6,v2,v98,v3,v4,v5],[(v98,v44,v5)],[0,2,6,20],[(0,122)]),
([v15,v0,v1,v6,v2,v10,v4,v5],[(v6,v0,v1),(v15,v2,v3)],[0,9,12,21,22],[(0,123),(0,163),(0,164),(0,165)]),
([v15,v0,v1,v6,v2,v14,v4,v5],[(v6,v0,v1),(v15,v2,v3)],[0,2,6,12,14,22],[(0,124),(0,166)]),
([v0,v1,v55,v2,v3,v4,v5],[(v6,v0,v1),(v16,v2,v5),(v55,v16,v6)],[0,1,3,6,9,13,21,22],[(0,167),(1,167)]),
([v16,v0,v1,v55,v2,v3,v4,v5],[(v6,v0,v1),(v55,v16,v6)],[0,6],[(0,129)]),
([v0,v1,v6,v55,v2,v3,v4,v5],[(v6,v0,v1),(v55,v16,v6)],[0,2,6],[(0,134),(0,168),(1,168)]),
([v0,v1,v68,v2,v3,v4,v5],[(v6,v0,v1),(v16,v2,v5),(v68,v16,v6)],[0,1,3,6,9,13,21,22],[(0,169),(1,169)]),
([v16,v0,v1,v68,v2,v3,v4,v5],[(v6,v0,v1),(v68,v16,v6)],[0,6],[(0,113)]),
([v0,v1,v68,v6,v2,v3,v4,v5],[(v6,v0,v1),(v68,v16,v6)],[0,2,6],[(0,153)]),
([v0,v1,v6,v99,v2,v3,v4,v5],[(v99,v16,v3)],[0,3,22,23],[(0,125)]),
([v16,v0,v1,v6,v2,v14,v3,v4],[(v6,v0,v1),(v16,v2,v5),(v14,v3,v5)],[0,2,3,14,22],[(0,126),(0,169),(1,170)]),
([v0,v6,v2,v3,v37,v4,v5],[(v6,v1,v0),(v10,v4,v3),(v37,v1,v10)],[1,3,9,13,21,22],[(0,22),(0,24),(0,141),(0,142),(0,164),(1,163),(1,171),(1,172)]),
([v0,v6,v2,v10,v3,v37,v4,v5],[(v10,v4,v3),(v37,v1,v10)],[1,13,21,22],[(0,173)]),
([v0,v1,v2,v3,v34,v4,v5],[(v6,v0,v1),(v10,v3,v4),(v34,v6,v10)],[0,1,2,3,6,9,13],[(0,78),(0,165),(0,174),(0,175),(0,176),(0,177),(0,178),(0,179),(0,180),(1,165),(1,174)]),
([v0,v1,v6,v2,v3,v34,v4,v5],[(v6,v0,v1),(v34,v6,v10)],[0,3,6,9,22],[(0,143),(0,181),(0,182),(0,183),(1,143),(1,181)]),
([v0,v1,v2,v10,v3,v34,v4,v5],[(v10,v3,v4)],[0,3,6,9,23],[(0,135),(0,184)]),
([v79,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v10,v3,v4),(v79,v6,v10)],[0,1,2,3,6,9,13],[(0,128),(0,185),(0,186),(1,186)]),
([v79,v0,v1,v6,v2,v3,v4,v5],[],[1,13,22],[]),
([v79,v0,v1,v2,v10,v3,v4,v5],[],[3,9],[(0,147)]),
([v0,v1,v6,v2,v3,v23,v4,v5],[(v10,v3,v4)],[0,1,13],[(0,23),(0,24),(0,77),(0,78),(0,128),(0,187),(0,188),(1,23),(1,24)]),
([v0,v1,v6,v2,v104,v3,v4,v5],[(v10,v3,v4),(v104,v10,v5)],[1,2,3,6,9,13,21,22],[(0,189),(0,190),(0,191),(1,189)]),
([v120,v0,v1,v6,v2,v3,v4,v5],[(v120,v10,v5)],[2,3,6,9,17,21,22],[]),
([v0,v1,v6,v2,v10,v14,v4,v5],[(v6,v0,v1),(v10,v3,v4),(v14,v3,v5)],[2,6,9,14,21,22],[(0,186),(0,193),(1,192)]),
([v0,v6,v2,v3,v4,v32,v5],[(v6,v1,v0),(v19,v4,v5),(v32,v1,v19)],[1,2,6,9,13,15,21],[(0,26),(0,144),(0,151),(0,170),(0,192),(0,195),(1,166),(1,194)]),
([v0,v1,v6,v2,v3,v113,v4,v5],[(v6,v0,v1),(v113,v6,v14)],[0,3,6,9,22],[(0,145),(0,152),(0,197),(0,198),(1,196),(1,199)]),
([0xeeeeeeeeeeee,v0,v1,v6,v2,v3,v4,v5],[],[1,13,21],[]),
([v0,v1,v6,v2,v3,v88,v4,v5],[(v6,v0,v1)],[1,14,24],[(0,27)]),
([v83,v0,v1,v6,v2,v3,v4,v5],[(v83,v19,v3)],[2,6,9,21,22,23],[]),
([v0,v1,v6,v2,v14,v3,v19,v4],[(v6,v0,v1),(v14,v3,v5),(v19,v4,v5)],[3,9,14,15,21,22],[(0,193),(0,195),(1,195)]),
([v11,v0,v7,v9,v3,v4,v5],[(v9,v1,v2),(v7,v0,v2),(v11,v1,v7)],[0,1,3,13],[(0,200)]),
([v0,v1,v38,v7,v9,v3,v4,v5],[(v7,v0,v2),(v38,v7,v3)],[1,13],[(0,4)]),
([v27,v0,v1,v7,v9,v3,v4,v5],[(v9,v1,v2),(v7,v0,v2),(v27,v9,v4)],[1,9,10,11,13],[(0,5),(1,201)]),
([v0,v1,v33,v7,v9,v3,v4,v5],[(v7,v0,v2),(v9,v1,v2),(v33,v7,v4)],[1,9,13],[(0,6)]),
([v30,v0,v1,v7,v9,v3,v4,v5],[(v9,v1,v2),(v7,v0,v2),(v30,v9,v3)],[1,3,5,6,12,13],[(0,7),(1,202),(1,203)]),
([v0,v1,v45,v7,v9,v3,v4,v5],[(v7,v0,v2),(v9,v1,v2),(v45,v7,v5)],[1,6,13],[(0,8)]),
([v36,v0,v1,v7,v9,v3,v4,v5],[(v9,v1,v2),(v7,v0,v2),(v36,v9,v5)],[1,3,6,8,13],[(0,9),(0,205),(1,204),(1,206)]),
([v0,v1,v7,v9,v10,v3,v4,v5],[(v10,v3,v4)],[1,13],[(0,10),(0,207),(0,208),(1,207),(1,208)]),
([v0,v1,v7,v9,v14,v3,v4,v5],[(v7,v0,v2),(v9,v1,v2),(v14,v3,v5)],[1,3,13,14],[(0,11)]),
([v11,v0,v2,v9,v3,v4,v5],[(v9,v1,v2),(v8,v0,v9),(v11,v1,v8)],[0,1,3,13],[(0,28),(0,210),(0,211),(1,209)]),
([v11,v0,v2,v9,v8,v3,v4,v5],[(v9,v1,v2),(v11,v1,v8)],[1,3],[(0,29),(0,212),(0,213),(0,215),(0,216),(0,217),(0,218),(1,209),(1,214)]),
([v11,v0,v2,v7,v8,v3,v4,v5],[(v7,v0,v2),(v8,v1,v7),(v11,v1,v7)],[0,3,13],[(0,209),(0,219),(0,220)]),
([v12,v0,v1,v7,v3,v4,v5],[(v7,v0,v2),(v8,v1,v7),(v12,v2,v8)],[0,3,13],[(0,30),(0,219),(0,221),(0,223),(0,225),(1,222),(1,224),(1,226)]),
([v12,v0,v1,v7,v8,v3,v4,v5],[(v7,v0,v2),(v8,v1,v7),(v12,v2,v8)],[0,3,13],[(0,31),(0,219),(0,227),(0,229),(0,230),(0,231),(0,232),(1,212),(1,228)]),
([v0,v1,v2,v38,v8,v3,v4,v5],[(v7,v0,v2),(v38,v7,v3)],[3,5,6,9,13],[(0,221),(0,233),(0,234)]),
([v27,v0,v1,v2,v8,v3,v4,v5],[(v9,v1,v2),(v27,v9,v4)],[1,3,6,9,21],[(0,222),(0,235),(0,236),(1,68)]),
([v0,v1,v2,v33,v8,v3,v4,v5],[(v7,v0,v2),(v33,v7,v4)],[3,6,9,10,13],[(0,223),(0,237),(0,238),(1,210)]),
([v30,v0,v1,v2,v8,v3,v4,v5],[(v9,v1,v2),(v8,v0,v9),(v30,v9,v3)],[1,3,6,9,22],[(0,211),(0,224),(0,240),(0,241),(1,67),(1,239)]),
([v0,v1,v2,v45,v8,v3,v4,v5],[(v7,v0,v2),(v45,v7,v5)],[3,6,8,9,13],[(0,225),(0,242),(0,243)]),
([v36,v0,v1,v2,v8,v3,v4,v5],[(v9,v1,v2),(v8,v0,v9),(v36,v9,v5)],[1,2,3,6,9],[(0,226),(0,245),(0,246),(1,74),(1,244)]),
([v0,v1,v2,v7,v13,v4,v5],[(v7,v0,v2),(v8,v1,v7),(v13,v8,v3)],[0,1,3,6,9,13],[(0,32),(0,220),(0,237),(0,242),(1,240),(1,246)]),
([v0,v1,v2,v7,v13,v8,v4,v5],[(v7,v0,v2),(v8,v1,v7),(v13,v8,v3)],[0,3,13],[(0,33),(0,220),(0,227),(0,247),(0,248),(0,249),(0,250),(1,215)]),
([v0,v1,v2,v7,v13,v3,v4,v5],[(v7,v0,v2),(v8,v1,v7),(v13,v8,v3)],[0,3,13,22],[(0,34)]),
([v18,v0,v1,v2,v9,v8,v3,v5],[(v9,v1,v2),(v18,v8,v4)],[1],[(0,35),(0,216),(0,228),(0,252),(0,254),(0,255),(1,251),(1,253)]),
([v57,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v8,v1,v7),(v57,v8,v3)],[0,5,6,9,13,24],[(0,36),(0,251),(0,257),(0,258),(1,256)]),
([v0,v1,v2,v7,v22,v3,v5],[(v7,v0,v2),(v8,v1,v7),(v22,v8,v4)],[0,1,3,6,9,13],[(0,233),(0,243),(1,235),(1,245)]),
([v0,v1,v2,v7,v22,v8,v3,v5],[(v7,v0,v2),(v8,v1,v7),(v22,v8,v4)],[0,9,13],[(0,37),(0,229),(0,247),(0,259),(0,260),(1,213),(1,252)]),
([v0,v1,v2,v7,v22,v3,v4,v5],[(v7,v0,v2),(v8,v1,v7),(v22,v8,v4)],[0,9,13,21],[]),
([v18,v0,v1,v2,v7,v8,v3,v5],[(v7,v0,v2),(v8,v1,v7),(v18,v8,v4)],[0,13],[(0,38),(0,214),(0,230),(0,248),(0,253),(0,261),(0,262),(0,263)]),
([v57,v0,v1,v2,v9,v3,v4,v5],[(v9,v1,v2)],[4,6,9,24],[(0,264),(0,265),(1,261),(1,266)]),
([v0,v1,v2,v7,v17,v3,v4],[(v7,v0,v2),(v8,v1,v7),(v17,v8,v5)],[0,1,3,6,9,13],[(0,234),(0,238),(1,236),(1,241)]),
([v0,v1,v2,v7,v17,v8,v3,v4],[(v7,v0,v2),(v8,v1,v7),(v17,v8,v5)],[0,6,13],[(0,39),(0,231),(0,249),(0,259),(0,262),(1,217),(1,254)]),
([v25,v0,v1,v2,v7,v8,v3,v4],[(v7,v0,v2),(v8,v1,v7),(v25,v8,v5)],[0,13,24],[(0,40),(0,232),(0,250),(0,260),(0,263),(1,218),(1,255)]),
([v102,v11,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7),(v102,v11,v3)],[3,13,22],[(0,267)]),
([v11,v0,v1,0xcd00cd00cd00cd00,v2,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7)],[3,22],[(0,36),(0,268)]),
([0x3232000032320000,v11,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7)],[9,21],[(0,269)]),
([v11,v0,v1,0xcdcd0000cdcd0000,v2,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7)],[6,9,21],[(0,270)]),
([0x3232323200000000,v11,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7)],[2,6],[(0,271)]),
([v11,v0,v1,0xcdcdcdcd00000000,v2,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7)],[2,6,9],[(0,272)]),
([v11,v24,v0,v2,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7),(v24,v1,v3)],[0,1,3,13],[(0,36),(0,268)]),
([v11,v0,v1,v2,v10,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7),(v10,v3,v4)],[0,3,9,13,21,22],[(0,273),(0,274),(0,275)]),
([v11,v0,v1,v2,v14,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7)],[2,3,6,14,22],[]),
([v11,v0,v1,v2,v3,v19,v4,v5],[],[2,6,15,21],[]),
([v102,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7),(v102,v11,v3)],[0,3,5,22],[]),
([v0,0xabab0000abab0000,v1,v2,v9,v3,v4,v5],[(v39,v0,v9)],[0,1,9,10,11,13,21],[]),
([0x3232000032320000,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7),(0x3232000032320000,v11,v4)],[0,9,10,21],[]),
([v0,0xab00ab00ab00ab00,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v39,v0,v9)],[0,1,3,5,6,12,13,22,24],[]),
([v11,v24,v0,v2,v7,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7),(v24,v1,v3)],[0,3,13],[(0,36),(0,276),(1,277)]),
([v11,v0,v1,v2,v38,v3,v4,v5],[(v7,v0,v2),(v38,v7,v3)],[3,13,22],[(0,267)]),
([v27,v39,v0,v1,v2,v3,v4,v5],[(v9,v1,v2)],[1,9,21,25],[(0,277),(1,36)]),
([v11,v0,v1,v2,v33,v3,v4,v5],[(v7,v0,v2)],[9,13,21],[(0,269)]),
([v30,v39,v0,v1,v2,v3,v4,v5],[(v9,v1,v2),(v39,v0,v9)],[3,4,6,22],[(1,278)]),
([v11,v0,v1,v2,v45,v3,v4,v5],[(v7,v0,v2)],[2,6,13],[(0,271)]),
([v36,v39,v0,v1,v2,v3,v4,v5],[(v9,v1,v2),(v39,v0,v9)],[2,3,6,7],[(1,279)]),
([v0,v1,v2,v7,v115,v3,v4,v5],[(v7,v0,v2),(v24,v1,v3),(v115,v24,v7)],[0,3,13,22],[(0,276),(0,281),(1,280)]),
([0xa8a8fcfca8a8fcfc,v0,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(0xa8a8fcfca8a8fcfc,v43,v9)],[1,9,21],[(0,282)]),
([v76,v0,v1,v2,v7,v3,v4,v5],[(v24,v1,v3),(v76,v24,v4)],[0,3,22],[(0,283),(0,284),(1,285)]),
([v121,v0,v1,v2,v9,v3,v4,v5],[(v121,v43,v3)],[3,9,18,21,22],[]),
([v27,v43,v0,v1,v2,v9,v3,v5],[(v9,v1,v2),(v27,v9,v4)],[1,9,10,11,21],[(0,277),(0,282)]),
([v30,v58,v0,v1,v2,v9,v4,v5],[(v9,v1,v2),(v58,v0,v3)],[1,3,4,5,6,12,22],[]),
([v20,v0,v1,v2,v7,v10,v3,v5],[(v7,v0,v2),(v20,v1,v4),(v10,v3,v4)],[0,3,10,13,21,22],[(0,286),(0,287)]),
([v0,v1,v2,v7,0xfbfbfbfbfafafafa,v3,v4,v5],[],[0,2,24],[(0,288)]),
([0xa8a8a8a8fcfcfcfc,v0,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(0xa8a8a8a8fcfcfcfc,v42,v9)],[1,2,6,24],[]),
([0xaaaa0000ffff0000,v0,v1,v2,v9,v3,v4,v5],[],[9,19,21],[]),
([v122,v0,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v42,v0,v5),(v122,v42,v3)],[2,3,6,22,23],[]),
([v0,v1,v2,v101,v3,v4,v5],[(v7,v0,v2),(v38,v7,v3),(v101,v1,v38)],[0,1,2,3,6,9,13,21,22],[]),
([v0,v1,v2,v7,v101,v3,v4,v5],[(v7,v0,v2),(v38,v7,v3),(v101,v1,v38)],[0,3,13,22],[(0,267)]),
([v27,v0,v1,v2,v69,v9,v3,v5],[],[3,9,10,11],[]),
([v0,v1,v2,0xfa000000fa000000,v7,v3,v4,v5],[(v7,v0,v2),(v38,v7,v3),(0xfa000000fa000000,v38,v4)],[0,1,3,22],[(0,289)]),
([0x300ff000300ff00,v0,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v69,v9,v4),(0x300ff000300ff00,v69,v3)],[3,9,21,22],[]),
([v0,v1,v2,v38,v33,v3,v4,v5],[(v7,v0,v2)],[3,9,21,22],[]),
([v30,v0,v1,v2,v69,v3,v4,v5],[(v9,v1,v2),(v69,v9,v4)],[6],[(1,290),(1,291)]),
([v0,v1,v2,v38,v45,v3,v4,v5],[(v7,v0,v2)],[2,3,6,22],[]),
([v36,v0,v1,v2,v69,v3,v4,v5],[(v9,v1,v2),(v69,v9,v4)],[3,15],[(1,292)]),
([v0,v109,v1,v2,v3,v4,v5],[(v27,v9,v4),(v109,v27,v0)],[0,1,2,3,6,9,13,21,22],[]),
([v0,v109,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v27,v9,v4)],[0,1,9,10,11,13],[(0,18),(1,68),(1,201)]),
([0x300000003000000,v0,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v27,v9,v4)],[3,6,22,24],[(0,293),(0,294),(1,295)]),
([v0,v1,v2,v7,0xfaff0000faff0000,v3,v4,v5],[(v7,v0,v2),(v117,v7,v3),(0xfaff0000faff0000,v117,v4)],[0,3,9,21],[]),
([v27,v0,v1,v2,v53,v3,v4,v5],[(v9,v1,v2)],[3,9,21,22],[(0,296),(0,297)]),
([v30,v27,v0,v1,v2,v3,v4,v5],[(v9,v1,v2),(v27,v9,v4)],[3,6,9,21,22],[(0,298)]),
([v27,v0,v1,v2,v70,v3,v4,v5],[(v9,v1,v2)],[2,6,15],[]),
([v27,v36,v0,v1,v2,v3,v4,v5],[(v9,v1,v2),(v27,v9,v4)],[2,3,6,9,21],[(0,299)]),
([v27,v0,v1,v2,v9,v10,v3,v5],[(v9,v1,v2),(v27,v9,v4)],[3,9,10,11,21],[(0,297),(1,300)]),
([v0,v1,v2,v118,v3,v4,v5],[(v9,v1,v2),(v53,v9,v3),(v118,v0,v53)],[0,1,2,3,6,9,13,16,17,21,22],[(0,302),(1,301)]),
([v0,v1,v2,v7,v81,v3,v4,v5],[(v7,v0,v2),(v33,v7,v4),(v81,v1,v33)],[0,3,6,9,13,21,24],[(0,269),(0,303)]),
([0x3ff000003ff0000,v0,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v53,v9,v3)],[3,9,21],[]),
([v30,v0,v1,v2,v53,v9,v4,v5],[(v9,v1,v2),(v53,v9,v3)],[3,5,6,12],[]),
([v0,v1,v2,v33,v45,v3,v4,v5],[(v7,v0,v2),(v33,v7,v4)],[2,6,9,21],[]),
([v36,v0,v1,v2,v53,v3,v4,v5],[(v9,v1,v2),(v53,v9,v3)],[2,3,6,14],[]),
([v0,v1,v2,v33,v7,v10,v3,v5],[(v7,v0,v2),(v33,v7,v4),(v10,v3,v4)],[0,3,9,21],[(0,304),(0,305),(1,297)]),
([v0,v90,v1,v2,v3,v4,v5],[(v30,v9,v3),(v90,v30,v0)],[0,1,2,3,6,9,13,16,21,22],[]),
([v0,v1,v2,v48,v3,v4],[(v7,v0,v2),(v47,v7,v4),(v48,v47,v5)],[0,1,2,3,6,9,13,23],[]),
([v0,v90,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v30,v9,v3)],[0,1,3,5,12,13],[(0,16),(1,67),(1,202)]),
([v0,v1,v2,0xfa00ff00fa00ff00,v7,v3,v4,v5],[(v7,v0,v2),(v47,v7,v4),(0xfa00ff00fa00ff00,v47,v3)],[0,3,9,21,22],[]),
([v30,v0,v1,v2,v9,v3,v4,0xffffffff03000300],[(v9,v1,v2),(0xffffffff03000300,v30,v5)],[3,5,12,22,24],[(1,306)]),
([v0,v1,v2,v7,v48,v3,v4],[(v7,v0,v2),(v47,v7,v4),(v48,v47,v5)],[0,1,3,6,9,13],[(0,203),(0,239),(0,278),(0,291),(1,17),(1,298)]),
([v30,v0,v1,v2,v9,v95,v3,v4],[(v9,v1,v2),(v95,v30,v5)],[3,5,6,12,22],[]),
([v30,v0,v1,v2,v70,v3,v4,v5],[(v9,v1,v2)],[3,6,14],[]),
([v30,v36,v0,v1,v2,v3,v4,v5],[(v9,v1,v2)],[2,3,6,22],[]),
([v0,v1,v2,0xfefefefeaaaaaaaa,v3,v4,v5],[(v9,v1,v2),(v70,v9,v5),(0xfefefefeaaaaaaaa,v0,v70)],[0,1,2,3,6,9,13,21,22],[]),
([v0,v1,v2,v7,0xfefefefecccccccc,v3,v4,v5],[(v7,v0,v2),(v45,v7,v5),(0xfefefefecccccccc,v1,v45)],[0,2,6,13],[(0,271)]),
([0x3030000ffff0000,v0,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v70,v9,v5)],[6,9,21],[]),
([0x3000300ff00ff00,v0,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v70,v9,v5),(0x3000300ff00ff00,v70,v3)],[2,3,6,22],[]),
([v0,v110,v1,v2,v3,v4,v5],[(v36,v9,v5),(v110,v36,v0)],[0,1,2,3,6,9,13,19,21,22],[]),
([v0,v1,v2,v46,v3,v5],[(v49,v7,v5),(v46,v49,v4)],[0,1,3,6,9,13,21,23],[]),
([v0,v110,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v36,v9,v5)],[0,1,6,8,13],[(0,19),(0,20),(1,74),(1,204)]),
([v0,v75,v2,v9,v3,v4,v5],[(v9,v1,v2),(v36,v9,v5),(v75,v36,v1)],[0,2,3,6,13,24],[(0,20),(0,205),(1,307)]),
([v0,v1,v2,v46,v7,v3,v5],[(v7,v0,v2),(v49,v7,v5),(v46,v49,v4)],[0,1,3,6,9,13],[(0,206),(0,244),(0,279),(0,292),(1,21),(1,299)]),
([v0,v1,v2,v46,v7,v3,v4,v5],[(v7,v0,v2),(v49,v7,v5),(v46,v49,v4)],[0,6,9,21],[]),
([v0,v1,v2,0xfa00fa00ff00ff00,v7,v3,v4,v5],[(v7,v0,v2),(v49,v7,v5),(0xfa00fa00ff00ff00,v49,v3)],[0,2,3,6,22],[]),
([v0,v1,v2,v7,v3,v37,v4,v5],[(v7,v0,v2),(v10,v3,v4),(v37,v1,v10)],[0,3,9,13,22],[(0,22),(0,78),(0,207),(0,274),(0,308),(1,309)]),
([v0,v1,v7,v3,v23,v4,v5],[(v7,v0,v2),(v10,v3,v4),(v23,v2,v10)],[0,1,3,9,21,22,23],[(0,77),(0,207),(0,275),(0,286),(0,304),(0,311),(0,312),(0,313),(1,23),(1,310)]),
([v0,v1,v7,v10,v3,v23,v4,v5],[(v10,v3,v4)],[0,1,21,22],[]),
([v0,v1,v2,v3,v54,v4,v5],[(v7,v0,v2),(v10,v3,v4),(v54,v7,v10)],[0,1,2,3,6,9,13],[(0,78),(0,287),(0,315),(0,316),(1,24),(1,207),(1,314)]),
([v0,v1,v2,v7,v3,v54,v4,v5],[(v7,v0,v2),(v10,v3,v4),(v54,v7,v10)],[0,3,9,22],[(0,305),(0,318),(1,317)]),
([v0,v1,v2,v10,v3,v54,v4,v5],[],[3,9],[(0,289)]),
([v60,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v10,v3,v4),(v60,v7,v10)],[0,1,2,3,6,9,13],[(0,25),(0,208),(0,274),(1,319)]),
([v60,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v10,v3,v4),(v60,v7,v10)],[0,1,3,9,22],[(0,300)]),
([v60,v0,v1,v2,v10,v3,v4,v5],[],[3,9],[(0,295)]),
([v0,v1,v2,v7,v10,v14,v4,v5],[(v7,v0,v2),(v10,v3,v4),(v14,v3,v5)],[0,2,6,9,14,21,22,24],[(0,312)]),
([v0,v1,v2,v7,v10,v3,v19,v5],[(v7,v0,v2),(v10,v3,v4),(v19,v4,v5)],[0,2,3,6,15,21,22,24],[(0,313),(0,320)]),
([v0,v1,v2,v7,v3,v59,v4,v5],[(v14,v3,v5),(v59,v1,v14)],[0,14],[(0,321),(1,322)]),
([v0,v1,v2,v7,v3,0xfffafffafafafafa,v4,v5],[(v7,v0,v2),(0xfffafffafafafafa,v7,v14)],[0,3,6,22,24],[(0,323)]),
([0xfcfcfcfcfcfc,v0,v1,v2,v9,v3,v4,v5],[],[21],[]),
([v83,v0,v1,v2,v9,v3,v4,v5],[],[3,22,23],[]),
([v0,v1,v2,v7,v3,v4,v32,v5],[(v7,v0,v2),(v19,v4,v5),(v32,v1,v19)],[0,2,6,9,13,15],[(0,26),(0,324),(1,325)]),
([v0,v1,v7,v3,v4,v82,v5],[(v7,v0,v2),(v19,v4,v5),(v82,v2,v19)],[0,1,6,9,15,21,24],[(0,320),(1,27)]),
([v0,v1,v2,v7,v3,v4,0xfffffafafafafafa,v5],[],[0,21,24],[(1,326)]),
([0xfafafafafafa,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(0xfafafafafafa,v7,v19)],[0,1,6,9,21,24],[]),
([v83,v0,v1,v2,v7,v3,v4,v5],[(v19,v4,v5),(v83,v3,v19)],[0,22,23],[]),
([v0,0xbbaaaaaabbaaaaaa,v1,v2,v3,v4,v5],[(v20,v1,v4),(v76,v20,v3),(0xbbaaaaaabbaaaaaa,v76,v0)],[0,1,2,3,6,9,13,21,22],[(0,284),(0,327)]),
([v0,v1,v2,v116,v3,v4,v5],[(v20,v1,v4),(v76,v20,v3),(v116,v76,v2)],[0,1,2,3,6,9,13,17,22],[(0,283),(0,284),(1,328)]),
([v0,0xbbbbaaaaaaaaaaaa,v1,v2,v3,v4,v5],[(v123,v20,v5),(0xbbbbaaaaaaaaaaaa,v123,v0)],[0,1,2,3,6,9,13,21,22,24],[]),
([v20,v58,v0,v1,v2,v10,v5],[(v20,v1,v4),(v58,v0,v3)],[1,3,4,6,9,10,13,21,22],[(0,329)]),
([v20,v0,v1,v2,v84,v3,v5],[(v20,v1,v4),(v84,v43,v2)],[0,1,6,9,13,21,22],[]),
([v20,v0,v1,v2,v124,v3,v4,v5],[(v20,v1,v4),(v42,v0,v5),(v124,v42,v2)],[2,6,9,10,21],[]),
([v20,v0,v50,v1,v2,v3,v4,v5],[(v15,v2,v3),(v50,v15,v0)],[3,9,10,21,22],[(0,330)]),
([v15,v20,v0,v1,v2,v10,v5],[(v20,v1,v4),(v15,v2,v3)],[0,1,3,9,10,13,19,21,22],[(0,330),(0,331)]),
([v20,v0,v64,v1,v2,v3,v5],[(v20,v1,v4),(v64,v44,v0)],[0,1,6,9,13,21,22],[]),
([v20,v0,v31,v1,v2,v3,v4,v5],[(v20,v1,v4),(v16,v2,v5),(v31,v16,v0)],[2,6,9,10,21],[]),
([v20,v0,v1,v2,v3,v21,v5],[(v20,v1,v4),(v21,v0,v10)],[1,3,6,9,10,13,21,22],[(0,287),(0,331),(0,332)]),
([v20,v0,v1,v2,v3,v23,v5],[(v20,v1,v4),(v10,v3,v4),(v23,v2,v10)],[0,3,6,9,10,13,20,21,22],[(0,286),(0,287),(0,329),(1,333)]),
([v20,v0,v1,v2,v3,v40,v4,v5],[(v20,v1,v4),(v14,v3,v5),(v40,v0,v14)],[1,2,3,6,9,10,20,21],[]),
([v20,v0,v1,v2,v3,v88,v4,v5],[(v20,v1,v4),(v14,v3,v5),(v88,v2,v14)],[2,6,9,10,20,21],[]),
([0xb0a0b0a0b0a0b0a,v0,v1,v2,v3,v4,v5],[(v24,v1,v3),(0xb0a0b0a0b0a0b0a,v77,v2)],[0,1,2,3,5,6,9,13,21],[]),
([v15,v0,v77,v1,v2,v4,v5],[(v77,v24,v0),(v15,v2,v3)],[0,1,2,3,13,21,22],[]),
([v15,v0,v1,0xddddccccddddcccc,v2,v3,v4,v5],[(v43,v0,v4),(0xddddccccddddcccc,v43,v1)],[3,12,22,25],[]),
([v16,v0,v77,v1,v2,v3,v4,v5],[(v24,v1,v3),(v77,v24,v0)],[2,5,6],[(0,334)]),
([v0,v77,v1,v2,v3,v19,v4,v5],[],[2,6,15,21],[]),
([0x3131303031313030,v0,v1,v2,v3,v4,v5],[(v43,v0,v4),(0x3131303031313030,v1,v84)],[0,1,2,3,6,9,13,22,25],[]),
([v24,v0,v1,v2,v84,v3,v4,v5],[(v43,v0,v4),(v84,v43,v2)],[3,5,22,25],[]),
([v29,v0,v1,v2,v84,v3,v4,v5],[(v43,v0,v4),(v84,v43,v2)],[2,6,8,25],[]),
([v0,v1,v2,0xf3f0f3f0f3f0f3f0,v3,v19,v4,v5],[],[2,6,15,21],[]),
([v0,0xbbaabbaaaaaaaaaa,v1,v2,v3,v4,v5],[(v125,v24,v5),(0xbbaabbaaaaaaaaaa,v125,v0)],[0,1,2,3,6,9,13,21,22,24],[]),
([v24,v0,v1,v2,v124,v3,v4,v5],[(v42,v0,v5),(v124,v42,v2)],[3,7,22,24],[]),
([v24,v0,v50,v1,v2,v4,v5],[(v24,v1,v3),(v50,v15,v0)],[0,1,3,13,16,22],[]),
([v24,v0,v64,v1,v2,v3,v4,v5],[(v44,v2,v4),(v64,v44,v0)],[3,5,22],[]),
([v24,v0,v31,v1,v2,v3,v4,v5],[(v16,v2,v5),(v31,v16,v0)],[3,5,22],[]),
([v24,v0,v1,v2,v3,v4,v105,v5],[(v19,v4,v5),(v105,v0,v19)],[2,3,5,6,15,22],[]),
([v24,v0,v1,v2,v3,v4,v82,v5],[(v19,v4,v5),(v82,v2,v19)],[3,15,22,24],[]),
([0xb0b0b0b0a0a0a0a,v0,v1,v2,v3,v4,v5],[(v29,v1,v5),(0xb0b0b0b0a0a0a0a,v78,v2)],[0,1,3,6,8,9,13,21,22],[]),
([v15,v0,v78,v1,v2,v3,v4,v5],[(v29,v1,v5),(v78,v29,v0)],[3,8,12,22],[]),
([v15,v0,v1,0xddddddddcccccccc,v2,v3,v4,v5],[(v42,v0,v5),(0xddddddddcccccccc,v42,v1)],[3,7,12,22],[]),
([v16,v0,v78,v1,v2,v3,v4],[(v78,v29,v0),(v16,v2,v5)],[0,1,2,6,13,21,22],[]),
([v0,v78,v1,v2,v10,v3,v4,v5],[],[2,3,6,8,9,21,22],[(0,335)]),
([v0,v1,v2,0xf3f3f3f3f0f0f0f0,v10,v3,v4,v5],[(v10,v3,v4)],[3,8,9,21,22,24],[]),
([v29,v0,v50,v1,v2,v3,v4,v5],[(v15,v2,v3),(v50,v15,v0)],[2,6,8],[]),
([v29,v0,v64,v1,v2,v3,v4,v5],[(v44,v2,v4),(v64,v44,v0)],[2,6,8],[]),
([v29,v0,v31,v1,v2,v3,v4],[(v29,v1,v5),(v31,v16,v0)],[0,1,2,6,9,13,19,22],[]),
([v29,v0,v1,v2,v3,v21,v4,v5],[(v29,v1,v5),(v10,v3,v4),(v21,v0,v10)],[1,2,3,6,8,22],[]),
([v29,v0,v1,v2,v3,v23,v4,v5],[(v10,v3,v4),(v23,v2,v10)],[0,2,6,8,9,21,23,24],[]),
([v29,v0,v1,v2,v3,v40,v4],[(v14,v3,v5),(v40,v0,v14)],[1,2,3,6,9,13,14,19,22,24],[]),
([0x2322232223222322,v0,v1,v2,v3,v4,v5],[(v15,v2,v3),(0x2322232223222322,v50,v1)],[0,1,2,3,6,9,12,13,21],[]),
([v0,v50,v1,v2,v10,v4,v5],[(v15,v2,v3),(v50,v15,v0),(v10,v3,v4)],[0,1,2,3,9,12,13,17,22],[(0,330),(0,336)]),
([v0,v50,v1,v2,v3,v19,v4,v5],[],[2,6,9,15,17,21],[]),
([0x2323222223232222,v0,v1,v2,v3,v4,v5],[(v44,v2,v4),(0x2323222223232222,v64,v1)],[0,1,2,3,6,9,11,13,22],[]),
([v0,v64,v1,v2,v14,v3,v4,v5],[(v44,v2,v4),(v64,v44,v0)],[2,3,6,14,22],[]),
([v0,0xafaaaaaaafaaaaaa,v1,v2,v3,v4,v5],[(v15,v2,v3),(v63,v15,v4),(0xafaaaaaaafaaaaaa,v63,v0)],[0,1,2,3,6,9,13,21,22],[(0,157),(0,337),(1,156)]),
([v0,v1,v2,v94,v3,v4],[(v15,v2,v3),(v63,v15,v4),(v94,v63,v5)],[0,1,2,3,6,9,13],[(0,159)]),
([v0,0xafaaafaaaaaaaaaa,v1,v2,v3,v4,v5],[(v15,v2,v3),(v80,v15,v5),(0xafaaafaaaaaaaaaa,v80,v0)],[0,1,2,3,6,9,13,19,21,22],[(0,161),(0,338),(1,160)]),
([v0,0xafafaaaaaaaaaaaa,v1,v2,v3,v4,v5],[(v44,v2,v4),(0xf0f000000000000,v44,v5),(0xafafaaaaaaaaaaaa,0xf0f000000000000,v0)],[0,1,3,6,9,13,21,22],[(0,339),(1,161)]),
([v15,v0,v1,v2,v21,v4,v5],[(v15,v2,v3),(v10,v3,v4),(v21,v0,v10)],[0,1,2,3,9,22],[(0,163),(0,165),(0,331),(0,340)]),
([v15,v0,v1,v2,v37,v4,v5],[(v15,v2,v3),(v10,v3,v4),(v37,v1,v10)],[0,2,3,9,13,22],[(0,164),(0,165),(0,336),(0,342),(1,341)]),
([v15,v0,v1,v2,v40,v4,v5],[(v15,v2,v3),(v14,v3,v5)],[0,1,3,6,14,16,21,22,24],[(0,166),(0,343)]),
([v15,v0,v1,v2,v59,v4,v5],[(v15,v2,v3),(v14,v3,v5),(v59,v1,v14)],[0,3,6,13,14,21,22],[(0,344)]),
([v15,v0,v1,v2,v3,v4,v105,v5],[(v19,v4,v5),(v105,v0,v19)],[3,12,15,22],[]),
([v15,v0,v1,v2,v3,v4,v32,v5],[(v32,v1,v19)],[2,3,6,9,12,13,15,17,21,22,24],[]),
([v0,v31,v1,v55,v2,v3,v4,v5],[(v16,v2,v5),(v31,v16,v0)],[0,6,13],[(0,167),(1,345)]),
([v66,v0,v1,v2,v3,v4,v5],[(v16,v2,v5),(v31,v16,v0),(v66,v31,v1)],[0,1,3,6,9,13,21,22],[(0,167)]),
([v66,v0,v31,v1,v2,v3,v4,v5],[(v16,v2,v5),(v31,v16,v0)],[13],[(0,167)]),
([v0,0xaf00af00aa00aa00,v31,v1,v2,v3,v4,v5],[(v16,v2,v5),(v31,v16,v0)],[2,3,6,22],[]),
([0x3030000033330000,v0,v1,v75,v2,v3,v4,v5],[],[9,19,21],[]),
([v0,0xafaf0000aaaa0000,v31,v1,v2,v3,v4,v5],[(v16,v2,v5),(v31,v16,v0)],[9,21],[]),
([0x3000300033003300,v0,v1,v75,v2,v3,v4,v5],[],[3,22,23],[]),
([v0,v31,v1,v2,v10,v3,v4,v5],[(v31,v16,v0)],[0,3,9,21,22,23],[(0,346),(0,347),(0,348)]),
([v0,v31,v1,v2,v3,v19,v4],[(v31,v16,v0),(v19,v4,v5)],[0,1,2,6,9,13,22,23],[(0,349)]),
([v0,v31,v1,v75,v2,v3,v4,v5],[(v16,v2,v5),(v31,v16,v0),(v75,v16,v1)],[1,2,6,13],[(0,345),(1,345)]),
([v16,v66,v0,v1,v2,v3,v4,v5],[(v16,v2,v5),(v31,v16,v0),(v66,v31,v1)],[1,2,6,13],[(0,345)]),
([v0,v1,v2,v3,0xff0f0f0fff000000,v4,v5],[],[0,1,3,6,9,13,17,19,20,23],[(0,346),(0,350),(1,346),(1,350)]),
([v16,v0,v1,v2,v3,v21,v4,v5],[(v16,v2,v5),(v10,v3,v4),(v21,v0,v10)],[1,2,3,6],[(0,346),(0,351)]),
([v16,v0,v1,v3,v23,v4,v5],[(v23,v2,v10)],[0,3,6,9,17,19,20,22,23],[(0,348),(1,348)]),
([v16,v0,v1,v2,v3,v40,v4],[(v16,v2,v5),(v14,v3,v5),(v40,v0,v14)],[0,1,2,3,6,14,19,21,22],[(0,352),(1,170),(1,349)]),
([v16,v0,v1,v2,v3,v59,v4],[(v16,v2,v5),(v14,v3,v5),(v59,v1,v14)],[0,2,3,6,13,14,21,22],[(1,353)]),
([v0,v1,v2,v3,v21,v34,v4,v5],[(v10,v3,v4),(v21,v0,v10),(v34,v1,v21)],[0,1,3,6,9,13],[(0,174),(0,355),(0,356),(1,354)]),
([v56,v0,v1,v2,v3,v4,v5],[(v10,v3,v4),(v21,v0,v10),(v56,v1,v21)],[0,1,2,3,6,9,13],[(0,174),(0,309),(0,340),(0,357),(1,342)]),
([v56,v0,v1,v2,v3,v21,v4,v5],[(v10,v3,v4),(v21,v0,v10),(v56,v1,v21)],[1,3,9,13,22],[(0,171),(0,174)]),
([v0,v1,v2,v3,v21,v54,v4,v5],[(v10,v3,v4),(v21,v0,v10),(v54,v2,v21)],[0,1,3,9],[(0,316),(1,358)]),
([v52,v0,v1,v2,v3,v4,v5],[(v10,v3,v4),(v21,v0,v10),(v52,v2,v21)],[0,1,2,3,6,9,13],[(0,172),(0,309),(0,316),(0,332),(1,359)]),
([v52,v0,v1,v2,v3,v21,v4,v5],[(v10,v3,v4),(v21,v0,v10),(v52,v2,v21)],[0,1,3,9],[(0,316)]),
([v0,v1,v2,v3,0xffaaaaaa00000000,v21,v4,v5],[(v10,v3,v4),(v21,v0,v10),(0xffaaaaaa00000000,v21,v5)],[1,2,3,6,22],[]),
([0x33333300000000,v0,v1,v2,v3,v37,v4,v5],[(v37,v1,v10)],[2,3,6,9,13,17],[]),
([v0,v1,v2,v3,v21,v37,v4,v5],[(v10,v3,v4),(v21,v0,v10),(v37,v1,v10)],[1,3,9,13,21,22],[(0,173),(0,354),(1,354)]),
([v56,v0,v1,v2,v10,v3,v4,v5],[(v10,v3,v4),(v21,v0,v10),(v56,v1,v21)],[1,3,9,13,22],[(0,354)]),
([v0,v1,v2,v3,v21,v23,v4,v5],[(v10,v3,v4),(v21,v0,v10),(v23,v2,v10)],[0,1,3,21,22],[(0,360),(1,358)]),
([v52,v0,v1,v2,v10,v3,v4,v5],[(v10,v3,v4),(v21,v0,v10),(v52,v2,v21)],[0,1,3,9,22],[(0,360)]),
([v0,v1,v2,v3,v23,v54,v4,v5],[(v10,v3,v4),(v23,v2,v10)],[1,3,9],[(0,360),(1,314)]),
([v67,v0,v1,v2,v3,v4,v5],[(v10,v4,v3),(v23,v2,v10),(v67,v1,v23)],[0,1,2,3,6,9,13],[(0,188),(0,311),(0,314),(0,333),(0,361)]),
([v67,v0,v1,v2,v3,v23,v4,v5],[(v10,v4,v3),(v23,v2,v10)],[0,13,22],[(0,310),(0,314)]),
([v0,v1,v2,v14,v23,v4,v5],[(v10,v3,v4),(v23,v2,v10)],[0,1,3,6,9,19,20,22,24],[(0,312),(1,313),(1,362)]),
([v0,v1,v2,v3,0xfff0f0f000000000,v23,v4,v5],[(v10,v3,v4),(v23,v2,v10)],[2,6,22,23],[]),
([0xf0f0f00000000,v0,v1,v2,v3,v23,v4,v5],[(v10,v3,v4),(0xf0f0f00000000,v23,v5)],[0,2,6,17,24],[]),
([v67,v0,v1,v2,v10,v3,v4,v5],[(v10,v4,v3),(v23,v2,v10)],[0,3,9,13,21,22],[(0,358)]),
([v0,v1,v2,v3,0xffaaaaaaaaaaaaaa,v4,v5],[(v10,v3,v4),(v104,v10,v5)],[0,1,2,3,6,9,13,21,22,24],[(0,190),(0,363),(1,189)]),
([v0,v1,v2,v10,v3,v32,v5],[(v10,v4,v3),(v19,v4,v5),(v32,v1,v19)],[1,3,6,9,13,15,17,21,23],[(0,192),(0,362),(0,365),(1,364)]),
([v0,v1,v2,v10,v3,v82,v5],[(v10,v4,v3),(v19,v4,v5),(v82,v2,v19)],[0,1,3,6,9,13,15,17,21,24],[(0,320)]),
([v0,v1,v2,v10,v14,v19],[(v10,v3,v4),(v14,v3,v5),(v19,v4,v5)],[0,1,3,6,9,13,21,22,24],[(0,193),(0,365),(1,365)]),
([v100,v0,v1,v2,v3,v4,v5],[(v14,v3,v5),(v100,v1,v40)],[0,1,3,6,9,13,14,21],[(0,325),(0,343),(0,352),(0,366)]),
([v89,v0,v1,v2,v3,v4,v5],[(v14,v3,v5),(v40,v0,v14),(v89,v2,v40)],[0,1,3,6,9,13,14,21,24],[(0,194),(0,325),(0,364),(1,367)]),
([v0,v1,v2,v14,v3,v4,v32],[(v19,v4,v5),(v32,v1,v19),(v14,v3,v5)],[1,2,3,6,9,13,15,21,24],[(0,195),(0,365),(0,368)]),
([v114,v0,v1,v2,v3,v4,v5],[(v19,v4,v5),(v114,v1,v105)],[0,1,3,6,9,13,15,22],[(0,322),(0,353),(0,369),(1,344)]),
([v119,v0,v1,v2,v3,v4,v5],[(v14,v3,v5),(v59,v1,v14),(v119,v2,v59)],[0,1,3,6,9,13,14,21],[(0,370),(1,322)])
]

def g6_L8 : Array W6Node := Array.mk [
([v0,v6,v2,v9,v3,v4,v5],[(v6,v1,v0),(v9,v1,v2)],[0,1,3,6,9,13],[(0,0),(0,2),(0,3),(0,4),(0,5),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(1,1),(1,6)]),
([v0,v1,v2,v8,v3,v4,v5],[(v6,v0,v1),(v8,v6,v2)],[0,1,2,3,6,9,13,21,22],[(0,18),(0,19),(0,20),(0,21),(0,22),(0,23),(0,24),(0,25),(0,26),(0,27),(0,28),(0,29),(0,30),(0,31),(1,18),(1,20),(1,21),(1,22),(1,23),(1,24),(1,31)]),
([v0,v1,v6,v2,v8,v3,v4,v5],[(v6,v0,v1),(v8,v6,v2)],[0,1,3,6,9,13],[(0,19),(0,32),(0,33),(0,34),(0,35),(0,36),(0,37),(0,38),(0,39),(0,40),(0,41),(0,42),(0,43),(0,44),(0,45),(0,46),(0,47),(0,48),(1,32),(1,33),(1,35),(1,36),(1,39),(1,40),(1,41),(1,42),(1,43)]),
([v12,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2)],[0,1,2,3,6,9,13,21,22],[(0,19),(0,49),(0,50),(0,51),(0,52),(0,53),(0,54),(0,55),(0,56),(1,49),(1,50),(1,53),(1,56)]),
([v12,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v12,v6,v2)],[0,1,3,6,9,13],[(0,2),(0,19),(0,34),(0,57),(0,58),(0,59),(0,60),(0,61),(0,62),(0,63),(0,64),(0,65),(0,66),(1,2),(1,57),(1,58),(1,61),(1,62),(1,65)]),
([v0,v1,v26,v2,v3,v4,v5],[(v6,v0,v1),(v26,v6,v3)],[0,1,2,3,6,9,13,16,17,21,22],[(0,67)]),
([v0,v1,v26,v6,v2,v3,v4,v5],[(v6,v0,v1),(v26,v6,v3)],[0,1,3,6,9,13,22],[(0,3),(0,35),(0,57),(0,61),(0,68),(0,69),(0,70),(0,72),(0,74),(0,76),(0,77),(0,78),(0,79),(1,5),(1,71),(1,73),(1,75)]),
([v28,v0,v1,v2,v3,v4,v5],[(v6,v0,v1),(v28,v6,v3)],[0,1,2,3,6,9,13,16,17,21,22],[(0,80)]),
([v28,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v28,v6,v3)],[0,1,3,4,5,6,9,13,22],[(0,4),(0,6),(0,36),(0,43),(0,62),(0,69),(0,75),(0,81),(0,82),(0,84),(0,86),(0,87),(0,88),(0,89),(1,83),(1,85)]),
([v0,v1,v35,v2,v3,v4,v5],[(v6,v0,v1),(v35,v6,v5)],[0,1,2,3,6,9,13,21,22,23,24],[]),
([v0,v1,v35,v6,v2,v3,v4,v5],[(v6,v0,v1),(v35,v6,v5)],[0,1,2,3,6,9,13],[(0,7),(0,37),(0,59),(0,63),(0,72),(0,76),(0,87),(0,90),(0,91),(0,92),(0,93),(1,7),(1,72),(1,76),(1,87),(1,91),(1,93)]),
([v41,v0,v1,v2,v3,v4,v5],[(v41,v6,v5)],[0,1,2,3,6,9,13,21,22,23,24],[]),
([v41,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v41,v6,v5)],[0,1,2,3,6,7,8,9,13],[(0,8),(0,38),(0,48),(0,64),(0,77),(0,84),(0,88),(0,92),(0,94),(0,95),(0,96),(1,8),(1,77),(1,84),(1,88),(1,95)]),
([v15,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v15,v2,v3)],[0,1,3,6,9,12,13,18,22,24],[(0,43),(0,53),(0,57),(0,65),(0,89),(0,97),(0,99),(0,101),(0,103),(0,104),(1,98),(1,100),(1,102)]),
([v16,v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1),(v16,v2,v5)],[0,1,2,3,6,9,13,17,20],[(0,48),(0,54),(0,59),(0,66),(0,96),(0,101),(0,105),(0,106),(0,107),(0,108),(0,109),(0,110),(0,111),(0,112),(1,101),(1,111),(1,112)]),
([v0,v1,v6,v2,v10,v3,v4,v5],[(v6,v0,v1),(v10,v3,v4)],[0,1,3,6,9,13,21,22,23],[(0,15),(0,30),(0,55),(0,70),(0,78),(0,82),(0,99),(0,103),(0,113),(0,114),(0,115),(0,116),(0,117),(0,118),(0,119),(0,120),(0,121),(0,122),(0,123),(0,124),(1,15),(1,78),(1,103),(1,113),(1,114),(1,124)]),
([v0,v1,v6,v2,v14,v3,v4,v5],[(v6,v0,v1),(v14,v3,v5)],[0,1,2,3,6,9,13,14,18,22],[(0,16),(0,31),(0,56),(0,72),(0,79),(0,84),(0,93),(0,101),(0,104),(0,112),(0,122),(0,124),(0,126),(0,128),(0,130),(1,17),(1,125),(1,127),(1,129)]),
([v0,v1,v7,v9,v3,v4,v5],[(v7,v0,v2),(v9,v1,v2)],[0,1,3,6,9,13],[(0,0),(0,131),(0,132),(0,133),(0,134),(0,135),(0,136),(0,137),(0,138),(0,139),(1,131),(1,132),(1,133),(1,134),(1,135),(1,136),(1,137),(1,139)]),
([v0,v1,v2,v7,v8,v3,v4,v5],[(v7,v0,v2),(v8,v1,v7)],[0,1,3,6,9,13,24],[(0,18),(0,142),(0,143),(0,144),(0,145),(0,147),(0,149),(0,151),(0,152),(0,153),(0,155),(0,156),(0,157),(0,158),(0,159),(0,161),(0,162),(0,163),(1,140),(1,141),(1,146),(1,148),(1,150),(1,154),(1,160)]),
([v11,v0,v1,v2,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7)],[0,1,2,3,6,9,13,21,22],[(0,18),(0,164),(0,165),(0,166),(0,167),(0,168),(0,169),(0,170),(0,171),(0,172),(0,173)]),
([v11,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v11,v1,v7)],[0,1,3,6,9,13,24],[(0,1),(0,18),(0,131),(0,142),(0,174),(0,176),(0,178),(0,179),(0,181),(0,183),(1,175),(1,177),(1,180),(1,182),(1,184)]),
([v24,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v24,v1,v3)],[0,1,3,5,6,9,13,18,22,23,24],[(0,155),(0,170),(0,174),(0,178),(0,185),(0,187),(1,186),(1,188),(1,189)]),
([v20,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v20,v1,v4)],[0,1,3,6,9,10,13,16,19,21,24],[(0,176),(0,187),(0,191),(1,160),(1,190)]),
([v29,v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2),(v29,v1,v5)],[0,1,2,3,6,8,9,13,17,20,24],[(0,192),(1,193),(1,194),(1,195)]),
([v0,v1,v2,v38,v3,v4,v5],[(v7,v0,v2),(v38,v7,v3)],[0,1,2,3,6,9,13,16,17,21,22],[(0,196)]),
([v0,v1,v2,v38,v7,v3,v4,v5],[(v7,v0,v2),(v38,v7,v3)],[0,1,3,6,9,13,22,24],[(0,132),(0,145),(0,174),(0,179),(0,197),(0,199),(0,201),(0,203),(1,11),(1,198),(1,200),(1,202),(1,204)]),
([v27,v0,v1,v2,v3,v4,v5],[(v9,v1,v2),(v27,v9,v4)],[0,1,2,3,6,9,13,18,20,21,22],[(0,205)]),
([v27,v0,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v27,v9,v4)],[0,1,3,6,9,10,11,13,21,24],[(0,12),(0,133),(0,146),(0,180),(0,189),(0,198),(0,206),(0,207),(0,209),(0,210),(0,211),(0,212),(0,213),(1,155),(1,208)]),
([v0,v1,v2,v33,v3,v4,v5],[(v7,v0,v2),(v33,v7,v4)],[0,1,2,3,6,9,13,18,20,21,22],[(1,214)]),
([v0,v1,v2,v33,v7,v3,v4,v5],[(v7,v0,v2),(v33,v7,v4)],[0,1,3,6,9,13,21,24],[(0,134),(0,147),(0,176),(0,181),(0,199),(0,201),(0,215),(0,218),(0,220),(1,9),(1,209),(1,216),(1,217),(1,219)]),
([v30,v0,v1,v2,v3,v4,v5],[(v9,v1,v2),(v30,v9,v3)],[0,1,2,3,6,9,13,16,17,21,22],[(0,221),(1,222)]),
([v30,v0,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v30,v9,v3)],[0,1,3,5,6,9,12,13,22,24],[(0,10),(0,135),(0,148),(0,160),(0,182),(0,190),(0,202),(0,207),(0,210),(0,217),(0,223),(0,225),(0,227),(0,228),(0,229),(1,224),(1,226)]),
([v0,v1,v2,v45,v3,v4,v5],[(v7,v0,v2),(v45,v7,v5)],[0,1,2,3,6,9,13,19,21,22,23],[(1,230)]),
([v0,v1,v2,v45,v7,v3,v4,v5],[(v7,v0,v2),(v45,v7,v5)],[0,1,2,3,6,9,13,24],[(0,136),(0,149),(0,183),(0,203),(0,218),(0,231),(1,13),(1,211),(1,228),(1,232),(1,233)]),
([v36,v0,v1,v2,v3,v4,v5],[(v9,v1,v2),(v36,v9,v5)],[0,1,2,3,6,9,13,19,21,22,23],[(0,234),(1,235)]),
([v36,v0,v1,v2,v9,v3,v4,v5],[(v9,v1,v2),(v36,v9,v5)],[0,1,2,3,6,8,9,13,24],[(0,14),(0,137),(0,150),(0,184),(0,204),(0,212),(0,219),(0,229),(0,236),(0,237),(1,238),(1,239),(1,240)]),
([v0,v1,v2,v7,v10,v3,v4,v5],[(v7,v0,v2),(v10,v3,v4)],[0,1,3,6,9,13,21,22,23,24],[(0,30),(0,138),(0,171),(0,187),(0,191),(0,199),(0,220),(0,241),(0,242),(0,243),(0,244),(0,245),(0,246),(0,247),(0,248),(0,249),(0,250),(0,251),(1,15),(1,207),(1,213)]),
([v0,v1,v2,v7,v14,v3,v4,v5],[(v7,v0,v2),(v14,v3,v5)],[0,1,2,3,6,9,13,14,18,22,24],[(0,31),(0,139),(0,172),(0,250),(0,252),(0,253),(1,17),(1,254),(1,255)]),
([v0,v1,v2,v7,v3,v19,v4,v5],[(v7,v0,v2),(v19,v4,v5)],[0,1,2,3,6,9,13,15,16,21,24],[(0,173),(0,251),(0,256),(0,257),(0,258),(0,259),(0,260),(1,16),(1,31),(1,139)]),
([v76,v0,v1,v2,v3,v4,v5],[(v20,v1,v4),(v76,v20,v3)],[0,1,2,3,6,9,13,17,21,22],[(0,187),(0,261),(0,262)]),
([v123,v0,v1,v2,v3,v4,v5],[(v20,v1,v4),(v123,v20,v5)],[0,1,2,3,6,9,13,21,22,23,24],[(0,263)]),
([v20,v58,v0,v1,v2,v3,v4,v5],[(v20,v1,v4),(v58,v0,v3)],[0,1,3,4,6,9,10,13,16,18,19,21,22,23],[(0,264)]),
([v24,v58,v0,v1,v2,v4,v5],[(v58,v0,v3)],[0,1,3,4,6,9,13,16,17,22],[(1,265)]),
([v20,v42,v0,v1,v2,v3,v4,v5],[(v20,v1,v4),(v42,v0,v5)],[0,1,2,3,6,9,10,13,16,17,19,20,21],[(0,266)]),
([v15,v20,v0,v1,v2,v3,v4,v5],[(v20,v1,v4),(v15,v2,v3)],[0,1,3,6,9,10,12,13,16,18,19,21,22,24],[(0,267),(0,268)]),
([v15,v58,v0,v1,v2,v4,v5],[(v58,v0,v3)],[0,1,3,4,6,9,13,16,17,22],[(1,269)]),
([v16,v20,v0,v1,v2,v3,v4,v5],[(v20,v1,v4),(v16,v2,v5)],[0,1,2,3,6,9,10,13,16,17,19,20,21],[(0,270)]),
([v20,v0,v1,v2,v10,v3,v5],[(v20,v1,v4),(v10,v3,v4)],[0,1,3,6,9,10,13,20,21,22],[(0,191),(0,264),(0,268),(0,271),(0,272)]),
([v20,v0,v1,v2,v14,v3,v4,v5],[(v20,v1,v4),(v14,v3,v5)],[0,1,2,3,6,9,10,13,14,16,18,19,20,21,22],[(0,273),(0,274)]),
([v0,v77,v1,v2,v3,v4,v5],[(v24,v1,v3),(v77,v24,v0)],[0,1,2,3,5,6,9,13,21,22],[(0,275),(0,276),(0,278),(0,279),(1,277)]),
([v0,v1,v2,0xf3f0f3f0f3f0f3f0,v3,v4,v5],[(v24,v1,v3),(0xf3f0f3f0f3f0f3f0,v24,v2)],[0,1,2,3,5,6,9,13,21,22],[(0,283),(1,265),(1,280),(1,281),(1,282)]),
([v121,v0,v1,v2,v3,v4,v5],[(v43,v0,v4),(v121,v43,v3)],[0,1,2,3,6,9,13,17,18,22],[(0,188)]),
([v125,v0,v1,v2,v3,v4,v5],[(v125,v24,v5)],[0,1,2,3,6,9,13,19,21,22,24],[(0,284)]),
([v0,0xaaaaffff00000000,v1,v2,v3,v4,v5],[(0xaaaaffff00000000,v43,v5)],[0,1,2,3,6,9,13,20,21,22,23,24],[]),
([v24,v43,v0,v1,v2,v3,v4,v5],[(v24,v1,v3),(v43,v0,v4)],[0,1,3,5,6,9,13,16,18,19,21,22,23,25],[(0,281),(1,281)]),
([v24,v42,v0,v1,v2,v3,v4,v5],[(v24,v1,v3),(v42,v0,v5)],[0,1,2,3,5,6,7,9,13,17,18,20,22,23],[(0,285),(1,282)]),
([v15,v24,v0,v1,v2,v4,v5],[(v24,v1,v3),(v15,v2,v3)],[0,1,3,6,9,13,16,17,22,24],[(0,276),(0,286)]),
([v15,v43,v0,v1,v2,v3,v4,v5],[(v43,v0,v4),(v15,v2,v3)],[0,1,3,6,9,12,13,16,18,19,21,22,24,25],[(0,277),(1,287)]),
([v16,v24,v0,v1,v2,v3,v4,v5],[(v24,v1,v3),(v16,v2,v5)],[0,1,2,3,5,6,9,13,17,18,20,22,23],[(0,278),(0,288)]),
([v24,v0,v1,v2,v3,v19,v4,v5],[(v24,v1,v3),(v19,v4,v5)],[0,1,2,3,5,6,9,13,15,16,18,21,22,23],[(0,279),(0,283),(0,289),(0,290)]),
([v0,v78,v1,v2,v3,v4,v5],[(v29,v1,v5),(v78,v29,v0)],[0,1,2,3,6,8,9,13,21,22],[(0,291),(0,292),(0,294),(0,295),(1,293)]),
([v0,v1,v2,0xf3f3f3f3f0f0f0f0,v3,v4,v5],[(v29,v1,v5),(0xf3f3f3f3f0f0f0f0,v29,v2)],[0,1,2,3,6,8,9,13,21,22,24],[(0,296),(1,266),(1,285)]),
([0xaaaa0000ffff0000,v0,v1,v2,v3,v4,v5],[(v42,v0,v5),(0xaaaa0000ffff0000,v42,v4)],[0,1,3,6,9,13,18,19,21,22],[(0,194)]),
([v122,v0,v1,v2,v3,v4,v5],[(v42,v0,v5),(v122,v42,v3)],[0,1,3,6,9,13,16,21,22,23],[(0,195)]),
([v29,v42,v0,v1,v2,v3,v4],[(v29,v1,v5)],[0,1,2,3,6,9,13,19,23,24],[]),
([v15,v29,v0,v1,v2,v3,v4,v5],[(v29,v1,v5),(v15,v2,v3)],[0,1,2,3,6,8,9,12,13,17,18,20,22,24],[(0,292),(0,297)]),
([v15,v42,v0,v1,v2,v3,v4,v5],[(v42,v0,v5),(v15,v2,v3)],[0,1,2,3,6,7,9,12,13,17,18,20,22,24],[(0,293),(1,298)]),
([v16,v29,v0,v1,v2,v3,v4],[(v29,v1,v5),(v16,v2,v5)],[0,1,2,3,6,9,13,19,23],[(0,294),(0,299)]),
([v29,v0,v1,v2,v10,v3,v4,v5],[(v29,v1,v5),(v10,v3,v4)],[0,1,2,3,6,8,9,13,17,19,20,21,22,23],[(0,295),(0,296),(0,300),(0,301)]),
([v29,v0,v1,v2,v14,v3,v4],[(v29,v1,v5),(v14,v3,v5)],[0,1,2,3,6,9,13,19,22,24],[(0,302)]),
([v0,v50,v1,v2,v3,v4,v5],[(v15,v2,v3),(v50,v15,v0)],[0,1,2,3,6,9,12,13,21,22],[(0,267),(0,286),(0,297),(0,303),(0,304),(0,305)]),
([v0,v64,v1,v2,v3,v4,v5],[(v44,v2,v4),(v64,v44,v0)],[0,1,2,3,6,9,11,13,21,22],[(0,269),(0,287),(0,298),(0,306),(0,307)]),
([v63,v0,v1,v2,v3,v4,v5],[(v15,v2,v3),(v63,v15,v4)],[0,1,2,3,6,9,13,17,21,22],[(0,99),(0,308),(0,309),(1,308)]),
([v0,v1,v97,v2,v3,v4,v5],[(v44,v2,v4),(v97,v44,v3)],[0,1,2,3,6,9,13,17,18,22],[(0,100)]),
([v80,v0,v1,v2,v3,v4,v5],[(v15,v2,v3),(v80,v15,v5)],[0,1,2,3,6,9,13,19,21,22],[(0,101),(0,310),(1,311)]),
([v0,v1,v2,v98,v3,v4,v5],[(v44,v2,v4),(v98,v44,v5)],[0,1,2,3,6,9,13,20,21,22,23],[(0,102)]),
([v15,v0,v1,v2,v10,v4,v5],[(v15,v2,v3),(v10,v3,v4)],[0,1,3,6,9,13,17,19,22,24],[(0,103),(0,268),(0,304),(0,312),(0,313)]),
([v15,v0,v1,v2,v14,v4,v5],[(v15,v2,v3),(v14,v3,v5)],[0,1,3,6,9,13,16,22,24],[(0,104),(0,314),(0,315)]),
([v15,v0,v1,v2,v3,v19,v4,v5],[(v15,v2,v3),(v19,v4,v5)],[0,1,2,3,6,9,12,13,15,16,17,21,22,24],[(0,305),(0,316),(0,317),(1,307)]),
([v0,v31,v1,v2,v3,v4,v5],[(v16,v2,v5),(v31,v16,v0)],[0,1,2,3,6,9,13,21,22],[(0,105),(0,270),(0,288),(0,299),(0,318),(0,319),(0,320),(0,321),(0,323),(0,325),(0,326),(1,322),(1,324)]),
([v16,v0,v31,v1,v2,v3,v4,v5],[(v16,v2,v5),(v31,v16,v0)],[0,1,2,3,6,9,13,19,23],[(0,106),(0,327),(0,328)]),
([v0,v1,v99,v2,v3,v4,v5],[(v16,v2,v5),(v99,v16,v3)],[0,1,3,6,9,13,16,21,22,23],[(0,111)]),
([v16,v0,v1,v2,v10,v3,v4,v5],[(v16,v2,v5),(v10,v3,v4)],[0,1,2,3,6,9,13,17,19,20,21,22,23],[(0,325),(0,329),(0,330),(0,331),(1,325),(1,330)]),
([v16,v0,v1,v2,v14,v3,v4],[(v16,v2,v5),(v14,v3,v5)],[0,1,2,3,6,9,13,19,22],[(0,112),(0,332),(0,333),(1,326)]),
([v0,v1,v2,v3,v21,v4,v5],[(v10,v3,v4),(v21,v0,v10)],[0,1,2,3,6,9,13,22],[(0,115),(0,244),(0,271),(0,300),(0,312),(0,330),(0,334),(0,335),(0,336),(0,337),(0,338),(0,339),(0,340),(1,113),(1,241),(1,313),(1,341)]),
([v0,v1,v2,v10,v3,v21,v4,v5],[(v10,v3,v4),(v21,v0,v10)],[0,1,3,6,9,13,17,21,22,23],[(0,117),(0,246),(0,342),(0,343),(0,344),(0,345),(1,114)]),
([v0,v1,v2,v3,v23,v4,v5],[(v10,v3,v4),(v23,v2,v10)],[0,1,2,3,6,9,13,22],[(0,121),(0,242),(0,244),(0,272),(0,301),(0,331),(0,346),(0,347),(0,348),(0,349),(0,350),(0,351),(1,242),(1,244),(1,272),(1,301),(1,346),(1,347),(1,348),(1,349)]),
([v0,v1,v2,v10,v3,v23,v4,v5],[(v10,v3,v4),(v23,v2,v10)],[0,1,3,6,9,13,17,21,22,23],[(0,243),(0,246),(0,344),(0,352),(1,243),(1,246),(1,344),(1,352)]),
([v0,v1,v2,v104,v3,v4,v5],[(v10,v3,v4),(v104,v10,v5)],[0,1,2,3,6,9,13,21,22,24],[(0,122),(0,353),(1,353)]),
([v120,v0,v1,v2,v3,v4,v5],[(v10,v3,v4),(v120,v10,v5)],[0,1,2,3,6,9,13,17,22,24],[(0,123)]),
([v0,v1,v2,v10,v14,v4,v5],[(v10,v3,v4),(v14,v3,v5)],[0,1,3,6,9,13,19,20,22],[(0,124),(0,250),(0,349),(0,356),(1,251),(1,354),(1,355)]),
([v0,v1,v2,v3,v40,v4,v5],[(v14,v3,v5),(v40,v0,v14)],[0,1,3,6,9,13,14,21,22],[(0,273),(0,302),(0,314),(0,332),(0,357),(0,358),(1,125),(1,256),(1,317),(1,354),(1,359)]),
([v0,v1,v2,v3,v59,v4,v5],[(v14,v3,v5),(v59,v1,v14)],[0,1,3,6,9,13,14,21,22],[(0,252),(0,315),(0,333),(0,361),(1,289),(1,316),(1,360)]),
([v0,v1,v2,v3,v88,v4,v5],[(v14,v3,v5),(v88,v2,v14)],[0,1,3,6,9,13,14,21,22,24],[(0,128),(0,274),(1,257),(1,290),(1,355)]),
([v83,v0,v1,v2,v3,v4,v5],[(v19,v4,v5),(v83,v19,v3)],[0,1,3,6,9,13,18,22,23],[(0,129),(0,255),(0,260)]),
([v0,v1,v2,v14,v3,v19,v4],[(v14,v3,v5),(v19,v4,v5)],[0,1,2,3,6,9,13,21,22,24],[(0,130),(0,356),(0,359),(1,359)])
]

def g6_L9 : Array W6Node := Array.mk [
([v0,v1,v6,v2,v3,v4,v5],[(v6,v0,v1)],[0,1,3,6,9,13],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(1,0),(1,5),(1,6),(1,7),(1,8),(1,13),(1,16)]),
([v0,v1,v2,v7,v3,v4,v5],[(v7,v0,v2)],[0,1,3,6,9,13],[(0,1),(0,17),(0,18),(0,19),(0,20),(0,21),(0,22),(0,23),(0,24),(0,25),(0,28),(0,29),(0,32),(0,33),(0,36),(0,37),(0,38),(1,0),(1,26),(1,27),(1,30),(1,31),(1,34),(1,35)]),
([v20,v0,v1,v2,v3,v4,v5],[(v20,v1,v4)],[0,1,3,6,9,10,13,21],[(0,22),(0,26),(0,39),(0,40),(0,41),(0,43),(0,44),(0,46),(0,47),(0,48),(1,7),(1,42),(1,45)]),
([v24,v0,v1,v2,v3,v4,v5],[(v24,v1,v3)],[0,1,3,5,6,9,13,22],[(0,7),(0,21),(0,30),(0,39),(0,42),(0,49),(0,50),(0,52),(0,54),(0,55),(0,56),(0,58),(0,59),(1,51),(1,53),(1,57)]),
([v29,v0,v1,v2,v3,v4,v5],[(v29,v1,v5)],[0,1,2,3,6,8,9,13,19,23,24],[(0,11),(0,23),(0,34),(0,40),(0,52),(0,60),(0,61),(0,64),(0,65),(0,67),(0,68),(0,69),(1,43),(1,55),(1,62),(1,63),(1,66)]),
([v15,v0,v1,v2,v3,v4,v5],[(v15,v2,v3)],[0,1,3,6,9,12,13,22],[(0,13),(0,30),(0,44),(0,45),(0,56),(0,57),(0,65),(0,66),(0,70),(0,72),(0,74),(0,76),(0,77),(0,78),(1,26),(1,71),(1,73),(1,75)]),
([v16,v0,v1,v2,v3,v4,v5],[(v16,v2,v5)],[0,1,2,3,6,9,13,19,23],[(0,14),(0,34),(0,46),(0,58),(0,67),(0,74),(0,79),(0,80),(0,81),(0,82),(0,83),(1,34),(1,46),(1,58),(1,67),(1,74),(1,79),(1,80),(1,81),(1,83)]),
([v0,v1,v2,v10,v3,v4,v5],[(v10,v3,v4)],[0,1,3,6,9,13,17,22],[(0,15),(0,36),(0,39),(0,47),(0,68),(0,72),(0,76),(0,82),(0,84),(0,85),(0,86),(0,87),(0,88),(0,89),(0,90),(1,36),(1,39),(1,47),(1,68),(1,76),(1,84),(1,85),(1,90)]),
([v0,v1,v2,v14,v3,v4,v5],[(v14,v3,v5)],[0,1,3,6,9,13,14,22],[(0,16),(0,37),(0,48),(0,52),(0,69),(0,74),(0,77),(0,83),(0,88),(0,90),(0,91),(0,92),(0,93),(0,95),(1,38),(1,40),(1,59),(1,78),(1,94)])
]

def g6_L10 : Array W6Node := Array.mk [
([v0,v1,v2,v3,v4,v5],[],[0,1,3,6,9,13],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,1),(1,2),(1,3),(1,4),(1,5),(1,8)])
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_3_0 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 3 g6_L3 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_3 : ∀ i < g6_L3.size, checkNodeW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 3 g6_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : g6_L3.size = 1 := by decide +kernel
  exact checkBlockW6_at g6_chk_3_0 i (Nat.zero_le _) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_4_0 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 g6_L3 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_4 : ∀ i < g6_L4.size, checkNodeW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 g6_L3 i = true := by
  intro i hi
  have hsz : g6_L4.size = 3 := by decide +kernel
  exact checkBlockW6_at g6_chk_4_0 i (Nat.zero_le _) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_0 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_1 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_2 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_3 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_4 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_5 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 80 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_5 : ∀ i < g6_L5.size, checkNodeW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 i = true := by
  intro i hi
  have hsz : g6_L5.size = 89 := by decide +kernel
  have hi' : i < 89 := hsz ▸ hi
  by_cases h : i < 48
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW6_at g6_chk_5_0 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_5_1 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_5_2 i (by omega) (by omega)
  ·
    by_cases h : i < 80
    ·
      by_cases h : i < 64
      ·
        exact checkBlockW6_at g6_chk_5_3 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_5_4 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_5_5 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_0 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_1 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_2 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_3 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_4 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_5 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_6 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_7 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_8 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_9 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_10 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_11 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_12 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_13 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_14 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_15 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_16 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_17 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_18 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_19 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_20 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_21 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_22 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_23 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 368 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_6 : ∀ i < g6_L6.size, checkNodeW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 i = true := by
  intro i hi
  have hsz : g6_L6.size = 371 := by decide +kernel
  have hi' : i < 371 := hsz ▸ hi
  by_cases h : i < 192
  ·
    by_cases h : i < 96
    ·
      by_cases h : i < 48
      ·
        by_cases h : i < 32
        ·
          by_cases h : i < 16
          ·
            exact checkBlockW6_at g6_chk_6_0 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_1 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_2 i (by omega) (by omega)
      ·
        by_cases h : i < 80
        ·
          by_cases h : i < 64
          ·
            exact checkBlockW6_at g6_chk_6_3 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_4 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_5 i (by omega) (by omega)
    ·
      by_cases h : i < 144
      ·
        by_cases h : i < 128
        ·
          by_cases h : i < 112
          ·
            exact checkBlockW6_at g6_chk_6_6 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_7 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_8 i (by omega) (by omega)
      ·
        by_cases h : i < 176
        ·
          by_cases h : i < 160
          ·
            exact checkBlockW6_at g6_chk_6_9 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_10 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_11 i (by omega) (by omega)
  ·
    by_cases h : i < 288
    ·
      by_cases h : i < 240
      ·
        by_cases h : i < 224
        ·
          by_cases h : i < 208
          ·
            exact checkBlockW6_at g6_chk_6_12 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_13 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_14 i (by omega) (by omega)
      ·
        by_cases h : i < 272
        ·
          by_cases h : i < 256
          ·
            exact checkBlockW6_at g6_chk_6_15 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_16 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_17 i (by omega) (by omega)
    ·
      by_cases h : i < 336
      ·
        by_cases h : i < 320
        ·
          by_cases h : i < 304
          ·
            exact checkBlockW6_at g6_chk_6_18 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_19 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_20 i (by omega) (by omega)
      ·
        by_cases h : i < 368
        ·
          by_cases h : i < 352
          ·
            exact checkBlockW6_at g6_chk_6_21 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_6_22 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_23 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_0 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_1 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_2 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_3 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_4 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_5 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_6 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_7 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_8 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_9 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_10 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_11 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_12 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_13 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_14 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_15 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_16 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_17 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_18 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_19 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_20 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_21 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_22 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 352 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_7 : ∀ i < g6_L7.size, checkNodeW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 i = true := by
  intro i hi
  have hsz : g6_L7.size = 362 := by decide +kernel
  have hi' : i < 362 := hsz ▸ hi
  by_cases h : i < 192
  ·
    by_cases h : i < 96
    ·
      by_cases h : i < 48
      ·
        by_cases h : i < 32
        ·
          by_cases h : i < 16
          ·
            exact checkBlockW6_at g6_chk_7_0 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_1 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_2 i (by omega) (by omega)
      ·
        by_cases h : i < 80
        ·
          by_cases h : i < 64
          ·
            exact checkBlockW6_at g6_chk_7_3 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_4 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_5 i (by omega) (by omega)
    ·
      by_cases h : i < 144
      ·
        by_cases h : i < 128
        ·
          by_cases h : i < 112
          ·
            exact checkBlockW6_at g6_chk_7_6 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_7 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_8 i (by omega) (by omega)
      ·
        by_cases h : i < 176
        ·
          by_cases h : i < 160
          ·
            exact checkBlockW6_at g6_chk_7_9 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_10 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_11 i (by omega) (by omega)
  ·
    by_cases h : i < 288
    ·
      by_cases h : i < 240
      ·
        by_cases h : i < 224
        ·
          by_cases h : i < 208
          ·
            exact checkBlockW6_at g6_chk_7_12 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_13 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_14 i (by omega) (by omega)
      ·
        by_cases h : i < 272
        ·
          by_cases h : i < 256
          ·
            exact checkBlockW6_at g6_chk_7_15 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_16 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_17 i (by omega) (by omega)
    ·
      by_cases h : i < 336
      ·
        by_cases h : i < 320
        ·
          by_cases h : i < 304
          ·
            exact checkBlockW6_at g6_chk_7_18 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_19 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_20 i (by omega) (by omega)
      ·
        by_cases h : i < 352
        ·
          exact checkBlockW6_at g6_chk_7_21 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_22 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_0 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_1 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_2 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_3 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_4 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_5 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_8 : ∀ i < g6_L8.size, checkNodeW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 i = true := by
  intro i hi
  have hsz : g6_L8.size = 96 := by decide +kernel
  have hi' : i < 96 := hsz ▸ hi
  by_cases h : i < 48
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW6_at g6_chk_8_0 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_8_1 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_8_2 i (by omega) (by omega)
  ·
    by_cases h : i < 80
    ·
      by_cases h : i < 64
      ·
        exact checkBlockW6_at g6_chk_8_3 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_8_4 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_8_5 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_9_0 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 0 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_9 : ∀ i < g6_L9.size, checkNodeW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 i = true := by
  intro i hi
  have hsz : g6_L9.size = 9 := by decide +kernel
  exact checkBlockW6_at g6_chk_9_0 i (Nat.zero_le _) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_10_0 : checkBlockW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 10 g6_L10 g6_L9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_10 : ∀ i < g6_L10.size, checkNodeW6 goal6 2 g6_pow 26 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 10 g6_L10 g6_L9 i = true := by
  intro i hi
  have hsz : g6_L10.size = 1 := by decide +kernel
  exact checkBlockW6_at g6_chk_10_0 i (Nat.zero_le _) (by omega)

theorem g6_L3_sound : ∀ i < g6_L3.size, ¬ live (basicOps 64) goal6 3 (g6_L3[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound (fun j hj => by simp at hj) g6_chk_3

theorem g6_L4_sound : ∀ i < g6_L4.size, ¬ live (basicOps 64) goal6 4 (g6_L4[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L3_sound g6_chk_4

theorem g6_L5_sound : ∀ i < g6_L5.size, ¬ live (basicOps 64) goal6 5 (g6_L5[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L4_sound g6_chk_5

theorem g6_L6_sound : ∀ i < g6_L6.size, ¬ live (basicOps 64) goal6 6 (g6_L6[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L5_sound g6_chk_6

theorem g6_L7_sound : ∀ i < g6_L7.size, ¬ live (basicOps 64) goal6 7 (g6_L7[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L6_sound g6_chk_7

theorem g6_L8_sound : ∀ i < g6_L8.size, ¬ live (basicOps 64) goal6 8 (g6_L8[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L7_sound g6_chk_8

theorem g6_L9_sound : ∀ i < g6_L9.size, ¬ live (basicOps 64) goal6 9 (g6_L9[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L8_sound g6_chk_9

theorem g6_L10_sound : ∀ i < g6_L10.size, ¬ live (basicOps 64) goal6 10 (g6_L10[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound g6_L9_sound g6_chk_10

set_option maxRecDepth 100000 in

theorem g6_sublists : rows6.sublists.filter (fun ws => cover 64 jumps6 goal6 ws) = [rows6] := by decide +kernel

theorem g6_top_match : sameSet (rows6.map (actB 64 (g6_pow[0]?.getD []))) (g6_L10[0]?.getD ([], [], [], [])).1 = true := by decide +kernel

theorem g6_no_build : ¬ build (basicOps 64) goal6 10 rows6.toFinset :=

  no_build_of_top g6_G_valid (by decide) g6_sublists g6_top_match (g6_L10_sound 0 (by decide))

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev W6 := BitVec 64
abbrev basicOps6 (a b : W6) : Finset W6 := (ops 64 a b).toFinset

def holds (av : Finset W6) (z : W6) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W6} {z a : W6} (h : holds av z) : holds (insert a av) z := by
  rcases h with h | h | ⟨u, hu, he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u, Finset.mem_insert_of_mem hu, he⟩)

theorem holds_not {av : Finset W6} {z : W6} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl | rfl | ⟨a, ha, he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he | he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W6) (z : W6) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps6 a b, holds (insert w av) z

theorem reachable_not {av : Finset W6} {z : W6} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h | ⟨a, ha, b, hb, ne, w, hop, hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a, ha, b, hb, ne, w, hop, holds_not hw⟩

theorem and_reach {av : Finset W6} {x y : W6} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W6) := .inl rfl
  have oldx := hx
  rcases hx with rfl | rfl | ⟨a, ha, ea⟩
  · rw [show (0 : W6) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 64 &&& y); rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl | rfl | ⟨b, hb, eb⟩
  · rw [show x &&& (0 : W6) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64); rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a, ha, .inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a, ha, .inr rfl⟩))
  have add (w : W6) (hw : w ∈ basicOps6 a b) (z : W6) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a, ha, b, hb, h, w, hw, .inr (.inr ⟨w, Finset.mem_insert_self .., hz⟩)⟩
  rcases ea with ea | ea <;> rcases eb with eb | eb <;> rw [ea, eb]
  · exact add _ (by simp [basicOps6, ops] : a &&& b ∈ basicOps6 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps6, ops] : a &&& ~~~b ∈ basicOps6 a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps6, ops] : b &&& ~~~a ∈ basicOps6 a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps6, ops] : a ||| b ∈ basicOps6 a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W6} {x y : W6} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit6 (k : Fin 64) (z : W6) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit6 (w : List W6) (i : ℕ) (k : Fin 64) :
    (w.map (bit6 k)).getD i false = bit6 k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (Nat.le_of_not_gt h), bit6]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W6) (g : Gate) : W6 := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

theorem action_spec (w : List W6) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit6 k)) g = (w ++ [action w g]).map (bit6 k) := by
  obtain ⟨op, args⟩ := g; obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop; change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W6)[k.val] = false := by simp
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [step, List.map_cons, List.map_nil, read_bit6, List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.map_cons, List.map_nil, id_eq,
      Bool.and_true, Bool.or_false, bit6, BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not,
      bit0, Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W6} {w : List W6} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]; exact .inl rfl

theorem gate_reach (w : List W6) (av : Finset W6) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op, args⟩ := g; obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop; change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;> simp only [isBinary, Bool.false_eq_true, ite_false, ite_true,
    action, List.head?_nil, List.head?_cons, List.map_nil, List.map_cons, List.foldr_nil, List.foldr_cons,
    Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
    show ∀ x : W6, x ||| (0 : W6) = x from fun x => BitVec.or_zero,
    show ∀ x : W6, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W6) (av : Finset W6) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit6 k))).getD out false = bit6 k goal6) :
    ∃ t, (t = goal6 ∨ t = ~~~goal6) ∧ build basicOps6 t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal6 := by
      apply BitVec.eq_of_getElem_eq; intro i hi
      simpa only [List.foldl_nil, read_bit6, bit6] using he ⟨i, hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero | ones | ⟨t, ht, eq | eq⟩
    · exact False.elim ((by decide : goal6 ≠ 0) zero)
    · exact False.elim ((by decide : goal6 ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W6 => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit6 k))).getD out false = bit6 k goal6 := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W6) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg, Bool.false_eq_true, ite_false] at stepClass
      simpa [binaryCost, neg] using cont av hw stepClass
    · simp only [neg, ite_true] at stepClass
      have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, neg]
      rw [len]
      rcases stepClass with existing | ⟨a, ha, b, hb, ne, new, op, rep⟩
      · obtain ⟨t, ht, run⟩ := cont av hw existing
        exact ⟨t, ht, Or.inl run⟩
      · obtain ⟨t, ht, run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t, ht, Or.inr ⟨a, ha, b, hb, ne, new, op, run⟩⟩

def F (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808936 * 2 ^ 32 + 4008241384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
theorem sample6_ok : ∀ k : Fin 64, F (fun i => (rows6.getD i.val 0)[k.val]) = goal6[k.val] := by decide +kernel

def idxs64 : List ℕ := List.range 64
theorem idxs64_spec : idxs64.length = 64 ∧ ∀ idx ∈ idxs64, idx < 64 := by decide
theorem projS64_goal6 : projS 64 idxs64 goal6 = goal6 := by decide +kernel
theorem projS64_rows6_sub : rows6.all (fun w => projS 64 idxs64 w == 0 || rows6.contains (projS 64 idxs64 w)) = true := by decide +kernel

theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) :
    10 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ rows6, holds rows6.toFinset u := fun u hu =>
    .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (rows6.map (bit6 k))).getD o false = bit6 k goal6 := by
    let x (i : Fin 6) : Bool := bit6 k (rows6.getD i.val 0)
    have same : List.ofFn x = rows6.map (bit6 k) := by
      apply List.ext_getElem
      · simp [rows6]
      · intro i hi hj
        have hlt : i < rows6.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (rows6.map (bit6 k)) = bit6 k goal6
    rw [← same, he]
    exact sample6_ok k
  obtain ⟨t, ht, run⟩ := compile gs o hg rows6 rows6.toFinset init evaluate
  obtain ⟨s, hs, hl⟩ := compress (build_mono_k low run)
  have hpt : projS 64 idxs64 t = goal6 := by
    rcases ht with rfl | rfl
    · exact projS64_goal6
    · rw [projS_not 64 (by decide) idxs64 idxs64_spec.1 idxs64_spec.2]; exact projS64_goal6
  have hb64 := live_restrict (by decide : 0 < 64) idxs64 idxs64_spec.1 idxs64_spec.2
    (fun a b z hz => List.mem_toFinset.mp hz) hpt (by decide : goal6 ≠ 0) hl
  have hsub64 : nonZeroImg (projS 64 idxs64) s ⊆ rows6.toFinset := by
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hu
    obtain ⟨hne, v, hv, rfl⟩ := hu
    have h1 := List.all_eq_true.mp projS64_rows6_sub v (List.mem_toFinset.mp (hs hv))
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h1
    exact List.mem_toFinset.mpr (h1.resolve_left hne)
  exact g6_no_build (build_mono_k (Nat.sub_le _ _) (build_mono_av hsub64 hb64))

def wg : List Gate := [
  ⟨.and, [3, 4]⟩,
  ⟨.and, [4, 5]⟩,
  ⟨.and, [3, 5]⟩,
  ⟨.or, [8, 0]⟩,
  ⟨.or, [1, 0]⟩,
  ⟨.or, [7, 1]⟩,
  ⟨.and, [9, 11]⟩,
  ⟨.or, [6, 2]⟩,
  ⟨.and, [13, 10]⟩,
  ⟨.or, [10, 2]⟩,
  ⟨.or, [14, 12]⟩,
  ⟨.and, [15, 16]⟩
]

theorem wfits : Monotone2 ⟨wg, 17⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = F x := by
  decide +kernel

end PEqualNP.Outside.L_meta_40277_aux

open PEqualNP.Outside.L_meta_40277_aux in
theorem PEqualNP.Outside.L_meta_40277 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4008241384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4008241384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, hfan, hsz, hev⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have hleg : ∀ g ∈ C.gates, legal g := fun g hg => by
      have hf := hfan g hg
      refine ⟨?_, hf.2⟩
      simpa using hf.1
    have hb := bound C.gates C.output hleg hev
    have hclen : C.gates.length ≤ s := hsz
    have hl : (⟨wg, 17⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = 12 := rfl
    exact ⟨⟨wg, 17⟩, wfits, by omega, weval⟩
  · refine ⟨C, fun g hg => ⟨?_, (hfan g hg).2⟩, hsz, hev⟩
    have hf := (hfan g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf ⊢
    rcases hf with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
