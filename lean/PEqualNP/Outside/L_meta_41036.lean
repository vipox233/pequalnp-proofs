import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41036_aux

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

def goal6 : BitVec 64 := 0xfeeaeaeafee8e8a8

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

def b4_0_goal : BitVec 16 := 0xfee8
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
def b4_0_s6 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_0_p6 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_0_s7 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_0_p7 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_0_s8 : List ℕ := [0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15]
def b4_0_p8 : List ℕ := [1,4,16,64,2,8,32,128,256,1024,4096,16384,512,2048,8192,32768]
def b4_0_s9 : List ℕ := [0,2,4,6,8,10,12,14,1,3,5,7,9,11,13,15]
def b4_0_p9 : List ℕ := [1,4,16,64,256,1024,4096,16384,2,8,32,128,512,2048,8192,32768]
def b4_0_s10 : List ℕ := [0,2,8,10,1,3,9,11,4,6,12,14,5,7,13,15]
def b4_0_p10 : List ℕ := [1,4,256,1024,2,8,512,2048,16,64,4096,16384,32,128,8192,32768]
def b4_0_s11 : List ℕ := [0,2,8,10,4,6,12,14,1,3,9,11,5,7,13,15]
def b4_0_p11 : List ℕ := [1,4,256,1024,16,64,4096,16384,2,8,512,2048,32,128,8192,32768]
def b4_0_s12 : List ℕ := [0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15]
def b4_0_p12 : List ℕ := [1,16,2,32,4,64,8,128,256,4096,512,8192,1024,16384,2048,32768]
def b4_0_s13 : List ℕ := [0,4,1,5,8,12,9,13,2,6,3,7,10,14,11,15]
def b4_0_p13 : List ℕ := [1,16,2,32,256,4096,512,8192,4,64,8,128,1024,16384,2048,32768]
def b4_0_s14 : List ℕ := [0,4,2,6,1,5,3,7,8,12,10,14,9,13,11,15]
def b4_0_p14 : List ℕ := [1,16,4,64,2,32,8,128,256,4096,1024,16384,512,8192,2048,32768]
def b4_0_s15 : List ℕ := [0,4,2,6,8,12,10,14,1,5,3,7,9,13,11,15]
def b4_0_p15 : List ℕ := [1,16,4,64,256,4096,1024,16384,2,32,8,128,512,8192,2048,32768]
def b4_0_s16 : List ℕ := [0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15]
def b4_0_p16 : List ℕ := [1,16,256,4096,2,32,512,8192,4,64,1024,16384,8,128,2048,32768]
def b4_0_s17 : List ℕ := [0,4,8,12,2,6,10,14,1,5,9,13,3,7,11,15]
def b4_0_p17 : List ℕ := [1,16,256,4096,4,64,1024,16384,2,32,512,8192,8,128,2048,32768]
def b4_0_s18 : List ℕ := [0,8,1,9,2,10,3,11,4,12,5,13,6,14,7,15]
def b4_0_p18 : List ℕ := [1,256,2,512,4,1024,8,2048,16,4096,32,8192,64,16384,128,32768]
def b4_0_s19 : List ℕ := [0,8,1,9,4,12,5,13,2,10,3,11,6,14,7,15]
def b4_0_p19 : List ℕ := [1,256,2,512,16,4096,32,8192,4,1024,8,2048,64,16384,128,32768]
def b4_0_s20 : List ℕ := [0,8,2,10,1,9,3,11,4,12,6,14,5,13,7,15]
def b4_0_p20 : List ℕ := [1,256,4,1024,2,512,8,2048,16,4096,64,16384,32,8192,128,32768]
def b4_0_s21 : List ℕ := [0,8,2,10,4,12,6,14,1,9,3,11,5,13,7,15]
def b4_0_p21 : List ℕ := [1,256,4,1024,16,4096,64,16384,2,512,8,2048,32,8192,128,32768]
def b4_0_s22 : List ℕ := [0,8,4,12,1,9,5,13,2,10,6,14,3,11,7,15]
def b4_0_p22 : List ℕ := [1,256,16,4096,2,512,32,8192,4,1024,64,16384,8,2048,128,32768]
def b4_0_s23 : List ℕ := [0,8,4,12,2,10,6,14,1,9,5,13,3,11,7,15]
def b4_0_p23 : List ℕ := [1,256,16,4096,4,1024,64,16384,2,512,32,8192,8,2048,128,32768]
def b4_0_idx : Array (List ℕ) := Array.mk [b4_0_s0,b4_0_s1,b4_0_s2,b4_0_s3,b4_0_s4,b4_0_s5,b4_0_s6,b4_0_s7,b4_0_s8,b4_0_s9,b4_0_s10,b4_0_s11,b4_0_s12,b4_0_s13,b4_0_s14,b4_0_s15,b4_0_s16,b4_0_s17,b4_0_s18,b4_0_s19,b4_0_s20,b4_0_s21,b4_0_s22,b4_0_s23]
def b4_0_pow : Array (List ℕ) := Array.mk [b4_0_p0,b4_0_p1,b4_0_p2,b4_0_p3,b4_0_p4,b4_0_p5,b4_0_p6,b4_0_p7,b4_0_p8,b4_0_p9,b4_0_p10,b4_0_p11,b4_0_p12,b4_0_p13,b4_0_p14,b4_0_p15,b4_0_p16,b4_0_p17,b4_0_p18,b4_0_p19,b4_0_p20,b4_0_p21,b4_0_p22,b4_0_p23]
def b4_0_inv : Array ℕ := Array.mk [0,1,2,4,3,5,6,7,12,18,13,19,8,10,14,20,16,22,9,11,15,21,17,23]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_G_valid : (List.range 24).all (symValid 16 24 b4_0_idx b4_0_pow b4_0_inv b4_0_goal) = true := by decide +kernel
def b4_0_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xff0,0xaaaa,0xcccc],[]),
([0xaaaa,0xfccc,0xfff0],[]),
([0xeaea,0xfcfc,0xffc0],[]),
([0xaaa,0xfccc,0xfff0],[]),
([0xff0,0xaaaa,0xfccc],[]),
([0xaaaa,0xdccc,0xfff0],[]),
([0xaaaa,0xaff0,0xcccc],[]),
([0xaaa,0xff0,0xcccc],[]),
([0xaaaa,0xfcec,0xfff0],[])
]
def b4_0_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0x8888,0xeeee,0xf0f0,0xff00],[(16,0),(16,1),(17,1)]),
([0xaa,0xcccc,0xfaf0,0xff00],[(12,1)]),
([0xaa,0x5500,0xcccc,0xf0f0],[(12,0)]),
([0xaaa,0xcccc,0xf0f0,0xff00],[]),
([0xaaaa,0xcccc,0xf0f0,0xff80],[]),
([0x2aaa,0xcccc,0xf0f0,0xff00],[]),
([0xaaaa,0xfccc,0xfff0],[]),
([0xaaaa,0xcccc,0xfaf0,0xffaa],[]),
([0xaaaa,0xcccc,0xf8f8,0xff88],[(8,2)]),
([0xaaa,0xf0f0,0xfccc,0xff00],[(0,3)]),
([0x8888,0xeeee,0xf0f0,0xff88],[(8,2),(16,3),(16,4)]),
([0xaaaa,0xcccc,0xfaaa,0xfff0],[]),
([0xaaaa,0xcccc,0xf0f0,0xff08],[(16,5)]),
([0x8aaa,0xcccc,0xf0f0,0xff00],[]),
([0xaaaa,0xcccc,0xf0f0,0xff88],[(16,1)]),
([0x88,0xeeee,0xf0f0,0xff00],[(16,1),(17,5),(17,6)]),
([0xaaa,0xccc,0xf0f0,0xff00],[]),
([0xaaa,0xcccc,0xf000,0xfff0],[(0,3),(0,7),(6,1)]),
([0xff0,0xaaaa,0xcccc],[]),
([0xff0,0xaaaa,0xcccc,0xf000],[(0,4),(0,7),(6,4),(6,7)]),
([0xff0,0xaaaa,0xcccc,0xfff0],[]),
([0xff0,0xaaaa,0xcccc,0xf0f0],[]),
([0xaaaa,0xfcfc,0xffcc,0xfff0],[(0,1),(2,1),(3,1)]),
([0xa8a8,0xcccc,0xfafa,0xff00],[(13,8),(15,1)]),
([0xaaaa,0xcccc,0xf0f0,0xffa8],[(13,8),(16,8)]),
([0x2aa,0xcccc,0xf0f0,0xff00],[]),
([0xaaa8,0xcccc,0xf0f0,0xff00],[]),
([0xfe,0xaaaa,0xcccc,0xf0f0],[]),
([0xaa,0xcccc,0xdd00,0xf0f0],[(12,6)]),
([0xaa,0x55aa,0xcccc,0xf0f0],[])
]
def b4_0_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaa,0xaa00,0xcccc,0xf0f0,0xff00],[(0,0),(0,2),(0,3),(2,2),(3,1)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,3)]),
([0x8080,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,5),(3,4),(9,6),(13,4),(16,4)]),
([0xaaaa,0xcccc,0xf0f0,0xff88],[(4,2),(4,8),(16,7),(18,2),(18,8)]),
([0x8888,0xaaaa,0xcccc,0xf0f0,0xff88],[(0,9),(0,11),(4,2),(16,10),(17,4),(18,2)]),
([0xaaaa,0xcccc,0xeaea,0xf0f0,0xff00],[(3,12)]),
([0x88,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,15),(0,16),(1,13),(16,14)]),
([0xaaa,0xcccc,0xf0f0,0xff00],[]),
([0xaaa,0xcccc,0xf000,0xf0f0,0xff00],[(0,10),(0,17),(0,18),(22,15)]),
([0xaaa,0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0x8888,0xeeee,0xf0f0,0xff00],[(0,11),(0,16),(1,11),(1,16),(16,7),(16,12),(16,18),(16,19),(16,20),(16,21),(17,7),(17,12),(17,18)]),
([0x8888,0xaaaa,0xeeee,0xf0f0,0xff00],[(4,8),(5,8),(16,22)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(0,3),(3,1)]),
([0xaaaa,0xcccc,0xf0f0,0xffaa,0xffcc],[(0,15),(1,24),(7,24),(8,23)]),
([0xaa,0xcccc,0xeeee,0xf0f0,0xff00],[(0,16)]),
([0xa8a8,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,24),(0,25),(1,15),(2,24),(4,15),(21,26)]),
([0xaaaa,0xcccc,0xf0f0,0xfefe,0xff00],[(0,28),(9,27)]),
([0xee,0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0xa,0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,1),(0,15),(1,15),(16,4),(17,4)]),
([0xaaaa,0xaaee,0xcccc,0xf0f0,0xff00],[]),
([0x88aa,0xaaaa,0xcccc,0xf0f0,0xff00],[(17,4),(21,29)]),
([0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00],[(0,1)]),
([0xaa,0xa0a,0xcccc,0xf0f0,0xff00],[(0,4),(2,29),(3,29)]),
([0xaa,0x5500,0xcccc,0xf0f0],[(0,30),(12,19),(21,30)]),
([0xaa,0x5500,0xaaaa,0xcccc,0xf0f0],[(12,22)])
]
def b4_0_L5 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,2),(0,3),(0,4),(0,6),(0,10),(0,11),(1,2),(1,3),(1,4),(1,6),(4,0),(4,1),(6,11),(8,5),(9,5),(16,7),(16,8),(16,9),(17,7),(17,8),(17,9),(18,0),(18,1)]),
([0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00],[(0,10),(0,11),(0,14),(0,16),(0,17),(1,14),(1,16),(1,17),(4,1),(4,12),(4,13),(5,13),(6,11),(6,14),(7,14),(8,15),(9,15),(16,18),(17,18),(18,1),(18,12),(18,13),(19,13)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,6),(0,12),(0,14),(0,18),(0,23),(0,24),(0,25),(2,6),(2,14),(2,18),(2,23),(3,19),(3,22),(6,20),(8,20),(19,21),(21,25),(22,21)])
]
def b4_0_L6 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(3,0),(3,1),(4,2),(6,2),(7,2),(8,2),(9,2),(10,2),(11,2),(12,0),(12,1),(13,0),(13,1),(16,0),(16,1),(18,2),(20,2),(21,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_2_0 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 2 b4_0_L2 (Array.mk []) 0 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_2 : ∀ i < b4_0_L2.size, checkNodeP 16 jumps4 b4_0_goal 24 b4_0_pow 2 b4_0_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_0_L2.size = 9 := by decide +kernel
  exact checkBlockP_at b4_0_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_3_0 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 3 b4_0_L3 b4_0_L2 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_3_1 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 3 b4_0_L3 b4_0_L2 16 15 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_3 : ∀ i < b4_0_L3.size, checkNodeP 16 jumps4 b4_0_goal 24 b4_0_pow 3 b4_0_L3 b4_0_L2 i = true := by
  intro i hi
  have hsz : b4_0_L3.size = 31 := by decide +kernel
  have hi' : i < 31 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockP_at b4_0_chk_3_0 i (by omega) (by omega)
  ·
    exact checkBlockP_at b4_0_chk_3_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_4_0 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 4 b4_0_L4 b4_0_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_4_1 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 4 b4_0_L4 b4_0_L3 16 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_4 : ∀ i < b4_0_L4.size, checkNodeP 16 jumps4 b4_0_goal 24 b4_0_pow 4 b4_0_L4 b4_0_L3 i = true := by
  intro i hi
  have hsz : b4_0_L4.size = 26 := by decide +kernel
  have hi' : i < 26 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockP_at b4_0_chk_4_0 i (by omega) (by omega)
  ·
    exact checkBlockP_at b4_0_chk_4_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_5_0 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 5 b4_0_L5 b4_0_L4 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_5 : ∀ i < b4_0_L5.size, checkNodeP 16 jumps4 b4_0_goal 24 b4_0_pow 5 b4_0_L5 b4_0_L4 i = true := by
  intro i hi
  have hsz : b4_0_L5.size = 3 := by decide +kernel
  exact checkBlockP_at b4_0_chk_5_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_6_0 : checkBlockP 16 jumps4 b4_0_goal 24 b4_0_pow 6 b4_0_L6 b4_0_L5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_6 : ∀ i < b4_0_L6.size, checkNodeP 16 jumps4 b4_0_goal 24 b4_0_pow 6 b4_0_L6 b4_0_L5 i = true := by
  intro i hi
  have hsz : b4_0_L6.size = 1 := by decide +kernel
  exact checkBlockP_at b4_0_chk_6_0 i (Nat.zero_le _) (by omega)
theorem b4_0_L2_sound : ∀ i < b4_0_L2.size, ¬ live (basicOps 16) b4_0_goal 2 (b4_0_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid (fun j hj => by simp at hj) b4_0_chk_2
theorem b4_0_L3_sound : ∀ i < b4_0_L3.size, ¬ live (basicOps 16) b4_0_goal 3 (b4_0_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L2_sound b4_0_chk_3
theorem b4_0_L4_sound : ∀ i < b4_0_L4.size, ¬ live (basicOps 16) b4_0_goal 4 (b4_0_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L3_sound b4_0_chk_4
theorem b4_0_L5_sound : ∀ i < b4_0_L5.size, ¬ live (basicOps 16) b4_0_goal 5 (b4_0_L5[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L4_sound b4_0_chk_5
theorem b4_0_L6_sound : ∀ i < b4_0_L6.size, ¬ live (basicOps 16) b4_0_goal 6 (b4_0_L6[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L5_sound b4_0_chk_6
set_option maxRecDepth 100000 in
theorem b4_0_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_0_goal ws) = [rows4] := by decide +kernel
theorem b4_0_top_match : sameSet (rows4.map (actB 16 (b4_0_pow[0]?.getD []))) (b4_0_L6[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_0_no_build : ¬ build (basicOps 16) b4_0_goal 6 rows4.toFinset :=
  no_build_of_top b4_0_G_valid (by decide) b4_0_sublists b4_0_top_match (b4_0_L6_sound 0 (by decide))

def b4_1_goal : BitVec 16 := 0xe880
def b4_1_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_1_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_1_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_1_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_1_s2 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_1_p2 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_1_s3 : List ℕ := [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15]
def b4_1_p3 : List ℕ := [1,2,16,32,256,512,4096,8192,4,8,64,128,1024,2048,16384,32768]
def b4_1_s4 : List ℕ := [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15]
def b4_1_p4 : List ℕ := [1,2,256,512,4,8,1024,2048,16,32,4096,8192,64,128,16384,32768]
def b4_1_s5 : List ℕ := [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15]
def b4_1_p5 : List ℕ := [1,2,256,512,16,32,4096,8192,4,8,1024,2048,64,128,16384,32768]
def b4_1_s6 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_1_p6 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_1_s7 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_1_p7 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_1_s8 : List ℕ := [0,2,4,6,1,3,5,7,8,10,12,14,9,11,13,15]
def b4_1_p8 : List ℕ := [1,4,16,64,2,8,32,128,256,1024,4096,16384,512,2048,8192,32768]
def b4_1_s9 : List ℕ := [0,2,4,6,8,10,12,14,1,3,5,7,9,11,13,15]
def b4_1_p9 : List ℕ := [1,4,16,64,256,1024,4096,16384,2,8,32,128,512,2048,8192,32768]
def b4_1_s10 : List ℕ := [0,2,8,10,1,3,9,11,4,6,12,14,5,7,13,15]
def b4_1_p10 : List ℕ := [1,4,256,1024,2,8,512,2048,16,64,4096,16384,32,128,8192,32768]
def b4_1_s11 : List ℕ := [0,2,8,10,4,6,12,14,1,3,9,11,5,7,13,15]
def b4_1_p11 : List ℕ := [1,4,256,1024,16,64,4096,16384,2,8,512,2048,32,128,8192,32768]
def b4_1_s12 : List ℕ := [0,4,1,5,2,6,3,7,8,12,9,13,10,14,11,15]
def b4_1_p12 : List ℕ := [1,16,2,32,4,64,8,128,256,4096,512,8192,1024,16384,2048,32768]
def b4_1_s13 : List ℕ := [0,4,1,5,8,12,9,13,2,6,3,7,10,14,11,15]
def b4_1_p13 : List ℕ := [1,16,2,32,256,4096,512,8192,4,64,8,128,1024,16384,2048,32768]
def b4_1_s14 : List ℕ := [0,4,2,6,1,5,3,7,8,12,10,14,9,13,11,15]
def b4_1_p14 : List ℕ := [1,16,4,64,2,32,8,128,256,4096,1024,16384,512,8192,2048,32768]
def b4_1_s15 : List ℕ := [0,4,2,6,8,12,10,14,1,5,3,7,9,13,11,15]
def b4_1_p15 : List ℕ := [1,16,4,64,256,4096,1024,16384,2,32,8,128,512,8192,2048,32768]
def b4_1_s16 : List ℕ := [0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15]
def b4_1_p16 : List ℕ := [1,16,256,4096,2,32,512,8192,4,64,1024,16384,8,128,2048,32768]
def b4_1_s17 : List ℕ := [0,4,8,12,2,6,10,14,1,5,9,13,3,7,11,15]
def b4_1_p17 : List ℕ := [1,16,256,4096,4,64,1024,16384,2,32,512,8192,8,128,2048,32768]
def b4_1_s18 : List ℕ := [0,8,1,9,2,10,3,11,4,12,5,13,6,14,7,15]
def b4_1_p18 : List ℕ := [1,256,2,512,4,1024,8,2048,16,4096,32,8192,64,16384,128,32768]
def b4_1_s19 : List ℕ := [0,8,1,9,4,12,5,13,2,10,3,11,6,14,7,15]
def b4_1_p19 : List ℕ := [1,256,2,512,16,4096,32,8192,4,1024,8,2048,64,16384,128,32768]
def b4_1_s20 : List ℕ := [0,8,2,10,1,9,3,11,4,12,6,14,5,13,7,15]
def b4_1_p20 : List ℕ := [1,256,4,1024,2,512,8,2048,16,4096,64,16384,32,8192,128,32768]
def b4_1_s21 : List ℕ := [0,8,2,10,4,12,6,14,1,9,3,11,5,13,7,15]
def b4_1_p21 : List ℕ := [1,256,4,1024,16,4096,64,16384,2,512,8,2048,32,8192,128,32768]
def b4_1_s22 : List ℕ := [0,8,4,12,1,9,5,13,2,10,6,14,3,11,7,15]
def b4_1_p22 : List ℕ := [1,256,16,4096,2,512,32,8192,4,1024,64,16384,8,2048,128,32768]
def b4_1_s23 : List ℕ := [0,8,4,12,2,10,6,14,1,9,5,13,3,11,7,15]
def b4_1_p23 : List ℕ := [1,256,16,4096,4,1024,64,16384,2,512,32,8192,8,2048,128,32768]
def b4_1_idx : Array (List ℕ) := Array.mk [b4_1_s0,b4_1_s1,b4_1_s2,b4_1_s3,b4_1_s4,b4_1_s5,b4_1_s6,b4_1_s7,b4_1_s8,b4_1_s9,b4_1_s10,b4_1_s11,b4_1_s12,b4_1_s13,b4_1_s14,b4_1_s15,b4_1_s16,b4_1_s17,b4_1_s18,b4_1_s19,b4_1_s20,b4_1_s21,b4_1_s22,b4_1_s23]
def b4_1_pow : Array (List ℕ) := Array.mk [b4_1_p0,b4_1_p1,b4_1_p2,b4_1_p3,b4_1_p4,b4_1_p5,b4_1_p6,b4_1_p7,b4_1_p8,b4_1_p9,b4_1_p10,b4_1_p11,b4_1_p12,b4_1_p13,b4_1_p14,b4_1_p15,b4_1_p16,b4_1_p17,b4_1_p18,b4_1_p19,b4_1_p20,b4_1_p21,b4_1_p22,b4_1_p23]
def b4_1_inv : Array ℕ := Array.mk [0,1,2,4,3,5,6,7,12,18,13,19,8,10,14,20,16,22,9,11,15,21,17,23]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_G_valid : (List.range 24).all (symValid 16 24 b4_1_idx b4_1_pow b4_1_inv b4_1_goal) = true := by decide +kernel
def b4_1_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xff0,0xaaaa,0xcccc],[]),
([0x8888,0xe0e0,0xff00],[]),
([0x8888,0xe0a0,0xff00],[]),
([0xff0,0xaaa0,0xcccc],[]),
([0xee,0x6666,0xf0f0],[]),
([0x8888,0xe0e0,0xee00],[]),
([0xee,0x8888,0xe0e0],[]),
([0x8888,0xe0f0,0xff00],[]),
([0x9898,0xf0f0,0xff00],[])
]
def b4_1_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0x8888,0xeeee,0xf0f0,0xff00],[(0,1),(1,1),(16,0)]),
([0xaa,0x5500,0xcccc,0xf0f0],[(12,0)]),
([0xaaaa,0xcccc,0xf0f0,0xff80],[]),
([0x2aaa,0xcccc,0xf0f0,0xff00],[]),
([0x8888,0xeaea,0xf0f0,0xff00],[(0,1),(1,2)]),
([0xa8a8,0xcccc,0xf0f0,0xff00],[(12,1)]),
([0xa888,0xcccc,0xf0f0,0xff00],[(12,2),(13,2)]),
([0xea,0xaaaa,0xcccc,0xf0f0],[]),
([0xff0,0xaaaa,0xcccc],[]),
([0xff0,0xaaaa,0xcccc,0xf000],[]),
([0xff0,0xaaaa,0xcccc,0xfff0],[(0,3),(6,3),(16,4),(22,4)]),
([0x8888,0xe0e0,0xff00],[]),
([0x8888,0xe0e0,0xeeee,0xff00],[(0,5),(0,6)]),
([0x8888,0xe0e0,0xf0f0,0xff00],[]),
([0xee,0x8888,0xeeee,0xf0f0],[(0,4),(0,6),(1,1)]),
([0xa,0xaaaa,0xcccc,0xf000],[(16,1),(16,8),(22,7)]),
([0xff0,0xaaaa,0xcccc,0xf0f0],[]),
([0x8888,0xaaaa,0xe0e0,0xff00],[]),
([0x8888,0xa0a0,0xc0c0,0xff00],[(0,1),(2,1),(12,1)]),
([0xaa,0xaaaa,0xcc88,0xf0f0],[(3,1)]),
([0xee,0xaaaa,0xcccc,0xf0f0],[]),
([0xa8a8,0xcccc,0xf0f0,0xfc00],[(12,5)]),
([0xee,0xaaaa,0xcccc,0xe0e0],[(0,6)]),
([0xaaa8,0xcccc,0xf0f0,0xff00],[]),
([0xfe,0xaaaa,0xcccc,0xf0f0],[]),
([0xee,0xe0e,0xaaaa,0xcccc],[]),
([0xaaaa,0xcccc,0xf0f0,0xff02],[]),
([0xa8aa,0xcccc,0xf0f0,0xff00],[(12,7)]),
([0xaa,0xaaee,0xcccc,0xf0f0],[(3,8)]),
([0xaa,0x55aa,0xcccc,0xf0f0],[])
]
def b4_1_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaa,0xaa00,0xcccc,0xf0f0,0xff00],[(0,0),(0,2),(3,1)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,2)]),
([0x8080,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,3),(9,4)]),
([0xaaaa,0xcccc,0xeaea,0xf0f0,0xff00],[(0,5),(0,8),(2,5),(6,6),(8,6),(9,7)]),
([0x88,0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0xaaa,0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0x8888,0xeeee,0xf0f0,0xff00],[(0,12),(0,13),(0,14),(0,15),(1,12),(1,13),(1,14),(1,15),(16,9),(16,10),(16,11),(16,16),(17,16)]),
([0x8888,0xaaaa,0xeeee,0xf0f0,0xff00],[(0,18),(1,18),(16,17)]),
([0x8888,0xa0a0,0xcccc,0xf0f0,0xff00],[(0,6),(0,19),(6,5),(8,5)]),
([0xaa,0xaaaa,0xcc00,0xcccc,0xf0f0],[(2,16)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(0,2),(0,20),(2,20),(3,1)]),
([0xa8a8,0xcccc,0xf0f0,0xff00],[(7,20),(10,20),(12,12),(12,18),(14,18)]),
([0xa8a8,0xcccc,0xf0f0,0xfcfc,0xff00],[(0,22),(7,20),(10,20),(12,13),(12,23),(18,21)]),
([0xa8a8,0xaaaa,0xcccc,0xf0f0,0xff00],[(12,14)]),
([0xaaaa,0xcccc,0xf0f0,0xfefe,0xff00],[(0,25),(1,21),(4,21),(9,24),(18,21)]),
([0xee,0xaaaa,0xcccc,0xf0f0],[]),
([0xee,0xaaaa,0xcccc,0xeeee,0xf0f0],[(0,15),(0,23),(0,26),(9,6)]),
([0xee,0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0xa,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,16),(4,6),(4,27),(18,28)]),
([0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,1)]),
([0xaaaa,0xaaee,0xcccc,0xf0f0,0xff00],[(0,21),(0,29)]),
([0x88aa,0xaaaa,0xcccc,0xf0f0,0xff00],[]),
([0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00],[(0,1),(0,21),(1,21),(8,6),(9,6)]),
([0xaa,0x5500,0xcccc,0xf0f0],[(0,30),(12,9),(21,30)]),
([0xaa,0x5500,0xaaaa,0xcccc,0xf0f0],[(12,17)]),
([0xaa,0xcc,0xaaaa,0xcccc,0xf0f0],[(0,21),(0,29),(6,29)])
]
def b4_1_L5 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,2),(0,4),(0,6),(0,7),(0,8),(1,2),(1,4),(1,8),(4,0),(4,1),(6,7),(6,8),(7,8),(8,3),(9,3),(10,9),(11,9),(16,5),(17,5),(18,0),(18,1),(20,9),(21,9)]),
([0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00],[(0,6),(0,7),(0,14),(0,15),(0,16),(0,17),(1,14),(1,15),(1,16),(1,17),(4,1),(4,10),(6,7),(8,11),(8,12),(8,13),(9,11),(9,12),(9,13),(16,18),(17,18),(18,1),(18,10)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,4),(0,9),(0,10),(0,18),(0,23),(0,24),(0,25),(2,4),(2,9),(2,18),(2,25),(3,19),(3,22),(6,20),(8,20),(19,21),(21,24),(22,21)])
]
def b4_1_L6 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,2),(2,0),(2,1),(3,0),(3,1),(4,2),(6,2),(7,2),(8,2),(9,2),(10,2),(11,2),(12,0),(12,1),(13,0),(13,1),(16,0),(16,1),(18,2),(20,2),(21,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_2_0 : checkBlockP 16 jumps4 b4_1_goal 24 b4_1_pow 2 b4_1_L2 (Array.mk []) 0 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_2 : ∀ i < b4_1_L2.size, checkNodeP 16 jumps4 b4_1_goal 24 b4_1_pow 2 b4_1_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_1_L2.size = 9 := by decide +kernel
  exact checkBlockP_at b4_1_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_3_0 : checkBlockP 16 jumps4 b4_1_goal 24 b4_1_pow 3 b4_1_L3 b4_1_L2 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_3_1 : checkBlockP 16 jumps4 b4_1_goal 24 b4_1_pow 3 b4_1_L3 b4_1_L2 16 15 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_3 : ∀ i < b4_1_L3.size, checkNodeP 16 jumps4 b4_1_goal 24 b4_1_pow 3 b4_1_L3 b4_1_L2 i = true := by
  intro i hi
  have hsz : b4_1_L3.size = 31 := by decide +kernel
  have hi' : i < 31 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockP_at b4_1_chk_3_0 i (by omega) (by omega)
  ·
    exact checkBlockP_at b4_1_chk_3_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_4_0 : checkBlockP 16 jumps4 b4_1_goal 24 b4_1_pow 4 b4_1_L4 b4_1_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_4_1 : checkBlockP 16 jumps4 b4_1_goal 24 b4_1_pow 4 b4_1_L4 b4_1_L3 16 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_4 : ∀ i < b4_1_L4.size, checkNodeP 16 jumps4 b4_1_goal 24 b4_1_pow 4 b4_1_L4 b4_1_L3 i = true := by
  intro i hi
  have hsz : b4_1_L4.size = 26 := by decide +kernel
  have hi' : i < 26 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockP_at b4_1_chk_4_0 i (by omega) (by omega)
  ·
    exact checkBlockP_at b4_1_chk_4_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_5_0 : checkBlockP 16 jumps4 b4_1_goal 24 b4_1_pow 5 b4_1_L5 b4_1_L4 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_5 : ∀ i < b4_1_L5.size, checkNodeP 16 jumps4 b4_1_goal 24 b4_1_pow 5 b4_1_L5 b4_1_L4 i = true := by
  intro i hi
  have hsz : b4_1_L5.size = 3 := by decide +kernel
  exact checkBlockP_at b4_1_chk_5_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_6_0 : checkBlockP 16 jumps4 b4_1_goal 24 b4_1_pow 6 b4_1_L6 b4_1_L5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_6 : ∀ i < b4_1_L6.size, checkNodeP 16 jumps4 b4_1_goal 24 b4_1_pow 6 b4_1_L6 b4_1_L5 i = true := by
  intro i hi
  have hsz : b4_1_L6.size = 1 := by decide +kernel
  exact checkBlockP_at b4_1_chk_6_0 i (Nat.zero_le _) (by omega)
theorem b4_1_L2_sound : ∀ i < b4_1_L2.size, ¬ live (basicOps 16) b4_1_goal 2 (b4_1_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid (fun j hj => by simp at hj) b4_1_chk_2
theorem b4_1_L3_sound : ∀ i < b4_1_L3.size, ¬ live (basicOps 16) b4_1_goal 3 (b4_1_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L2_sound b4_1_chk_3
theorem b4_1_L4_sound : ∀ i < b4_1_L4.size, ¬ live (basicOps 16) b4_1_goal 4 (b4_1_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L3_sound b4_1_chk_4
theorem b4_1_L5_sound : ∀ i < b4_1_L5.size, ¬ live (basicOps 16) b4_1_goal 5 (b4_1_L5[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L4_sound b4_1_chk_5
theorem b4_1_L6_sound : ∀ i < b4_1_L6.size, ¬ live (basicOps 16) b4_1_goal 6 (b4_1_L6[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L5_sound b4_1_chk_6
set_option maxRecDepth 100000 in
theorem b4_1_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_1_goal ws) = [rows4] := by decide +kernel
theorem b4_1_top_match : sameSet (rows4.map (actB 16 (b4_1_pow[0]?.getD []))) (b4_1_L6[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_1_no_build : ¬ build (basicOps 16) b4_1_goal 6 rows4.toFinset :=
  no_build_of_top b4_1_G_valid (by decide) b4_1_sublists b4_1_top_match (b4_1_L6_sound 0 (by decide))

def b4_2_goal : BitVec 16 := 0xe888
def b4_2_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_2_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_2_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_2_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_2_s2 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_2_p2 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_2_s3 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_2_p3 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_2_idx : Array (List ℕ) := Array.mk [b4_2_s0,b4_2_s1,b4_2_s2,b4_2_s3]
def b4_2_pow : Array (List ℕ) := Array.mk [b4_2_p0,b4_2_p1,b4_2_p2,b4_2_p3]
def b4_2_inv : Array ℕ := Array.mk [0,1,2,3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_G_valid : (List.range 4).all (symValid 16 4 b4_2_idx b4_2_pow b4_2_inv b4_2_goal) = true := by decide +kernel
def b4_2_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf000],[])
]
def b4_2_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf000],[]),
([0xaaaa,0xcccc,0xf000,0xf0f0],[]),
([0xf0,0xaaaa,0xcccc,0xf0f0],[(0,0)])
]
def b4_2_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,1),(1,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_2_0 : checkBlockP 16 jumps4 b4_2_goal 4 b4_2_pow 2 b4_2_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_2 : ∀ i < b4_2_L2.size, checkNodeP 16 jumps4 b4_2_goal 4 b4_2_pow 2 b4_2_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_2_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_2_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_3_0 : checkBlockP 16 jumps4 b4_2_goal 4 b4_2_pow 3 b4_2_L3 b4_2_L2 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_3 : ∀ i < b4_2_L3.size, checkNodeP 16 jumps4 b4_2_goal 4 b4_2_pow 3 b4_2_L3 b4_2_L2 i = true := by
  intro i hi
  have hsz : b4_2_L3.size = 3 := by decide +kernel
  exact checkBlockP_at b4_2_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_2_chk_4_0 : checkBlockP 16 jumps4 b4_2_goal 4 b4_2_pow 4 b4_2_L4 b4_2_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_2_chk_4 : ∀ i < b4_2_L4.size, checkNodeP 16 jumps4 b4_2_goal 4 b4_2_pow 4 b4_2_L4 b4_2_L3 i = true := by
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

def b4_3_goal : BitVec 16 := 0xe8a8
def b4_3_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_3_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_3_s1 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_3_p1 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_3_idx : Array (List ℕ) := Array.mk [b4_3_s0,b4_3_s1]
def b4_3_pow : Array (List ℕ) := Array.mk [b4_3_p0,b4_3_p1]
def b4_3_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_G_valid : (List.range 2).all (symValid 16 2 b4_3_idx b4_3_pow b4_3_inv b4_3_goal) = true := by decide +kernel
def b4_3_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcc88,0xf0f0],[]),
([0xaaaa,0xcc0c,0xf0f0],[])
]
def b4_3_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(1,0)]),
([0x5500,0xaaaa,0xcccc,0xf0f0],[]),
([0xaaaa,0xcc00,0xcccc,0xf0f0],[]),
([0xcc,0xaaaa,0xcccc,0xf0f0],[(1,1)])
]
def b4_3_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(0,3),(1,2),(1,3)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_2_0 : checkBlockP 16 jumps4 b4_3_goal 2 b4_3_pow 2 b4_3_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_2 : ∀ i < b4_3_L2.size, checkNodeP 16 jumps4 b4_3_goal 2 b4_3_pow 2 b4_3_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_3_L2.size = 2 := by decide +kernel
  exact checkBlockP_at b4_3_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_3_0 : checkBlockP 16 jumps4 b4_3_goal 2 b4_3_pow 3 b4_3_L3 b4_3_L2 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_3 : ∀ i < b4_3_L3.size, checkNodeP 16 jumps4 b4_3_goal 2 b4_3_pow 3 b4_3_L3 b4_3_L2 i = true := by
  intro i hi
  have hsz : b4_3_L3.size = 4 := by decide +kernel
  exact checkBlockP_at b4_3_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_4_0 : checkBlockP 16 jumps4 b4_3_goal 2 b4_3_pow 4 b4_3_L4 b4_3_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_4 : ∀ i < b4_3_L4.size, checkNodeP 16 jumps4 b4_3_goal 2 b4_3_pow 4 b4_3_L4 b4_3_L3 i = true := by
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

def b4_4_goal : BitVec 16 := 0xfeea
def b4_4_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_4_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_4_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_4_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_4_s2 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_4_p2 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_4_s3 : List ℕ := [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15]
def b4_4_p3 : List ℕ := [1,2,16,32,256,512,4096,8192,4,8,64,128,1024,2048,16384,32768]
def b4_4_s4 : List ℕ := [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15]
def b4_4_p4 : List ℕ := [1,2,256,512,4,8,1024,2048,16,32,4096,8192,64,128,16384,32768]
def b4_4_s5 : List ℕ := [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15]
def b4_4_p5 : List ℕ := [1,2,256,512,16,32,4096,8192,4,8,1024,2048,64,128,16384,32768]
def b4_4_idx : Array (List ℕ) := Array.mk [b4_4_s0,b4_4_s1,b4_4_s2,b4_4_s3,b4_4_s4,b4_4_s5]
def b4_4_pow : Array (List ℕ) := Array.mk [b4_4_p0,b4_4_p1,b4_4_p2,b4_4_p3,b4_4_p4,b4_4_p5]
def b4_4_inv : Array ℕ := Array.mk [0,1,2,4,3,5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_G_valid : (List.range 6).all (symValid 16 6 b4_4_idx b4_4_pow b4_4_inv b4_4_goal) = true := by decide +kernel
def b4_4_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xcccc,0xfafa,0xffaa],[])
]
def b4_4_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(2,0)]),
([0x4444,0xaaaa,0xf0f0,0xff00],[])
]
def b4_4_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(1,0),(2,1),(3,1),(4,0)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_2_0 : checkBlockP 16 jumps4 b4_4_goal 6 b4_4_pow 2 b4_4_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_2 : ∀ i < b4_4_L2.size, checkNodeP 16 jumps4 b4_4_goal 6 b4_4_pow 2 b4_4_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_4_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_4_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_3_0 : checkBlockP 16 jumps4 b4_4_goal 6 b4_4_pow 3 b4_4_L3 b4_4_L2 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_3 : ∀ i < b4_4_L3.size, checkNodeP 16 jumps4 b4_4_goal 6 b4_4_pow 3 b4_4_L3 b4_4_L2 i = true := by
  intro i hi
  have hsz : b4_4_L3.size = 2 := by decide +kernel
  exact checkBlockP_at b4_4_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_4_chk_4_0 : checkBlockP 16 jumps4 b4_4_goal 6 b4_4_pow 4 b4_4_L4 b4_4_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_4_chk_4 : ∀ i < b4_4_L4.size, checkNodeP 16 jumps4 b4_4_goal 6 b4_4_pow 4 b4_4_L4 b4_4_L3 i = true := by
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

def u0 : BitVec 32 := 0xcccccccc
def u1 : BitVec 32 := 0xf0f0f0f0
def u2 : BitVec 32 := 0xff00ff00
def u3 : BitVec 32 := 0xaaaaaaaa
def u4 : BitVec 32 := 0xffff0000
def u5 : BitVec 32 := 0xfcfcfcfc
def u6 : BitVec 32 := 0xff000000
def u7 : BitVec 32 := 0xc0c0c0c0
def u8 : BitVec 32 := 0xc0c0c0c
def u9 : BitVec 32 := 0x3c3c3c3c
def u10 : BitVec 32 := 0x55005500
def u11 : BitVec 32 := 0xf000f00
def u12 : BitVec 32 := 0xeeeeeeee
def u13 : BitVec 32 := 0x44444444
def u14 : BitVec 32 := 0xcc00cc00
def u15 : BitVec 32 := 0xfafafafa
def u16 : BitVec 32 := 0x30303030
def u17 : BitVec 32 := 0xf0f00000
def u18 : BitVec 32 := 0xf000f000
def u19 : BitVec 32 := 0x55550000
def u20 : BitVec 32 := 0xeaeaeaea
def u21 : BitVec 32 := 0xffaaaaaa
def u22 : BitVec 32 := 0x50505050
def u23 : BitVec 32 := 0x54545454
def u24 : BitVec 32 := 0xcccc0000
def u25 : BitVec 32 := 0xfc00fc00
def u26 : BitVec 32 := 0xcccccc
def u27 : BitVec 32 := 0xaeaeaeae
def u28 : BitVec 32 := 0x3f003f00
def u29 : BitVec 32 := 0x33330000
def u30 : BitVec 32 := 0xffcccccc
def u31 : BitVec 32 := 0xafaaafaa
def u32 : BitVec 32 := 0xeeaaeeaa
def u33 : BitVec 32 := 0xc0ccccc
def u34 : BitVec 32 := 0xfaaafaaa
def u35 : BitVec 32 := 0xf0f0000
def u36 : BitVec 32 := 0xcf00cf00
def u37 : BitVec 32 := 0xfff0f0f0
def u38 : BitVec 32 := 0xfafaaaaa
def u39 : BitVec 32 := 0xc8c8c8c8
def u40 : BitVec 32 := 0xe0e0e0e
def u41 : BitVec 32 := 0x14141414
def u42 : BitVec 32 := 0xbebebebe
def u43 : BitVec 32 := 0xee00ee00
def u44 : BitVec 32 := 0xf00ff00
def u45 : BitVec 32 := 0xffc0c0c0
def u46 : BitVec 32 := 0xc300c300
def u47 : BitVec 32 := 0x33003300
def u48 : BitVec 32 := 0x8888cccc
def u49 : BitVec 32 := 0x3c003c00
def u50 : BitVec 32 := 0xfcccfccc
def u51 : BitVec 32 := 0xf300f300
def u52 : BitVec 32 := 0xcfcccfcc
def u53 : BitVec 32 := 0x40404040
def u54 : BitVec 32 := 0xaa00ff00
def u55 : BitVec 32 := 0xcc00ff00
def u56 : BitVec 32 := 0xddccddcc
def u57 : BitVec 32 := 0xbabababa
def u58 : BitVec 32 := 0xfa00fa00
def u59 : BitVec 32 := 0xcc000000
def u60 : BitVec 32 := 0x8c8c8c8c
def u61 : BitVec 32 := 0xaf00af00
def u62 : BitVec 32 := 0xfcfcfc
def u63 : BitVec 32 := 0xc0c0cccc
def u64 : BitVec 32 := 0xdcdcdcdc
def u65 : BitVec 32 := 0x55000000
def u66 : BitVec 32 := 0x3f3f0000
def u67 : BitVec 32 := 0xfcf0fcf0
def u68 : BitVec 32 := 0xe0e0e0e0
def u69 : BitVec 32 := 0xf0f0f0
def u70 : BitVec 32 := 0xb0b0b0b0
def u71 : BitVec 32 := 0xeeeeee
def u72 : BitVec 32 := 0xff0c0c0c
def u73 : BitVec 32 := 0xcc888888
def u74 : BitVec 32 := 0xeeeeaaaa
def u75 : BitVec 32 := 0xa8a8fcfc
def u76 : BitVec 32 := 0xfefefefe
def u77 : BitVec 32 := 0xf0000000
def u78 : BitVec 32 := 0xbb00bb00
def u79 : BitVec 32 := 0xeeee0000
def u80 : BitVec 32 := 0x5d0c5d0c
def u81 : BitVec 32 := 0xfeaafeaa
def u82 : BitVec 32 := 0xc888c888
def u83 : BitVec 32 := 0xf000000
def u84 : BitVec 32 := 0xbcbcbcbc
def u85 : BitVec 32 := 0xbfaabfaa
def u86 : BitVec 32 := 0xea00ea00
def u87 : BitVec 32 := 0x5005500
def u88 : BitVec 32 := 0xff444444
def u89 : BitVec 32 := 0xeeaaaaaa
def u90 : BitVec 32 := 0xa0f0a0f0
def u91 : BitVec 32 := 0xc0c00000
def u92 : BitVec 32 := 0xfcfc0000
def u93 : BitVec 32 := 0xcfcf0000
def u94 : BitVec 32 := 0xf0ff0000
def u95 : BitVec 32 := 0xd5c0d5c0
def u96 : BitVec 32 := 0x15001500
def u97 : BitVec 32 := 0xab00ab00
def u98 : BitVec 32 := 0xc0cfcfc
def u99 : BitVec 32 := 0xe0eeeee
def u100 : BitVec 32 := 0xffeeeeee
def u101 : BitVec 32 := 0xbbaabbaa
def u102 : BitVec 32 := 0xefeeefee
def u103 : BitVec 32 := 0xfafa0000
def u104 : BitVec 32 := 0xc8c8fafa
def u105 : BitVec 32 := 0x54005400
def u106 : BitVec 32 := 0xafaaffaa
def u107 : BitVec 32 := 0xfefafefa
def u108 : BitVec 32 := 0xafaf0000
def u109 : BitVec 32 := 0xddddcccc
def u110 : BitVec 32 := 0xdd55cc00
def u111 : BitVec 32 := 0xc000c000
def u112 : BitVec 32 := 0xeaeaaaaa
def u113 : BitVec 32 := 0xaaeeeeee
def u114 : BitVec 32 := 0xaeaeeeee
def u115 : BitVec 32 := 0xfcccf000
def u116 : BitVec 32 := 0xf5f5f0f0
def u117 : BitVec 32 := 0xfcfccccc
def u118 : BitVec 32 := 0xc0ccc0cc
def u119 : BitVec 32 := 0xcacacaca
def u120 : BitVec 32 := 0xfaaaaaaa
def u121 : BitVec 32 := 0x3f000000
def u122 : BitVec 32 := 0xdc50dc50
def u123 : BitVec 32 := 0xfbaafbaa
def u124 : BitVec 32 := 0x4f444f44
def u125 : BitVec 32 := 0xacacacac
def u126 : BitVec 32 := 0x55444444
def u127 : BitVec 32 := 0x8c888c88

def c5_0_goal : BitVec 32 := 0xfee8e8a8
def c5_0_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_0_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_0_s1 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
def c5_0_p1 : List ℕ := [1,2,4,8,16,32,64,128,65536,131072,262144,524288,1048576,2097152,4194304,8388608,256,512,1024,2048,4096,8192,16384,32768,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_0_s2 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31]
def c5_0_p2 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768,65536,131072,1048576,2097152,262144,524288,4194304,8388608,16777216,33554432,268435456,536870912,67108864,134217728,1073741824,2147483648]
def c5_0_s3 : List ℕ := [0,1,4,5,2,3,6,7,16,17,20,21,18,19,22,23,8,9,12,13,10,11,14,15,24,25,28,29,26,27,30,31]
def c5_0_p3 : List ℕ := [1,2,16,32,4,8,64,128,65536,131072,1048576,2097152,262144,524288,4194304,8388608,256,512,4096,8192,1024,2048,16384,32768,16777216,33554432,268435456,536870912,67108864,134217728,1073741824,2147483648]
def c5_0_idx : Array (List ℕ) := Array.mk [c5_0_s0,c5_0_s1,c5_0_s2,c5_0_s3]
def c5_0_pow : Array (List ℕ) := Array.mk [c5_0_p0,c5_0_p1,c5_0_p2,c5_0_p3]
def c5_0_inv : Array ℕ := Array.mk [0,1,2,3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_G_valid : (List.range 4).all (symValid 32 4 c5_0_idx c5_0_pow c5_0_inv c5_0_goal) = true := by decide +kernel
def c5_0_m0 : BitVec 32 := 0xff00ff00
def c5_0_st0 : List (BitVec 32) := [0xaa00aa00,0xcc00cc00,0xf000f000,0xff000000]
def c5_0_ix0 : List ℕ := [8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_0 : c5_0_ix0.length = 16 ∧ (∀ idx ∈ c5_0_ix0, idx < 32) ∧ (∀ idx ∈ c5_0_ix0, c5_0_m0.getLsbD idx = true) ∧ projS 16 c5_0_ix0 c5_0_goal = b4_0_goal ∧ c5_0_st0.all (fun w => rows4.contains (projS 16 c5_0_ix0 w)) = true := by decide +kernel
def c5_0_m1 : BitVec 32 := 0x55555555
def c5_0_st1 : List (BitVec 32) := [0x44444444,0x50505050,0x55005500,0x55550000]
def c5_0_ix1 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_1 : c5_0_ix1.length = 16 ∧ (∀ idx ∈ c5_0_ix1, idx < 32) ∧ (∀ idx ∈ c5_0_ix1, c5_0_m1.getLsbD idx = true) ∧ projS 16 c5_0_ix1 c5_0_goal = b4_1_goal ∧ c5_0_st1.all (fun w => rows4.contains (projS 16 c5_0_ix1 w)) = true := by decide +kernel
def c5_0_m2 : BitVec 32 := 0xffff0000
def c5_0_st2 : List (BitVec 32) := [0xaaaa0000,0xcccc0000,0xf0f00000,0xff000000]
def c5_0_ix2 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_2 : c5_0_ix2.length = 16 ∧ (∀ idx ∈ c5_0_ix2, idx < 32) ∧ (∀ idx ∈ c5_0_ix2, c5_0_m2.getLsbD idx = true) ∧ projS 16 c5_0_ix2 c5_0_goal = b4_0_goal ∧ c5_0_st2.all (fun w => rows4.contains (projS 16 c5_0_ix2 w)) = true := by decide +kernel
def c5_0_m3 : BitVec 32 := 0x33333333
def c5_0_st3 : List (BitVec 32) := [0x22222222,0x30303030,0x33003300,0x33330000]
def c5_0_ix3 : List ℕ := [0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_3 : c5_0_ix3.length = 16 ∧ (∀ idx ∈ c5_0_ix3, idx < 32) ∧ (∀ idx ∈ c5_0_ix3, c5_0_m3.getLsbD idx = true) ∧ projS 16 c5_0_ix3 c5_0_goal = b4_2_goal ∧ c5_0_st3.all (fun w => rows4.contains (projS 16 c5_0_ix3 w)) = true := by decide +kernel
def c5_0_m4 : BitVec 32 := 0xf0f0f0f
def c5_0_st4 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def c5_0_ix4 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_4 : c5_0_ix4.length = 16 ∧ (∀ idx ∈ c5_0_ix4, idx < 32) ∧ (∀ idx ∈ c5_0_ix4, c5_0_m4.getLsbD idx = true) ∧ projS 16 c5_0_ix4 c5_0_goal = b4_2_goal ∧ c5_0_st4.all (fun w => rows4.contains (projS 16 c5_0_ix4 w)) = true := by decide +kernel
def c5_0_m5 : BitVec 32 := 0xff00ff
def c5_0_st5 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def c5_0_ix5 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_5 : c5_0_ix5.length = 16 ∧ (∀ idx ∈ c5_0_ix5, idx < 32) ∧ (∀ idx ∈ c5_0_ix5, c5_0_m5.getLsbD idx = true) ∧ projS 16 c5_0_ix5 c5_0_goal = b4_3_goal ∧ c5_0_st5.all (fun w => rows4.contains (projS 16 c5_0_ix5 w)) = true := by decide +kernel
def c5_0_m6 : BitVec 32 := 0xf0f0f0f0
def c5_0_st6 : List (BitVec 32) := [0xa0a0a0a0,0xc0c0c0c0,0xf000f000,0xf0f00000]
def c5_0_ix6 : List ℕ := [4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_6 : c5_0_ix6.length = 16 ∧ (∀ idx ∈ c5_0_ix6, idx < 32) ∧ (∀ idx ∈ c5_0_ix6, c5_0_m6.getLsbD idx = true) ∧ projS 16 c5_0_ix6 c5_0_goal = b4_4_goal ∧ c5_0_st6.all (fun w => rows4.contains (projS 16 c5_0_ix6 w)) = true := by decide +kernel
def c5_0_m7 : BitVec 32 := 0xffff
def c5_0_st7 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def c5_0_ix7 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_7 : c5_0_ix7.length = 16 ∧ (∀ idx ∈ c5_0_ix7, idx < 32) ∧ (∀ idx ∈ c5_0_ix7, c5_0_m7.getLsbD idx = true) ∧ projS 16 c5_0_ix7 c5_0_goal = b4_3_goal ∧ c5_0_st7.all (fun w => rows4.contains (projS 16 c5_0_ix7 w)) = true := by decide +kernel
def c5_0_m8 : BitVec 32 := 0xcccccccc
def c5_0_st8 : List (BitVec 32) := [0x88888888,0xc0c0c0c0,0xcc00cc00,0xcccc0000]
def c5_0_ix8 : List ℕ := [2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_8 : c5_0_ix8.length = 16 ∧ (∀ idx ∈ c5_0_ix8, idx < 32) ∧ (∀ idx ∈ c5_0_ix8, c5_0_m8.getLsbD idx = true) ∧ projS 16 c5_0_ix8 c5_0_goal = b4_4_goal ∧ c5_0_st8.all (fun w => rows4.contains (projS 16 c5_0_ix8 w)) = true := by decide +kernel
def c5_0_cfMasks : Array (BitVec 32) := Array.mk [c5_0_m0,c5_0_m1,c5_0_m2,c5_0_m3,c5_0_m4,c5_0_m5,c5_0_m6,c5_0_m7,c5_0_m8]
def c5_0_cfB0s : Array ℕ := Array.mk [8,0,16,0,0,0,4,0,2]
def c5_0_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_0_st0,c5_0_st1,c5_0_st2,c5_0_st3,c5_0_st4,c5_0_st5,c5_0_st6,c5_0_st7,c5_0_st8]
def c5_0_cfLBs : Array ℕ := Array.mk [7,7,7,5,5,5,5,5,5]
theorem c5_0_cof_sound (c fuel : ℕ) (hc : c < 9) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_0_cfLBs[c]?.getD 0) fuel (c5_0_cfMasks[c]?.getD 0) (c5_0_cfB0s[c]?.getD 0) (c5_0_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_0_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_0_goal 7 c5_0_ix0 c5_0_cspec_0.1 c5_0_cspec_0.2.1 c5_0_m0 c5_0_cspec_0.2.2.1 8 c5_0_st0 b4_0_goal (by decide) c5_0_cspec_0.2.2.2.1 c5_0_cspec_0.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_0_goal 7 c5_0_ix1 c5_0_cspec_1.1 c5_0_cspec_1.2.1 c5_0_m1 c5_0_cspec_1.2.2.1 0 c5_0_st1 b4_1_goal (by decide) c5_0_cspec_1.2.2.2.1 c5_0_cspec_1.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_0_goal 7 c5_0_ix2 c5_0_cspec_2.1 c5_0_cspec_2.2.1 c5_0_m2 c5_0_cspec_2.2.2.1 16 c5_0_st2 b4_0_goal (by decide) c5_0_cspec_2.2.2.2.1 c5_0_cspec_2.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix3 c5_0_cspec_3.1 c5_0_cspec_3.2.1 c5_0_m3 c5_0_cspec_3.2.2.1 0 c5_0_st3 b4_2_goal (by decide) c5_0_cspec_3.2.2.2.1 c5_0_cspec_3.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix4 c5_0_cspec_4.1 c5_0_cspec_4.2.1 c5_0_m4 c5_0_cspec_4.2.2.1 0 c5_0_st4 b4_2_goal (by decide) c5_0_cspec_4.2.2.2.1 c5_0_cspec_4.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix5 c5_0_cspec_5.1 c5_0_cspec_5.2.1 c5_0_m5 c5_0_cspec_5.2.2.1 0 c5_0_st5 b4_3_goal (by decide) c5_0_cspec_5.2.2.2.1 c5_0_cspec_5.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 6 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix6 c5_0_cspec_6.1 c5_0_cspec_6.2.1 c5_0_m6 c5_0_cspec_6.2.2.1 4 c5_0_st6 b4_4_goal (by decide) c5_0_cspec_6.2.2.2.1 c5_0_cspec_6.2.2.2.2 b4_4_no_build fuel hist nxt hnd hchk
  | 7 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix7 c5_0_cspec_7.1 c5_0_cspec_7.2.1 c5_0_m7 c5_0_cspec_7.2.2.1 0 c5_0_st7 b4_3_goal (by decide) c5_0_cspec_7.2.2.2.1 c5_0_cspec_7.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 8 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix8 c5_0_cspec_8.1 c5_0_cspec_8.2.1 c5_0_m8 c5_0_cspec_8.2.2.1 2 c5_0_st8 b4_4_goal (by decide) c5_0_cspec_8.2.2.2.1 c5_0_cspec_8.2.2.2.2 b4_4_no_build fuel hist nxt hnd hchk
  | c + 9 => omega
def c5_0_L3 : Array W5Node := Array.mk [
([u0,0xeee0e0e0,u34,u4],[],[],[]),
([u9,u3,0xd700c300,u4],[],[],[]),
([0x28283c3c,u3,0xc3c30000,u2],[],[],[]),
([u9,u3,0xbe00ff00,u4],[],[],[]),
([0xbca8bca8,u20,u2,u4],[],[],[]),
([u20,0xfca8a8a8,u2,u4],[],[],[]),
([u3,0xfce8e8e8,u2,u4],[],[],[]),
([u9,0xbeaaaaaa,u2,u4],[],[],[]),
([0x3c3c3c,u3,u46,u4],[],[],[]),
([u9,0xfeaaaaaa,u2,u4],[],[],[]),
([u3,u25,0xff3c3c3c,u4],[],[],[])
]
set_option maxRecDepth 100000 in
def c5_0_L4 : Array W5Node := Array.mk [
([u3,u5,u2,0xffc8c8c8,u4],[(u15,u3,u1),(u5,u1,u0),(u39,u0,u15),(u6,u2,u4),(0xffc8c8c8,u39,u6)],[0],[]),
([u0,u15,0xfca8a8a8,u2,u4],[],[],[]),
([u119,u0,0xefaaefaa,u2,u4],[],[],[]),
([u3,u0,0xefe0e0e0,u2,u4],[],[],[]),
([u39,u32,u1,u58,u4],[],[],[]),
([u3,u39,u1,0xfe00cc00,u4],[(u15,u3,u1),(u39,u15,u0),(u103,u15,u4),(0xfefecccc,u0,u103),(0xfe00cc00,0xfefecccc,u2)],[1],[]),
([u3,u0,0xfe0e0e0e,u2,u4],[],[],[]),
([u40,u0,u120,u2,u4],[],[],[]),
([u40,u0,u43,u34,u4],[],[],[]),
([u0,u43,u79,u1,u21],[],[],[]),
([u104,u0,u74,u1,u2],[],[],[]),
([u0,u12,u34,u37,u4],[],[],[(0,0)]),
([u71,u0,u1,u34,u4],[],[],[]),
([u3,u14,u1,0xfac8c8c8,u4],[(u15,u3,u1),(u14,u0,u2),(u6,u2,u4),(u30,u0,u6),(0xfac8c8c8,u15,u30)],[1],[(2,0)]),
([u12,0xfcf8f8f8,u2,u21,u4],[],[],[]),
([u3,0xbc00bc00,u84,u2,u4],[],[],[]),
([0x43004300,u3,u84,u2,u4],[(u13,u3,u0),(u53,u13,u1),(u5,u0,u1),(u84,u53,u5),(0x43004300,u84,u2)],[0],[]),
([u3,u84,u6,u2,u4],[],[],[]),
([u3,u84,u25,u2,u4],[],[],[]),
([u3,u5,u2,0xff404040,u4],[(u13,u3,u0),(u53,u13,u1),(u5,u0,u1),(u6,u2,u4),(0xff404040,u53,u6)],[0],[]),
([u3,0xd5c0c0c0,u5,u2,u4],[],[],[]),
([u9,u65,u3,u2,u4],[],[],[]),
([u9,u54,u3,u2,u4],[],[],[]),
([u9,u3,u95,u2,u4],[],[],[]),
([u96,u9,u3,u2,u4],[],[],[]),
([u9,u10,u3,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u8,u7,u0),(u5,u8,u1),(u9,u7,u5)],[1],[]),
([u9,u28,u10,u3,u4],[(u10,u3,u2),(u7,u0,u1),(u28,u7,u2),(u5,u0,u1),(u9,u7,u5)],[1],[]),
([u9,u105,u3,u2,u4],[],[],[]),
([u9,u75,u3,u2,u4],[(u19,u3,u4),(u7,u0,u1),(u5,u0,u1),(u75,u19,u5),(u9,u7,u5)],[1],[]),
([u9,u23,u10,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u5,u0,u1),(u23,u3,u5),(u9,u7,u5)],[0],[]),
([0x14001400,u9,u3,u2,u4],[],[],[]),
([u9,0x7d3c7d3c,u3,u2,u4],[],[],[]),
([0x28283c3c,u9,u3,u2,u4],[(u19,u3,u4),(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(0x28283c3c,u9,u19)],[0,1],[(0,1),(0,2)]),
([u9,0x41004100,u3,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(0x41004100,u9,u10)],[2],[(1,3)]),
([u9,u10,u3,u46,u4],[(u10,u3,u2),(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u46,u9,u2)],[1],[(1,2)]),
([u10,u3,u5,u45,u4],[(u10,u3,u2),(u7,u0,u1),(u5,u0,u1),(u6,u2,u4),(u45,u7,u6)],[2],[]),
([u10,u0,u1,0xff545454,u4],[],[],[]),
([u9,u80,u3,u2,u4],[],[],[]),
([u9,0x45004500,u3,u2,u4],[],[],[]),
([u9,u10,u3,u36,u4],[(u10,u3,u2),(u16,u1,u0),(u36,u16,u2),(u8,u1,u0),(u9,u8,u16)],[1],[]),
([u41,u42,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u41,u20,u5),(u42,u41,u3)],[1],[]),
([u42,u20,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u41,u20,u5),(u42,u41,u3)],[1],[]),
([u85,u20,u5,u2,u4],[],[],[(0,4)]),
([u20,u5,u81,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u25,u5,u2),(u81,u3,u25)],[1],[]),
([u20,u5,u2,u21,u4],[],[],[(0,5)]),
([u3,u5,u2,0xffeaeaea,u4],[],[],[(0,6)]),
([0xeaeaea,u3,u5,u2,u4],[],[],[]),
([u9,u23,u20,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u23,u3,u5),(u9,u7,u5)],[1],[]),
([u9,u42,u20,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u9,u7,u5),(u42,u9,u3)],[1],[]),
([u9,u3,u86,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u9,u7,u5),(u86,u20,u2)],[0],[]),
([u9,u3,u42,u2,u4],[(u7,u0,u1),(u8,u7,u0),(u5,u8,u1),(u9,u7,u5),(u42,u9,u3)],[1],[]),
([u41,u9,u3,u2,u4],[],[],[]),
([u49,u9,u3,u2,u4],[],[],[]),
([u9,u3,u46,u2,u4],[(u7,u0,u1),(u8,u7,u0),(u5,u8,u1),(u9,u7,u5),(u46,u9,u2)],[0],[]),
([u9,u3,u6,u2,u4],[],[],[]),
([u3,u5,u2,u45,u4],[(u7,u0,u1),(u8,u7,u0),(u5,u8,u1),(u6,u2,u4),(u45,u7,u6)],[0],[]),
([u3,0xbca8bca8,u7,u2,u4],[],[],[(0,4)]),
([u9,u3,u85,u2,u4],[],[],[]),
([u9,u121,u3,u2,u4],[],[],[]),
([u9,u3,0xc000ff00,u2,u4],[(u7,u0,u1),(u66,u7,u4),(0xc000ff00,u66,u2),(u5,u0,u1),(u9,u7,u5)],[0],[]),
([u9,u28,u3,u46,u4],[(u7,u0,u1),(u28,u7,u2),(u5,u0,u1),(u9,u7,u5),(u46,u9,u2)],[0,1],[]),
([u9,u28,u3,u25,u4],[(u7,u0,u1),(u28,u7,u2),(u5,u0,u1),(u9,u7,u5),(u25,u5,u2)],[0,1],[]),
([u23,u42,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u23,u3,u5),(u41,u23,u7),(u42,u41,u3)],[1],[]),
([u3,0xebc0ebc0,u5,u2,u4],[],[],[]),
([u9,u3,u97,u2,u4],[],[],[]),
([u9,u23,u42,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u23,u3,u5),(u9,u7,u5),(u42,u9,u3)],[1],[]),
([u41,u9,u42,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u42,u9,u3),(u41,u9,u3)],[1],[]),
([u9,u3,0xbe00be00,u2,u4],[],[],[]),
([u9,u3,0xeb00eb00,u2,u4],[],[],[]),
([u9,u3,0xbeaabeaa,u2,u4],[],[],[]),
([u49,u9,u3,u46,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u49,u9,u2),(u46,u49,u2)],[0,1],[]),
([0x3c000000,u9,u3,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u49,u9,u2),(0x3c000000,u49,u4)],[1],[(0,7)]),
([u9,u3,0xc300ff00,u2,u4],[],[],[]),
([u9,u3,0xebaaebaa,u2,u4],[],[],[]),
([u9,u3,0xc3000000,u2,u4],[],[],[]),
([0x3c00ff00,u9,u3,u2,u4],[],[],[]),
([u9,u3,u46,u6,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u46,u9,u2),(u6,u2,u4)],[2],[(0,8)]),
([u9,u3,u2,0xff3c3c3c,u4],[],[],[]),
([0x3c3c3c,u9,u3,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u6,u2,u4),(0x3c3c3c,u9,u6)],[0,2],[(0,8),(1,8)]),
([u9,u3,u2,u21,u4],[],[],[]),
([u9,u10,u3,u6,u4],[],[],[]),
([u9,u3,u2,u45,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u6,u2,u4),(u45,u7,u6)],[0],[]),
([u9,u3,u46,u25,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u46,u9,u2),(u25,u5,u2)],[0,1],[]),
([u9,u3,u81,u2,u4],[],[],[]),
([u9,u3,0xfc000000,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u25,u5,u2),(0xfc000000,u25,u4)],[1,3],[(0,9)]),
([0x300ff00,u9,u3,u2,u4],[],[],[]),
([u3,u5,u2,0xff3c3c3c,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u6,u2,u4),(0xff3c3c3c,u9,u6)],[3],[(1,10)]),
([0x3c3c3c,u3,u5,u2,u4],[],[],[]),
([u62,u9,u3,u2,u4],[],[],[]),
([u9,u3,u25,u6,u4],[],[],[]),
([u7,u5,0xfeaaaaaa,u2,u4],[],[],[(0,9)]),
([u3,0xfcc0c0c0,u5,u2,u4],[],[],[]),
([u3,u25,u5,u45,u4],[(u7,u0,u1),(u5,u0,u1),(u25,u5,u2),(u6,u2,u4),(u45,u7,u6)],[2],[]),
([u3,u7,0xfca8a8a8,u2,u4],[],[],[(0,5),(0,6)]),
([0x55404040,u3,u5,u2,u4],[],[],[]),
([u3,0xfc3c3c3c,u6,u2,u4],[],[],[]),
([u9,u3,0xae00ae00,u2,u4],[],[],[]),
([u41,u9,u27,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u16,u0,u1),(u9,u8,u16),(u41,u9,u3)],[1],[]),
([u9,u27,u57,u2,u4],[(u16,u1,u0),(u57,u16,u3),(u8,u1,u0),(u9,u16,u8),(u27,u8,u3)],[1],[]),
([u9,u3,0xefaaefaa,u2,u4],[],[],[]),
([u49,u9,u3,u36,u4],[(u16,u1,u0),(u36,u16,u2),(u8,u1,u0),(u9,u8,u16),(u49,u9,u2)],[1],[]),
([u9,u3,0xcf000000,u2,u4],[],[],[]),
([0xc00ff00,u9,u3,u2,u4],[],[],[]),
([u9,u3,u36,u6,u4],[(u16,u1,u0),(u36,u16,u2),(u8,u1,u0),(u9,u8,u16),(u6,u2,u4)],[2],[]),
([u9,u3,u36,u51,u4],[(u16,u1,u0),(u36,u16,u2),(u8,u1,u0),(u9,u8,u16),(u51,u8,u2)],[0,1],[]),
([u9,u3,u2,u72,u4],[],[],[]),
([0x1e1e5a5a,u3,u0,u2,u4],[],[],[]),
([u3,u82,u1,0xfeee0000,u2],[],[],[]),
([u106,u0,u1,u38,u6],[(u17,u1,u4),(u38,u3,u17),(u87,u38,u2),(u106,u87,u3),(u6,u2,u4)],[4],[]),
([u0,u32,u1,u38,u6],[(u17,u1,u4),(u38,u3,u17),(u14,u0,u2),(u32,u3,u14),(u6,u2,u4)],[3,4],[]),
([u3,u0,u1,0xfeeefaaa,u6],[(u18,u1,u2),(u34,u3,u18),(u24,u0,u4),(0xfeeefaaa,u24,u34),(u6,u2,u4)],[0,2],[]),
([0xc8888888,u1,0xfeeeeeee,u2,u4],[],[],[]),
([0x4444444,0x32222222,u1,u2,u4],[],[],[]),
([0x54445000,u3,u0,u1,u6],[],[],[]),
([0x4b4b5a5a,u3,u0,u2,u4],[],[],[]),
([u3,0xfcececec,u2,0xfffafafa,u4],[],[],[(0,6)]),
([0xf5a5a5a,u3,u0,u2,u4],[],[],[]),
([u3,u73,0xf0e0e0e0,u2,u4],[],[],[(0,6)]),
([u3,0xfcececec,u2,u37,u4],[(u6,u2,u4),(u21,u3,u6),(u37,u1,u6),(0xf0a0a0a0,u1,u21),(0xfcececec,0xf0a0a0a0,u0)],[0],[])
]
set_option maxRecDepth 100000 in
def c5_0_L5 : Array W5Node := Array.mk [
([u0,u122,u1,u15,u2,u4],[(u15,u3,u1),(u22,u3,u1),(u14,u0,u2),(u122,u22,u14)],[1],[]),
([u0,u12,u1,u2,u88,u4],[],[],[]),
([u3,u39,u5,u6,u2,u4],[(u15,u3,u1),(u5,u1,u0),(u39,u0,u15),(u6,u2,u4)],[0,3],[(0,0)]),
([u0,u32,u15,u5,u2,u4],[(u15,u3,u1),(u5,u1,u0),(u14,u0,u2),(u32,u3,u14)],[0,1,3],[]),
([u98,u3,u12,u1,u2,u4],[(u12,u3,u0),(u5,u0,u1),(u17,u1,u4),(u98,u17,u5)],[1],[]),
([u0,u15,u5,u2,u21,u4],[],[],[(0,1)]),
([u26,u3,u15,u5,u2,u4],[(u15,u3,u1),(u5,u1,u0),(u6,u2,u4),(u26,u0,u6)],[3],[]),
([u71,u3,u1,u5,u2,u4],[(u12,u3,u0),(u5,u0,u1),(u6,u2,u4),(u71,u12,u6)],[4],[]),
([u62,u3,u0,u15,u2,u4],[(u15,u3,u1),(u5,u1,u0),(u6,u2,u4),(u62,u5,u6)],[1],[]),
([u3,u119,u0,u36,u2,u4],[],[],[(0,2)]),
([u3,u119,u0,u58,u2,u4],[],[],[]),
([u8,u12,u1,u123,u2,u4],[],[],[(2,2)]),
([u3,u0,u15,0xfc30fc30,u2,u4],[(u15,u3,u1),(u16,u1,u0),(u14,u0,u2),(0xfc30fc30,u16,u14)],[3],[]),
([u8,u12,u1,u34,u2,u4],[(u12,u3,u0),(u8,u0,u1),(u18,u1,u2),(u34,u3,u18)],[4],[]),
([u3,u0,u15,u2,0xff303030,u4],[],[],[]),
([u8,u12,u1,u2,u21,u4],[],[],[]),
([u71,u8,u3,u1,u2,u4],[],[],[]),
([u0,u12,u1,u123,u2,u4],[(u12,u3,u0),(u8,u0,u1),(u51,u8,u2),(u123,u3,u51)],[3,5],[]),
([0xa0afafa,u3,u0,u1,u6,u2],[(u15,u3,u1),(u17,u1,u4),(0xa0afafa,u17,u15),(u6,u2,u4)],[0],[]),
([u3,u39,u1,u50,u2,u4],[(u15,u3,u1),(u18,u1,u2),(u50,u18,u0),(u39,u15,u0)],[0],[]),
([u3,u0,0xece0ece0,u1,u2,u4],[(u12,u3,u0),(u14,u0,u2),(u67,u14,u1),(0xece0ece0,u12,u67)],[1],[]),
([u3,u0,0xce0ece0e,u1,u2,u4],[],[],[]),
([u33,0x32323232,u3,u1,u2,u4],[],[],[]),
([u11,u3,u0,0xefe0efe0,u2,u4],[],[],[]),
([u83,u3,u0,u68,u2,u4],[],[],[(0,3)]),
([u3,u39,u55,u1,u2,u4],[],[],[]),
([u3,u0,u1,u2,0xffc8c8c8,u4],[(u15,u3,u1),(u39,u15,u0),(u6,u2,u4),(0xffc8c8c8,u39,u6)],[0,2,3],[(0,0)]),
([u99,u3,u0,u1,u2,u4],[],[],[]),
([0x1f00ff00,u3,u0,u12,u1,u4],[],[],[]),
([u39,u32,u1,u15,u2,u4],[(u15,u3,u1),(u39,u15,u0),(u14,u0,u2),(u32,u3,u14)],[0],[(0,4)]),
([u3,u39,u14,u1,u58,u4],[(u15,u3,u1),(u39,u15,u0),(u14,u0,u2),(u58,u15,u2)],[0,1,6],[(0,4)]),
([u3,u39,u1,0xfeccfecc,u2,u4],[(u15,u3,u1),(u39,u15,u0),(u58,u15,u2),(0xfeccfecc,u0,u58)],[1,6],[(1,5)]),
([u0,u1,u76,u2,u21,u4],[(u12,u3,u0),(u76,u12,u1),(u6,u2,u4),(u21,u3,u6)],[5,7],[]),
([u26,u3,u1,u76,u2,u4],[(u12,u3,u0),(u76,u12,u1),(u6,u2,u4),(u26,u0,u6)],[5,7],[(2,6)]),
([0xfefefe,u3,u0,u1,u2,u4],[(u12,u3,u0),(u76,u12,u1),(u6,u2,u4),(0xfefefe,u76,u6)],[0],[]),
([u3,u14,u1,0xfe32fe32,u2,u4],[(u15,u3,u1),(0x32323232,u15,u0),(u14,u0,u2),(0xfe32fe32,0x32323232,u14)],[0,8],[]),
([u40,u3,u0,u77,u2,u4],[(u12,u3,u0),(u40,u12,u1),(u18,u1,u2),(u77,u18,u4)],[8],[(0,6),(0,7)]),
([u40,u44,u3,u0,u2,u4],[],[],[]),
([u40,u3,u0,u18,u6,u4],[(u12,u3,u0),(u40,u12,u1),(u18,u1,u2),(u6,u2,u4)],[6],[]),
([u3,u0,u1,u2,0xff0e0e0e,u4],[(u12,u3,u0),(u40,u12,u1),(u6,u2,u4),(0xff0e0e0e,u40,u6)],[8],[]),
([u40,u0,u1,u2,u21,u4],[],[],[]),
([u26,u40,u3,u1,u2,u4],[],[],[]),
([u3,u104,u0,u1,u2,u4],[],[],[]),
([0x404cccc,0x32323232,u3,u1,u2,u4],[],[],[]),
([u40,u3,u0,u43,u18,u4],[(u12,u3,u0),(u40,u12,u1),(u43,u12,u2),(u18,u1,u2)],[8],[(0,8)]),
([u40,u0,u12,u34,u2,u4],[(u12,u3,u0),(u40,u12,u1),(u18,u1,u2),(u34,u3,u18)],[4],[(0,8)]),
([u3,u0,u1,u2,0xff040404,u4],[],[],[]),
([0x4040404,u3,u1,u2,u30,u4],[],[],[(2,3)]),
([u3,u0,u1,0xfeccfa00,u2,u4],[(u15,u3,u1),(u58,u15,u2),(u24,u0,u4),(0xfeccfa00,u24,u58)],[2,5,6,8],[]),
([u3,u0,0xef0fee00,u1,u2,u4],[],[],[]),
([u3,u0,u12,u1,0xfe00f000,u4],[(u12,u3,u0),(u79,u12,u4),(0xfefef0f0,u79,u1),(0xfe00f000,0xfefef0f0,u2)],[6],[(2,5)]),
([u71,u3,u0,u1,u2,u4],[],[],[]),
([u3,u0,u12,0xfef0f0f0,u2,u4],[],[],[]),
([0x4cccccc,u3,u1,u15,u2,u4],[(u15,u3,u1),(u58,u15,u2),(0xfa000000,u58,u4),(0x4cccccc,0xfa000000,u0)],[1],[]),
([u3,u0,u43,u79,u1,u6],[(u12,u3,u0),(u43,u12,u2),(u79,u12,u4),(u6,u2,u4)],[0,2,8],[(0,9)]),
([u0,u43,u12,u1,u34,u4],[],[],[(0,8),(2,4)]),
([u3,u14,u1,u15,0xfeccfecc,u4],[(u15,u3,u1),(u58,u15,u2),(u14,u0,u2),(0xfeccfecc,u0,u58)],[0,1],[]),
([u0,u43,u12,u1,u21,u4],[(u12,u3,u0),(u43,u12,u2),(u6,u2,u4),(u21,u3,u6)],[2],[(0,9)]),
([u3,u0,0xcd05cc00,u1,u2,u4],[],[],[]),
([0x1f0f1100,u3,u0,u1,u2,u4],[],[],[]),
([u11,u0,u12,u1,u34,u4],[(u12,u3,u0),(u18,u1,u2),(u34,u3,u18),(u11,u1,u2)],[4],[(3,10)]),
([u82,u12,u1,u34,u2,u4],[(u12,u3,u0),(u18,u1,u2),(u34,u3,u18),(u82,u34,u0)],[1],[]),
([0xe0a0e0a,u0,u32,u15,u2,u4],[(u15,u3,u1),(u14,u0,u2),(u32,u3,u14),(0xe0a0e0a,u32,u1)],[4],[]),
([u0,u32,u1,u15,u6,u4],[(u15,u3,u1),(u14,u0,u2),(u32,u3,u14),(u6,u2,u4)],[2,3,4],[(2,11),(2,12)]),
([u0,u32,u15,u67,u2,u4],[(u15,u3,u1),(u14,u0,u2),(u32,u3,u14),(u67,u14,u1)],[0,1,3,5],[]),
([u33,u12,u1,u38,u2,u4],[(u12,u3,u0),(u17,u1,u4),(u38,u3,u17),(u33,u17,u0)],[3,4,7],[]),
([u82,u12,u18,u1,u2,u4],[],[],[]),
([u3,0xca0aca0a,u0,u15,u2,u4],[(u15,u3,u1),(u14,u0,u2),(0x30f030f0,u14,u1),(0xca0aca0a,0x30f030f0,u15)],[1,4],[]),
([u33,u3,u12,u1,u6,u2],[(u12,u3,u0),(u17,u1,u4),(u33,u17,u0),(u6,u2,u4)],[0],[]),
([u3,u14,u0,u1,0xfefa0000,u2],[(u15,u3,u1),(u14,u0,u2),(u107,u14,u15),(0xfefa0000,u107,u4)],[0],[]),
([u99,u3,u0,u1,u6,u2],[(u12,u3,u0),(u17,u1,u4),(u99,u17,u12),(u6,u2,u4)],[0],[]),
([u3,u104,u24,u0,u1,u2],[(u15,u3,u1),(u24,u0,u4),(u29,u24,u4),(u104,u29,u15)],[2],[(0,10)]),
([u0,u89,u1,u15,u2,u4],[(u15,u3,u1),(u14,u0,u2),(u59,u14,u4),(u89,u3,u59)],[0,2,3,4,5,7],[(2,7)]),
([0xeeeeeee,u3,u0,u1,u2,u4],[(u12,u3,u0),(u18,u1,u2),(u77,u18,u4),(0xeeeeeee,u77,u12)],[1],[]),
([u3,0xc800fafa,u0,u1,u2,u4],[(u15,u3,u1),(u14,u0,u2),(0x33ff0000,u14,u4),(0xc800fafa,0x33ff0000,u15)],[3],[]),
([u3,u14,u1,u15,u30,u4],[(u15,u3,u1),(u14,u0,u2),(u6,u2,u4),(u30,u0,u6)],[1,8],[(0,13),(2,11)]),
([u71,u3,u0,u18,u1,u4],[(u12,u3,u0),(u18,u1,u2),(u6,u2,u4),(u71,u12,u6)],[6],[(0,12)]),
([0xafaaaaaa,u0,u12,u1,u2,u4],[(u12,u3,u0),(u11,u1,u2),(u83,u11,u4),(0xafaaaaaa,u83,u3)],[3,6],[]),
([u3,0xc8fafafa,u0,u1,u2,u4],[],[],[]),
([0xe00eeee,u3,u0,u1,u2,u4],[],[],[]),
([u73,u12,u1,u2,u21,u4],[],[],[(0,14)]),
([0xf0a0a0a,u0,u15,u2,u21,u4],[(u15,u3,u1),(u6,u2,u4),(u21,u3,u6),(0xf0a0a0a,u1,u21)],[4],[]),
([u0,u15,u2,u21,u37,u4],[(u15,u3,u1),(u6,u2,u4),(u21,u3,u6),(u37,u1,u6)],[0,1,5,7],[]),
([u26,u12,u1,u2,u21,u4],[(u12,u3,u0),(u6,u2,u4),(u21,u3,u6),(u26,u0,u6)],[3,5,7],[]),
([u3,u0,0xfa0a0a0a,u15,u2,u4],[(u15,u3,u1),(u6,u2,u4),(u69,u1,u6),(0xfa0a0a0a,u69,u15)],[1,4],[]),
([u3,0xccc8c8c8,u1,u6,u2,u4],[(u15,u3,u1),(u6,u2,u4),(0xfffafafa,u15,u6),(0xccc8c8c8,u0,0xfffafafa)],[0],[]),
([0xf0e0e0e,u3,u0,u6,u2,u4],[(u12,u3,u0),(u6,u2,u4),(u100,u12,u6),(0xf0e0e0e,u1,u100)],[0],[]),
([u3,u0,0xeee0e0e0,u1,u2,u4],[(u12,u3,u0),(u6,u2,u4),(u37,u1,u6),(0xeee0e0e0,u12,u37)],[1,6],[(2,13),(3,13)]),
([u3,u0,0xee0e0e0e,u1,u2,u4],[(u12,u3,u0),(u6,u2,u4),(u69,u1,u6),(0xee0e0e0e,u69,u12)],[4],[]),
([u3,u84,u2,u4],[(u13,u3,u0),(u53,u13,u1),(u5,u0,u1),(u84,u53,u5)],[0,1,2],[(0,15),(0,16),(0,17),(1,15),(1,16)]),
([u3,u84,u5,u2,u4],[(u13,u3,u0),(u53,u13,u1),(u5,u0,u1),(u84,u53,u5)],[0,1,2,8],[(0,18),(1,18)]),
([u53,u3,u25,u5,u2,u4],[],[],[(0,18)]),
([u53,u3,u5,u6,u2,u4],[(u13,u3,u0),(u53,u13,u1),(u5,u0,u1),(u6,u2,u4)],[0,3],[(0,17),(0,19)]),
([u3,u0,u1,u2,0xff404040,u4],[(u13,u3,u0),(u53,u13,u1),(u6,u2,u4),(0xff404040,u53,u6)],[0,2],[(0,19)]),
([u3,u63,u64,u1,u2,u4],[],[],[]),
([u3,0xc4c4f4f4,u0,u1,u2,u4],[],[],[]),
([u26,u3,u64,u1,u2,u4],[],[],[]),
([0xdcdcdc,u3,u0,u1,u2,u4],[],[],[]),
([u3,u0,u64,u2,u37,u4],[(u22,u3,u1),(u64,u22,u0),(u6,u2,u4),(u37,u1,u6)],[5,7],[]),
([0x4040cccc,u3,u64,u1,u2,u4],[],[],[]),
([u124,u3,u0,u1,u2,u4],[],[],[]),
([u8,u3,u70,u6,u2,u4],[],[],[(0,17)]),
([0x8f8c8f8c,u3,u0,u1,u2,u4],[(u22,u3,u1),(u60,u22,u0),(u11,u1,u2),(0x8f8c8f8c,u11,u60)],[1],[]),
([u60,u3,u52,u1,u2,u4],[(u22,u3,u1),(u60,u22,u0),(u11,u1,u2),(u52,u11,u0)],[0],[]),
([u3,u0,u1,u2,0xff8c8c8c,u4],[],[],[]),
([u60,u3,u1,u2,u30,u4],[],[],[]),
([u60,u3,0xefccefcc,u1,u2,u4],[],[],[]),
([u3,u0,u122,u1,u2,u4],[],[],[]),
([u3,u0,0xdc50cc00,u1,u2,u4],[(u22,u3,u1),(0x50500000,u22,u4),(u14,u0,u2),(0xdc50cc00,0x50500000,u14)],[0,7],[]),
([0x4f0f4400,u3,u0,u1,u2,u4],[],[],[]),
([u3,u0,0xefafcc00,u1,u2,u4],[],[],[]),
([u3,0xbf0fbb00,u0,u1,u2,u4],[],[],[]),
([u13,0x51505150,u0,u1,u2,u4],[(u13,u3,u0),(u78,u13,u2),(0xfbf0fbf0,u78,u1),(0x51505150,u3,0xfbf0fbf0)],[0,6,8],[]),
([0x4040cccc,u22,u3,u5,u2,u4],[(u22,u3,u1),(u108,u22,u4),(0x4040cccc,u108,u0),(u5,u0,u1)],[2],[]),
([u3,u0,u1,u2,u88,u4],[(u13,u3,u0),(u78,u13,u2),(0xbb000000,u78,u4),(u88,u13,0xbb000000)],[0,2],[]),
([u3,u125,u61,u0,u2,u4],[(u22,u3,u1),(u61,u22,u2),(u5,u1,u0),(u125,u22,u5)],[8],[]),
([u3,u125,u0,u25,u2,u4],[],[],[]),
([u98,u13,u3,u1,u2,u4],[],[],[]),
([u3,u0,u5,u2,0xff505050,u4],[(u22,u3,u1),(u5,u1,u0),(u6,u2,u4),(0xff505050,u22,u6)],[3],[]),
([u26,u22,u3,u5,u2,u4],[(u22,u3,u1),(u5,u1,u0),(u6,u2,u4),(u26,u0,u6)],[3],[]),
([u62,u13,u3,u1,u2,u4],[],[],[]),
([u13,u3,u1,0xfc0cfc0c,u2,u4],[],[],[]),
([u13,u3,u1,u2,u72,u4],[],[],[]),
([u8,u3,u1,u2,u88,u4],[],[],[]),
([0x5f005000,0x5f5f5050,u3,u0,u1,u4],[(u22,u3,u1),(u35,u1,u4),(0x5f5f5050,u35,u22),(0x5f005000,0x5f5f5050,u2)],[0,1,2],[]),
([0x5f50,0x5f505f50,u3,u0,u1,u2],[(u22,u3,u1),(u11,u1,u2),(0x5f505f50,u11,u22),(0x5f50,0x5f505f50,u4)],[1,7],[]),
([u13,u3,0xb888b888,u1,u2,u4],[(u13,u3,u0),(u18,u1,u2),(u50,u0,u18),(0xb888b888,u13,u50)],[1],[]),
([u3,u0,0xdc505050,u1,u2,u4],[(u22,u3,u1),(u14,u0,u2),(u59,u14,u4),(0xdc505050,u22,u59)],[1],[]),
([u13,u0,u1,u120,u2,u4],[(u13,u3,u0),(u18,u1,u2),(u77,u18,u4),(u120,u3,u77)],[8],[]),
([0x4f44ff44,u3,u0,u1,u2,u4],[(u13,u3,u0),(u17,u1,u4),(u44,u17,u2),(0x4f44ff44,u44,u13)],[0],[]),
([u13,u3,u0,u18,u37,u4],[],[],[]),
([0x4f444444,u3,u0,u1,u2,u4],[],[],[]),
([u3,u0,0xdc50ff50,u1,u2,u4],[(u22,u3,u1),(u29,u0,u4),(u55,u29,u2),(0xdc50ff50,u22,u55)],[0],[]),
([u13,u3,0xbb888888,u1,u2,u4],[],[],[]),
([u3,0xaf8c8c8c,u0,u1,u2,u4],[(u22,u3,u1),(u6,u2,u4),(u30,u0,u6),(0xaf8c8c8c,u22,u30)],[1],[]),
([u13,0x55505050,u0,u1,u2,u4],[(u13,u3,u0),(u6,u2,u4),(u37,u1,u6),(0x55505050,u3,u37)],[6,8],[]),
([0x44f4f4f4,u3,u0,u1,u2,u4],[],[],[]),
([u33,u3,u56,u1,u2,u4],[],[],[]),
([0xd0cddcc,u3,u0,u1,u2,u4],[],[],[]),
([u3,0xc4c0f5f0,u0,u1,u2,u4],[],[],[]),
([u3,0xc4c0c4c0,u56,u1,u2,u4],[],[],[]),
([u3,u0,u95,u1,u2,u4],[],[],[]),
([0x4c0c4c0c,u3,u56,u1,u2,u4],[],[],[]),
([u80,u3,u0,u1,u2,u4],[],[],[]),
([0xd0c0d0c,u90,u3,u0,u2,u4],[],[],[]),
([0x4400cccc,u3,u56,u1,u2,u4],[],[],[]),
([u75,u3,u0,u1,u2,u4],[(u19,u3,u4),(u109,u19,u0),(0xfdfdfcfc,u109,u1),(u75,u19,0xfdfdfcfc)],[1],[]),
([u10,u3,u0,0xdfcf0000,u1,u2],[(u10,u3,u2),(u56,u10,u0),(0x20302030,u56,u1),(0xdfcf0000,0x20302030,u4)],[1],[]),
([0x5f0f5500,u3,u0,u1,u2,u4],[(u10,u3,u2),(0xf5f0f5f0,u10,u1),(0xa0f0000,0xf5f0f5f0,u4),(0x5f0f5500,0xa0f0000,u10)],[1],[]),
([u11,u90,u3,u24,u0,u4],[],[],[]),
([u11,u29,u48,u3,u1,u2],[(u19,u3,u4),(u48,u19,u0),(u29,u0,u4),(u11,u1,u2)],[0],[]),
([u3,u0,0xeca0fcf0,u1,u2,u4],[],[],[]),
([u48,u3,u1,u50,u2,u4],[],[],[]),
([u48,u3,u0,u18,u1,u6],[(u19,u3,u4),(u48,u19,u0),(u18,u1,u2),(u6,u2,u4)],[3,4],[]),
([0x8f88cfcc,u3,u0,u1,u2,u4],[],[],[]),
([u48,u3,0xececfcfc,u1,u2,u4],[(u19,u3,u4),(0xa0a0f0f0,u19,u1),(u48,u19,u0),(0xececfcfc,0xa0a0f0f0,u0)],[8],[]),
([u48,u3,0xeeccffcc,u1,u2,u4],[],[],[]),
([0x44445454,u19,u0,u1,u2,u4],[(u19,u3,u4),(0xa0a0f0f0,u19,u1),(0xececfcfc,0xa0a0f0f0,u0),(0x44445454,u3,0xececfcfc)],[2,8],[]),
([u3,u0,u110,u1,u2,u4],[(u19,u3,u4),(u48,u19,u0),(0x8800cc00,u48,u2),(u110,u19,0x8800cc00)],[5],[]),
([u3,u0,0xd5c0c0c0,u1,u2,u4],[],[],[(0,20)]),
([u65,u3,u7,u5,u2,u4],[(u10,u3,u2),(u65,u10,u4),(u7,u0,u1),(u5,u0,u1)],[3],[(0,20),(0,21)]),
([0xa8fcfcfc,u3,u0,u1,u2,u4],[],[],[]),
([u23,u65,u0,u1,u2,u4],[(u10,u3,u2),(u65,u10,u4),(u5,u0,u1),(u23,u3,u5)],[6,8],[]),
([0x5d0c0c0c,u3,u0,u1,u2,u4],[],[],[]),
([u8,u16,u65,u3,u2,u4],[],[],[(0,21)]),
([u3,u0,0xeac0ffc0,u1,u2,u4],[(u19,u3,u4),(u54,u19,u2),(u7,u0,u1),(0xeac0ffc0,u54,u7)],[0],[]),
([u54,u3,u7,u5,u2,u4],[],[],[(0,22)]),
([0x5400fcfc,u3,u0,u1,u2,u4],[],[],[]),
([u23,u54,u0,u1,u2,u4],[],[],[]),
([u3,0xae0cff0c,u0,u1,u2,u4],[],[],[]),
([u8,u16,u54,u3,u2,u4],[],[],[(0,22)]),
([u3,u7,u95,u5,u2,u4],[],[],[(0,23)]),
([u96,u3,u7,u5,u2,u4],[],[],[(0,24)]),
([u10,u3,u7,u5,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u8,u7,u0),(u5,u8,u1)],[1],[(0,25)]),
([u8,u16,u10,u3,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u8,u7,u0),(u16,u7,u1)],[1],[(0,25)]),
([u28,u10,u3,u7,u5,u4],[(u10,u3,u2),(u7,u0,u1),(u28,u7,u2),(u5,u0,u1)],[1,3],[(0,26)]),
([u3,u0,0xd555c000,u1,u2,u4],[(u19,u3,u4),(u7,u0,u1),(u111,u7,u2),(0xd555c000,u19,u111)],[1,5],[]),
([u10,u0,u112,u1,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u91,u7,u4),(u112,u3,u91)],[0,7],[]),
([0x7f3f5500,u3,u0,u1,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u66,u7,u4),(0x7f3f5500,u66,u10)],[1],[]),
([u105,u3,u7,u5,u2,u4],[],[],[(0,27)]),
([u75,u3,u7,u5,u2,u4],[(u19,u3,u4),(u7,u0,u1),(u5,u0,u1),(u75,u19,u5)],[1,8],[(0,28)]),
([u23,u10,u7,u5,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u5,u0,u1),(u23,u3,u5)],[0,8],[(0,29)]),
([u9,u10,u3,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u5,u0,u1),(u9,u7,u5)],[0,1,2],[(0,21),(0,30),(0,31),(0,33),(0,34),(1,22),(1,32)]),
([u9,u10,u3,u7,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u5,u0,u1),(u9,u7,u5)],[1,3],[(0,23),(0,24),(0,26)]),
([u9,u10,u3,u5,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u5,u0,u1),(u9,u7,u5)],[1,8],[(0,27),(0,29),(1,28)]),
([u10,u3,u7,u5,u6,u4],[(u10,u3,u2),(u7,u0,u1),(u5,u0,u1),(u6,u2,u4)],[1,2],[(0,35)]),
([u9,u10,u3,u0,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u5,u0,u1),(u9,u7,u5)],[1,3,8],[]),
([u10,u3,u0,0xcfc0cfc0,u1,u4],[],[],[]),
([u10,u3,u0,u1,u45,u4],[(u10,u3,u2),(u7,u0,u1),(u6,u2,u4),(u45,u7,u6)],[0,2],[(0,35)]),
([u75,u3,u0,u1,u6,u2],[(u19,u3,u4),(u5,u0,u1),(u75,u19,u5),(u6,u2,u4)],[0],[]),
([u23,u10,u97,u0,u1,u4],[(u10,u3,u2),(u5,u0,u1),(u23,u3,u5),(u97,u23,u2)],[0],[]),
([u23,u10,u0,u1,u6,u4],[(u10,u3,u2),(u5,u0,u1),(u23,u3,u5),(u6,u2,u4)],[6,8],[(0,36)]),
([u3,u0,u1,0xfd55fc00,u2,u4],[(u19,u3,u4),(u5,u0,u1),(u25,u5,u2),(0xfd55fc00,u19,u25)],[5],[]),
([0x57035500,u3,u0,u1,u2,u4],[(u10,u3,u2),(u5,u0,u1),(0x3030000,u5,u4),(0x57035500,0x3030000,u10)],[1],[]),
([u10,0xababaaaa,u0,u1,u2,u4],[(u10,u3,u2),(u5,u0,u1),(0x3030000,u5,u4),(0xababaaaa,0x3030000,u3)],[0],[]),
([u80,u3,u0,u1,u6,u4],[(u10,u3,u2),(u8,u0,u1),(u80,u8,u10),(u6,u2,u4)],[2],[]),
([u8,u16,u80,u3,u2,u4],[],[],[(0,37)]),
([u8,u16,0x45004500,u3,u2,u4],[],[],[(0,38)]),
([u23,u10,u0,u1,u2,u4],[(u10,u3,u2),(u8,u0,u1),(u5,u8,u1),(u23,u3,u5)],[0],[]),
([u8,u16,u10,u3,u36,u4],[(u10,u3,u2),(u16,u1,u0),(u36,u16,u2),(u8,u1,u0)],[1,8],[(0,39)]),
([0x5d0c5500,u3,u0,u1,u2,u4],[],[],[]),
([u3,u0,0xdf55cf00,u1,u2,u4],[(u19,u3,u4),(u16,u1,u0),(u36,u16,u2),(0xdf55cf00,u19,u36)],[1,5,8],[]),
([u8,u9,u10,u3,u2,u4],[(u10,u3,u2),(u8,u0,u1),(u16,u0,u1),(u9,u8,u16)],[0,1,3],[(0,37),(2,38),(2,39)]),
([0x3f0c3f0c,u10,u3,u0,u1,u4],[],[],[]),
([u10,u3,u0,u1,u72,u4],[],[],[]),
([u8,u10,u3,u1,u30,u4],[],[],[]),
([u10,u3,u0,0xcfcc0f00,u1,u4],[],[],[]),
([u11,u3,u0,0xddcc5500,u1,u4],[],[],[]),
([u10,u3,u0,u1,0xffcc3300,u4],[(u10,u3,u2),(u47,u0,u2),(u24,u0,u4),(0xffcc3300,u47,u24)],[0],[]),
([u3,u0,u110,u1,u6],[(u19,u3,u4),(u14,u0,u2),(u110,u19,u14),(u6,u2,u4)],[0,1,4,5],[]),
([0xa888fccc,u3,u0,u1,u2,u4],[(u19,u3,u4),(u18,u1,u2),(u50,u18,u0),(0xa888fccc,u19,u50)],[1],[]),
([0x5d0cddcc,u3,u0,u1,u2,u4],[],[],[]),
([u33,u10,u3,u0,u1,u6],[(u10,u3,u2),(u17,u1,u4),(u33,u17,u0),(u6,u2,u4)],[3],[]),
([u10,u3,u24,u1,u30],[(u10,u3,u2),(u24,u0,u4),(u6,u2,u4),(u30,u0,u6)],[0,1,2,7,8],[]),
([0x8a88cfcc,u3,u0,u1,u2,u4],[],[],[]),
([u3,u0,0xd5c0ddcc,u1,u2,u4],[],[],[]),
([u23,u20,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u23,u3,u5)],[0,1,2],[]),
([u41,u3,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u41,u20,u5)],[1],[(0,40)]),
([u41,u3,u20,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u41,u20,u5)],[1],[(0,41)]),
([u3,u86,u20,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u86,u20,u2)],[0,1],[]),
([u96,u3,u20,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u96,u20,u2)],[0],[(0,42)]),
([u3,u20,u25,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u25,u5,u2)],[1],[(0,43)]),
([u3,u20,u5,u6,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u6,u2,u4)],[0,1,2],[(0,44),(0,45),(0,46)]),
([u23,u0,u20,u1,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u23,u3,u5)],[1],[]),
([u41,u3,u0,u1,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u41,u20,u5)],[1],[]),
([u3,u20,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u8,u0,u1),(u5,u8,u1)],[0,1,2,3,8],[]),
([u31,u0,u20,u1,u2,u4],[(u7,u1,u0),(u20,u3,u7),(u11,u1,u2),(u31,u11,u3)],[1,6],[]),
([u3,u0,0xefeaefea,u1,u2,u4],[(u7,u1,u0),(u20,u3,u7),(u11,u1,u2),(0xefeaefea,u11,u20)],[0],[]),
([u85,u0,u20,u1,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u96,u20,u2),(u85,u96,u3)],[1,4,5],[(0,42)]),
([u0,u20,u1,u2,u21,u4],[(u7,u0,u1),(u20,u3,u7),(u6,u2,u4),(u21,u3,u6)],[3,4,5,7],[(0,44)]),
([u3,u0,u1,u2,0xffeaeaea,u4],[(u7,u0,u1),(u20,u3,u7),(u6,u2,u4),(0xffeaeaea,u20,u6)],[0,2,3,8],[(0,45)]),
([0xeaeaea,u3,u0,u1,u2,u4],[],[],[(0,46)]),
([u28,u3,u20,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u28,u7,u2),(u5,u0,u1)],[0,1],[(0,42)]),
([u23,u7,u20,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u23,u3,u5)],[1],[(0,47)]),
([u9,u3,u20,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u9,u7,u5)],[0,1,2,3],[(0,24),(0,48),(0,49),(1,24),(1,49)]),
([u9,u3,u20,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u9,u7,u5)],[1],[(0,41),(0,47)]),
([u41,u3,u7,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u41,u20,u5)],[1],[]),
([u3,u7,u86,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1),(u86,u20,u2)],[0,1],[(0,49)]),
([u9,u3,u2,u4],[(u7,u0,u1),(u8,u7,u0),(u5,u8,u1),(u9,u7,u5)],[0,1,2],[(0,25),(0,50),(0,51),(0,52),(0,53),(0,54),(1,25),(1,52),(1,53)]),
([u3,u7,u5,u6,u2,u4],[(u7,u0,u1),(u8,u7,u0),(u5,u8,u1),(u6,u2,u4)],[0,3],[(0,54),(0,55)]),
([u8,u16,u3,u6,u2,u4],[],[],[(0,54)]),
([u8,u3,u1,u2,u45,u4],[(u7,u0,u1),(u8,u7,u0),(u6,u2,u4),(u45,u7,u6)],[0],[(0,55)]),
([u3,u0,u1,u2,u72,u4],[],[],[]),
([u0,0xea00aa00,u112,u1,u2,u4],[(u7,u0,u1),(u91,u7,u4),(u112,u3,u91),(0xea00aa00,u112,u2)],[0],[]),
([0x15005500,u0,u112,u1,u2,u4],[(u7,u0,u1),(u91,u7,u4),(u112,u3,u91),(0x15005500,u112,u2)],[0,7],[]),
([u3,u85,u7,u5,u2,u4],[(u7,u0,u1),(u28,u7,u2),(u85,u28,u3),(u5,u0,u1)],[0,1],[(0,42),(0,56),(0,57)]),
([u3,u0,u1,u2,u45,u4],[(u7,u0,u1),(u28,u7,u2),(u121,u28,u4),(u45,u121,u7)],[0,2],[(0,55)]),
([u121,u3,u7,u5,u2,u4],[(u7,u0,u1),(u28,u7,u2),(u121,u28,u4),(u5,u0,u1)],[0],[(0,55),(0,58)]),
([u3,0xc000ff00,u7,u5,u2,u4],[(u7,u0,u1),(u66,u7,u4),(0xc000ff00,u66,u2),(u5,u0,u1)],[0],[(0,59)]),
([u28,u66,u3,u5,u2,u4],[(u7,u0,u1),(u28,u7,u2),(u66,u7,u4),(u5,u0,u1)],[0,2],[]),
([u49,u3,u7,u5,u2,u4],[(u7,u0,u1),(u28,u7,u2),(u5,u0,u1),(u49,u28,u5)],[0],[]),
([u9,u28,u3,u2,u4],[(u7,u0,u1),(u28,u7,u2),(u5,u0,u1),(u9,u7,u5)],[0,1,2,3],[(0,24),(0,26),(0,57),(0,58),(0,60),(1,59)]),
([u9,u28,u3,u5,u2,u4],[(u7,u0,u1),(u28,u7,u2),(u5,u0,u1),(u9,u7,u5)],[0],[(0,61)]),
([u28,u3,u7,u25,u5,u4],[(u7,u0,u1),(u28,u7,u2),(u5,u0,u1),(u25,u5,u2)],[0,1],[(0,61)]),
([u41,u23,u3,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u23,u3,u5),(u41,u23,u7)],[1],[(0,62)]),
([u3,u97,u7,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u23,u3,u5),(u97,u23,u2)],[1],[(0,63),(0,64)]),
([u9,u23,u3,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u23,u3,u5),(u9,u7,u5)],[0,1,2,8],[(0,27),(0,29),(0,64),(0,65),(1,27),(1,29),(1,64)]),
([u9,u23,u3,u7,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u23,u3,u5),(u9,u7,u5)],[1],[(0,47)]),
([u9,u3,u42,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u42,u9,u3)],[0,1,2],[(0,33),(0,66),(0,67),(1,33),(1,67)]),
([u41,u9,u3,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u41,u9,u3)],[0,1,2],[(0,30),(0,66),(0,68),(1,30),(1,68)]),
([u49,u9,u3,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u49,u9,u2)],[0,1,2],[(0,30),(0,69),(0,70),(0,71),(1,72)]),
([u9,u3,u46,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u46,u9,u2)],[0,1,2],[(0,33),(0,34),(0,70),(0,73),(0,74),(0,76),(1,75)]),
([u9,u3,u6,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u6,u2,u4)],[0,1,2],[(0,21),(0,71),(0,74),(0,76),(0,77),(0,78),(0,79),(1,76),(1,80)]),
([u9,u3,u42,u7,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u42,u9,u3)],[1],[(0,48)]),
([u41,u9,u3,u7,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u41,u9,u3)],[1],[]),
([u49,u9,u3,u7,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u49,u9,u2)],[0],[]),
([u9,u3,u7,u46,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u46,u9,u2)],[0],[(0,60)]),
([u9,u3,u7,u6,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u6,u2,u4)],[0,2,3],[(0,58),(0,81)]),
([u3,u42,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u42,u9,u3)],[1,8],[(0,40)]),
([u9,u3,u42,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u42,u9,u3)],[1],[(0,40),(0,65)]),
([u41,u9,u3,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u41,u9,u3)],[1],[(0,40)]),
([u49,u9,u3,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u49,u9,u2)],[0],[]),
([u9,u3,u46,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u46,u9,u2)],[0],[(0,82)]),
([u9,u3,u25,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u25,u5,u2)],[0,1,2,8],[(0,27),(0,82),(0,83),(0,84),(1,85)]),
([u9,u3,u5,u6,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u6,u2,u4)],[0,2,8],[(0,84),(0,86),(0,87),(0,88),(1,89)]),
([u3,u42,u7,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u42,u9,u3)],[1],[(0,41)]),
([u3,u7,u46,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u46,u9,u2)],[0],[]),
([u9,u3,u7,u25,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u25,u5,u2)],[0],[(0,61)]),
([u3,u7,u5,u81,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u25,u5,u2),(u81,u3,u25)],[1],[(0,43),(0,83)]),
([u3,u7,0xfc000000,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u25,u5,u2),(0xfc000000,u25,u4)],[1,3],[(0,84),(0,90),(0,91)]),
([0x300ff00,u3,u7,u5,u2,u4],[],[],[(0,85)]),
([u3,u7,u25,u5,u6,u4],[(u7,u0,u1),(u5,u0,u1),(u25,u5,u2),(u6,u2,u4)],[2,8],[(0,92)]),
([u3,u7,u5,u2,u21,u4],[(u7,u0,u1),(u5,u0,u1),(u6,u2,u4),(u21,u3,u6)],[3,8],[(0,44),(0,45),(0,79),(0,93)]),
([u3,u5,u2,u45,u4],[(u7,u0,u1),(u5,u0,u1),(u6,u2,u4),(u45,u7,u6)],[0,2],[(0,35),(0,45),(0,87),(0,91),(0,92),(0,94),(1,35),(1,92)]),
([u3,u7,u5,u2,u45,u4],[(u7,u0,u1),(u5,u0,u1),(u6,u2,u4),(u45,u7,u6)],[0,2,3],[(0,81)]),
([u3,u5,u6,u2,u45,u4],[(u7,u0,u1),(u5,u0,u1),(u6,u2,u4),(u45,u7,u6)],[0,2,3],[]),
([0xc0c0c0,u3,u5,u6,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u6,u2,u4),(0xc0c0c0,u7,u6)],[0],[(0,55),(0,95)]),
([u62,u3,u7,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u6,u2,u4),(u62,u5,u6)],[3],[(0,87),(0,88)]),
([u9,u3,u42,u0,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u42,u9,u3)],[1,3,8],[]),
([u41,u9,u3,u0,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u41,u9,u3)],[1,3,8],[]),
([u49,u9,u3,u0,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u49,u9,u2)],[0,3,8],[]),
([u9,u3,u46,u0,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u46,u9,u2)],[0,3,8],[]),
([u9,u3,u0,u6,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u6,u2,u4)],[0,2,3,8],[]),
([u3,u0,u5,u2,u45,u4],[(u7,u0,u1),(u5,u0,u1),(u6,u2,u4),(u45,u7,u6)],[0,2,3],[]),
([u3,u42,u0,u1,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5),(u42,u9,u3)],[1],[]),
([0x45404540,u3,u0,u1,u2,u4],[],[],[]),
([0x3f2a2a2a,u3,u0,u1,u2,u4],[],[],[]),
([0x55404040,u3,u0,u1,u2,u4],[],[],[(0,94)]),
([u23,u0,u1,u81,u2,u4],[(u5,u0,u1),(u23,u3,u5),(u105,u23,u2),(u81,u105,u3)],[1,5],[]),
([0x4045454,u3,u0,u1,u2,u4],[],[],[]),
([u23,u0,u32,u1,u2,u4],[(u5,u0,u1),(u23,u3,u5),(u14,u0,u2),(u32,u3,u14)],[1],[]),
([u3,u0,u1,u2,0xff545454,u4],[(u5,u0,u1),(u23,u3,u5),(u6,u2,u4),(0xff545454,u23,u6)],[0,2,8],[(0,36),(1,36)]),
([0x545454,u3,u0,u1,u2,u4],[],[],[]),
([u26,u23,u3,u1,u2,u4],[],[],[]),
([u3,u0,u5,u2,u72,u4],[(u5,u0,u1),(u8,u0,u1),(u6,u2,u4),(u72,u8,u6)],[3],[]),
([u3,0xaeaefefe,u0,u1,u2,u4],[(u5,u1,u0),(u17,u1,u4),(u98,u17,u5),(0xaeaefefe,u98,u3)],[2],[]),
([u98,u3,u0,u1,u6,u2],[(u5,u1,u0),(u17,u1,u4),(u98,u17,u5),(u6,u2,u4)],[0],[]),
([u0,u1,u5,0xfeaaaaaa,u2,u4],[],[],[(0,90)]),
([u62,u3,u0,u1,u2,u4],[],[],[]),
([u3,u0,u1,u25,u92,u6],[(u5,u0,u1),(u25,u5,u2),(u92,u5,u4),(u6,u2,u4)],[0,2,6,8],[]),
([u3,u0,u1,0xfca8a8a8,u2,u4],[(u5,u0,u1),(u6,u2,u4),(u21,u3,u6),(0xfca8a8a8,u5,u21)],[1,3,5,8],[(0,1),(0,93),(2,1)]),
([u3,u5,u2,u30,u37,u4],[(u5,u1,u0),(u6,u2,u4),(u37,u1,u6),(u30,u0,u6)],[0,5,7],[(0,55)]),
([u26,u3,u5,u2,u37,u4],[(u5,u1,u0),(u6,u2,u4),(u37,u1,u6),(u26,u0,u6)],[3,5,7],[]),
([u3,0xccc0c0c0,u5,u6,u2,u4],[(u5,u1,u0),(u6,u2,u4),(u37,u1,u6),(0xccc0c0c0,u0,u37)],[0,3],[(0,55)]),
([u3,u113,u1,u5,u2,u4],[(u5,u0,u1),(u6,u2,u4),(u26,u0,u6),(u113,u26,u3)],[4],[]),
([u3,u0,0xfc0c0c0c,u5,u2,u4],[(u5,u1,u0),(u6,u2,u4),(u69,u1,u6),(0xfc0c0c0c,u69,u5)],[3,4],[]),
([u26,u69,u3,u5,u2,u4],[(u5,u0,u1),(u6,u2,u4),(u26,u0,u6),(u69,u1,u6)],[3],[]),
([0x55545454,u0,u1,u6,u2,u4],[(u5,u0,u1),(u6,u2,u4),(0xfffcfcfc,u5,u6),(0x55545454,u3,0xfffcfcfc)],[0],[]),
([u3,0xaafefefe,u0,u1,u2,u4],[(u5,u0,u1),(u6,u2,u4),(u62,u5,u6),(0xaafefefe,u62,u3)],[0,2],[]),
([u27,u0,u1,u123,u2,u4],[(u8,u0,u1),(u27,u8,u3),(0x51005100,u27,u2),(u123,0x51005100,u3)],[1,5,6],[]),
([u27,u57,u0,u1,u2,u4],[(u16,u1,u0),(u57,u16,u3),(u8,u1,u0),(u27,u8,u3)],[1,8],[]),
([u27,u101,u0,u1,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u47,u0,u2),(u101,u47,u3)],[1,6],[]),
([u3,0xbfaebfae,u0,u1,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u47,u0,u2),(0xbfaebfae,u47,u27)],[0],[]),
([u27,u0,u1,u34,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u18,u1,u2),(u34,u3,u18)],[1,5],[]),
([u3,u0,u1,0xfeaefeae,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u18,u1,u2),(0xfeaefeae,u27,u18)],[8],[]),
([u27,u0,u1,u2,u21,u4],[(u8,u0,u1),(u27,u8,u3),(u6,u2,u4),(u21,u3,u6)],[3,6],[]),
([u3,u0,u1,u2,0xffaeaeae,u4],[(u8,u0,u1),(u27,u8,u3),(u6,u2,u4),(0xffaeaeae,u27,u6)],[8],[]),
([0xaeaeae,u3,u0,u1,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u6,u2,u4),(0xaeaeae,u27,u6)],[0,2],[]),
([u3,u27,u1,u2,u30,u4],[],[],[]),
([u8,u16,u3,0xae00ae00,u2,u4],[],[],[(0,96)]),
([u9,u3,u27,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u16,u0,u1),(u9,u8,u16)],[0,1,2,3],[(0,96),(0,97),(1,96),(2,38),(3,38)]),
([u8,u9,u3,u57,u2,u4],[(u16,u1,u0),(u57,u16,u3),(u8,u1,u0),(u9,u16,u8)],[1],[(0,98)]),
([u8,u16,u27,u57,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u16,u0,u1),(u57,u16,u3)],[1],[(0,98)]),
([u8,u16,u3,u42,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u16,u0,u1),(u42,u16,u27)],[1],[]),
([u3,u0,u36,u93,u1,u6],[(u16,u1,u0),(u36,u16,u2),(u93,u16,u4),(u6,u2,u4)],[0,2,4],[]),
([u8,u16,u3,0xefaaefaa,u2,u4],[],[],[(0,99)]),
([u9,u3,u36,u2,u4],[(u16,u1,u0),(u36,u16,u2),(u8,u1,u0),(u9,u8,u16)],[0,1,2,8],[(0,38),(0,39),(0,99),(0,100),(0,101),(0,103),(3,102)]),
([u8,u9,u3,u36,u2,u4],[(u16,u1,u0),(u36,u16,u2),(u8,u1,u0),(u9,u8,u16)],[0],[(0,104)]),
([u8,u16,u3,u46,u2,u4],[(u16,u1,u0),(u36,u16,u2),(u8,u1,u0),(u46,u8,u36)],[0],[]),
([u8,u16,u3,u36,u51,u4],[(u16,u1,u0),(u36,u16,u2),(u8,u1,u0),(u51,u8,u2)],[0,1],[(0,104)]),
([u8,u16,u3,0xcf000000,u2,u4],[],[],[(0,101)]),
([0xc00ff00,u8,u16,u3,u2,u4],[],[],[(0,102)]),
([u8,u16,u3,u36,u6,u4],[(u16,u1,u0),(u36,u16,u2),(u8,u1,u0),(u6,u2,u4)],[2,8],[(0,103)]),
([u8,u9,u3,u42,u2,u4],[(u8,u0,u1),(u16,u0,u1),(u9,u8,u16),(u42,u9,u3)],[1],[]),
([u8,u41,u9,u3,u2,u4],[(u8,u0,u1),(u16,u0,u1),(u9,u8,u16),(u41,u9,u3)],[1],[(0,97)]),
([u8,u49,u9,u3,u2,u4],[(u8,u0,u1),(u16,u0,u1),(u9,u8,u16),(u49,u9,u2)],[0],[(2,100)]),
([u8,u9,u3,u46,u2,u4],[(u8,u0,u1),(u16,u0,u1),(u9,u8,u16),(u46,u9,u2)],[0],[]),
([u8,u9,u3,u6,u2,u4],[(u8,u0,u1),(u16,u0,u1),(u9,u8,u16),(u6,u2,u4)],[0,2,3],[(0,105),(2,101),(2,103),(3,103)]),
([u8,u41,u16,u3,u2,u4],[(u8,u0,u1),(u16,u0,u1),(u9,u8,u16),(u41,u9,u3)],[1],[]),
([u8,u16,u49,u3,u2,u4],[(u8,u0,u1),(u16,u0,u1),(u9,u8,u16),(u49,u9,u2)],[0],[]),
([u8,u16,u3,u2,u72,u4],[],[],[(0,105)]),
([u8,u16,u3,u2,u21,u4],[],[],[(0,79)]),
([u8,u16,u10,u3,u6,u4],[],[],[]),
([u8,u3,u1,u2,0xff303030,u4],[(u16,u1,u0),(u8,u1,u0),(u6,u2,u4),(0xff303030,u16,u6)],[3,4],[]),
([0x15041504,u3,u0,u1,u2,u4],[],[],[]),
([0x54045404,u3,u0,u1,u2,u4],[],[],[]),
([u3,u0,u1,0xfc0cfc0c,u6,u4],[(u8,u0,u1),(u18,u1,u2),(0xfc0cfc0c,u8,u18),(u6,u2,u4)],[2,6],[]),
([0x55040404,u3,u0,u1,u2,u4],[],[],[]),
([u3,u0,0xcf8a8a8a,u1,u2,u4],[(u16,u1,u0),(u6,u2,u4),(u21,u3,u6),(0xcf8a8a8a,u16,u21)],[3],[]),
([u8,u3,u1,0xf3c0c0c0,u2,u4],[(u8,u0,u1),(u6,u2,u4),(u30,u0,u6),(0xf3c0c0c0,u8,u30)],[8],[]),
([u8,u126,u3,u1,u2,u4],[],[],[]),
([u8,u3,0xf0303030,u6,u2,u4],[],[],[(0,95)]),
([u3,u55,u0,u74,u1,u2],[],[],[]),
([u31,u0,u1,u38,u2,u4],[(u17,u1,u4),(u38,u3,u17),(u11,u1,u2),(u31,u11,u3)],[1,7],[]),
([u3,u0,u1,u2,0xffaffaaa,u4],[(u18,u1,u2),(u34,u3,u18),(u35,u1,u4),(0xffaffaaa,u35,u34)],[2],[]),
([0x1f005f00,u3,u0,u74,u1,u4],[],[],[]),
([u3,u82,u1,0xfeeefeee,u2,u4],[],[],[(0,107),(3,106)]),
([0x54445444,u0,u1,u34,u2,u4],[(u18,u1,u2),(u34,u3,u18),(0xfeeefeee,u34,u0),(0x54445444,u3,0xfeeefeee)],[1,8],[]),
([u40,u3,u0,u34,u2,u4],[],[],[]),
([u3,u0,u32,u1,0xfefa0000,u2],[(u14,u0,u2),(u32,u3,u14),(u107,u32,u1),(0xfefa0000,u107,u4)],[6],[(2,107)]),
([0x4044444,0x32322222,u3,u1,u2,u4],[],[],[(2,106)]),
([u114,u0,u1,u38,u2,u4],[(u17,u1,u4),(u38,u3,u17),(0x4044444,u38,u0),(u114,0x4044444,u3)],[1,4,7],[]),
([u106,u0,u1,u38,u2,u4],[(u17,u1,u4),(u38,u3,u17),(u87,u38,u2),(u106,u87,u3)],[1,4,5,7],[(0,108)]),
([u87,u3,u0,u1,u38,u6],[(u17,u1,u4),(u38,u3,u17),(u87,u38,u2),(u6,u2,u4)],[0],[(0,108)]),
([u0,u32,u1,u38,u2,u4],[(u17,u1,u4),(u38,u3,u17),(u14,u0,u2),(u32,u3,u14)],[3,4,5,7],[(0,109)]),
([u3,u0,u1,0xfeeefaaa,u2,u4],[(u18,u1,u2),(u34,u3,u18),(u24,u0,u4),(0xfeeefaaa,u24,u34)],[0,2,6,8],[(0,110)]),
([0xe0aeeaa,u3,u0,u1,u2,u4],[],[],[]),
([u3,u14,u0,u1,u38,u6],[(u17,u1,u4),(u38,u3,u17),(u14,u0,u2),(u6,u2,u4)],[3],[(0,109),(1,110)]),
([u31,u0,u74,u1,u2,u4],[(u24,u0,u4),(u74,u3,u24),(u11,u1,u2),(u31,u11,u3)],[3,6],[]),
([u3,u0,0xefafeeaa,u1,u2,u4],[(u14,u0,u2),(u32,u3,u14),(u35,u1,u4),(0xefafeeaa,u35,u32)],[2],[]),
([u3,0xc888faaa,u0,u1,u2,u4],[(u18,u1,u2),(u34,u3,u18),(u29,u0,u4),(0xc888faaa,u29,u34)],[1,3],[]),
([u3,u0,u34,u37,u4],[(u18,u1,u2),(u34,u3,u18),(u6,u2,u4),(u37,u1,u6)],[0,1,2,4,6],[(0,11)]),
([u3,u82,u1,u50,u2,u4],[(u18,u1,u2),(u34,u3,u18),(u50,u18,u0),(u82,u34,u0)],[2,4],[]),
([u33,0x32322222,u3,u1,u2,u4],[],[],[]),
([0x1f005f00,u3,u24,u0,u1,u4],[(u24,u0,u4),(u74,u3,u24),(0xe0e0a0a0,u74,u1),(0x1f005f00,0xe0e0a0a0,u2)],[2],[]),
([u3,u63,u1,u50,u2,u4],[],[],[]),
([u3,0xccc0fcf0,u0,u1,u2,u4],[],[],[]),
([u3,0xc000cccc,u1,u50,u2,u4],[],[],[]),
([u3,u0,0xcf0fcc00,u1,u2,u4],[],[],[]),
([u3,u114,u0,u1,u6,u2],[(u17,u1,u4),(u33,u17,u0),(u114,u33,u3),(u6,u2,u4)],[0],[]),
([0xf0ccfcc,u3,u0,u1,u2,u4],[],[],[]),
([u33,u3,u52,u1,u2,u4],[],[],[]),
([u3,u0,u1,u115,u2,u4],[(u18,u1,u2),(0xccc0ccc,u18,u0),(0xccc0000,0xccc0ccc,u4),(u115,0xccc0000,u18)],[2,5],[]),
([u33,u3,0xcfccffcc,u1,u2,u4],[],[],[]),
([u11,u3,u0,u1,u115,u4],[(u18,u1,u2),(u11,u18,u2),(u24,u0,u4),(u115,u24,u18)],[2],[]),
([0xc8888888,u0,u1,u120,u2,u4],[(u18,u1,u2),(u77,u18,u4),(u120,u3,u77),(0xc8888888,u120,u0)],[1,4,5,7],[]),
([u0,u89,u1,0xfefafafa,u2,u4],[(u14,u0,u2),(u59,u14,u4),(u89,u3,u59),(0xfefafafa,u89,u1)],[0,2,3,5,7],[(2,7),(2,111)]),
([0xe0a0a0a,u0,u89,u1,u2,u4],[],[],[(2,112)]),
([0x4444444,u0,u1,u120,u2,u4],[],[],[(0,112)]),
([u11,u3,0xc0f000f0,u24,u0,u4],[],[],[]),
([0x55055000,u3,u0,u1,u2,u4],[],[],[]),
([0x54445000,u3,u0,u1,u2,u4],[],[],[(0,113)]),
([u3,u0,u1,u115,u6],[(u24,u0,u4),(u18,u1,u2),(u115,u24,u18),(u6,u2,u4)],[0,2,5],[(0,110),(0,113)]),
([0xb0abbaa,u3,u0,u1,u2,u4],[],[],[]),
([0x45054400,u3,u0,u1,u2,u4],[],[],[]),
([u127,u3,u102,u1,u2,u4],[],[],[(3,114)]),
([0x45444544,u31,u0,u1,u2,u4],[(u11,u1,u2),(u31,u11,u3),(u102,u31,u0),(0x45444544,u3,u102)],[1,8],[]),
([u3,u31,u0,u68,u2,u4],[(u11,u1,u2),(u31,u11,u3),(u102,u31,u0),(u68,u102,u1)],[8],[]),
([0xb0a0b0a,0x40504050,u3,u0,u2,u4],[],[],[(1,114)]),
([u31,u0,0xeaeeeaee,u1,u2,u4],[(u11,u1,u2),(u31,u11,u3),(0x40444044,u31,u0),(0xeaeeeaee,0x40444044,u3)],[1,6],[]),
([u31,u0,u1,0xfaffaaaa,u2,u4],[(u11,u1,u2),(u31,u11,u3),(0x50550000,u31,u4),(0xfaffaaaa,0x50550000,u3)],[1,6,7],[]),
([u3,0xbfafbbaa,u0,u1,u2,u4],[],[],[]),
([0x8c88afaa,u3,u0,u1,u2,u4],[(u11,u1,u2),(u31,u11,u3),(u29,u0,u4),(0x8c88afaa,u29,u31)],[1],[]),
([u127,u3,u52,u1,u2,u4],[(u11,u1,u2),(u31,u11,u3),(u52,u11,u0),(u127,u31,u0)],[0],[]),
([0xb0a0b0a,u3,0xc0f0c0f0,u0,u2,u4],[],[],[]),
([0xc00cccc,u3,u52,u1,u2,u4],[],[],[]),
([0x3f0f3300,u3,u0,u1,u2,u4],[],[],[]),
([u3,u63,u1,0xfcccffcc,u2,u4],[],[],[]),
([0x15051100,u3,u0,u1,u2,u4],[],[],[]),
([u3,u0,0xfcf8f8f8,u2,u21,u4],[(u6,u2,u4),(u21,u3,u6),(u73,u0,u21),(0xfcf8f8f8,u73,u1)],[3],[(0,14),(2,115)]),
([0xc4c4c4c,u3,u1,u2,u21,u4],[],[],[]),
([u3,u73,u1,u2,u100,u4],[],[],[(0,117),(2,115),(2,116)]),
([u126,u0,u1,u2,u21,u4],[(u6,u2,u4),(u21,u3,u6),(u100,u0,u21),(u126,u3,u100)],[1,8],[]),
([u3,0xccc8c8c8,u1,u2,u21,u4],[(u6,u2,u4),(u21,u3,u6),(0xfffafafa,u1,u21),(0xccc8c8c8,u0,0xfffafafa)],[6],[(2,117)]),
([0xf0e0e0e,u3,u0,u2,u21,u4],[],[],[]),
([u113,u0,u1,u2,u21,u4],[(u6,u2,u4),(u21,u3,u6),(0x444444,u0,u21),(u113,0x444444,u3)],[1,5,7],[]),
([0x444444,0x33222222,u3,u1,u2,u4],[],[],[(2,116)]),
([u3,u73,u1,u2,u30,u4],[(u6,u2,u4),(u21,u3,u6),(u30,u0,u6),(u73,u0,u21)],[0,5],[(2,118)]),
([u26,0x33222222,u3,u1,u2,u4],[],[],[]),
([u3,u0,0xfcf8f8f8,u6,u2,u4],[(u6,u2,u4),(u21,u3,u6),(u73,u0,u21),(0xfcf8f8f8,u73,u1)],[0,3],[(2,118)]),
([0xc4c4c4c,u3,u1,u6,u2,u4],[(u6,u2,u4),(u21,u3,u6),(0xf0a0a0a0,u1,u21),(0xc4c4c4c,0xf0a0a0a0,u0)],[0],[]),
([u3,0xccc0c0c0,u1,u2,u30,u4],[(u6,u2,u4),(u30,u0,u6),(u37,u1,u6),(0xccc0c0c0,u0,u37)],[0,3,5],[]),
([u3,0xcc0c0c0c,u1,u2,u30,u4],[],[],[]),
([u26,0x33303030,u3,u1,u2,u4],[],[],[]),
([u26,u3,0xccfcfcfc,u1,u2,u4],[],[],[])
]
set_option maxRecDepth 100000 in
def c5_0_L6 : Array W5Node := Array.mk [
([u13,u0,u12,u18,u1,u2,u4],[(u12,u3,u0),(u13,u3,u0),(u18,u1,u2)],[1,3,8],[(2,0)]),
([u11,u13,u0,u12,u1,u2,u4],[(u12,u3,u0),(u13,u3,u0),(u11,u1,u2)],[0,1],[]),
([u13,u0,u12,u1,u6,u2,u4],[(u12,u3,u0),(u13,u3,u0),(u6,u2,u4)],[0,1,3,8],[(0,1)]),
([u8,u3,u12,u1,u2,u4],[(u12,u3,u0),(u7,u0,u1),(u8,u7,u0)],[1,3,8],[]),
([0x2e2e2e2e,u3,u0,u1,u2,u4],[(u12,u3,u0),(u7,u0,u1),(0x2e2e2e2e,u7,u12)],[0,1,2,3,5,7,8],[]),
([u28,u3,u0,u12,u1,u2,u4],[(u12,u3,u0),(u7,u0,u1),(u28,u7,u2)],[0,5],[]),
([u3,u7,u0,u43,u1,u2,u4],[(u12,u3,u0),(u7,u0,u1),(u43,u12,u2)],[0,5,8],[]),
([u3,u39,u5,u2,u4],[(u15,u3,u1),(u5,u1,u0),(u39,u0,u15)],[0,1,2,3,6,8],[(0,2)]),
([u3,u14,u0,u15,u5,u2,u4],[(u15,u3,u1),(u5,u1,u0),(u14,u0,u2)],[0,1,3],[(0,3),(3,4)]),
([u3,u0,u15,u5,u6,u2,u4],[(u15,u3,u1),(u5,u1,u0),(u6,u2,u4)],[0,1,6,8],[(0,2),(0,5),(0,6),(0,8),(2,7)]),
([u8,u3,0xe2e2e2e2,u1,u2,u4],[(u12,u3,u0),(u8,u0,u1),(0xe2e2e2e2,u8,u12)],[1,3,8],[(2,9),(3,9)]),
([u3,u119,u0,u15,u2,u4],[(u15,u3,u1),(u16,u1,u0),(u119,u16,u15)],[1,4,6,8],[(0,10),(1,10)]),
([u8,u3,0xe2e2e2e2,u12,u1,u2,u4],[(u12,u3,u0),(u8,u0,u1),(0xe2e2e2e2,u8,u12)],[3,8],[]),
([u8,u3,u12,u1,u51,u2,u4],[(u12,u3,u0),(u8,u0,u1),(u51,u8,u2)],[0,1],[(0,11),(2,9)]),
([u8,u3,u68,u12,u1,u2,u4],[(u12,u3,u0),(u8,u0,u1),(u68,u12,u1)],[1,8],[]),
([u8,u3,u43,u12,u1,u2,u4],[(u12,u3,u0),(u8,u0,u1),(u43,u12,u2)],[0],[(2,10)]),
([u8,u3,u12,u18,u1,u2,u4],[(u12,u3,u0),(u8,u0,u1),(u18,u1,u2)],[1,4],[(0,13),(2,12)]),
([u8,u3,u12,u1,u6,u2,u4],[(u12,u3,u0),(u8,u0,u1),(u6,u2,u4)],[0,1,3,8],[(0,15),(0,16),(2,14)]),
([u3,u119,u0,u1,u2,u4],[(u15,u3,u1),(u16,u1,u0),(u119,u16,u15)],[0,1,2,3,4,5,6,7,8],[]),
([u3,u0,u36,u1,u15,u2,u4],[(u15,u3,u1),(u16,u1,u0),(u36,u16,u2)],[0,1,5],[(2,17)]),
([u8,u3,u0,u43,u1,u2,u4],[(u12,u3,u0),(u8,u0,u1),(u43,u12,u2)],[0,1,5,8],[]),
([0xa0afafa,u3,u0,u1,u2,u4],[(u15,u3,u1),(u17,u1,u4),(0xa0afafa,u17,u15)],[0,1,2,3,4,5,8],[(0,18)]),
([u3,u0,u12,u1,u67,u2,u4],[(u12,u3,u0),(u14,u0,u2),(u67,u14,u1)],[0,3,6,8],[(0,20),(2,19)]),
([u33,u3,u0,u1,u15,u2,u4],[(u15,u3,u1),(u17,u1,u4),(u33,u17,u0)],[1,2,3,4,8],[(0,22),(3,21)]),
([u44,u3,u0,u1,u15,u2,u4],[(u15,u3,u1),(u17,u1,u4),(u44,u17,u2)],[0,1,5],[]),
([u3,u39,u0,u18,u1,u2,u4],[(u15,u3,u1),(u18,u1,u2),(u39,u15,u0)],[0,1,3,5,6,8],[(0,19),(2,20)]),
([u40,u3,u14,u0,u1,u2,u4],[(u12,u3,u0),(u14,u0,u2),(u40,u12,u1)],[0,3,6],[(0,21),(3,22)]),
([u3,u14,u0,u79,u1,u2,u4],[(u12,u3,u0),(u14,u0,u2),(u79,u12,u4)],[0,2,7],[]),
([u3,u14,u0,u12,u1,u6,u4],[(u12,u3,u0),(u14,u0,u2),(u6,u2,u4)],[2,7,8],[(3,18)]),
([u11,u3,u0,u68,u2,u4],[(u12,u3,u0),(u68,u12,u1),(u11,u1,u2)],[0,1,4,8],[(0,23),(0,24),(3,25)]),
([u3,u39,u0,u1,u6,u2,u4],[(u15,u3,u1),(u39,u15,u0),(u6,u2,u4)],[0,1,2,3,5],[(0,2),(0,26),(2,24)]),
([u40,u3,u0,u68,u1,u2,u4],[(u12,u3,u0),(u68,u12,u1),(u40,u68,u12)],[1,8],[]),
([u3,0xc800c800,u0,u1,u15,u2,u4],[(u15,u3,u1),(u39,u15,u0),(0xc800c800,u39,u2)],[1,2,4],[(3,27),(3,28)]),
([0x1f001f00,u3,u0,u12,u1,u2,u4],[(u12,u3,u0),(u68,u12,u1),(0x1f001f00,u68,u2)],[0,5,6],[]),
([u3,u39,u14,u1,u15,u2,u4],[(u15,u3,u1),(u39,u15,u0),(u14,u0,u2)],[0,1,3,6,8],[(0,29),(0,30)]),
([u11,u3,u0,u68,u12,u2,u4],[(u12,u3,u0),(u68,u12,u1),(u11,u1,u2)],[6,8],[]),
([u3,u39,u0,u1,u58,u2,u4],[(u15,u3,u1),(u39,u15,u0),(u58,u15,u2)],[0,1,3,5,6,8],[(0,30),(0,31)]),
([u3,u0,u1,0xfe00fe00,u4],[(u12,u3,u0),(u76,u12,u1),(0xfe00fe00,u76,u2)],[0,1,2,5,6,8],[]),
([u3,u0,u1,u76,u6,u2,u4],[(u12,u3,u0),(u76,u12,u1),(u6,u2,u4)],[0,1,2,5,6,7,8],[(0,32),(0,33),(0,34),(2,33)]),
([u40,u3,u0,u18,u2,u4],[(u12,u3,u0),(u40,u12,u1),(u18,u1,u2)],[0,1,6,8],[(0,36),(0,38),(1,37),(2,35)]),
([u40,u3,u0,u1,u6,u2,u4],[(u12,u3,u0),(u40,u12,u1),(u6,u2,u4)],[0,1,2,5,6,7,8],[(0,36),(0,38),(0,39),(0,40),(0,41),(1,38)]),
([0xe000e00,u3,u0,u12,u1,u2,u4],[],[],[(3,42)]),
([u3,u0,0xcd00cd00,u1,u15,u2,u4],[(u15,u3,u1),(0x32323232,u15,u0),(0xcd00cd00,0x32323232,u2)],[0,1,3,4,5,6],[(2,17)]),
([u40,u3,u0,u43,u1,u2,u4],[(u12,u3,u0),(u40,u12,u1),(u43,u12,u2)],[0,4,5,6],[(0,44),(3,43)]),
([u40,u3,u0,u12,u18,u2,u4],[(u12,u3,u0),(u40,u12,u1),(u18,u1,u2)],[0,4,8],[(0,44),(0,45)]),
([u40,u11,u3,u0,u12,u2,u4],[(u12,u3,u0),(u40,u12,u1),(u11,u1,u2)],[0,4,8],[]),
([0x4040404,u3,u0,u1,u6,u2,u4],[(u15,u3,u1),(0x4040404,u15,u0),(u6,u2,u4)],[0,2,3,5,7],[(0,46),(0,47)]),
([u3,u14,u0,u1,u103,u2,u4],[(u15,u3,u1),(u103,u15,u4),(u14,u0,u2)],[0,2,3,5,7],[(1,48)]),
([u11,u3,u0,u79,u1,u2,u4],[(u12,u3,u0),(u79,u12,u4),(u11,u1,u2)],[0,2,5,6,7],[(1,49)]),
([u3,u0,u12,u1,0xfef0fef0,u2,u4],[(u12,u3,u0),(u43,u12,u2),(0xfef0fef0,u43,u1)],[0,2,6,8],[(1,50),(2,31)]),
([0x404cccc,u3,u0,u1,u15,u2,u4],[(u15,u3,u1),(u103,u15,u4),(0x404cccc,u103,u0)],[1,2,3,6,8],[(0,43)]),
([u3,u0,0xee000000,u12,u1,u2,u4],[(u12,u3,u0),(u43,u12,u2),(0xee000000,u43,u4)],[1,3],[(0,51),(0,52),(2,53)]),
([0x500ff00,u3,u0,u1,u15,u2,u4],[(u15,u3,u1),(u103,u15,u4),(0x500ff00,u103,u2)],[0,1,2,5],[]),
([u3,u0,u43,u79,u1,u2,u4],[(u12,u3,u0),(u43,u12,u2),(u79,u12,u4)],[0,2,5,7],[(0,54)]),
([u3,u14,u0,u1,u58,u15,u4],[(u15,u3,u1),(u58,u15,u2),(u14,u0,u2)],[0,1,6],[(0,30),(0,56),(2,44),(2,55)]),
([u3,u0,u43,u12,u1,u6,u4],[(u12,u3,u0),(u43,u12,u2),(u6,u2,u4)],[0,2,8],[(0,54),(0,57)]),
([0x5000500,u3,u24,u0,u1,u2,u4],[(u15,u3,u1),(0x5000500,u15,u2),(u24,u0,u4)],[0,2,3,5,6,7,8],[(1,58)]),
([0x5000500,u29,u3,u0,u1,u2,u4],[(u15,u3,u1),(0x5000500,u15,u2),(u29,u0,u4)],[2,3,6,8],[(2,59)]),
([u0,u32,u1,u15,u2,u4],[(u15,u3,u1),(u14,u0,u2),(u32,u3,u14)],[0,1,2,3,4,5],[(0,3),(0,29),(0,62),(0,63),(2,13),(2,45),(2,55),(2,60),(2,61)]),
([u14,u0,u32,u1,u15,u2,u4],[(u15,u3,u1),(u14,u0,u2),(u32,u3,u14)],[0,1,3,5],[(0,64),(2,60),(2,66),(3,65)]),
([u3,u14,u0,u15,u67,u2,u4],[(u15,u3,u1),(u14,u0,u2),(u67,u14,u1)],[0,1,3,4,5],[(0,64)]),
([u33,u3,u12,u1,u2,u4],[(u12,u3,u0),(u17,u1,u4),(u33,u17,u0)],[0,1,2,3,4,8],[(0,68),(3,67)]),
([u33,u3,u12,u17,u1,u2,u4],[(u12,u3,u0),(u17,u1,u4),(u33,u17,u0)],[1,2,4,7,8],[(0,65)]),
([u3,u14,u0,u1,u107,u2,u4],[(u15,u3,u1),(u14,u0,u2),(u107,u14,u15)],[0,2,8],[(0,69),(3,27)]),
([u99,u3,u0,u1,u2,u4],[(u12,u3,u0),(u17,u1,u4),(u99,u17,u12)],[0,1,2,3,5,8],[(0,70)]),
([u99,u3,u0,u17,u1,u2,u4],[(u12,u3,u0),(u17,u1,u4),(u99,u17,u12)],[2,6,8],[]),
([u99,u3,u0,u12,u1,u2,u4],[(u12,u3,u0),(u17,u1,u4),(u99,u17,u12)],[1,3,4],[]),
([u11,u3,u0,u12,u18,u1,u4],[(u12,u3,u0),(u18,u1,u2),(u11,u18,u2)],[0,1,4,6],[(0,60),(3,71)]),
([u3,u59,u0,u1,u15,u2,u4],[(u15,u3,u1),(u14,u0,u2),(u59,u14,u4)],[0,1,2,3,4,5,6,7],[(0,72),(2,36),(2,73)]),
([u44,u3,u0,u12,u1,u2,u4],[(u12,u3,u0),(u17,u1,u4),(u44,u17,u2)],[0,2,4,5,7,8],[(0,37),(3,74)]),
([u3,u14,u0,u1,u15,u6,u4],[(u15,u3,u1),(u14,u0,u2),(u6,u2,u4)],[1,2,3,5,7],[(0,63),(0,75),(2,38),(2,76),(3,68),(3,70)]),
([u11,u3,u0,u102,u1,u2,u4],[(u12,u3,u0),(u11,u1,u2),(u102,u11,u12)],[0,4],[(3,42)]),
([u3,u104,u0,u1,u2,u4],[(u15,u3,u1),(u29,u0,u4),(u104,u29,u15)],[0,1,2,3,5,8],[(0,71)]),
([u11,u3,u0,0xe0eee0ee,u1,u2,u4],[(u12,u3,u0),(u11,u1,u2),(0xe0eee0ee,u11,u12)],[0,8],[(3,71)]),
([u3,u104,u0,u1,u15,u2,u4],[(u15,u3,u1),(u29,u0,u4),(u104,u29,u15)],[1,8],[]),
([u83,u3,u0,u12,u1,u2,u4],[(u12,u3,u0),(u11,u1,u2),(u83,u11,u4)],[1,3,6,8],[(0,24),(0,77),(2,78)]),
([u3,u55,u0,u1,u15,u2,u4],[(u15,u3,u1),(u29,u0,u4),(u55,u29,u2)],[0,1,5,6,8],[(0,25),(3,79)]),
([u0,u12,u1,u2,u21,u4],[(u12,u3,u0),(u6,u2,u4),(u21,u3,u6)],[0,1,2,3,5,7],[(0,15),(0,32),(0,40),(0,57),(0,80),(1,57),(2,5),(2,81)]),
([u0,u12,u1,u6,u2,u21,u4],[(u12,u3,u0),(u6,u2,u4),(u21,u3,u6)],[0,1,5,7],[(0,83),(2,82)]),
([u3,u0,u15,u6,u2,u37,u4],[(u15,u3,u1),(u6,u2,u4),(u37,u1,u6)],[0,1,4,5,6,7],[(0,82)]),
([u26,u3,u12,u1,u2,u4],[(u12,u3,u0),(u6,u2,u4),(u26,u0,u6)],[0,1,2,3,6],[(0,33),(0,41),(2,84)]),
([u26,u3,u12,u1,u6,u2,u4],[(u12,u3,u0),(u6,u2,u4),(u26,u0,u6)],[0,1,5,7,8],[(0,83)]),
([u3,u0,u1,u6,u2,u100,u4],[(u12,u3,u0),(u6,u2,u4),(u100,u12,u6)],[0,2],[(0,51),(0,86),(2,85)]),
([u71,u3,u0,u1,u2,u4],[(u12,u3,u0),(u6,u2,u4),(u71,u12,u6)],[0,1,2,3,4,6],[(0,7),(0,16),(0,76),(1,76)]),
([u71,u3,u0,u12,u1,u2,u4],[(u12,u3,u0),(u6,u2,u4),(u71,u12,u6)],[1,3,5],[]),
([u71,u3,u0,u1,u6,u2,u4],[(u12,u3,u0),(u6,u2,u4),(u71,u12,u6)],[0,2,8],[]),
([u3,u0,u12,u1,u2,u37,u4],[(u12,u3,u0),(u6,u2,u4),(u37,u1,u6)],[0,2,3,6,8],[(0,87),(2,47),(2,75),(3,75)]),
([u26,u3,u0,u1,u15,u2,u4],[(u15,u3,u1),(u6,u2,u4),(u26,u0,u6)],[0,1,2,3,4,5,6,7],[(0,6),(0,33),(2,88)]),
([u53,u3,u5,u2,u4],[(u13,u3,u0),(u53,u13,u1),(u5,u0,u1)],[0,1,2,3,8],[(0,89),(0,90),(0,91),(0,92),(1,91)]),
([u53,u3,u0,u1,u6,u2,u4],[(u13,u3,u0),(u53,u13,u1),(u6,u2,u4)],[0,2,3,5],[(0,92),(0,93)]),
([u11,u3,u0,u64,u1,u2,u4],[(u22,u3,u1),(u64,u22,u0),(u11,u1,u2)],[0,3,5,8],[(1,94),(3,95)]),
([u3,u0,u64,u1,u6,u2,u4],[(u22,u3,u1),(u64,u22,u0),(u6,u2,u4)],[0,2,4,5,7,8],[(0,96),(0,97),(0,98)]),
([u60,u3,u0,u64,u1,u2,u4],[(u22,u3,u1),(u64,u22,u0),(u60,u22,u0)],[1,4,8],[]),
([u3,u61,u0,u64,u1,u2,u4],[(u22,u3,u1),(u64,u22,u0),(u61,u22,u2)],[0,3,5,8],[(1,99)]),
([u13,u3,u0,u1,0xf400f400,u2,u4],[(u13,u3,u0),(0xf4f4f4f4,u13,u1),(0xf400f400,0xf4f4f4f4,u2)],[0,1,3,4,5,8],[]),
([0xb000b00,u13,u3,u0,u1,u2,u4],[(u13,u3,u0),(0xf4f4f4f4,u13,u1),(0xb000b00,0xf4f4f4f4,u2)],[1],[(0,100)]),
([u8,u3,u70,u2,u4],[(u13,u3,u0),(u70,u13,u1),(u8,u1,u0)],[0,1,2,3,4],[(0,89),(0,101)]),
([u11,u60,u3,u0,u1,u2,u4],[(u22,u3,u1),(u60,u22,u0),(u11,u1,u2)],[0,1,3,4,5,8],[(0,102),(0,103)]),
([u60,u3,u0,u1,u6,u2,u4],[(u22,u3,u1),(u60,u22,u0),(u6,u2,u4)],[0,1,2,3,5,7],[(0,104),(0,105),(2,101)]),
([u60,u3,u61,u0,u1,u2,u4],[(u22,u3,u1),(u60,u22,u0),(u61,u22,u2)],[0,1,3,4,5,8],[(0,106)]),
([u13,u3,u1,u5,u2,u4],[(u13,u3,u0),(u70,u13,u1),(u5,u70,u0)],[1,3],[]),
([u13,u3,u70,u1,u5,u2,u4],[(u13,u3,u0),(u70,u13,u1),(u5,u70,u0)],[1,3],[]),
([u13,u3,0xb000b000,u0,u1,u2,u4],[(u13,u3,u0),(u70,u13,u1),(0xb000b000,u70,u2)],[1,8],[(2,107)]),
([u13,0x4f004f00,u3,u0,u1,u2,u4],[(u13,u3,u0),(u70,u13,u1),(0x4f004f00,u70,u2)],[0,1,5,6],[]),
([0x44004400,u3,u0,u17,u1,u2,u4],[(u13,u3,u0),(0x44004400,u13,u2),(u17,u1,u4)],[2,3,4,5],[(3,108)]),
([u11,0x44440000,u3,u0,u1,u2,u4],[(u13,u3,u0),(0x44440000,u13,u4),(u11,u1,u2)],[0,3,5,6],[(1,109)]),
([u3,u61,u0,u1,u5,u2,u4],[(u22,u3,u1),(u61,u22,u2),(u5,u0,u1)],[0,1,3,4,5,8],[]),
([u8,u3,u61,u0,u1,u2,u4],[(u22,u3,u1),(u61,u22,u2),(u8,u0,u1)],[0,3,4,5,8],[]),
([u3,u61,u24,u0,u1,u2,u4],[(u22,u3,u1),(u61,u22,u2),(u24,u0,u4)],[0,2,3,5],[(1,110)]),
([u11,u3,0xbbbb0000,u0,u1,u2,u4],[(u13,u3,u0),(0xbbbb0000,u13,u4),(u11,u1,u2)],[0,6,7],[(1,111)]),
([u11,u3,u108,u0,u1,u2,u4],[(u22,u3,u1),(u108,u22,u4),(u11,u1,u2)],[0,2,5,7],[]),
([u3,u61,u108,u0,u1,u2,u4],[(u22,u3,u1),(u61,u22,u2),(u108,u22,u4)],[0,2,5,7],[]),
([u13,u3,u0,u1,0xfbf0fbf0,u2,u4],[(u13,u3,u0),(u78,u13,u2),(0xfbf0fbf0,u78,u1)],[0,1,3,6],[(0,112),(2,106)]),
([0x4040cccc,u22,u3,u0,u1,u2,u4],[(u22,u3,u1),(u108,u22,u4),(0x4040cccc,u108,u0)],[1,2,3,4,8],[(0,99),(0,113)]),
([u13,u3,0xbb000000,u0,u1,u2,u4],[(u13,u3,u0),(u78,u13,u2),(0xbb000000,u78,u4)],[0,1,2,3,8],[(0,114)]),
([0x4400ff00,u13,u3,u0,u1,u2,u4],[(u13,u3,u0),(0xbbbb0000,u13,u4),(0x4400ff00,0xbbbb0000,u2)],[0,1,2,3,5],[]),
([u13,u3,u78,u1,u5,u2,u4],[(u13,u3,u0),(u78,u13,u2),(u5,u0,u1)],[0,3,6],[(2,115),(3,113)]),
([u13,u3,0xb8b8b8b8,u1,u2,u4],[(u13,u3,u0),(u5,u0,u1),(0xb8b8b8b8,u13,u5)],[1,3,8],[(2,115),(3,115)]),
([u3,u125,u0,u5,u2,u4],[(u22,u3,u1),(u5,u1,u0),(u125,u22,u5)],[1,3,4,8],[(0,116),(1,116)]),
([u13,u3,0xb8b8b8b8,u1,u5,u2,u4],[(u13,u3,u0),(u5,u0,u1),(0xb8b8b8b8,u13,u5)],[1,3,8],[]),
([u13,u3,u18,u1,u5,u2,u4],[(u13,u3,u0),(u5,u0,u1),(u18,u1,u2)],[0,4],[(1,117)]),
([u13,u3,u1,u25,u5,u2,u4],[(u13,u3,u0),(u5,u0,u1),(u25,u5,u2)],[0],[(0,91),(2,116)]),
([u13,u3,u1,u5,u6,u2,u4],[(u13,u3,u0),(u5,u0,u1),(u6,u2,u4)],[0,3,6,8],[(0,92),(0,120),(2,118),(2,119)]),
([u3,u125,u0,u1,u2,u4],[(u22,u3,u1),(u5,u1,u0),(u125,u22,u5)],[0,1,2,3,4,5,6,7,8],[]),
([u13,u3,u0,u1,u25,u2,u4],[(u13,u3,u0),(u5,u0,u1),(u25,u5,u2)],[0,1,5],[]),
([u8,u13,u3,u18,u1,u2,u4],[(u13,u3,u0),(u8,u0,u1),(u18,u1,u2)],[1,4],[(0,121)]),
([u8,u13,u3,u1,u6,u2,u4],[(u13,u3,u0),(u8,u0,u1),(u6,u2,u4)],[0,1,3],[(0,101),(0,122),(0,123)]),
([0x5c5c5c5c,u3,u0,u1,u2,u4],[(u22,u3,u1),(u8,u1,u0),(0x5c5c5c5c,u8,u22)],[0,1,2,4,5,7,8],[]),
([u13,u3,u0,u36,u1,u2,u4],[(u13,u3,u0),(u16,u0,u1),(u36,u16,u2)],[0,1,5],[]),
([0x5f505f50,u3,u0,u1,u2,u4],[(u22,u3,u1),(u11,u1,u2),(0x5f505f50,u11,u22)],[0,1,2,3,4,7,8],[(0,125),(1,124)]),
([u13,u3,u0,u1,0xf3f0f3f0,u2,u4],[(u13,u3,u0),(u47,u0,u2),(0xf3f0f3f0,u47,u1)],[0,1,3,6,8],[(0,112),(2,102),(2,103)]),
([u13,u3,0xc0c0f0f0,u0,u1,u2,u4],[(u13,u3,u0),(u29,u0,u4),(0xc0c0f0f0,u29,u1)],[1,2,3,4,8],[(0,95),(2,94)]),
([u13,u3,u55,u0,u1,u2,u4],[(u13,u3,u0),(u29,u0,u4),(u55,u29,u2)],[0,1,2,3,5],[]),
([u3,u0,u122,u1,u2,u4],[(u22,u3,u1),(u14,u0,u2),(u122,u22,u14)],[0,1,2,3,7,8],[(0,0)]),
([u13,u3,u0,u1,0xf444f444,u2,u4],[(u13,u3,u0),(u18,u1,u2),(0xf444f444,u13,u18)],[1,4],[(2,0)]),
([u3,u14,u0,u122,u1,u2,u4],[(u22,u3,u1),(u14,u0,u2),(u122,u22,u14)],[0,4],[]),
([0x4044444,u3,u0,u17,u1,u2,u4],[(u13,u3,u0),(u17,u1,u4),(0x4044444,u13,u17)],[2],[(3,107)]),
([u13,u3,u1,u50,u2,u4],[(u13,u3,u0),(u18,u1,u2),(u50,u0,u18)],[0,1,2,3,4,8],[(0,126)]),
([u13,u3,u18,u1,u50,u2,u4],[(u13,u3,u0),(u18,u1,u2),(u50,u0,u18)],[3,4],[]),
([u33,u13,u3,u17,u1,u2,u4],[(u13,u3,u0),(u17,u1,u4),(u33,u0,u17)],[1,2,3,4,8],[]),
([u11,u13,u3,u0,u18,u1,u4],[(u13,u3,u0),(u18,u1,u2),(u11,u18,u2)],[0,1],[]),
([u13,u3,u0,u77,u1,u2,u4],[(u13,u3,u0),(u18,u1,u2),(u77,u18,u4)],[1,3,4,8],[(0,128),(2,127)]),
([u44,u13,u3,u0,u1,u2,u4],[(u13,u3,u0),(u17,u1,u4),(u44,u17,u2)],[0,1,3,5],[(0,129)]),
([u13,u3,u0,u18,u1,u6,u4],[(u13,u3,u0),(u18,u1,u2),(u6,u2,u4)],[1,2,3,7],[(0,130)]),
([u124,u3,u0,u1,u2,u4],[(u13,u3,u0),(u11,u1,u2),(u124,u11,u13)],[0,1,2,3,6,7,8],[]),
([u11,u124,u3,u0,u1,u2,u4],[(u13,u3,u0),(u11,u1,u2),(u124,u11,u13)],[0,3],[]),
([u13,u124,u3,u0,u1,u2,u4],[(u13,u3,u0),(u11,u1,u2),(u124,u11,u13)],[1,6],[]),
([u11,0x40444044,u3,u0,u1,u2,u4],[(u13,u3,u0),(u11,u1,u2),(0x40444044,u11,u13)],[0],[(0,100)]),
([u83,u13,u3,u0,u1,u2,u4],[(u13,u3,u0),(u11,u1,u2),(u83,u11,u4)],[1,3,6,8],[(0,131)]),
([u13,u3,u0,0xf000ff00,u1,u2,u4],[(u13,u3,u0),(u35,u1,u4),(0xf000ff00,u35,u2)],[1,3,5],[(2,132)]),
([u3,u0,u1,u2,u88,u4],[(u13,u3,u0),(u6,u2,u4),(u88,u13,u6)],[0,1,2,3,4,6,8],[(0,1),(0,123),(2,118)]),
([u13,u3,u0,u1,u2,u88,u4],[(u13,u3,u0),(u6,u2,u4),(u88,u13,u6)],[0,1,2,3,5],[(0,1)]),
([u3,u0,u1,u6,u2,u88,u4],[(u13,u3,u0),(u6,u2,u4),(u88,u13,u6)],[0,2,3],[]),
([0x444444,u3,u0,u1,u6,u2,u4],[(u13,u3,u0),(u6,u2,u4),(0x444444,u13,u6)],[0,2],[(0,114)]),
([u13,u3,u1,u2,u30,u4],[(u13,u3,u0),(u6,u2,u4),(u30,u0,u6)],[0,1,2,3,5,6,7,8],[(0,47),(0,133),(2,98)]),
([u13,u3,u1,u6,u2,u30,u4],[(u13,u3,u0),(u6,u2,u4),(u30,u0,u6)],[0,3,5,7],[]),
([u26,u13,u3,u1,u6,u2,u4],[(u13,u3,u0),(u6,u2,u4),(u26,u0,u6)],[0,1,3,5,8],[]),
([u13,u3,u0,u1,u2,u37,u4],[(u13,u3,u0),(u6,u2,u4),(u37,u1,u6)],[0,1,2,3,6,8],[(0,130),(0,135),(1,130),(2,105),(2,134)]),
([u26,u22,u3,u0,u1,u2,u4],[(u22,u3,u1),(u6,u2,u4),(u26,u0,u6)],[1,3,4,6],[(0,96),(0,119),(2,136)]),
([u3,u14,u0,u1,u116,u2,u4],[(u19,u3,u4),(u116,u19,u1),(u14,u0,u2)],[0,2,3,6,7],[(3,137),(3,138)]),
([u11,u3,u0,u109,u1,u2,u4],[(u19,u3,u4),(u109,u19,u0),(u11,u1,u2)],[0,5,6,8],[(3,139)]),
([u48,u3,u0,u109,u1,u2,u4],[(u19,u3,u4),(u109,u19,u0),(u48,u19,u0)],[1,7,8],[]),
([u3,u0,u56,u1,0xf5f0f5f0,u2,u4],[(u10,u3,u2),(u56,u10,u0),(0xf5f0f5f0,u10,u1)],[3,6,8],[(0,140),(0,141),(2,140)]),
([u48,u3,u0,u1,u116,u2,u4],[(u19,u3,u4),(u116,u19,u1),(u48,u19,u0)],[1,3,6,7,8],[(3,142),(3,143),(3,144)]),
([u54,u3,u0,u109,u1,u2,u4],[(u19,u3,u4),(u109,u19,u0),(u54,u19,u2)],[0,3,5,8],[(1,145)]),
([u10,u3,0xc4c0c4c0,u0,u1,u2,u4],[(u10,u3,u2),(0xf5f0f5f0,u10,u1),(0xc4c0c4c0,0xf5f0f5f0,u0)],[0,1,3,5,8],[(0,140),(0,141)]),
([u10,u3,u0,u1,0xfdfcfdfc,u2,u4],[(u10,u3,u2),(u56,u10,u0),(0xfdfcfdfc,u56,u1)],[0,1],[(1,146)]),
([0xd0c0d0c,u10,u3,u0,u1,u2,u4],[(u10,u3,u2),(u56,u10,u0),(0xd0c0d0c,u56,u1)],[0,1,3,4,5,6],[(0,143),(0,144)]),
([0x8080c0c,u19,u3,u0,u1,u2,u4],[(u19,u3,u4),(u116,u19,u1),(0x8080c0c,u116,u0)],[0,1,2],[(1,143),(3,147)]),
([u10,u3,u0,0xddcc0000,u1,u2,u4],[(u10,u3,u2),(u56,u10,u0),(0xddcc0000,u56,u4)],[0,1,2,3,5,7],[]),
([0xa000f00,u19,u3,u0,u1,u2,u4],[(u19,u3,u4),(u116,u19,u1),(0xa000f00,u116,u2)],[1],[(1,148)]),
([u11,u90,u3,u0,u4],[(u10,u3,u2),(u90,u10,u1),(u11,u1,u2)],[1,2,4,5,6],[(0,149),(3,150)]),
([u48,u3,u0,u18,u1,u2,u4],[(u19,u3,u4),(u48,u19,u0),(u18,u1,u2)],[0,1,3,4,5,6],[(0,152),(0,153),(2,151),(3,149)]),
([u11,u48,u3,u0,u1,u2,u4],[(u19,u3,u4),(u48,u19,u0),(u11,u1,u2)],[0,1,3,4,6],[(0,150),(0,154)]),
([u48,u3,u0,u1,u6,u2],[(u19,u3,u4),(u48,u19,u0),(u6,u2,u4)],[0,1,2,3,4,7],[(0,153)]),
([u48,0xa0a0f0f0,u3,u0,u1,u2,u4],[(u19,u3,u4),(u48,u19,u0),(0xa0a0f0f0,u19,u1)],[1,3,4,7,8],[(0,146),(0,155),(2,155)]),
([u48,u54,u3,u0,u1,u2,u4],[(u19,u3,u4),(u48,u19,u0),(u54,u19,u2)],[0,1,3,5,7,8],[(0,156)]),
([u10,0x80c080c0,u3,u0,u1,u2,u4],[(u10,u3,u2),(0x88cc88cc,u10,u0),(0x80c080c0,0x88cc88cc,u1)],[0,1],[(0,141)]),
([u10,u3,u0,0xecfcecfc,u1,u2,u4],[(u10,u3,u2),(u90,u10,u1),(0xecfcecfc,u90,u0)],[0,1,3,8],[(1,146),(1,155),(1,157)]),
([0x4c0c4c0c,u10,u3,u0,u1,u2,u4],[(u10,u3,u2),(u90,u10,u1),(0x4c0c4c0c,u90,u0)],[0,1,3,5,8],[(0,142),(0,143)]),
([u10,0x88cc0000,u3,u0,u1,u2,u4],[(u10,u3,u2),(0x88cc88cc,u10,u0),(0x88cc0000,0x88cc88cc,u4)],[0,1,5],[(1,158)]),
([u10,0x5f0f0000,u3,u0,u1,u2,u4],[(u10,u3,u2),(u90,u10,u1),(0x5f0f0000,u90,u4)],[0,1,2,5,6,7],[]),
([u65,u3,u7,u0,u1,u2,u4],[(u10,u3,u2),(u65,u10,u4),(u7,u0,u1)],[3,5],[(0,159),(0,160)]),
([u65,u3,u0,u1,u5,u2,u4],[(u10,u3,u2),(u65,u10,u4),(u5,u0,u1)],[1,3,4,5,6,8],[(0,160),(0,161),(0,162)]),
([u8,u65,u3,u0,u1,u2,u4],[(u10,u3,u2),(u65,u10,u4),(u8,u0,u1)],[0,2,3,5,7,8],[(0,163),(0,164)]),
([u54,u3,u7,u0,u1,u2,u4],[(u19,u3,u4),(u54,u19,u2),(u7,u0,u1)],[0,3,5],[(0,165),(0,166)]),
([u54,u3,u0,u1,u5,u2,u4],[(u19,u3,u4),(u54,u19,u2),(u5,u0,u1)],[0,1,5,8],[(0,166),(0,168),(1,167)]),
([u8,u54,u3,u0,u1,u2,u4],[(u19,u3,u4),(u54,u19,u2),(u8,u0,u1)],[2,3,5,7],[(0,169),(0,170)]),
([u10,u3,u0,0xeeffcccc,u1,u2,u4],[(u10,u3,u2),(0xaaff0000,u10,u4),(0xeeffcccc,0xaaff0000,u0)],[0,1,2,3,5,8],[(1,156)]),
([0x4400cccc,u10,u3,u0,u1,u2,u4],[(u10,u3,u2),(0xaaff0000,u10,u4),(0x4400cccc,0xaaff0000,u0)],[0,1,2,3,5,8],[(0,145)]),
([u3,u0,u95,u1,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u95,u10,u7)],[0,1,2,3,6,7,8],[]),
([u10,u3,u0,u95,u1,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u95,u10,u7)],[0,1,3],[]),
([u3,u7,u0,u95,u1,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u95,u10,u7)],[5],[(0,171)]),
([u96,u3,u7,u0,u1,u2,u4],[],[],[(0,141),(0,172)]),
([u8,u10,u3,u7,u1,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u8,u7,u0)],[1],[(0,173),(0,174)]),
([u8,u10,u3,u0,u1,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u8,u7,u0)],[0,1,3,5],[(0,143),(0,174)]),
([u28,u10,u3,u7,u0,u1,u4],[(u10,u3,u2),(u7,u0,u1),(u28,u7,u2)],[0,1,3],[(0,175)]),
([u10,u3,u91,u0,u1,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u91,u7,u4)],[0,1,3,5,7],[(0,177),(1,176)]),
([u28,u19,u3,u0,u1,u2,u4],[(u19,u3,u4),(u7,u0,u1),(u28,u7,u2)],[0,1,2,5,7],[(1,178)]),
([u10,u3,u7,u5,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u5,u0,u1)],[0,1,2,3,8],[(0,160),(0,171),(0,172),(0,175),(0,179),(0,181),(0,182),(0,183),(0,184),(0,185),(1,166),(1,180)]),
([u10,u3,u7,u0,u5,u2,u4],[(u10,u3,u2),(u7,u0,u1),(u5,u0,u1)],[0,1,3,8],[(0,186)]),
([u11,u10,u3,u7,u0,u1,u4],[(u10,u3,u2),(u7,u1,u0),(u11,u1,u2)],[1,4,6],[(0,187)]),
([u10,u3,u7,u0,u1,u6,u4],[(u10,u3,u2),(u7,u0,u1),(u6,u2,u4)],[1,2,3,5,7],[(0,185),(0,188)]),
([u105,u3,u0,u1,u5,u2,u4],[(u10,u3,u2),(u5,u0,u1),(u105,u10,u5)],[0,8],[(0,179),(1,146)]),
([u75,u3,u0,u1,u2,u4],[(u19,u3,u4),(u5,u0,u1),(u75,u19,u5)],[0,1,2,3,4,5,6,8],[(0,189)]),
([u10,0xa8fca8fc,u3,u0,u1,u2,u4],[(u10,u3,u2),(u5,u0,u1),(0xa8fca8fc,u10,u5)],[0,1,8],[]),
([u75,u3,u0,u1,u5,u2,u4],[(u19,u3,u4),(u5,u0,u1),(u75,u19,u5)],[1,2,7,8],[(0,180)]),
([u23,u10,u0,u1,u2,u4],[(u10,u3,u2),(u5,u0,u1),(u23,u3,u5)],[0,1,6,8],[(0,162),(0,190),(0,191),(1,168)]),
([u23,u10,u0,u1,u5,u2,u4],[(u10,u3,u2),(u5,u0,u1),(u23,u3,u5)],[0,1,8],[(0,181)]),
([u8,u10,u3,u0,u5,u2,u4],[(u10,u3,u2),(u5,u0,u1),(u8,u0,u1)],[1],[(0,173),(0,174)]),
([u10,u3,u0,u1,u92,u2,u4],[(u10,u3,u2),(u5,u0,u1),(u92,u5,u4)],[0,1,2,5,7],[(1,192)]),
([0x3000300,u19,u3,u0,u1,u2,u4],[(u19,u3,u4),(u5,u0,u1),(0x3000300,u5,u2)],[1,2,7,8],[(1,193),(1,194)]),
([u10,u3,u0,u1,u5,u6,u4],[(u10,u3,u2),(u5,u0,u1),(u6,u2,u4)],[1,2,5,6,7,8],[(0,185),(0,191),(1,189)]),
([u80,u3,u0,u1,u2,u4],[(u10,u3,u2),(u8,u0,u1),(u80,u8,u10)],[0,1,2,3,4,6,7,8],[(0,195)]),
([u8,u80,u3,u0,u1,u2,u4],[(u10,u3,u2),(u8,u0,u1),(u80,u8,u10)],[5],[(0,196)]),
([u10,u80,u3,u0,u1,u2,u4],[(u10,u3,u2),(u8,u0,u1),(u80,u8,u10)],[1,3],[]),
([u8,0x51005100,u3,u0,u1,u2,u4],[],[],[(0,143),(2,197)]),
([u10,u3,u7,u0,u1,u2,u4],[(u10,u3,u2),(u8,u0,u1),(u7,u8,u0)],[0,1,3,5],[(0,141),(0,173)]),
([u10,u3,u0,u1,u5,u2,u4],[(u10,u3,u2),(u8,u0,u1),(u5,u8,u1)],[0,1,5,8],[(0,173),(0,198),(1,146)]),
([u8,u10,u3,u0,u1,u51,u4],[(u10,u3,u2),(u8,u0,u1),(u51,u8,u2)],[0,1,3],[(2,199)]),
([0xc000c00,u19,u3,u0,u1,u2,u4],[(u19,u3,u4),(u8,u0,u1),(0xc000c00,u8,u2)],[1,2,3,7],[(1,200)]),
([u10,u3,u0,u93,u1,u2,u4],[(u10,u3,u2),(u16,u1,u0),(u93,u16,u4)],[0,1,2,5,7],[(1,201)]),
([u8,u16,u10,u3,u2,u4],[(u10,u3,u2),(u8,u0,u1),(u16,u0,u1)],[0,1,2,3,8],[(0,164),(0,182),(0,196),(0,197),(0,199),(0,202),(1,170),(2,196),(2,197),(2,199),(2,202)]),
([u8,u16,u10,u3,u0,u2,u4],[(u10,u3,u2),(u8,u0,u1),(u16,u0,u1)],[1,3,8],[(0,186)]),
([u8,u47,u10,u3,u0,u1,u4],[(u10,u3,u2),(u8,u0,u1),(u47,u0,u2)],[1,3,8],[(0,203)]),
([u8,u10,u3,u0,u1,u6,u4],[(u10,u3,u2),(u8,u0,u1),(u6,u2,u4)],[1,2,5,7],[(0,195),(0,204),(0,205)]),
([u10,u3,u0,u52,u1,u4],[(u10,u3,u2),(u11,u1,u2),(u52,u11,u0)],[0,1,5,6,7,8],[]),
([u10,u3,u0,0xccff0000,u1,u4],[(u10,u3,u2),(u47,u0,u2),(0xccff0000,u47,u4)],[0,1,2,3,5,6,8],[]),
([u11,u10,u3,u24,u0,u1,u4],[(u10,u3,u2),(u11,u1,u2),(u24,u0,u4)],[1,2,5,6],[(0,149),(0,206),(0,207)]),
([u11,u29,u10,u3,u0,u1,u4],[(u10,u3,u2),(u11,u1,u2),(u29,u0,u4)],[1,2,8],[(3,150)]),
([u11,u10,u3,u0,u17,u1,u4],[(u10,u3,u2),(u11,u1,u2),(u17,u1,u4)],[1,4,6],[(2,208)]),
([u3,u0,u110,u1,u2,u4],[(u19,u3,u4),(u14,u0,u2),(u110,u19,u14)],[0,1,2,4,6,8],[(0,209),(1,207)]),
([u10,u3,u0,0xddcc5500,u1,u2,u4],[(u10,u3,u2),(u24,u0,u4),(0xddcc5500,u10,u24)],[0,1,3,5],[]),
([u3,u14,u0,u110,u1,u2,u4],[(u19,u3,u4),(u14,u0,u2),(u110,u19,u14)],[0,5,7],[]),
([u87,u3,u0,u17,u1,u2,u4],[(u10,u3,u2),(u17,u1,u4),(u87,u10,u17)],[2,5],[(3,158)]),
([u10,u3,u0,u1,u117,u2,u4],[(u10,u3,u2),(u17,u1,u4),(u117,u17,u0)],[0,1,5,8],[(1,152),(1,210)]),
([u33,u10,u3,u0,u1,u2,u4],[(u10,u3,u2),(u17,u1,u4),(u33,u17,u0)],[0,1,3,5],[(0,137),(0,211),(0,212)]),
([u44,u10,u3,u0,u17,u1,u4],[(u10,u3,u2),(u17,u1,u4),(u44,u17,u2)],[0,1,2,4,6],[]),
([u11,u19,u3,u0,u18,u1,u4],[(u19,u3,u4),(u18,u1,u2),(u11,u18,u2)],[0,1,6],[]),
([u10,u3,u24,u0,u1,u6],[(u10,u3,u2),(u24,u0,u4),(u6,u2,u4)],[0,1,2,3,5,7,8],[(0,213),(1,209),(2,212),(3,153)]),
([0x5f0f5500,u3,u0,u1,u2,u4],[(u10,u3,u2),(u35,u1,u4),(0x5f0f5500,u35,u10)],[0,1,2,3,4,6,8],[]),
([u11,0x5f550f00,u3,u0,u1,u2,u4],[(u19,u3,u4),(u11,u1,u2),(0x5f550f00,u11,u19)],[0,1,2,6,7],[]),
([u10,0x5f0f5500,u3,u0,u1,u2,u4],[(u10,u3,u2),(u35,u1,u4),(0x5f0f5500,u35,u10)],[0,1,6],[]),
([u11,0x50550000,u3,u0,u1,u2,u4],[(u19,u3,u4),(u11,u1,u2),(0x50550000,u11,u19)],[0,2,6],[(1,148)]),
([u10,u3,u0,0xcfcfcccc,u1,u2,u4],[(u10,u3,u2),(u35,u1,u4),(0xcfcfcccc,u35,u0)],[0,1,5,8],[(1,214)]),
([u10,u3,u63,u0,u1,u2,u4],[(u10,u3,u2),(u35,u1,u4),(u63,u35,u0)],[0,1,3,5],[(0,215)]),
([u10,u3,u0,u1,u30,u4],[(u10,u3,u2),(u6,u2,u4),(u30,u0,u6)],[0,1,2,3,5,6,8],[(0,205),(0,213)]),
([u3,u20,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1)],[0,1,2,3,8],[(0,216),(0,217),(0,218),(0,219),(0,220),(0,221),(0,222),(1,219),(1,220),(1,221)]),
([u3,u0,u20,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1)],[0,1,2,3,8],[]),
([u3,u0,u20,u1,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1)],[1,3,4,8],[(0,223),(0,224)]),
([u8,u3,u20,u1,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u8,u0,u1)],[0,1,2,3,4,8],[(0,225)]),
([u11,u3,u0,u20,u1,u2,u4],[(u7,u1,u0),(u20,u3,u7),(u11,u1,u2)],[0,1,6],[(0,226),(0,227)]),
([u3,u0,u86,u20,u1,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u86,u20,u2)],[0,1,5],[(0,219)]),
([u96,u3,u0,u20,u1,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u96,u20,u2)],[0,5],[(0,220),(0,228)]),
([u3,u0,u20,u1,u6,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u6,u2,u4)],[0,1,2,5,7],[(0,222),(0,229),(0,230),(0,231)]),
([u28,u3,u0,u20,u1,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u28,u7,u2)],[0,1,5],[(0,228),(0,232)]),
([u3,u7,u20,u5,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u5,u0,u1)],[0,1,2,3],[(0,172),(0,232),(0,233),(0,234),(0,235),(0,236),(0,237),(1,172),(1,232),(1,237)]),
([u3,u7,u0,u86,u1,u2,u4],[(u7,u0,u1),(u20,u3,u7),(u86,u20,u2)],[0,1,5],[(0,237)]),
([u3,u7,u5,u2,u4],[(u7,u0,u1),(u8,u7,u0),(u5,u8,u1)],[0,1,2,3,8],[(0,173),(0,225),(0,238),(0,239),(1,173)]),
([u8,u16,u3,u2,u4],[(u7,u0,u1),(u8,u7,u0),(u16,u7,u1)],[0,1,2,3,8],[(0,174),(0,238),(0,240),(1,174)]),
([u8,u3,u7,u1,u6,u2,u4],[(u7,u0,u1),(u8,u7,u0),(u6,u2,u4)],[0,1,3],[(0,239),(0,240),(0,241)]),
([u3,u27,u0,u1,u2,u4],[(u7,u0,u1),(u8,u7,u0),(u27,u8,u3)],[0,1,2,3,5,6,7,8],[]),
([u8,u3,u0,u1,u6,u2,u4],[(u7,u0,u1),(u8,u7,u0),(u6,u2,u4)],[0,2,3,5,7,8],[(0,240),(0,242)]),
([u0,0xeaaaeaaa,u1,u2,u4],[(u7,u0,u1),(u111,u7,u2),(0xeaaaeaaa,u3,u111)],[0,1,2,3,4,5],[(1,243),(1,244)]),
([u3,u0,0xeaaaeaaa,u1,u2,u4],[(u7,u0,u1),(u111,u7,u2),(0xeaaaeaaa,u3,u111)],[0,1,2,3,4,5,7],[(1,177)]),
([0x3f00ff00,u3,u0,u1,u4],[(u7,u0,u1),(u91,u7,u4),(0x3f00ff00,u91,u2)],[0,1,2,3,4,5],[]),
([u3,u85,u0,u1,u2,u4],[(u7,u0,u1),(u28,u7,u2),(u85,u28,u3)],[0,1,2,3,4,5,7],[]),
([u28,u3,u0,u1,u5,u2,u4],[(u7,u0,u1),(u28,u7,u2),(u5,u0,u1)],[0,5],[]),
([u11,u66,u3,u0,u1,u2,u4],[(u7,u1,u0),(u66,u7,u4),(u11,u1,u2)],[0,2,7],[]),
([u3,u85,u7,u0,u1,u2,u4],[(u7,u0,u1),(u28,u7,u2),(u85,u28,u3)],[0,1,3,4],[(0,228),(0,245)]),
([u121,u3,u7,u0,u1,u2,u4],[(u7,u0,u1),(u28,u7,u2),(u121,u28,u4)],[0,2,3],[(0,246),(0,247)]),
([u3,0xc000ff00,u7,u0,u1,u2,u4],[(u7,u0,u1),(u66,u7,u4),(0xc000ff00,u66,u2)],[0,2,3,5],[(0,248)]),
([u28,u66,u3,u0,u1,u2,u4],[(u7,u0,u1),(u28,u7,u2),(u66,u7,u4)],[0,2,5,7],[(0,249)]),
([u28,u3,u7,u5,u2,u4],[(u7,u0,u1),(u28,u7,u2),(u5,u0,u1)],[0,1,2,3],[(0,172),(0,175),(0,232),(0,245),(0,247),(0,249),(0,250),(0,251),(0,252),(0,253),(1,248)]),
([u23,u3,u7,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u23,u3,u5)],[0,1,2,8],[(0,179),(0,181),(0,216),(0,217),(0,233),(0,236),(0,254),(0,255),(0,256),(0,257),(1,179),(1,181),(1,255)]),
([u9,u3,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5)],[0,1,2],[(0,182),(0,258),(0,259),(0,260),(0,261),(0,262),(1,182),(1,260),(1,261)]),
([u9,u3,u7,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5)],[0,1,2,3,8],[(0,183),(0,234),(0,251),(0,263),(0,264),(0,265),(0,266),(0,267),(1,183),(1,251),(1,265),(1,266)]),
([u9,u3,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5)],[0,1,2,3,8],[(0,184),(0,217),(0,256),(0,268),(0,269),(0,270),(0,271),(0,272),(0,273),(0,274),(1,184),(1,271),(1,272),(1,273)]),
([u9,u3,u7,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5)],[0,1,2,3,8],[(0,235),(0,236),(0,250),(0,252),(0,257),(0,275),(0,276),(0,277),(1,250),(1,252),(1,276),(1,277)]),
([u3,u7,u25,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u25,u5,u2)],[0,1,2,8],[(0,91),(0,179),(0,221),(0,250),(0,253),(0,273),(0,277),(0,278),(0,279),(0,281),(1,280)]),
([u3,u7,u5,u6,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u6,u2,u4)],[0,1,2,3,8],[(0,92),(0,160),(0,185),(0,222),(0,247),(0,262),(0,267),(0,274),(0,279),(0,281),(0,282),(0,283),(0,284),(0,285),(0,286),(0,287),(1,185),(1,281)]),
([u9,u3,u0,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5)],[0,1,2,3,8],[(0,186),(0,288),(0,289),(0,290),(0,291),(0,292),(1,186),(1,290),(1,291)]),
([u3,u7,u0,u5,u6,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u6,u2,u4)],[0,2,3,8],[(0,292),(0,293)]),
([u23,u3,u7,u0,u1,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u23,u3,u5)],[1],[(0,223),(0,224)]),
([u9,u3,u0,u1,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u9,u7,u5)],[0,1,2,3,4,5,6,7,8],[(0,224),(0,294)]),
([u3,u7,u0,u1,u25,u2,u4],[(u7,u0,u1),(u5,u0,u1),(u25,u5,u2)],[0,5],[]),
([u3,u31,u7,u0,u1,u2,u4],[(u7,u1,u0),(u11,u1,u2),(u31,u11,u3)],[1,3,6,8],[(0,226),(0,227)]),
([u3,u0,0xcfc0cfc0,u1,u2,u4],[(u7,u1,u0),(u11,u1,u2),(0xcfc0cfc0,u11,u7)],[0,1,2,4,7,8],[(0,187),(0,227),(0,295)]),
([u3,u7,u55,u0,u1,u2,u4],[(u7,u0,u1),(u29,u0,u4),(u55,u29,u2)],[0,5,8],[]),
([u3,u7,u0,u1,u2,u21,u4],[(u7,u0,u1),(u6,u2,u4),(u21,u3,u6)],[1,3,4,6,8],[(0,229),(0,230),(0,282),(0,296)]),
([u3,u0,u1,u2,u45,u4],[(u7,u0,u1),(u6,u2,u4),(u45,u7,u6)],[0,1,2,3,4,6,8],[(0,188),(0,230),(0,241),(0,283),(0,293),(0,297),(1,188),(2,241),(2,293)]),
([u3,u7,u0,u1,u2,u45,u4],[(u7,u0,u1),(u6,u2,u4),(u45,u7,u6)],[0,2,3,5],[(0,241),(0,284),(2,241)]),
([u3,u0,u1,u6,u2,u45,u4],[(u7,u0,u1),(u6,u2,u4),(u45,u7,u6)],[0,2,3],[(0,285)]),
([0xc0c0c0,u3,u0,u1,u6,u2,u4],[(u7,u0,u1),(u6,u2,u4),(0xc0c0c0,u7,u6)],[0,2],[(0,246),(0,286)]),
([u105,u23,u3,u0,u1,u2,u4],[(u5,u0,u1),(u23,u3,u5),(u105,u23,u2)],[0,1,5],[(0,298)]),
([u23,u3,u97,u0,u1,u2,u4],[(u5,u0,u1),(u23,u3,u5),(u97,u23,u2)],[0,1,5,8],[(0,190)]),
([u23,u3,u14,u0,u1,u2,u4],[(u5,u0,u1),(u23,u3,u5),(u14,u0,u2)],[0,1],[(0,300),(3,299)]),
([u23,u3,u0,u1,u6,u2,u4],[(u5,u0,u1),(u23,u3,u5),(u6,u2,u4)],[0,1,2,5,6,7,8],[(0,162),(0,191),(0,301),(0,302),(0,303),(1,191),(2,303)]),
([u3,u97,u0,u1,u5,u2,u4],[(u5,u0,u1),(u23,u3,u5),(u97,u23,u2)],[0,1,5,6,8],[(0,255)]),
([u23,u3,u0,u1,u25,u2,u4],[(u5,u0,u1),(u23,u3,u5),(u25,u5,u2)],[0,1,5],[(0,298)]),
([u3,u27,u0,u5,u2,u4],[(u5,u0,u1),(u8,u0,u1),(u27,u8,u3)],[1,3,8],[]),
([u8,u3,u0,u5,u6,u2,u4],[(u5,u0,u1),(u8,u0,u1),(u6,u2,u4)],[0,1,3,8],[(0,239),(0,240),(0,304)]),
([u3,u0,u32,u1,u5,u2,u4],[(u5,u0,u1),(u14,u0,u2),(u32,u3,u14)],[0,1,3],[(0,3),(0,300),(3,299)]),
([u98,u3,u0,u1,u2,u4],[(u5,u1,u0),(u17,u1,u4),(u98,u17,u5)],[0,1,2,3,4,5],[(0,4),(0,117),(0,299),(0,305),(0,306)]),
([u44,u3,u0,u1,u5,u2,u4],[(u5,u1,u0),(u17,u1,u4),(u44,u17,u2)],[0,4,5],[]),
([u3,u14,u0,u1,u92,u2,u4],[(u5,u0,u1),(u14,u0,u2),(u92,u5,u4)],[0,2,7],[]),
([u3,u14,u0,u1,u5,u6,u4],[(u5,u0,u1),(u14,u0,u2),(u6,u2,u4)],[2,3,7,8],[(3,306)]),
([u3,u0,u1,u81,u2,u4],[(u5,u0,u1),(u25,u5,u2),(u81,u3,u25)],[0,1,2,5,6,7,8],[]),
([u3,u0,u1,u5,u81,u2,u4],[(u5,u0,u1),(u25,u5,u2),(u81,u3,u25)],[0,1,8],[(0,278),(0,298)]),
([u3,u0,u1,0xfc000000,u5,u2,u4],[(u5,u0,u1),(u25,u5,u2),(0xfc000000,u25,u4)],[1,3,4,8],[(0,279),(0,307),(0,308)]),
([0x300ff00,u3,u0,u1,u5,u2,u4],[(u5,u0,u1),(u92,u5,u4),(0x300ff00,u92,u2)],[0,2,5],[(0,280)]),
([u3,u0,u1,u25,u92,u2,u4],[(u5,u0,u1),(u25,u5,u2),(u92,u5,u4)],[0,2,5,7],[(0,309)]),
([u3,u0,u1,u25,u5,u6,u4],[(u5,u0,u1),(u25,u5,u2),(u6,u2,u4)],[0,2,6,8],[(0,281),(0,309)]),
([u3,0xabaaabaa,u0,u1,u2,u4],[(u5,u0,u1),(0x3000300,u5,u2),(0xabaaabaa,0x3000300,u3)],[0,1,2,6,7,8],[(1,194)]),
([u3,u0,u1,u5,u2,u21,u4],[(u5,u0,u1),(u6,u2,u4),(u21,u3,u6)],[1,3,4,6,8],[(0,5),(0,32),(0,282),(0,302),(0,310),(2,5)]),
([u3,u0,u5,u6,u2,u37,u4],[(u5,u1,u0),(u6,u2,u4),(u37,u1,u6)],[0,4,5,6,7],[(0,311),(0,312),(0,313)]),
([u26,u3,u1,u5,u2,u4],[(u5,u0,u1),(u6,u2,u4),(u26,u0,u6)],[0,2,3,4],[(0,6),(0,33),(0,119),(0,303),(0,314),(2,315)]),
([u26,u3,u1,u5,u6,u2,u4],[(u5,u0,u1),(u6,u2,u4),(u26,u0,u6)],[0,5,7,8],[(0,286),(0,312),(0,316)]),
([u3,u0,u1,u6,u2,0xfffcfcfc,u4],[(u5,u0,u1),(u6,u2,u4),(0xfffcfcfc,u5,u6)],[0,1,2],[(0,308),(0,317)]),
([u62,u3,u0,u1,u2,u4],[(u5,u0,u1),(u6,u2,u4),(u62,u5,u6)],[0,1,2,3,4,8],[(0,8),(0,120),(0,302),(0,318),(2,8),(2,120)]),
([u62,u3,u0,u1,u5,u2,u4],[(u5,u0,u1),(u6,u2,u4),(u62,u5,u6)],[3,4,5,8],[(0,287)]),
([u62,u3,u0,u1,u6,u2,u4],[(u5,u0,u1),(u6,u2,u4),(u62,u5,u6)],[0,2,8],[]),
([u3,0xae00ae00,u27,u0,u1,u2,u4],[(u8,u0,u1),(u27,u8,u3),(0xae00ae00,u27,u2)],[0,5],[]),
([0x45004500,u3,u57,u0,u1,u2,u4],[(u16,u1,u0),(u57,u16,u3),(0x45004500,u57,u2)],[0,5],[(2,319)]),
([u8,u3,u57,u1,u2,u4],[(u16,u1,u0),(u57,u16,u3),(u8,u1,u0)],[1,3,4,6,8],[]),
([u8,u3,u57,u0,u1,u2,u4],[(u16,u1,u0),(u57,u16,u3),(u8,u1,u0)],[1,8],[(0,294),(0,320)]),
([u11,u3,u57,u0,u1,u2,u4],[(u16,u1,u0),(u57,u16,u3),(u11,u1,u2)],[0,1],[(2,321),(2,322)]),
([u3,u27,u0,u18,u1,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u18,u1,u2)],[0,1,5],[(0,323),(0,324)]),
([u3,u27,u0,u1,u6,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u6,u2,u4)],[0,1,2,3,5,7],[(0,325),(0,326),(0,327),(0,328)]),
([u3,u27,u0,u1,u51,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u51,u8,u2)],[0,1,5],[(0,319)]),
([u8,u3,0xae00ae00,u0,u1,u2,u4],[(u8,u0,u1),(u27,u8,u3),(0xae00ae00,u27,u2)],[0,1,3,5],[(0,329)]),
([u8,u16,u3,u27,u2,u4],[(u8,u0,u1),(u27,u8,u3),(u16,u0,u1)],[0,1,2,3],[(0,329),(0,330),(0,332),(0,333),(1,329),(2,197),(2,331),(3,197)]),
([u3,u0,u20,u1,u2,u4],[(u8,u0,u1),(u7,u8,u0),(u20,u3,u7)],[0,1,2,3,4,5,7,8],[(0,225)]),
([u3,u7,u0,u1,u6,u2,u4],[(u8,u0,u1),(u7,u8,u0),(u6,u2,u4)],[0,2,3,5],[(0,239),(0,246)]),
([u23,u3,u0,u1,u2,u4],[(u8,u0,u1),(u5,u8,u1),(u23,u3,u5)],[0,1,2,5,6,7,8],[(0,198),(1,198)]),
([u3,u0,u1,u5,u6,u2,u4],[(u8,u0,u1),(u5,u8,u1),(u6,u2,u4)],[0,2,3,4,5,6,7,8],[(0,239),(0,308)]),
([u3,0xaeaaaeaa,u0,u1,u2,u4],[(u8,u0,u1),(0xc000c00,u8,u2),(0xaeaaaeaa,0xc000c00,u3)],[0,1,2,3,6,7],[]),
([u3,u0,0xefaaefaa,u1,u2,u4],[(u16,u1,u0),(u36,u16,u2),(0xefaaefaa,u3,u36)],[0,1,2,4,5,7,8],[(2,17)]),
([u8,u3,u0,u36,u1,u2,u4],[(u16,u1,u0),(u36,u16,u2),(u8,u0,u1)],[0,5],[]),
([u3,u14,u0,u93,u1,u2,u4],[(u16,u1,u0),(u93,u16,u4),(u14,u0,u2)],[0,2,7],[]),
([u11,u3,u0,u93,u1,u2,u4],[(u16,u1,u0),(u93,u16,u4),(u11,u1,u2)],[0,2,5,7],[]),
([u3,u0,u36,u93,u1,u2,u4],[(u16,u1,u0),(u36,u16,u2),(u93,u16,u4)],[0,2,5,7],[(0,334)]),
([u8,u3,u0,u1,u123,u2,u4],[(u8,u0,u1),(u51,u8,u2),(u123,u3,u51)],[0,1,6],[(0,11),(0,319),(2,335)]),
([u8,u16,u3,u36,u2,u4],[(u16,u1,u0),(u36,u16,u2),(u8,u1,u0)],[0,1,2,8],[(0,197),(0,199),(0,335),(0,336),(0,337),(0,338),(0,339),(0,340),(0,342),(3,341)]),
([u8,u3,u0,u1,0xf3000000,u2,u4],[(u8,u0,u1),(u51,u8,u2),(0xf3000000,u51,u4)],[3,8],[(0,242),(2,340)]),
([0xc00ff00,u8,u3,u0,u1,u2,u4],[(u8,u0,u1),(0xf3f30000,u8,u4),(0xc00ff00,0xf3f30000,u2)],[0,2,5],[(0,341)]),
([u8,u3,u0,u1,u51,u6,u4],[(u8,u0,u1),(u51,u8,u2),(u6,u2,u4)],[0,2,3],[(2,334),(2,342)]),
([u8,u9,u3,u2,u4],[(u8,u0,u1),(u16,u0,u1),(u9,u8,u16)],[0,1,2,3,8],[(0,202),(0,330),(0,343),(0,344),(0,345),(0,346),(0,347),(1,202),(1,345),(1,346),(2,336),(3,336)]),
([u8,u16,u9,u3,u2,u4],[(u8,u0,u1),(u16,u0,u1),(u9,u8,u16)],[0,1,2,3,8],[(0,331),(0,333),(0,337),(0,338),(0,348),(0,349),(1,337),(1,338),(1,349),(2,331),(2,337),(3,337)]),
([u8,u16,u3,u6,u2,u4],[(u8,u0,u1),(u16,u0,u1),(u6,u2,u4)],[0,1,2,3,8],[(0,164),(0,262),(0,340),(0,342),(0,347),(0,350),(0,351),(1,342),(1,352),(2,340),(2,342),(2,347),(2,350),(3,342)]),
([u8,u16,u3,u0,u6,u2,u4],[(u8,u0,u1),(u16,u0,u1),(u6,u2,u4)],[0,2,3,8],[(0,292),(2,353)]),
([0x3f0c3f0c,u3,u0,u1,u2,u4],[(u8,u0,u1),(u47,u0,u2),(0x3f0c3f0c,u8,u47)],[0,1,2,3,7,8],[(0,203),(0,322),(0,354)]),
([u8,u3,u101,u0,u1,u2,u4],[(u8,u0,u1),(u47,u0,u2),(u101,u47,u3)],[1,4,6,8],[(0,321),(0,322)]),
([u8,u3,u55,u0,u1,u2,u4],[(u8,u0,u1),(u29,u0,u4),(u55,u29,u2)],[0,5,8],[]),
([u3,u0,u1,0xfc0cfc0c,u2,u4],[(u8,u0,u1),(u18,u1,u2),(0xfc0cfc0c,u8,u18)],[0,1,2,4,7,8],[(0,121),(0,324),(0,355),(0,356),(2,12)]),
([u8,u3,u0,u1,u34,u2,u4],[(u8,u0,u1),(u18,u1,u2),(u34,u3,u18)],[1,4],[(0,13),(0,323),(0,324)]),
([u8,u44,u3,u0,u1,u2,u4],[(u8,u0,u1),(u17,u1,u4),(u44,u17,u2)],[0,4,5],[]),
([u8,u3,u0,u18,u1,u6,u4],[(u8,u0,u1),(u18,u1,u2),(u6,u2,u4)],[2,6,7],[(0,356)]),
([u3,u0,u1,u2,u72,u4],[(u8,u0,u1),(u6,u2,u4),(u72,u8,u6)],[0,1,2,3,4,8],[(0,122),(0,204),(0,304),(0,326),(0,357),(1,204),(2,14),(2,353)]),
([u8,u3,u0,u1,u2,u72,u4],[(u8,u0,u1),(u6,u2,u4),(u72,u8,u6)],[3,5,8],[(0,304),(0,350)]),
([u3,u0,u1,u6,u2,u72,u4],[(u8,u0,u1),(u6,u2,u4),(u72,u8,u6)],[0,2,3],[]),
([0xc0c0c,u3,u0,u1,u6,u2,u4],[(u8,u0,u1),(u6,u2,u4),(0xc0c0c,u8,u6)],[0,2],[(0,242)]),
([u8,u3,u0,u1,u2,u21,u4],[(u8,u0,u1),(u6,u2,u4),(u21,u3,u6)],[0,1,2,3,4,5,6,7,8],[(0,15),(0,325),(0,326),(0,351),(2,358)]),
([u8,u3,u1,u2,u30,u4],[(u8,u0,u1),(u6,u2,u4),(u30,u0,u6)],[0,2,4,8],[(0,47),(0,205),(0,328),(0,359),(0,360),(1,205)]),
([u8,u3,u1,u6,u2,u30,u4],[(u8,u0,u1),(u6,u2,u4),(u30,u0,u6)],[0,3,5,7],[]),
([u26,u8,u3,u1,u6,u2,u4],[(u8,u0,u1),(u6,u2,u4),(u26,u0,u6)],[0,3,5,7,8],[(0,361)]),
([u11,u3,u0,u1,u34,u4],[(u18,u1,u2),(u34,u3,u18),(u11,u1,u2)],[0,1,2,4,6],[(0,60),(3,362)]),
([u11,u3,u0,u1,u38,u2,u4],[(u17,u1,u4),(u38,u3,u17),(u11,u1,u2)],[0,1,2,6],[(0,363),(1,364)]),
([u3,u82,u0,u1,u34,u2,u4],[(u18,u1,u2),(u34,u3,u18),(u82,u34,u0)],[1,2,3,4,5,8],[(0,61),(0,366),(3,365)]),
([u3,u0,u32,u1,u107,u2,u4],[(u14,u0,u2),(u32,u3,u14),(u107,u32,u1)],[0,2,4,5,6],[(0,369),(2,366),(2,367),(2,368)]),
([0xe0a0e0a,u3,u0,u32,u1,u2,u4],[(u14,u0,u2),(u32,u3,u14),(0xe0a0e0a,u32,u1)],[1,3,4,6],[(0,62),(3,370)]),
([0x4044444,u3,u0,u1,u38,u2,u4],[(u17,u1,u4),(u38,u3,u17),(0x4044444,u38,u0)],[3,8],[(0,370),(0,371)]),
([u3,u0,0xee00aa00,u74,u1,u2,u4],[(u24,u0,u4),(u74,u3,u24),(0xee00aa00,u74,u2)],[0,1,5],[]),
([u87,u3,u0,u1,u38,u2,u4],[(u17,u1,u4),(u38,u3,u17),(u87,u38,u2)],[0,5],[(0,372),(0,373)]),
([u3,u14,u0,u1,u38,u2,u4],[(u17,u1,u4),(u38,u3,u17),(u14,u0,u2)],[0,1,3,5,8],[(0,374),(0,377),(1,375),(3,376)]),
([u11,u3,u0,u74,u1,u2,u4],[(u24,u0,u4),(u74,u3,u24),(u11,u1,u2)],[0,1,4,5,6],[(0,378),(1,379),(3,380)]),
([u3,u0,u32,u1,u6,u4],[(u14,u0,u2),(u32,u3,u14),(u6,u2,u4)],[0,1,2,3,4,5,8],[(0,63),(2,381),(3,373),(3,377)]),
([u3,u0,u32,u1,u67,u2,u4],[(u14,u0,u2),(u32,u3,u14),(u67,u14,u1)],[0,1,4,6],[(0,64),(2,367),(2,382)]),
([u33,u3,u0,u1,u38,u2,u4],[(u17,u1,u4),(u38,u3,u17),(u33,u17,u0)],[1,3,8],[(0,65),(0,371),(0,383)]),
([u44,u3,u0,u1,u38,u2,u4],[(u17,u1,u4),(u38,u3,u17),(u44,u17,u2)],[0,1,5,6,7],[(0,372)]),
([u3,u82,u0,u18,u1,u2,u4],[(u18,u1,u2),(u34,u3,u18),(u82,u34,u0)],[1,2,3,4,5,8],[(0,382),(3,384)]),
([0xe0a0e0a,u3,u14,u0,u1,u2,u4],[(u14,u0,u2),(u32,u3,u14),(0xe0a0e0a,u32,u1)],[0,1,3,6],[(3,383)]),
([u3,u14,u0,0xeeaa0000,u1,u2,u4],[(u14,u0,u2),(u32,u3,u14),(0xeeaa0000,u32,u4)],[0,1,2,7],[]),
([0x54445444,u3,u0,u1,u2,u4],[(u18,u1,u2),(u50,u18,u0),(0x54445444,u3,u50)],[0,1,2,3,4,7,8],[]),
([u11,u3,u0,u1,u117,u2,u4],[(u17,u1,u4),(u117,u17,u0),(u11,u1,u2)],[0,3,5,8],[(1,385),(3,386)]),
([0x54445444,u3,u0,u18,u1,u2,u4],[(u18,u1,u2),(u50,u18,u0),(0x54445444,u3,u50)],[1,3],[(0,367)]),
([u33,u3,u0,u1,u117,u2,u4],[(u17,u1,u4),(u117,u17,u0),(u33,u17,u0)],[2,4],[]),
([u44,u3,u0,u1,u117,u2,u4],[(u17,u1,u4),(u117,u17,u0),(u44,u17,u2)],[0,3,5,8],[(1,387)]),
([u3,u14,u0,u1,0xfcf00000,u2,u4],[(u14,u0,u2),(u67,u14,u1),(0xfcf00000,u67,u4)],[0,2,4,5,7],[]),
([0x3000f00,u3,u24,u0,u1,u2,u4],[(u24,u0,u4),(0xfcfcf0f0,u24,u1),(0x3000f00,0xfcfcf0f0,u2)],[2],[(1,388)]),
([u3,u114,u0,u1,u2,u4],[(u17,u1,u4),(u33,u17,u0),(u114,u33,u3)],[0,1,2,3,4,5,8],[(0,389)]),
([u33,u11,u3,u0,u1,u2,u4],[(u17,u1,u4),(u33,u17,u0),(u11,u1,u2)],[0,2,3,4,8],[(0,390),(0,391)]),
([u33,u3,u0,u1,u6,u2],[(u17,u1,u4),(u33,u17,u0),(u6,u2,u4)],[0,2,3,4,7],[(0,68),(0,212),(0,389)]),
([u3,u114,u0,u17,u1,u2,u4],[(u17,u1,u4),(u33,u17,u0),(u114,u33,u3)],[1,2,4,6,7,8],[(0,371)]),
([0xc00cc00,u3,u0,u17,u1,u2,u4],[(u17,u1,u4),(u33,u17,u0),(0xc00cc00,u33,u2)],[0,2,5],[(1,392)]),
([u3,u14,u0,0xcf0f0000,u1,u2,u4],[(u14,u0,u2),(0x30f030f0,u14,u1),(0xcf0f0000,0x30f030f0,u4)],[0,2,6,7],[]),
([u33,u44,u3,u0,u1,u2,u4],[(u17,u1,u4),(u33,u17,u0),(u44,u17,u2)],[0,3,5,7,8],[(0,393)]),
([u3,u14,u0,0xccff0000,u1,u4],[(u14,u0,u2),(u47,u14,u2),(0xccff0000,u47,u4)],[0,2,3,8],[(1,362)]),
([u11,u3,u24,u0,u18,u1,u4],[(u18,u1,u2),(u11,u18,u2),(u24,u0,u4)],[0,1,2,4],[(0,394)]),
([u11,u29,u3,u24,u0,u1,u2],[(u24,u0,u4),(u29,u24,u4),(u11,u1,u2)],[0,1,2],[]),
([u0,u89,u1,u2,u4],[(u14,u0,u2),(u59,u14,u4),(u89,u3,u59)],[0,1,2,3],[(0,396),(0,397),(2,395),(2,398)]),
([u3,u0,u89,u1,u2,u4],[(u14,u0,u2),(u59,u14,u4),(u89,u3,u59)],[0,1,2,3,4,6],[(0,72),(2,128)]),
([u3,u0,0xfcf0f0f0,u2,u4],[(u14,u0,u2),(u59,u14,u4),(0xfcf0f0f0,u59,u1)],[0,1,2,3,6],[]),
([0xccccccc,u3,u1,u2,u4],[(u18,u1,u2),(u77,u18,u4),(0xccccccc,u77,u0)],[0,1,2,3,4],[]),
([u3,u106,u0,u1,u2,u4],[(u17,u1,u4),(u44,u17,u2),(u106,u44,u3)],[0,1,2,3,4,5,8],[]),
([u3,u106,u0,u17,u1,u2,u4],[(u17,u1,u4),(u44,u17,u2),(u106,u44,u3)],[0,1,2,4,7],[(0,372)]),
([u3,u14,u0,u1,0xf3fff0f0,u2,u4],[(u14,u0,u2),(0x33ff0000,u14,u4),(0xf3fff0f0,0x33ff0000,u1)],[0,2,3,5,6],[(3,393)]),
([u3,0xc000cccc,u0,u18,u1,u2,u4],[(u18,u1,u2),(0xfff0000,u18,u4),(0xc000cccc,0xfff0000,u0)],[0,2,3,4,5,8],[(0,387),(3,399)]),
([u11,0x3300ff00,u3,u24,u0,u1,u4],[(u24,u0,u4),(0x3300ff00,u24,u2),(u11,u1,u2)],[0,2,3],[(0,399)]),
([u3,u31,u0,u17,u1,u2,u4],[(u17,u1,u4),(u11,u1,u2),(u31,u11,u3)],[1,2,7],[(0,363),(1,364)]),
([u3,u14,u0,u1,0xf3f3f0f0,u2,u4],[(u14,u0,u2),(u29,u0,u4),(0xf3f3f0f0,u29,u1)],[0,3,5,6],[(3,390),(3,391)]),
([u3,u63,u0,u18,u1,u2,u4],[(u18,u1,u2),(u35,u1,u4),(u63,u35,u0)],[0,2,3,5,6,8],[(0,385),(2,386)]),
([u3,u0,u1,u2,0xff0ff000,u4],[(u18,u1,u2),(u35,u1,u4),(0xff0ff000,u35,u18)],[0,1,2,3,4,6,8],[(0,364),(0,400),(3,208)]),
([u3,u0,u1,u115,u2,u4],[(u24,u0,u4),(u18,u1,u2),(u115,u24,u18)],[0,1,2,3,8],[(0,375),(0,394),(0,401),(0,402),(3,394)]),
([u3,u14,u0,u1,0xfcf0cc00,u2,u4],[(u14,u0,u2),(u17,u1,u4),(0xfcf0cc00,u14,u17)],[0,2,4,5],[(2,394)]),
([u3,u14,u0,u17,u1,u6],[(u14,u0,u2),(u17,u1,u4),(u6,u2,u4)],[0,2,3,4,5,7],[(0,377),(1,402),(3,377)]),
([u3,u31,u24,u0,u1,u2,u4],[(u24,u0,u4),(u11,u1,u2),(u31,u11,u3)],[0,1,2,3,5],[(0,378),(1,379),(2,403)]),
([u3,u0,0xcf0fcc00,u1,u2,u4],[(u14,u0,u2),(u35,u1,u4),(0xcf0fcc00,u35,u14)],[0,1,2,3,8],[(0,379),(0,404),(1,206)]),
([u11,u3,u0,0xcfcc0f00,u1,u2,u4],[(u24,u0,u4),(u11,u1,u2),(0xcfcc0f00,u11,u24)],[0,3,4],[]),
([u3,u14,u0,0xcf0fcc00,u1,u2,u4],[(u14,u0,u2),(u35,u1,u4),(0xcf0fcc00,u35,u14)],[0,6],[]),
([u11,u3,0xc0cc0000,u0,u1,u2,u4],[(u24,u0,u4),(u11,u1,u2),(0xc0cc0000,u11,u24)],[0,4],[(1,388)]),
([u3,u14,u1,u30,u4],[(u14,u0,u2),(u6,u2,u4),(u30,u0,u6)],[0,1,2,3,5,8],[(0,75),(1,213),(2,130),(2,381)]),
([u127,u3,u31,u0,u1,u2,u4],[(u11,u1,u2),(u31,u11,u3),(u127,u31,u0)],[1,3,5,6,8],[(0,405)]),
([u3,u31,u0,u102,u1,u2,u4],[(u11,u1,u2),(u31,u11,u3),(u102,u31,u0)],[0,3,8],[(0,405),(0,406),(0,407)]),
([0xb0a0b0a,u3,u101,u0,u1,u2,u4],[(u47,u0,u2),(u101,u47,u3),(0xb0a0b0a,u101,u1)],[4,6],[(0,408)]),
([0x40404444,u3,0xafafaaaa,u0,u1,u2,u4],[(u35,u1,u4),(0xafafaaaa,u35,u3),(0x40404444,0xafafaaaa,u0)],[3,8],[(1,409),(3,408)]),
([u3,0xaf00aa00,0xafafaaaa,u0,u1,u2,u4],[(u35,u1,u4),(0xafafaaaa,u35,u3),(0xaf00aa00,0xafafaaaa,u2)],[0,5],[]),
([0x44005500,u3,0xbbbbaaaa,u0,u1,u2,u4],[(u29,u0,u4),(0xbbbbaaaa,u29,u3),(0x44005500,0xbbbbaaaa,u2)],[0,5],[(3,410)]),
([u11,u3,0xbbbbaaaa,u0,u1,u2,u4],[(u29,u0,u4),(0xbbbbaaaa,u29,u3),(u11,u1,u2)],[0,6],[(1,411),(3,412)]),
([u3,u31,u0,u52,u1,u2,u4],[(u11,u1,u2),(u31,u11,u3),(u52,u11,u0)],[0,1,3,5,8],[(0,406),(0,413)]),
([u3,u31,u118,u0,u1,u2,u4],[(u11,u1,u2),(u31,u11,u3),(u118,u11,u0)],[1,3,8],[(0,409),(2,414)]),
([u3,u31,u0,u1,u94,u2,u4],[(u11,u1,u2),(u31,u11,u3),(u94,u11,u4)],[1,2,4,5,7],[(0,410)]),
([u11,u127,u3,u0,u1,u2,u4],[(u11,u1,u2),(u31,u11,u3),(u127,u31,u0)],[0,1,3,5,6,8],[(0,413)]),
([0xb0a0b0a,u47,u3,u0,u1,u2,u4],[(u47,u0,u2),(u101,u47,u3),(0xb0a0b0a,u101,u1)],[0,1,5,6,8],[(0,414)]),
([u11,u3,0xafaa0000,u0,u1,u2,u4],[(u11,u1,u2),(u31,u11,u3),(0xafaa0000,u31,u4)],[0,1,2,5,7],[]),
([0x45444544,u3,u0,u1,u2,u4],[(u11,u1,u2),(u52,u11,u0),(0x45444544,u3,u52)],[0,1,2,3,6,7,8],[(2,112)]),
([u3,u63,u0,0xcfcfcccc,u1,u2,u4],[(u35,u1,u4),(0xcfcfcccc,u35,u0),(u63,u35,u0)],[2,6],[]),
([u3,u55,u0,u1,0xf3f3f0f0,u2,u4],[(u29,u0,u4),(0xf3f3f0f0,u29,u1),(u55,u29,u2)],[0,4,5,6],[(3,415)]),
([u11,0x45444544,u3,u0,u1,u2,u4],[(u11,u1,u2),(u52,u11,u0),(0x45444544,u3,u52)],[0,1,3],[(0,406)]),
([u11,u3,u0,0xcfcc0000,u1,u2,u4],[(u11,u1,u2),(u52,u11,u0),(0xcfcc0000,u52,u4)],[0,2,3,5,7],[]),
([0xc000f00,u29,u3,u0,u1,u2,u4],[(u29,u0,u4),(0xf3f3f0f0,u29,u1),(0xc000f00,0xf3f3f0f0,u2)],[2],[(1,416)]),
([u3,u0,0xeaeaeeee,u1,u2,u4],[(u35,u1,u4),(u63,u35,u0),(0xeaeaeeee,u3,u63)],[0,1,2,3,5,6,8],[]),
([u3,u63,u0,0xf000ff00,u1,u2,u4],[(u35,u1,u4),(u63,u35,u0),(0xf000ff00,u35,u2)],[0,3,5,8],[(0,417)]),
([u11,u3,u0,0xeaeeeaee,u1,u2,u4],[(u11,u1,u2),(u118,u11,u0),(0xeaeeeaee,u3,u118)],[0,1,4,6,8],[(0,409)]),
([u11,0x3f330000,u3,u0,u1,u2,u4],[(u11,u1,u2),(u118,u11,u0),(0x3f330000,u118,u4)],[0,2,7,8],[]),
([u3,0xafaaaaaa,u0,u1,u2,u4],[(u11,u1,u2),(u83,u11,u4),(0xafaaaaaa,u83,u3)],[0,1,2,3,6,8],[(0,77)]),
([u3,u0,0xeeaaffaa,u1,u2,u4],[(u29,u0,u4),(u55,u29,u2),(0xeeaaffaa,u3,u55)],[0,1,2,4,5,6,8],[]),
([u11,u3,u0,u1,0xfaffaaaa,u2,u4],[(u11,u1,u2),(u94,u11,u4),(0xfaffaaaa,u3,u94)],[0,1,2,6],[(0,410)]),
([u11,u3,u0,u1,0xfcffcccc,u2,u4],[(u11,u1,u2),(u94,u11,u4),(0xfcffcccc,u0,u94)],[0,2,3,5,8],[(1,417)]),
([0xc00cccc,u11,u3,u0,u1,u2,u4],[(u11,u1,u2),(u94,u11,u4),(0xc00cccc,u0,u94)],[0,2,3,6,8],[(0,415)]),
([0x3f0f3300,u3,u0,u1,u2,u4],[(u35,u1,u4),(u47,u0,u2),(0x3f0f3300,u35,u47)],[0,1,2,3,8],[(0,411),(0,418)]),
([u11,0x3f330f00,u3,u0,u1,u2,u4],[(u11,u1,u2),(u29,u0,u4),(0x3f330f00,u11,u29)],[0,8],[]),
([u3,u73,u0,u1,u2,u21,u4],[(u6,u2,u4),(u21,u3,u6),(u73,u0,u21)],[1,3,5,7,8],[(0,80),(0,419),(0,421),(2,420)]),
([u3,u0,u1,u2,u21,u100,u4],[(u6,u2,u4),(u21,u3,u6),(u100,u0,u21)],[0,2,3,8],[(0,421),(0,422),(0,424),(2,423)]),
([0x444444,u3,u0,u1,u2,u21,u4],[(u6,u2,u4),(u21,u3,u6),(0x444444,u0,u21)],[3,8],[(0,425),(0,426)]),
([0xf0a0a0a,u3,u0,u1,u2,u21,u4],[(u6,u2,u4),(u21,u3,u6),(0xf0a0a0a,u1,u21)],[1,4,5,6],[(0,81),(2,426)]),
([u3,u0,u1,u2,u21,u30,u4],[(u6,u2,u4),(u21,u3,u6),(u30,u0,u6)],[0,1,2,3,5,7,8],[(0,422),(0,427),(2,82)]),
([u26,u3,u0,u1,u2,u21,u4],[(u6,u2,u4),(u21,u3,u6),(u26,u0,u6)],[1,3,8],[(0,83),(0,425),(0,428)]),
([u3,u73,u0,u1,u6,u2,u4],[(u6,u2,u4),(u21,u3,u6),(u73,u0,u21)],[0,1,3,5,7,8],[(0,427),(0,429),(2,430)]),
([0xf0a0a0a,u3,u0,u1,u6,u2,u4],[(u6,u2,u4),(u21,u3,u6),(0xf0a0a0a,u1,u21)],[0,1,4,5,6,7],[(2,428)]),
([u126,u3,u0,u1,u2,u4],[(u6,u2,u4),(u30,u0,u6),(u126,u3,u30)],[0,1,2,4,6,8],[(0,360),(2,135)]),
([u126,u3,u0,u1,u6,u2,u4],[(u6,u2,u4),(u30,u0,u6),(u126,u3,u30)],[0,1,2,3,5,7],[(0,422)]),
([u26,u3,u0,u1,u2,u30,u4],[(u6,u2,u4),(u30,u0,u6),(u26,u0,u6)],[0,2,3,5],[]),
([u3,u0,u1,u2,u30,u37,u4],[(u6,u2,u4),(u30,u0,u6),(u37,u1,u6)],[0,2,3,5,6,7,8],[(0,246),(0,311),(0,431),(2,431)]),
([u26,u3,u0,u1,u2,u37,u4],[(u6,u2,u4),(u37,u1,u6),(u26,u0,u6)],[0,2,3,5,6,7,8],[(0,312),(0,433),(2,242),(2,432)]),
([u3,0xccc0c0c0,u0,u1,u6,u2,u4],[(u6,u2,u4),(u37,u1,u6),(0xccc0c0c0,u0,u37)],[0,2,3,5,8],[(0,246),(0,313),(0,431)]),
([0xf0c0c0c,u3,u0,u1,u6,u2,u4],[(u6,u2,u4),(u30,u0,u6),(0xf0c0c0c,u1,u30)],[0,2,3,4,5,6,7],[(0,242),(2,433)]),
([u3,u113,u0,u1,u2,u4],[(u6,u2,u4),(u26,u0,u6),(u113,u26,u3)],[0,1,2,3,4,6],[(0,314)]),
([u3,u113,u0,u1,u6,u2,u4],[(u6,u2,u4),(u26,u0,u6),(u113,u26,u3)],[0,1,2,5,7,8],[(0,425)]),
([u3,u0,0xccfcfcfc,u1,u6,u2,u4],[(u6,u2,u4),(u69,u1,u6),(0xccfcfcfc,u69,u0)],[0,2,3,5,7,8],[(0,308),(0,434)]),
([u3,0xcc0c0c0c,u0,u1,u6,u2,u4],[(u6,u2,u4),(u69,u1,u6),(0xcc0c0c0c,u69,u0)],[0,2,3,5,7,8],[(0,242),(0,432),(2,361)]),
([u26,u69,u3,u0,u1,u2,u4],[(u6,u2,u4),(u26,u0,u6),(u69,u1,u6)],[3,4,8],[(0,308),(0,316),(0,434),(2,434)])
]
set_option maxRecDepth 100000 in
def c5_0_L7 : Array W5Node := Array.mk [
([u13,u0,u12,u1,u2,u4],[(u12,u3,u0),(u13,u3,u0)],[0,1,2,3,8],[(0,0),(0,1),(0,2),(1,0),(1,1)]),
([u3,u7,u0,u12,u1,u2,u4],[(u12,u3,u0),(u7,u0,u1)],[0,1,2,3,6,8],[(0,3),(0,4),(0,5),(0,6),(1,5),(1,6)]),
([u3,u0,u15,u5,u2,u4],[(u15,u3,u1),(u5,u1,u0)],[0,1,2,3,6,8],[(0,7),(0,8),(0,9),(1,8),(2,3)]),
([u8,u3,u12,u1,u2,u4],[(u12,u3,u0),(u8,u0,u1)],[0,1,2,3,4,6,8],[(0,10),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(1,13),(1,15),(1,16),(2,11)]),
([u8,u3,u0,u12,u1,u2,u4],[(u12,u3,u0),(u8,u0,u1)],[0,1,2,3,4,8],[(0,20),(1,20),(2,18),(2,19),(3,19)]),
([u3,u14,u0,u12,u1,u2,u4],[(u12,u3,u0),(u14,u0,u2)],[0,1,2,3,8],[(0,22),(0,26),(0,27),(0,28),(2,25),(3,21),(3,23),(3,24)]),
([u3,u39,u0,u1,u2,u4],[(u15,u3,u1),(u39,u15,u0)],[0,1,2,3,5,6,7,8],[(0,7),(0,25),(0,30),(1,25),(2,29),(3,29)]),
([u3,u39,u0,u1,u15,u2,u4],[(u15,u3,u1),(u39,u15,u0)],[0,1,2,3,4,6,8],[(0,32),(0,34),(0,36),(1,32),(1,34),(1,36),(2,3),(2,14),(2,31),(2,33),(2,35),(3,33),(3,35)]),
([u3,u0,u1,u76,u2,u4],[(u12,u3,u0),(u76,u12,u1)],[0,1,2,5,6,7,8],[(0,37),(0,38),(1,37)]),
([u40,u3,u0,u1,u2,u4],[(u12,u3,u0),(u40,u12,u1)],[0,1,2,3,5,6,7,8],[(0,26),(0,39),(0,40),(1,26),(1,39)]),
([u40,u3,u0,u12,u1,u2,u4],[(u12,u3,u0),(u40,u12,u1)],[0,1,2,3,4,8],[(0,31),(0,41),(0,43),(0,44),(0,45),(1,41),(1,43),(1,44),(1,45),(2,42),(3,42)]),
([0x4040404,u3,u0,u1,u2,u4],[(u15,u3,u1),(0x4040404,u15,u0)],[0,1,2,3,5,6,7],[(0,46)]),
([u3,u0,u43,u1,u2,u4],[(u12,u3,u0),(u43,u12,u2)],[0,1,2,4,5,6,7,8],[(0,6),(0,20),(1,27),(1,48),(3,47)]),
([u3,u0,u43,u12,u1,u2,u4],[(u12,u3,u0),(u43,u12,u2)],[0,1,2,8],[(0,15),(0,41),(0,43),(0,49),(0,51),(0,53),(0,55),(2,32),(2,36),(2,54),(3,50),(3,52)]),
([0x5000500,u3,u0,u1,u2,u4],[(u15,u3,u1),(0x5000500,u15,u2)],[0,1,2,3,6,7,8],[(0,56),(0,57)]),
([u3,u14,u0,u1,u15,u2,u4],[(u15,u3,u1),(u14,u0,u2)],[0,1,2,3,4,5,6,8],[(0,8),(0,32),(0,34),(0,47),(0,54),(0,58),(0,59),(0,60),(0,63),(0,68),(0,70),(1,56),(2,0),(2,16),(2,39),(2,44),(2,67),(3,61),(3,62),(3,64),(3,65),(3,66),(3,69)]),
([u11,u3,u0,u12,u1,u2,u4],[(u12,u3,u0),(u11,u1,u2)],[0,1,2,3,4,6,8],[(0,1),(0,29),(0,35),(0,41),(0,45),(0,48),(0,67),(0,71),(0,73),(0,75),(3,57),(3,72),(3,74),(3,76)]),
([u3,u0,u12,u1,u6,u2,u4],[(u12,u3,u0),(u6,u2,u4)],[0,1,2,3,5,7,8],[(0,2),(0,17),(0,28),(0,38),(0,40),(0,51),(0,55),(0,75),(0,77),(0,78),(0,80),(0,81),(0,82),(0,83),(0,84),(0,85),(0,86),(1,28),(1,55),(2,9),(2,30),(2,46),(2,68),(2,70),(2,79),(2,87),(3,70)]),
([u53,u3,u0,u1,u2,u4],[(u13,u3,u0),(u53,u13,u1)],[0,1,2,3,4,5,7],[(0,88),(0,89)]),
([u3,u0,u64,u1,u2,u4],[(u22,u3,u1),(u64,u22,u0)],[0,1,2,3,4,5,7,8],[(0,90),(0,91),(1,90)]),
([u13,u3,u0,u1,0xf4f4f4f4,u2,u4],[(u13,u3,u0),(0xf4f4f4f4,u13,u1)],[0,1,2,3,4],[(0,94),(0,95),(1,94),(1,95),(2,92),(2,93),(3,93)]),
([u60,u3,u0,u1,u2,u4],[(u22,u3,u1),(u60,u22,u0)],[0,1,2,3,4,5,7,8],[(0,97),(0,98),(1,97),(2,96)]),
([u13,u3,u70,u0,u1,u2,u4],[(u13,u3,u0),(u70,u13,u1)],[0,1,2,3,6],[(0,100),(0,101),(0,102),(0,103),(1,102),(1,103),(2,92),(2,99),(3,99)]),
([0x44004400,u3,u0,u1,u2,u4],[(u13,u3,u0),(0x44004400,u13,u2)],[0,1,2,3,4,5,6,7],[(0,104),(1,105)]),
([u3,u61,u0,u1,u2,u4],[(u22,u3,u1),(u61,u22,u2)],[0,1,2,3,4,5,7,8],[(0,106),(0,107),(0,108),(1,110),(3,109)]),
([u13,u3,u78,u0,u1,u2,u4],[(u13,u3,u0),(u78,u13,u2)],[0,1,2,3],[(0,95),(0,102),(0,112),(0,114),(0,116),(1,115),(2,93),(2,99),(2,111),(3,113)]),
([u13,u3,u1,u5,u2,u4],[(u13,u3,u0),(u5,u0,u1)],[0,1,2,3,4,6,8],[(0,88),(0,101),(0,116),(0,117),(0,119),(0,120),(0,121),(0,122),(1,116),(1,120),(1,121),(2,118)]),
([u13,u3,u0,u1,u5,u2,u4],[(u13,u3,u0),(u5,u0,u1)],[0,1,2,3,4,8],[(0,124),(1,124),(2,106),(2,123),(3,106)]),
([u8,u13,u3,u1,u2,u4],[(u13,u3,u0),(u8,u0,u1)],[0,1,2,3,4,6],[(0,96),(0,100),(0,125),(0,126),(1,125)]),
([u8,u22,u3,u0,u1,u2,u4],[(u22,u3,u1),(u8,u1,u0)],[0,1,2,3,4,6,8],[(0,107),(0,127),(1,107),(2,100),(2,128),(3,128)]),
([u11,u22,u3,u0,u1,u2,u4],[(u22,u3,u1),(u11,u1,u2)],[0,1,2,4,6],[(0,90),(0,97),(0,110),(0,129),(2,130),(3,131),(3,132)]),
([u13,u3,u0,u18,u1,u2,u4],[(u13,u3,u0),(u18,u1,u2)],[0,1,2,3,4,6,8],[(0,0),(0,102),(0,120),(0,125),(0,134),(0,137),(0,138),(0,140),(0,141),(0,143),(1,104),(1,136),(1,139),(1,142),(2,133),(2,135),(3,108)]),
([u11,u13,u3,u0,u1,u2,u4],[(u13,u3,u0),(u11,u1,u2)],[0,1,2,3,4,6,8],[(0,1),(0,95),(0,105),(0,109),(0,140),(0,144),(0,145),(0,146),(0,147),(0,148),(1,149)]),
([u13,u3,u0,u1,u6,u2,u4],[(u13,u3,u0),(u6,u2,u4)],[0,1,2,3,5,7,8],[(0,2),(0,46),(0,89),(0,114),(0,122),(0,126),(0,141),(0,143),(0,148),(0,150),(0,151),(0,152),(0,153),(0,154),(0,155),(0,156),(0,157),(1,143),(2,91),(2,98),(2,158)]),
([u3,u0,u56,u1,u2,u4],[(u10,u3,u2),(u56,u10,u0)],[0,1,2,4,6,7,8],[(1,160),(3,159)]),
([u10,u3,u0,u56,u1,u2,u4],[(u10,u3,u2),(u56,u10,u0)],[0,1,2,3,5,8],[(0,162),(0,166),(0,167),(0,169),(1,161),(1,164),(2,165),(3,163),(3,168),(3,170)]),
([u48,u3,u0,u1,u2,u4],[(u19,u3,u4),(u48,u19,u0)],[0,1,2,3,4,5,6],[(0,172),(0,173),(0,174),(3,171)]),
([u10,0x88cc88cc,u3,u0,u1,u2,u4],[(u10,u3,u2),(0x88cc88cc,u10,u0)],[0,1,2,3,5,8],[(0,177),(0,180),(1,161),(1,163),(1,168),(1,175),(1,176),(2,178),(2,179),(2,181)]),
([u65,u3,u0,u1,u2,u4],[(u10,u3,u2),(u65,u10,u4)],[0,1,2,3,4,5,6,8],[(0,182),(0,183),(0,184),(2,184)]),
([u54,u3,u0,u1,u2,u4],[(u19,u3,u4),(u54,u19,u2)],[0,1,2,3,4,5,6,8],[(0,185),(0,186),(0,187),(2,187)]),
([u10,u3,0xaaff0000,u0,u1,u2,u4],[(u10,u3,u2),(0xaaff0000,u10,u4)],[0,1,2,5],[(0,180),(0,188),(0,189),(1,164),(1,170),(1,176),(2,180),(2,188),(2,189),(3,164),(3,170),(3,176)]),
([u10,u3,u7,u0,u1,u2,u4],[(u10,u3,u2),(u7,u0,u1)],[0,1,2,3,4,5,6,8],[(0,177),(0,182),(0,190),(0,191),(0,192),(0,193),(0,194),(0,195),(0,196),(0,197),(0,199),(0,200),(0,201),(0,202),(1,185),(1,198),(2,194),(2,195),(2,200),(2,201)]),
([u10,u3,u0,u1,u5,u2,u4],[(u10,u3,u2),(u5,u0,u1)],[0,1,2,3,4,5,6,8],[(0,166),(0,183),(0,195),(0,199),(0,200),(0,203),(0,205),(0,207),(0,208),(0,209),(0,210),(0,212),(1,186),(1,204),(1,206),(1,211),(2,195),(2,200),(2,209)]),
([u8,u10,u3,u0,u1,u2,u4],[(u10,u3,u2),(u8,u0,u1)],[0,1,2,3,4,5,6,8],[(0,184),(0,194),(0,209),(0,213),(0,214),(0,215),(0,216),(0,217),(0,218),(0,219),(0,222),(0,223),(0,224),(0,225),(1,168),(1,187),(1,220),(2,221),(2,223)]),
([u11,u10,u3,u0,u1,u4],[(u10,u3,u2),(u11,u1,u2)],[0,1,2,4,5,6],[(0,171),(0,201),(0,226),(0,228),(0,229),(0,230),(2,224),(2,227)]),
([u10,u3,u24,u0,u1,u2,u4],[(u10,u3,u2),(u24,u0,u4)],[0,1,2,3,5,8],[(0,56),(0,180),(0,197),(0,228),(0,232),(0,239),(1,159),(1,220),(1,231),(1,233),(2,104),(2,230),(2,234),(2,235),(2,236),(2,237),(3,172),(3,238)]),
([u11,u19,u3,u0,u1,u2,u4],[(u19,u3,u4),(u11,u1,u2)],[0,1,2,4,6,7],[(0,105),(0,160),(0,170),(0,173),(0,211),(0,220),(0,238),(0,241),(0,243),(1,240),(1,242),(1,244),(1,245),(3,57),(3,229)]),
([u10,u3,u0,u1,u6,u4],[(u10,u3,u2),(u6,u2,u4)],[0,1,2,5],[(0,202),(0,212),(0,225),(0,239),(0,246),(1,174),(2,225),(2,239),(2,246),(3,174)]),
([u3,u0,u20,u1,u2,u4],[(u7,u0,u1),(u20,u3,u7)],[0,1,2,3,4,5,7,8],[(0,247),(0,248),(0,249),(0,250),(0,251),(0,252),(0,253),(0,254),(1,251),(1,252),(1,253),(2,248),(2,250),(2,251),(3,251)]),
([u3,u7,u0,u20,u1,u2,u4],[(u7,u0,u1),(u20,u3,u7)],[0,1,2,3,4,8],[(0,193),(0,250),(0,255),(0,256),(0,257),(1,193),(1,255),(1,257),(2,250)]),
([u8,u3,u7,u1,u2,u4],[(u7,u0,u1),(u8,u7,u0)],[0,1,2,3,4],[(0,194),(0,250),(0,258),(0,259),(0,260),(1,194)]),
([u8,u3,u0,u1,u2,u4],[(u7,u0,u1),(u8,u7,u0)],[0,1,2,3,4,5,6,7,8],[(0,3),(0,195),(0,259),(0,261),(0,262),(1,195)]),
([u3,u111,u0,u1,u2,u4],[(u7,u0,u1),(u111,u7,u2)],[0,1,2,3,4,5,7],[(0,263),(0,264),(1,197),(1,265)]),
([u28,u3,u0,u1,u2,u4],[(u7,u0,u1),(u28,u7,u2)],[0,1,2,3,4,5,7,8],[(0,5),(0,198),(0,266),(0,267),(1,268),(2,5),(3,268)]),
([u28,u3,u7,u0,u1,u2,u4],[(u7,u0,u1),(u28,u7,u2)],[0,1,2,3,4,8],[(0,193),(0,196),(0,255),(0,269),(0,270),(0,272),(0,273),(1,271)]),
([u3,u7,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1)],[0,1,2,3,8],[(0,88),(0,199),(0,247),(0,256),(0,273),(0,274),(0,275),(0,276),(0,277),(0,278),(0,279),(0,280),(1,199),(1,273),(1,279)]),
([u3,u7,u0,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1)],[0,1,2,3,8],[(0,200),(0,248),(0,281),(0,282),(1,200)]),
([u3,u7,u0,u1,u5,u2,u4],[(u7,u0,u1),(u5,u0,u1)],[0,1,2,3,4,6,8],[(0,249),(0,267),(0,283),(0,284),(0,285),(1,267),(1,285)]),
([u11,u3,u7,u0,u1,u2,u4],[(u7,u1,u0),(u11,u1,u2)],[0,1,2,3,4,6,8],[(0,201),(0,251),(0,268),(0,286),(0,287),(3,288)]),
([u3,u7,u0,u1,u6,u2,u4],[(u7,u0,u1),(u6,u2,u4)],[0,1,2,3,4,5,6,7,8],[(0,89),(0,182),(0,202),(0,254),(0,260),(0,262),(0,270),(0,280),(0,282),(0,289),(0,290),(0,291),(0,292),(0,293),(1,202),(2,260),(2,262),(2,282)]),
([u23,u3,u0,u1,u2,u4],[(u5,u0,u1),(u23,u3,u5)],[0,1,2,3,5,6,7,8],[(0,207),(0,283),(0,294),(0,295),(0,296),(0,297),(1,207),(1,294),(1,295),(1,296),(2,296),(3,296)]),
([u23,u3,u0,u1,u5,u2,u4],[(u5,u0,u1),(u23,u3,u5)],[0,1,2,3,6,8],[(0,203),(0,208),(0,274),(0,298),(0,299),(1,203),(1,208),(1,298),(1,299)]),
([u8,u3,u0,u5,u2,u4],[(u5,u0,u1),(u8,u0,u1)],[0,1,2,3,8],[(0,209),(0,258),(0,259),(0,300),(0,301),(1,209)]),
([u3,u14,u0,u1,u5,u2,u4],[(u5,u0,u1),(u14,u0,u2)],[0,1,2,3,4,8],[(0,8),(0,296),(0,302),(0,305),(0,306),(2,120),(3,303),(3,304)]),
([u3,u0,u1,u25,u2,u4],[(u5,u0,u1),(u25,u5,u2)],[0,1,2,3,5,6,7,8],[(0,124),(0,285),(0,307),(1,210),(1,305),(2,124),(3,305)]),
([u3,u0,u1,u25,u5,u2,u4],[(u5,u0,u1),(u25,u5,u2)],[0,1,2,3,6,8],[(0,121),(0,203),(0,279),(0,299),(0,308),(0,309),(0,311),(0,312),(1,310),(2,121)]),
([0x3000300,u3,u0,u1,u2,u4],[(u5,u0,u1),(0x3000300,u5,u2)],[0,1,2,5,6,7,8],[(0,211),(0,313)]),
([u3,u0,u1,u5,u6,u2,u4],[(u5,u0,u1),(u6,u2,u4)],[0,1,2,3,4,5,6,7,8],[(0,9),(0,38),(0,122),(0,183),(0,212),(0,262),(0,280),(0,282),(0,297),(0,301),(0,306),(0,309),(0,312),(0,314),(0,315),(0,316),(0,317),(0,318),(0,319),(0,320),(0,321),(1,212),(1,306),(1,312),(2,9),(2,122),(2,262),(2,282),(2,301),(2,306),(2,315),(2,316),(2,317),(3,306)]),
([u3,u27,u0,u1,u2,u4],[(u8,u0,u1),(u27,u8,u3)],[0,1,2,3,5,6,7,8],[(0,300),(0,322),(0,327),(0,328),(1,322),(1,327),(2,323),(2,324),(2,325),(2,326),(3,323),(3,326)]),
([u8,u3,u27,u0,u1,u2,u4],[(u8,u0,u1),(u27,u8,u3)],[0,1,2,3,6,8],[(0,216),(0,300),(0,329),(0,330),(0,331),(1,216),(1,329),(1,330)]),
([u3,u7,u0,u1,u2,u4],[(u8,u0,u1),(u7,u8,u0)],[0,1,2,3,4,5,7,8],[(0,217),(0,258),(0,332),(0,333),(1,217)]),
([u3,u0,u1,u5,u2,u4],[(u8,u0,u1),(u5,u8,u1)],[0,1,2,3,4,5,6,7,8],[(0,100),(0,218),(0,258),(0,334),(0,335),(1,218),(2,100)]),
([0xc000c00,u3,u0,u1,u2,u4],[(u8,u0,u1),(0xc000c00,u8,u2)],[0,1,2,3,6,7],[(0,220),(0,336)]),
([u3,u0,u36,u1,u2,u4],[(u16,u1,u0),(u36,u16,u2)],[0,1,2,3,4,5,7,8],[(0,19),(0,128),(0,337),(0,338),(1,221),(1,339),(1,340)]),
([u8,u3,u0,u1,u51,u2,u4],[(u8,u0,u1),(u51,u8,u2)],[0,1,2,3,6,8],[(0,13),(0,216),(0,219),(0,329),(0,342),(0,344),(0,346),(1,345),(2,341),(2,343)]),
([u8,u16,u3,u2,u4],[(u8,u0,u1),(u16,u0,u1)],[0,1,2,3,8],[(0,222),(0,275),(0,331),(0,343),(0,347),(0,348),(0,349),(1,222),(1,343),(2,331),(2,343),(2,347),(3,343)]),
([u8,u16,u3,u0,u2,u4],[(u8,u0,u1),(u16,u0,u1)],[0,1,2,3,8],[(0,223),(0,281),(0,350),(1,223),(2,324)]),
([u8,u16,u3,u0,u1,u2,u4],[(u8,u0,u1),(u16,u0,u1)],[0,1,2,3,4,6,8],[(0,284),(0,325),(0,338),(1,338),(2,325),(2,338),(3,338)]),
([u8,u47,u3,u0,u1,u2,u4],[(u8,u0,u1),(u47,u0,u2)],[0,1,2,3,4,8],[(0,224),(0,351),(0,352),(1,353),(2,326),(2,340)]),
([u8,u3,u0,u18,u1,u2,u4],[(u8,u0,u1),(u18,u1,u2)],[0,1,2,3,4,6,8],[(0,16),(0,125),(0,327),(0,354),(0,355),(0,357),(1,356),(2,339)]),
([u8,u3,u0,u1,u6,u2,u4],[(u8,u0,u1),(u6,u2,u4)],[0,1,2,3,4,5,6,7,8],[(0,17),(0,46),(0,126),(0,184),(0,225),(0,260),(0,301),(0,328),(0,333),(0,335),(0,344),(0,346),(0,349),(0,350),(0,357),(0,358),(0,359),(0,360),(0,361),(0,362),(0,363),(0,364),(0,365),(1,225),(1,346),(1,357),(2,350)]),
([u3,u0,u32,u1,u2,u4],[(u14,u0,u2),(u32,u3,u14)],[0,1,2,3,4,6,7],[(0,58),(0,302),(0,369),(0,370),(0,376),(1,372),(1,375),(2,355),(2,366),(2,368),(3,367),(3,371),(3,373),(3,374)]),
([u3,u14,u0,u32,u1,u2,u4],[(u14,u0,u2),(u32,u3,u14)],[0,1,2,3,5],[(0,59),(0,63),(0,377),(0,381),(0,382),(2,366),(2,380),(3,136),(3,234),(3,378),(3,379)]),
([u3,u0,u1,u50,u2,u4],[(u18,u1,u2),(u50,u18,u0)],[0,1,2,3,4,7,8],[(0,137),(0,383),(1,235),(1,384),(2,22)]),
([u3,u14,u0,u1,u67,u2,u4],[(u14,u0,u2),(u67,u14,u1)],[0,1,2,3,4,5],[(0,60),(0,63),(0,377),(0,388),(1,389),(2,138),(2,385),(3,386),(3,387)]),
([u33,u3,u0,u1,u2,u4],[(u17,u1,u4),(u33,u17,u0)],[0,1,2,3,4,5,8],[(0,23),(0,61),(0,236),(0,390),(0,391),(0,392)]),
([u33,u3,u0,u17,u1,u2,u4],[(u17,u1,u4),(u33,u17,u0)],[0,1,2,3,4,7,8],[(0,62),(0,136),(0,139),(0,378),(0,386),(0,393),(0,394),(0,396),(3,395)]),
([u11,u3,u0,u18,u1,u4],[(u18,u1,u2),(u11,u18,u2)],[0,1,2,4,6],[(0,67),(0,140),(0,238),(0,366),(0,398),(2,397),(3,399)]),
([u3,u59,u0,u1,u2,u4],[(u14,u0,u2),(u59,u14,u4)],[0,1,2,3,4,6],[(0,68),(0,400),(0,401),(0,402),(2,141),(2,403)]),
([u44,u3,u0,u1,u2,u4],[(u17,u1,u4),(u44,u17,u2)],[0,1,2,3,4,5,8],[(0,24),(0,69),(0,142),(0,304),(0,356),(0,404)]),
([u44,u3,u0,u17,u1,u2,u4],[(u17,u1,u4),(u44,u17,u2)],[0,1,2,4,5,6,7],[(0,234),(0,237),(0,379),(0,387),(0,394),(0,396),(0,405),(1,407),(2,389),(2,408),(3,406)]),
([u11,u3,u0,u17,u1,u2,u4],[(u17,u1,u4),(u11,u1,u2)],[0,1,2,4,6],[(0,230),(0,367),(0,384),(0,391),(0,409),(1,411),(1,412),(3,410)]),
([u3,u14,u0,u17,u1,u2,u4],[(u14,u0,u2),(u17,u1,u4)],[0,1,2,3,4,6,8],[(0,104),(0,374),(0,394),(0,414),(0,415),(1,398),(1,413),(2,398),(3,104),(3,374),(3,394),(3,414)]),
([u11,u3,u24,u0,u1,u2,u4],[(u24,u0,u4),(u11,u1,u2)],[0,1,2,3,4,5,6,8],[(0,56),(0,105),(0,228),(0,375),(0,389),(0,398),(0,399),(0,408),(0,416),(0,418),(0,420),(1,417),(1,419)]),
([u3,u14,u0,u1,u6,u4],[(u14,u0,u2),(u6,u2,u4)],[0,1,2,3,5,8],[(0,28),(0,70),(0,306),(0,376),(0,415),(0,421),(1,239),(2,143),(2,357),(3,392)]),
([u3,u31,u0,u1,u2,u4],[(u11,u1,u2),(u31,u11,u3)],[0,1,2,3,6,7,8],[(0,286),(0,409),(0,416),(0,422),(0,423),(1,425),(1,426),(2,352),(2,424),(3,427),(3,428)]),
([u11,u3,u31,u0,u1,u2,u4],[(u11,u1,u2),(u31,u11,u3)],[0,1,2,4,5,6],[(0,71),(0,147),(0,243),(0,429),(0,430),(0,431),(0,432),(0,434),(2,433)]),
([u3,u0,u52,u1,u2,u4],[(u11,u1,u2),(u52,u11,u0)],[0,1,2,3,6,7,8],[(0,226),(0,435),(1,244),(2,130),(3,410)]),
([u11,u3,u0,u52,u1,u2,u4],[(u11,u1,u2),(u52,u11,u0)],[0,1,2,3,4,5,6,8],[(0,71),(0,429),(0,438),(0,439),(1,436),(3,437),(3,440)]),
([u3,u63,u0,u1,u2,u4],[(u35,u1,u4),(u63,u35,u0)],[0,1,2,3,5,6,8],[(0,245),(0,411),(0,441),(2,131)]),
([u11,u3,u118,u0,u1,u2,u4],[(u11,u1,u2),(u118,u11,u0)],[0,1,2,3,4,5,6,8],[(0,147),(0,420),(0,430),(0,443),(0,444),(1,436),(1,442)]),
([u83,u3,u0,u1,u2,u4],[(u11,u1,u2),(u83,u11,u4)],[0,1,2,3,5,6,7,8],[(0,75),(0,148),(0,445)]),
([u3,u55,u0,u1,u2,u4],[(u29,u0,u4),(u55,u29,u2)],[0,1,2,4,5,6,8],[(0,76),(0,132),(0,288),(0,353),(0,446),(1,227),(1,397),(2,149)]),
([u11,u3,u0,u1,u94,u2,u4],[(u11,u1,u2),(u94,u11,u4)],[0,1,2,5,6],[(0,243),(0,420),(0,431),(0,447),(0,448),(0,449),(1,442),(2,397),(3,437),(3,440)]),
([u11,u29,u3,u0,u1,u2,u4],[(u11,u1,u2),(u29,u0,u4)],[0,1,2,3,4,6,8],[(0,57),(0,229),(0,399),(0,428),(0,440),(0,451),(1,450),(3,57),(3,229),(3,399),(3,428),(3,440),(3,451)]),
([u3,u0,u1,u2,u21,u4],[(u6,u2,u4),(u21,u3,u6)],[0,1,2,3,4,5,6,8],[(0,77),(0,289),(0,314),(0,362),(0,452),(0,453),(0,454),(0,455),(2,77),(2,362),(2,452),(2,453),(2,454),(2,455)]),
([u3,u0,u1,u6,u2,u21,u4],[(u6,u2,u4),(u21,u3,u6)],[0,1,2,5,7],[(0,78),(0,82),(0,153),(0,456),(0,457),(0,458),(0,459),(2,78),(2,82),(2,153),(2,456),(2,457),(2,458),(2,459)]),
([u3,u0,u1,u2,u30,u4],[(u6,u2,u4),(u30,u0,u6)],[0,1,2,4,6,8],[(0,154),(0,246),(0,363),(0,421),(0,460),(1,246),(1,421),(2,86),(2,157)]),
([u3,u0,u1,u6,u2,u30,u4],[(u6,u2,u4),(u30,u0,u6)],[0,1,2,3,5,7,8],[(0,82),(0,155),(0,318),(0,364),(0,456),(0,461),(0,462),(0,463),(0,466),(2,79),(2,315),(2,361),(2,464),(2,465)]),
([u26,u3,u0,u1,u2,u4],[(u6,u2,u4),(u26,u0,u6)],[0,1,2,3,4,6],[(0,80),(0,87),(0,158),(0,316),(0,467)]),
([u26,u3,u0,u1,u6,u2,u4],[(u6,u2,u4),(u26,u0,u6)],[0,1,2,3,5,7,8],[(0,81),(0,153),(0,156),(0,293),(0,317),(0,361),(0,365),(0,457),(0,462),(0,464),(0,468),(0,471),(2,469),(2,470)])
]
def c5_0_L8 : Array W5Node := Array.mk [
([u3,u0,u12,u1,u2,u4],[(u12,u3,u0)],[0,1,2,8],[(0,0),(0,1),(0,3),(0,4),(0,5),(0,8),(0,9),(0,10),(0,12),(0,13),(0,16),(0,17),(1,5),(1,12),(1,13),(1,16),(2,2),(2,6),(2,7),(2,11),(2,14),(2,15),(3,14),(3,15)]),
([u13,u3,u0,u1,u2,u4],[(u13,u3,u0)],[0,1,2,3],[(0,0),(0,11),(0,18),(0,20),(0,22),(0,23),(0,25),(0,26),(0,27),(0,28),(0,31),(0,32),(0,33),(1,23),(1,25),(1,31),(1,32),(2,19),(2,21),(2,24),(2,29),(2,30),(3,24),(3,30)]),
([u10,u3,u0,u1,u2,u4],[(u10,u3,u2)],[0,1,2,5],[(0,14),(0,23),(0,34),(0,35),(0,37),(0,38),(0,40),(0,41),(0,42),(0,43),(0,44),(0,45),(0,47),(1,36),(1,39),(1,46),(2,14),(2,23),(2,34),(2,35),(2,37),(2,43),(2,44),(2,45),(3,36),(3,46)]),
([u3,u7,u0,u1,u2,u4],[(u7,u0,u1)],[0,1,2,3,4],[(0,1),(0,18),(0,41),(0,48),(0,49),(0,50),(0,51),(0,52),(0,53),(0,54),(0,55),(0,56),(0,57),(0,58),(0,59),(1,41),(1,52),(1,53),(1,54),(1,58),(2,1),(2,50),(2,51),(2,56),(2,58),(3,58)]),
([u3,u0,u1,u5,u2,u4],[(u5,u0,u1)],[0,1,2,6,8],[(0,2),(0,8),(0,26),(0,27),(0,42),(0,51),(0,55),(0,56),(0,57),(0,60),(0,61),(0,62),(0,63),(0,64),(0,65),(0,66),(0,67),(1,42),(1,63),(1,64),(1,65),(1,66),(2,2),(2,26),(2,27),(2,51),(2,56),(2,62),(2,63),(3,63)]),
([u8,u3,u0,u1,u2,u4],[(u8,u0,u1)],[0,1,2,3,6],[(0,3),(0,4),(0,11),(0,28),(0,29),(0,43),(0,50),(0,62),(0,68),(0,69),(0,70),(0,71),(0,72),(0,74),(0,75),(0,76),(0,77),(0,78),(0,79),(0,80),(1,43),(1,72),(1,74),(1,78),(1,79),(2,73),(2,76),(3,73)]),
([u3,u14,u0,u1,u2,u4],[(u14,u0,u2)],[0,1,2,3],[(0,5),(0,15),(0,23),(0,52),(0,63),(0,72),(0,81),(0,82),(0,84),(0,88),(0,92),(0,94),(1,45),(1,93),(2,31),(2,79),(2,83),(2,87),(3,85),(3,86),(3,89),(3,90),(3,91)]),
([u11,u3,u0,u1,u2,u4],[(u11,u1,u2)],[0,1,2,6],[(0,14),(0,16),(0,30),(0,32),(0,44),(0,46),(0,58),(0,66),(0,72),(0,87),(0,91),(0,93),(0,95),(0,96),(0,97),(0,98),(0,100),(0,101),(0,103),(0,104),(1,99),(2,78),(3,102)]),
([u3,u0,u1,u6,u2,u4],[(u6,u2,u4)],[0,1,2,5],[(0,17),(0,33),(0,38),(0,47),(0,59),(0,67),(0,80),(0,88),(0,94),(0,101),(0,105),(0,106),(0,107),(0,108),(0,109),(0,110),(1,47),(1,94),(2,17),(2,33),(2,80),(2,88),(2,94),(2,101),(2,107),(2,108),(2,109),(2,110),(3,94)])
]
def c5_0_L9 : Array W5Node := Array.mk [
([u3,u0,u1,u2,u4],[],[0,1,2],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,6),(1,7),(2,0),(2,1),(2,5),(2,6),(2,7),(3,6),(3,7)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_3_0 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 3 c5_0_L3 (Array.mk []) 0 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_3 : ∀ i < c5_0_L3.size, checkNodeW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 3 c5_0_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_0_L3.size = 11 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_0 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_1 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_2 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_3 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_4 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_5 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_6 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_7 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 112 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_4 : ∀ i < c5_0_L4.size, checkNodeW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 i = true := by
  intro i hi
  have hsz : c5_0_L4.size = 119 := by decide +kernel
  have hi' : i < 119 := hsz ▸ hi
  by_cases h : i < 64
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW5_at c5_0_chk_4_0 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_4_1 i (by omega) (by omega)
    ·
      by_cases h : i < 48
      ·
        exact checkBlockW5_at c5_0_chk_4_2 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_4_3 i (by omega) (by omega)
  ·
    by_cases h : i < 96
    ·
      by_cases h : i < 80
      ·
        exact checkBlockW5_at c5_0_chk_4_4 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_4_5 i (by omega) (by omega)
    ·
      by_cases h : i < 112
      ·
        exact checkBlockW5_at c5_0_chk_4_6 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_4_7 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_0 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_1 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_2 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_3 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_4 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_5 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_6 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_7 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_8 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_9 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_10 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_11 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_12 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_13 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_14 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_15 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_16 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_17 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_18 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_19 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_20 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_21 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_22 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_23 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 368 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_24 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 384 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_25 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 400 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_26 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 416 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_27 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 432 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_5 : ∀ i < c5_0_L5.size, checkNodeW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 i = true := by
  intro i hi
  have hsz : c5_0_L5.size = 435 := by decide +kernel
  have hi' : i < 435 := hsz ▸ hi
  by_cases h : i < 224
  ·
    by_cases h : i < 112
    ·
      by_cases h : i < 64
      ·
        by_cases h : i < 32
        ·
          by_cases h : i < 16
          ·
            exact checkBlockW5_at c5_0_chk_5_0 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_5_1 i (by omega) (by omega)
        ·
          by_cases h : i < 48
          ·
            exact checkBlockW5_at c5_0_chk_5_2 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_5_3 i (by omega) (by omega)
      ·
        by_cases h : i < 96
        ·
          by_cases h : i < 80
          ·
            exact checkBlockW5_at c5_0_chk_5_4 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_5_5 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_5_6 i (by omega) (by omega)
    ·
      by_cases h : i < 176
      ·
        by_cases h : i < 144
        ·
          by_cases h : i < 128
          ·
            exact checkBlockW5_at c5_0_chk_5_7 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_5_8 i (by omega) (by omega)
        ·
          by_cases h : i < 160
          ·
            exact checkBlockW5_at c5_0_chk_5_9 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_5_10 i (by omega) (by omega)
      ·
        by_cases h : i < 208
        ·
          by_cases h : i < 192
          ·
            exact checkBlockW5_at c5_0_chk_5_11 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_5_12 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_5_13 i (by omega) (by omega)
  ·
    by_cases h : i < 336
    ·
      by_cases h : i < 288
      ·
        by_cases h : i < 256
        ·
          by_cases h : i < 240
          ·
            exact checkBlockW5_at c5_0_chk_5_14 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_5_15 i (by omega) (by omega)
        ·
          by_cases h : i < 272
          ·
            exact checkBlockW5_at c5_0_chk_5_16 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_5_17 i (by omega) (by omega)
      ·
        by_cases h : i < 320
        ·
          by_cases h : i < 304
          ·
            exact checkBlockW5_at c5_0_chk_5_18 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_5_19 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_5_20 i (by omega) (by omega)
    ·
      by_cases h : i < 400
      ·
        by_cases h : i < 368
        ·
          by_cases h : i < 352
          ·
            exact checkBlockW5_at c5_0_chk_5_21 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_5_22 i (by omega) (by omega)
        ·
          by_cases h : i < 384
          ·
            exact checkBlockW5_at c5_0_chk_5_23 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_5_24 i (by omega) (by omega)
      ·
        by_cases h : i < 432
        ·
          by_cases h : i < 416
          ·
            exact checkBlockW5_at c5_0_chk_5_25 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_5_26 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_5_27 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_0 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_1 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_2 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_3 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_4 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_5 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_6 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_7 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_8 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_9 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_10 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_11 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_12 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_13 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_14 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_15 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_16 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_17 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_18 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_19 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_20 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_21 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_22 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_23 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 368 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_24 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 384 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_25 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 400 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_26 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 416 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_27 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 432 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_28 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 448 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_29 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 464 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_6 : ∀ i < c5_0_L6.size, checkNodeW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 i = true := by
  intro i hi
  have hsz : c5_0_L6.size = 472 := by decide +kernel
  have hi' : i < 472 := hsz ▸ hi
  by_cases h : i < 240
  ·
    by_cases h : i < 128
    ·
      by_cases h : i < 64
      ·
        by_cases h : i < 32
        ·
          by_cases h : i < 16
          ·
            exact checkBlockW5_at c5_0_chk_6_0 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_1 i (by omega) (by omega)
        ·
          by_cases h : i < 48
          ·
            exact checkBlockW5_at c5_0_chk_6_2 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_3 i (by omega) (by omega)
      ·
        by_cases h : i < 96
        ·
          by_cases h : i < 80
          ·
            exact checkBlockW5_at c5_0_chk_6_4 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_5 i (by omega) (by omega)
        ·
          by_cases h : i < 112
          ·
            exact checkBlockW5_at c5_0_chk_6_6 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_7 i (by omega) (by omega)
    ·
      by_cases h : i < 192
      ·
        by_cases h : i < 160
        ·
          by_cases h : i < 144
          ·
            exact checkBlockW5_at c5_0_chk_6_8 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_9 i (by omega) (by omega)
        ·
          by_cases h : i < 176
          ·
            exact checkBlockW5_at c5_0_chk_6_10 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_11 i (by omega) (by omega)
      ·
        by_cases h : i < 224
        ·
          by_cases h : i < 208
          ·
            exact checkBlockW5_at c5_0_chk_6_12 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_13 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_6_14 i (by omega) (by omega)
  ·
    by_cases h : i < 368
    ·
      by_cases h : i < 304
      ·
        by_cases h : i < 272
        ·
          by_cases h : i < 256
          ·
            exact checkBlockW5_at c5_0_chk_6_15 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_16 i (by omega) (by omega)
        ·
          by_cases h : i < 288
          ·
            exact checkBlockW5_at c5_0_chk_6_17 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_18 i (by omega) (by omega)
      ·
        by_cases h : i < 336
        ·
          by_cases h : i < 320
          ·
            exact checkBlockW5_at c5_0_chk_6_19 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_20 i (by omega) (by omega)
        ·
          by_cases h : i < 352
          ·
            exact checkBlockW5_at c5_0_chk_6_21 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_22 i (by omega) (by omega)
    ·
      by_cases h : i < 432
      ·
        by_cases h : i < 400
        ·
          by_cases h : i < 384
          ·
            exact checkBlockW5_at c5_0_chk_6_23 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_24 i (by omega) (by omega)
        ·
          by_cases h : i < 416
          ·
            exact checkBlockW5_at c5_0_chk_6_25 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_26 i (by omega) (by omega)
      ·
        by_cases h : i < 464
        ·
          by_cases h : i < 448
          ·
            exact checkBlockW5_at c5_0_chk_6_27 i (by omega) (by omega)
          ·
            exact checkBlockW5_at c5_0_chk_6_28 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_6_29 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_7_0 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_7_1 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_7_2 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_7_3 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_7_4 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_7_5 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_7_6 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 96 15 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_7 : ∀ i < c5_0_L7.size, checkNodeW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 i = true := by
  intro i hi
  have hsz : c5_0_L7.size = 111 := by decide +kernel
  have hi' : i < 111 := hsz ▸ hi
  by_cases h : i < 64
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW5_at c5_0_chk_7_0 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_7_1 i (by omega) (by omega)
    ·
      by_cases h : i < 48
      ·
        exact checkBlockW5_at c5_0_chk_7_2 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_7_3 i (by omega) (by omega)
  ·
    by_cases h : i < 96
    ·
      by_cases h : i < 80
      ·
        exact checkBlockW5_at c5_0_chk_7_4 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_7_5 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_0_chk_7_6 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_8_0 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 8 c5_0_L8 c5_0_L7 0 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_8 : ∀ i < c5_0_L8.size, checkNodeW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 8 c5_0_L8 c5_0_L7 i = true := by
  intro i hi
  have hsz : c5_0_L8.size = 9 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_8_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_9_0 : checkBlockW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 9 c5_0_L9 c5_0_L8 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_9 : ∀ i < c5_0_L9.size, checkNodeW5 c5_0_goal 4 c5_0_pow 9 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 9 c5_0_L9 c5_0_L8 i = true := by
  intro i hi
  have hsz : c5_0_L9.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_9_0 i (Nat.zero_le _) (by omega)
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
theorem c5_0_L8_sound : ∀ i < c5_0_L8.size, ¬ live (basicOps 32) c5_0_goal 8 (c5_0_L8[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L7_sound c5_0_chk_8
theorem c5_0_L9_sound : ∀ i < c5_0_L9.size, ¬ live (basicOps 32) c5_0_goal 9 (c5_0_L9[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L8_sound c5_0_chk_9
set_option maxRecDepth 100000 in
theorem c5_0_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_0_goal ws) = [rows5] := by decide +kernel
theorem c5_0_top_match : sameSet (rows5.map (actB 32 (c5_0_pow[0]?.getD []))) (c5_0_L9[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_0_no_build : ¬ build (basicOps 32) c5_0_goal 9 rows5.toFinset :=
  no_build_of_top c5_0_G_valid (by decide) c5_0_sublists c5_0_top_match (c5_0_L9_sound 0 (by decide))

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4276676776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
theorem sample6_ok : ∀ k : Fin 64, F (fun i => (rows6.getD i.val 0)[k.val]) = goal6[k.val] := by decide +kernel

def idx65 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem idx65_spec : idx65.length = 32 ∧ ∀ idx ∈ idx65, idx < 64 := by decide
theorem projS65_goal6 : projS 32 idx65 goal6 = c5_0_goal := by decide +kernel
theorem projS65_xv : projS 32 idx65 (rows6.getD 5 0) = 0 := by decide +kernel
theorem projS65_rows6_sub : rows6.all (fun w => projS 32 idx65 w == 0 || rows5.contains (projS 32 idx65 w)) = true := by decide +kernel
theorem xv_ess_only : rows6.all (fun w => w == rows6.getD 5 0 || w.getLsbD 1 == w.getLsbD 33) = true := by decide +kernel
theorem goal6_diff : goal6.getLsbD 1 ≠ goal6.getLsbD 33 := by decide
theorem ops6_diff (a b z : W6) (hz : z ∈ basicOps6 a b) (hd : z.getLsbD 1 ≠ z.getLsbD 33) :
    a.getLsbD 1 ≠ a.getLsbD 33 ∨ b.getLsbD 1 ≠ b.getLsbD 33 := by
  simp only [basicOps6, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail; obtain ⟨ha, hb⟩ := fail; apply hd
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
      show (1 : ℕ) < 64 by decide, show (33 : ℕ) < 64 by decide, decide_true, Bool.true_and, ha, hb]

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
  have hdt : t.getLsbD 1 ≠ t.getLsbD 33 := by
    rcases ht with rfl | rfl
    · exact goal6_diff
    · intro h
      have hgd := goal6_diff
      simp only [BitVec.getLsbD_not, show (1 : ℕ) < 64 by decide, show (33 : ℕ) < 64 by decide,
        decide_true, Bool.true_and] at h
      cases h1 : goal6.getLsbD 1 <;> cases h2 : goal6.getLsbD 33 <;>
        simp only [h1, h2, Bool.not_true, Bool.not_false] at h hgd <;>
        first | exact Bool.noConfusion h | exact hgd rfl
  obtain ⟨w, hw, hdw⟩ := live_separates (fun u : W6 => u.getLsbD 1 ≠ u.getLsbD 33) hdt ops6_diff hl
  have hw_eq : w = rows6.getD 5 0 := by
    have h1 := List.all_eq_true.mp xv_ess_only w (List.mem_toFinset.mp (hs hw))
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    exact h1.resolve_right hdw
  have hxv_mem : rows6.getD 5 0 ∈ s.filter (fun u => projS 32 idx65 u = 0) :=
    Finset.mem_filter.mpr ⟨hw_eq ▸ hw, projS65_xv⟩
  have hzc_pos : 1 ≤ zCount (projS 32 idx65) s := Finset.one_le_card.mpr ⟨_, hxv_mem⟩
  have hpt : projS 32 idx65 t = c5_0_goal := by
    rcases ht with rfl | rfl
    · exact projS65_goal6
    · rw [projS_not 32 (by decide) idx65 idx65_spec.1 idx65_spec.2]; exact projS65_goal6
  have hb32 := live_restrict (by decide : 0 < 32) idx65 idx65_spec.1 idx65_spec.2
    (fun a b z hz => List.mem_toFinset.mp hz) hpt (by decide : c5_0_goal ≠ 0) hl
  have hsub32 : nonZeroImg (projS 32 idx65) s ⊆ rows5.toFinset := by
    intro u hu
    simp only [nonZeroImg, Finset.mem_erase, Finset.mem_image] at hu
    obtain ⟨hne, v, hv, rfl⟩ := hu
    have h1 := List.all_eq_true.mp projS65_rows6_sub v (List.mem_toFinset.mp (hs hv))
    simp only [Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at h1
    exact List.mem_toFinset.mpr (h1.resolve_left hne)
  exact c5_0_no_build (build_mono_k (by omega) (build_mono_av hsub32 hb32))

def wg : List Gate := [
  ⟨.and, [3, 4]⟩,
  ⟨.or, [3, 5]⟩,
  ⟨.or, [7, 4]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.or, [9, 6]⟩,
  ⟨.and, [1, 2]⟩,
  ⟨.or, [6, 11]⟩,
  ⟨.and, [9, 8]⟩,
  ⟨.or, [10, 5]⟩,
  ⟨.and, [14, 0]⟩,
  ⟨.and, [13, 12]⟩,
  ⟨.or, [15, 16]⟩
]

theorem wfits : Monotone2 ⟨wg, 17⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = F x := by
  decide +kernel

end PEqualNP.Outside.L_meta_41036_aux

open PEqualNP.Outside.L_meta_41036_aux in
theorem PEqualNP.Outside.L_meta_41036 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4276676776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4276676776) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
