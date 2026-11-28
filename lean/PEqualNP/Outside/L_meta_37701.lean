import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37701_aux

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

def goal6 : BitVec 64 := 0xfeeeeeeaeeeaeee0

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

def b4_1_goal : BitVec 16 := 0xfeea
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
def b4_1_idx : Array (List ℕ) := Array.mk [b4_1_s0,b4_1_s1,b4_1_s2,b4_1_s3,b4_1_s4,b4_1_s5]
def b4_1_pow : Array (List ℕ) := Array.mk [b4_1_p0,b4_1_p1,b4_1_p2,b4_1_p3,b4_1_p4,b4_1_p5]
def b4_1_inv : Array ℕ := Array.mk [0,1,2,4,3,5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_G_valid : (List.range 6).all (symValid 16 6 b4_1_idx b4_1_pow b4_1_inv b4_1_goal) = true := by decide +kernel
def b4_1_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xcccc,0xfafa,0xffaa],[])
]
def b4_1_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(2,0)]),
([0x4444,0xaaaa,0xf0f0,0xff00],[])
]
def b4_1_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(1,0),(2,1),(3,1),(4,0)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_2_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 2 b4_1_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_2 : ∀ i < b4_1_L2.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 2 b4_1_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_1_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_1_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_3_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 3 b4_1_L3 b4_1_L2 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_3 : ∀ i < b4_1_L3.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 3 b4_1_L3 b4_1_L2 i = true := by
  intro i hi
  have hsz : b4_1_L3.size = 2 := by decide +kernel
  exact checkBlockP_at b4_1_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_4_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 4 b4_1_L4 b4_1_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_4 : ∀ i < b4_1_L4.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 4 b4_1_L4 b4_1_L3 i = true := by
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

def b4_2_goal : BitVec 16 := 0xe8a8
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
([0xaaaa,0xcc88,0xf0f0],[]),
([0xaaaa,0xcc0c,0xf0f0],[])
]
def b4_2_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(1,0)]),
([0x5500,0xaaaa,0xcccc,0xf0f0],[]),
([0xaaaa,0xcc00,0xcccc,0xf0f0],[]),
([0xcc,0xaaaa,0xcccc,0xf0f0],[(1,1)])
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

def b4_3_goal : BitVec 16 := 0xeac8
def b4_3_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_3_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_3_s1 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_3_p1 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_3_idx : Array (List ℕ) := Array.mk [b4_3_s0,b4_3_s1]
def b4_3_pow : Array (List ℕ) := Array.mk [b4_3_p0,b4_3_p1]
def b4_3_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_G_valid : (List.range 2).all (symValid 16 2 b4_3_idx b4_3_pow b4_3_inv b4_3_goal) = true := by decide +kernel
def b4_3_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_3_chk_3_0 : checkBlockP 16 jumps4 b4_3_goal 2 b4_3_pow 3 b4_3_L3 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_3_chk_3 : ∀ i < b4_3_L3.size, checkNodeP 16 jumps4 b4_3_goal 2 b4_3_pow 3 b4_3_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_3_L3.size = 1 := by decide +kernel
  exact checkBlockP_at b4_3_chk_3_0 i (Nat.zero_le _) (by omega)
theorem b4_3_L3_sound : ∀ i < b4_3_L3.size, ¬ live (basicOps 16) b4_3_goal 3 (b4_3_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_3_G_valid (fun j hj => by simp at hj) b4_3_chk_3
set_option maxRecDepth 100000 in
theorem b4_3_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_3_goal ws) = [rows4] := by decide +kernel
theorem b4_3_top_match : sameSet (rows4.map (actB 16 (b4_3_pow[0]?.getD []))) (b4_3_L3[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_3_no_build : ¬ build (basicOps 16) b4_3_goal 3 rows4.toFinset :=
  no_build_of_top b4_3_G_valid (by decide) b4_3_sublists b4_3_top_match (b4_3_L3_sound 0 (by decide))

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

def u0 : BitVec 32 := 0xcccccccc
def u1 : BitVec 32 := 0xaaaaaaaa
def u2 : BitVec 32 := 0xffff0000
def u3 : BitVec 32 := 0xf0f0f0f0
def u4 : BitVec 32 := 0xff00ff00
def u5 : BitVec 32 := 0xcccc
def u6 : BitVec 32 := 0xc0c0c0c0
def u7 : BitVec 32 := 0x88888888
def u8 : BitVec 32 := 0xaaaa0000
def u9 : BitVec 32 := 0xfcfcfcfc
def u10 : BitVec 32 := 0xaaaa
def u11 : BitVec 32 := 0xeeeeeeee
def u12 : BitVec 32 := 0xffffff00
def u13 : BitVec 32 := 0xff000000
def u14 : BitVec 32 := 0xf0f0000
def u15 : BitVec 32 := 0xc0c0cccc
def u16 : BitVec 32 := 0x44444444
def u17 : BitVec 32 := 0xfafafafa
def u18 : BitVec 32 := 0xfff0fff0
def u19 : BitVec 32 := 0x33330000
def u20 : BitVec 32 := 0xf000f000
def u21 : BitVec 32 := 0xc8c8c8c8
def u22 : BitVec 32 := 0xffffaaaa
def u23 : BitVec 32 := 0xffff00
def u24 : BitVec 32 := 0x55550000
def u25 : BitVec 32 := 0x4444cccc
def u26 : BitVec 32 := 0x5555aaaa
def u27 : BitVec 32 := 0xc0c0c0c
def u28 : BitVec 32 := 0xa0a0a0a0
def u29 : BitVec 32 := 0xa8a8a8a8
def u30 : BitVec 32 := 0xff0000
def u31 : BitVec 32 := 0x30303030
def u32 : BitVec 32 := 0xffff8888
def u33 : BitVec 32 := 0xcccc0000
def u34 : BitVec 32 := 0xffaaff00
def u35 : BitVec 32 := 0xeaeaeaea
def u36 : BitVec 32 := 0xc0c0f0f0
def u37 : BitVec 32 := 0x22222222
def u38 : BitVec 32 := 0xe0e0e0e0
def u39 : BitVec 32 := 0xfffff0f0
def u40 : BitVec 32 := 0xffffa0a0
def u41 : BitVec 32 := 0xf8f8f8f8
def u42 : BitVec 32 := 0xffff00f0
def u43 : BitVec 32 := 0xffff3030
def u44 : BitVec 32 := 0xffaaffaa
def u45 : BitVec 32 := 0x55005500
def u46 : BitVec 32 := 0xc000c000
def u47 : BitVec 32 := 0xfffcfffc
def u48 : BitVec 32 := 0xcc00cc00
def u49 : BitVec 32 := 0xccccfcfc
def u50 : BitVec 32 := 0xff0fff00
def u51 : BitVec 32 := 0xffff00cc
def u52 : BitVec 32 := 0x33003300

def c5_0_goal : BitVec 32 := 0xfeeeeeea
def c5_0_idxs4 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]
set_option maxRecDepth 100000 in
theorem c5_0_no_build : ¬ build (basicOps 32) c5_0_goal 6 rows5.toFinset :=
  no_build5_of_proj4 5 b4_0_goal (by decide) b4_0_no_build c5_0_goal c5_0_idxs4 0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

def c5_1_goal : BitVec 32 := 0xeeeaeae0
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
def c5_1_m0 : BitVec 32 := 0xcccccccc
def c5_1_st0 : List (BitVec 32) := [0x88888888,0xc0c0c0c0,0xcc00cc00,0xcccc0000]
def c5_1_ix0 : List ℕ := [2,6,3,7,10,14,11,15,18,22,19,23,26,30,27,31]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_0 : c5_1_ix0.length = 16 ∧ (∀ idx ∈ c5_1_ix0, idx < 32) ∧ (∀ idx ∈ c5_1_ix0, c5_1_m0.getLsbD idx = true) ∧ projS 16 c5_1_ix0 c5_1_goal = b4_1_goal ∧ c5_1_st0.all (fun w => rows4.contains (projS 16 c5_1_ix0 w)) = true := by decide +kernel
def c5_1_m1 : BitVec 32 := 0xf0f0f0f
def c5_1_st1 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def c5_1_ix1 : List ℕ := [0,1,8,9,16,17,24,25,2,3,10,11,18,19,26,27]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_1 : c5_1_ix1.length = 16 ∧ (∀ idx ∈ c5_1_ix1, idx < 32) ∧ (∀ idx ∈ c5_1_ix1, c5_1_m1.getLsbD idx = true) ∧ projS 16 c5_1_ix1 c5_1_goal = b4_2_goal ∧ c5_1_st1.all (fun w => rows4.contains (projS 16 c5_1_ix1 w)) = true := by decide +kernel
def c5_1_m2 : BitVec 32 := 0xff00ff
def c5_1_st2 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def c5_1_ix2 : List ℕ := [0,1,4,5,2,3,6,7,16,17,20,21,18,19,22,23]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_2 : c5_1_ix2.length = 16 ∧ (∀ idx ∈ c5_1_ix2, idx < 32) ∧ (∀ idx ∈ c5_1_ix2, c5_1_m2.getLsbD idx = true) ∧ projS 16 c5_1_ix2 c5_1_goal = b4_3_goal ∧ c5_1_st2.all (fun w => rows4.contains (projS 16 c5_1_ix2 w)) = true := by decide +kernel
def c5_1_m3 : BitVec 32 := 0xffff
def c5_1_st3 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def c5_1_ix3 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
set_option maxRecDepth 100000 in
theorem c5_1_cspec_3 : c5_1_ix3.length = 16 ∧ (∀ idx ∈ c5_1_ix3, idx < 32) ∧ (∀ idx ∈ c5_1_ix3, c5_1_m3.getLsbD idx = true) ∧ projS 16 c5_1_ix3 c5_1_goal = b4_3_goal ∧ c5_1_st3.all (fun w => rows4.contains (projS 16 c5_1_ix3 w)) = true := by decide +kernel
def c5_1_cfMasks : Array (BitVec 32) := Array.mk [c5_1_m0,c5_1_m1,c5_1_m2,c5_1_m3]
def c5_1_cfB0s : Array ℕ := Array.mk [2,0,0,0]
def c5_1_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_1_st0,c5_1_st1,c5_1_st2,c5_1_st3]
def c5_1_cfLBs : Array ℕ := Array.mk [5,5,4,4]
theorem c5_1_cof_sound (c fuel : ℕ) (hc : c < 4) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_1_cfLBs[c]?.getD 0) fuel (c5_1_cfMasks[c]?.getD 0) (c5_1_cfB0s[c]?.getD 0) (c5_1_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_1_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_1_goal 5 c5_1_ix0 c5_1_cspec_0.1 c5_1_cspec_0.2.1 c5_1_m0 c5_1_cspec_0.2.2.1 2 c5_1_st0 b4_1_goal (by decide) c5_1_cspec_0.2.2.2.1 c5_1_cspec_0.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_1_goal 5 c5_1_ix1 c5_1_cspec_1.1 c5_1_cspec_1.2.1 c5_1_m1 c5_1_cspec_1.2.2.1 0 c5_1_st1 b4_2_goal (by decide) c5_1_cspec_1.2.2.2.1 c5_1_cspec_1.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_1_goal 4 c5_1_ix2 c5_1_cspec_2.1 c5_1_cspec_2.2.1 c5_1_m2 c5_1_cspec_2.2.2.1 0 c5_1_st2 b4_3_goal (by decide) c5_1_cspec_2.2.2.2.1 c5_1_cspec_2.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_1_goal 4 c5_1_ix3 c5_1_cspec_3.1 c5_1_cspec_3.2.1 c5_1_m3 c5_1_cspec_3.2.2.1 0 c5_1_st3 b4_3_goal (by decide) c5_1_cspec_3.2.2.2.1 c5_1_cspec_3.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | c + 4 => omega
def c5_1_L4 : Array W5Node := Array.mk [
([0xffaa,u1,u0,u3,u4],[(u44,u1,u4),(0xffaa,u44,u2)],[],[]),
([u1,0xcc44cc44,u3,u4,u2],[(0xaa00aa,u1,u4),(0xcc44cc44,0xaa00aa,u0)],[],[])
]
def c5_1_L5 : Array W5Node := Array.mk [
([u16,u1,u3,u4,u2],[(u16,u1,u0)],[0,1],[]),
([u1,u0,u3,u4,u44,u2],[(u44,u1,u4)],[2,3],[(0,0)]),
([u10,u1,u0,u3,u4,u2],[(u10,u1,u2)],[0,3],[(1,1)]),
([u1,u0,u3,u4,u2,u12],[(u12,u4,u2)],[2],[])
]
def c5_1_L6 : Array W5Node := Array.mk [
([u1,u0,u3,u4,u2],[],[0,1,2,3],[(0,0),(0,1),(0,2),(0,3),(1,1),(1,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_4_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_4 : ∀ i < c5_1_L4.size, checkNodeW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 4 c5_1_L4 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_1_L4.size = 2 := by decide +kernel
  exact checkBlockW5_at c5_1_chk_4_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_5_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 0 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_5 : ∀ i < c5_1_L5.size, checkNodeW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 5 c5_1_L5 c5_1_L4 i = true := by
  intro i hi
  have hsz : c5_1_L5.size = 4 := by decide +kernel
  exact checkBlockW5_at c5_1_chk_5_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_1_chk_6_0 : checkBlockW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 6 c5_1_L6 c5_1_L5 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_1_chk_6 : ∀ i < c5_1_L6.size, checkNodeW5 c5_1_goal 2 c5_1_pow 4 c5_1_cfLBs c5_1_cfMasks c5_1_cfB0s c5_1_cfStocks 6 c5_1_L6 c5_1_L5 i = true := by
  intro i hi
  have hsz : c5_1_L6.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_1_chk_6_0 i (Nat.zero_le _) (by omega)
theorem c5_1_L4_sound : ∀ i < c5_1_L4.size, ¬ live (basicOps 32) c5_1_goal 4 (c5_1_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound (fun j hj => by simp at hj) c5_1_chk_4
theorem c5_1_L5_sound : ∀ i < c5_1_L5.size, ¬ live (basicOps 32) c5_1_goal 5 (c5_1_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L4_sound c5_1_chk_5
theorem c5_1_L6_sound : ∀ i < c5_1_L6.size, ¬ live (basicOps 32) c5_1_goal 6 (c5_1_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_1_G_valid c5_1_cof_sound c5_1_L5_sound c5_1_chk_6
set_option maxRecDepth 100000 in
theorem c5_1_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_1_goal ws) = [rows5] := by decide +kernel
theorem c5_1_top_match : sameSet (rows5.map (actB 32 (c5_1_pow[0]?.getD []))) (c5_1_L6[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_1_no_build : ¬ build (basicOps 32) c5_1_goal 6 rows5.toFinset :=
  no_build_of_top c5_1_G_valid (by decide) c5_1_sublists c5_1_top_match (c5_1_L6_sound 0 (by decide))

def c5_2_goal : BitVec 32 := 0xeaaaaaa8
def c5_2_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_2_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_2_s1 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
def c5_2_p1 : List ℕ := [1,2,4,8,16,32,64,128,65536,131072,262144,524288,1048576,2097152,4194304,8388608,256,512,1024,2048,4096,8192,16384,32768,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_2_s2 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31]
def c5_2_p2 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768,65536,131072,262144,524288,16777216,33554432,67108864,134217728,1048576,2097152,4194304,8388608,268435456,536870912,1073741824,2147483648]
def c5_2_s3 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31]
def c5_2_p3 : List ℕ := [1,2,4,8,256,512,1024,2048,65536,131072,262144,524288,16777216,33554432,67108864,134217728,16,32,64,128,4096,8192,16384,32768,1048576,2097152,4194304,8388608,268435456,536870912,1073741824,2147483648]
def c5_2_s4 : List ℕ := [0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,8,9,10,11,24,25,26,27,12,13,14,15,28,29,30,31]
def c5_2_p4 : List ℕ := [1,2,4,8,65536,131072,262144,524288,16,32,64,128,1048576,2097152,4194304,8388608,256,512,1024,2048,16777216,33554432,67108864,134217728,4096,8192,16384,32768,268435456,536870912,1073741824,2147483648]
def c5_2_s5 : List ℕ := [0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,4,5,6,7,20,21,22,23,12,13,14,15,28,29,30,31]
def c5_2_p5 : List ℕ := [1,2,4,8,65536,131072,262144,524288,256,512,1024,2048,16777216,33554432,67108864,134217728,16,32,64,128,1048576,2097152,4194304,8388608,4096,8192,16384,32768,268435456,536870912,1073741824,2147483648]
def c5_2_s6 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15,16,17,20,21,18,19,22,23,24,25,28,29,26,27,30,31]
def c5_2_p6 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768,65536,131072,1048576,2097152,262144,524288,4194304,8388608,16777216,33554432,268435456,536870912,67108864,134217728,1073741824,2147483648]
def c5_2_s7 : List ℕ := [0,1,4,5,2,3,6,7,16,17,20,21,18,19,22,23,8,9,12,13,10,11,14,15,24,25,28,29,26,27,30,31]
def c5_2_p7 : List ℕ := [1,2,16,32,4,8,64,128,65536,131072,1048576,2097152,262144,524288,4194304,8388608,256,512,4096,8192,1024,2048,16384,32768,16777216,33554432,268435456,536870912,67108864,134217728,1073741824,2147483648]
def c5_2_s8 : List ℕ := [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15,16,17,20,21,24,25,28,29,18,19,22,23,26,27,30,31]
def c5_2_p8 : List ℕ := [1,2,16,32,256,512,4096,8192,4,8,64,128,1024,2048,16384,32768,65536,131072,1048576,2097152,16777216,33554432,268435456,536870912,262144,524288,4194304,8388608,67108864,134217728,1073741824,2147483648]
def c5_2_s9 : List ℕ := [0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31]
def c5_2_p9 : List ℕ := [1,2,16,32,256,512,4096,8192,65536,131072,1048576,2097152,16777216,33554432,268435456,536870912,4,8,64,128,1024,2048,16384,32768,262144,524288,4194304,8388608,67108864,134217728,1073741824,2147483648]
def c5_2_s10 : List ℕ := [0,1,4,5,16,17,20,21,2,3,6,7,18,19,22,23,8,9,12,13,24,25,28,29,10,11,14,15,26,27,30,31]
def c5_2_p10 : List ℕ := [1,2,16,32,65536,131072,1048576,2097152,4,8,64,128,262144,524288,4194304,8388608,256,512,4096,8192,16777216,33554432,268435456,536870912,1024,2048,16384,32768,67108864,134217728,1073741824,2147483648]
def c5_2_s11 : List ℕ := [0,1,4,5,16,17,20,21,8,9,12,13,24,25,28,29,2,3,6,7,18,19,22,23,10,11,14,15,26,27,30,31]
def c5_2_p11 : List ℕ := [1,2,16,32,65536,131072,1048576,2097152,256,512,4096,8192,16777216,33554432,268435456,536870912,4,8,64,128,262144,524288,4194304,8388608,1024,2048,16384,32768,67108864,134217728,1073741824,2147483648]
def c5_2_s12 : List ℕ := [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15,16,17,24,25,18,19,26,27,20,21,28,29,22,23,30,31]
def c5_2_p12 : List ℕ := [1,2,256,512,4,8,1024,2048,16,32,4096,8192,64,128,16384,32768,65536,131072,16777216,33554432,262144,524288,67108864,134217728,1048576,2097152,268435456,536870912,4194304,8388608,1073741824,2147483648]
def c5_2_s13 : List ℕ := [0,1,8,9,2,3,10,11,16,17,24,25,18,19,26,27,4,5,12,13,6,7,14,15,20,21,28,29,22,23,30,31]
def c5_2_p13 : List ℕ := [1,2,256,512,4,8,1024,2048,65536,131072,16777216,33554432,262144,524288,67108864,134217728,16,32,4096,8192,64,128,16384,32768,1048576,2097152,268435456,536870912,4194304,8388608,1073741824,2147483648]
def c5_2_s14 : List ℕ := [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15,16,17,24,25,20,21,28,29,18,19,26,27,22,23,30,31]
def c5_2_p14 : List ℕ := [1,2,256,512,16,32,4096,8192,4,8,1024,2048,64,128,16384,32768,65536,131072,16777216,33554432,1048576,2097152,268435456,536870912,262144,524288,67108864,134217728,4194304,8388608,1073741824,2147483648]
def c5_2_s15 : List ℕ := [0,1,8,9,4,5,12,13,16,17,24,25,20,21,28,29,2,3,10,11,6,7,14,15,18,19,26,27,22,23,30,31]
def c5_2_p15 : List ℕ := [1,2,256,512,16,32,4096,8192,65536,131072,16777216,33554432,1048576,2097152,268435456,536870912,4,8,1024,2048,64,128,16384,32768,262144,524288,67108864,134217728,4194304,8388608,1073741824,2147483648]
def c5_2_s16 : List ℕ := [0,1,8,9,16,17,24,25,2,3,10,11,18,19,26,27,4,5,12,13,20,21,28,29,6,7,14,15,22,23,30,31]
def c5_2_p16 : List ℕ := [1,2,256,512,65536,131072,16777216,33554432,4,8,1024,2048,262144,524288,67108864,134217728,16,32,4096,8192,1048576,2097152,268435456,536870912,64,128,16384,32768,4194304,8388608,1073741824,2147483648]
def c5_2_s17 : List ℕ := [0,1,8,9,16,17,24,25,4,5,12,13,20,21,28,29,2,3,10,11,18,19,26,27,6,7,14,15,22,23,30,31]
def c5_2_p17 : List ℕ := [1,2,256,512,65536,131072,16777216,33554432,16,32,4096,8192,1048576,2097152,268435456,536870912,4,8,1024,2048,262144,524288,67108864,134217728,64,128,16384,32768,4194304,8388608,1073741824,2147483648]
def c5_2_s18 : List ℕ := [0,1,16,17,2,3,18,19,4,5,20,21,6,7,22,23,8,9,24,25,10,11,26,27,12,13,28,29,14,15,30,31]
def c5_2_p18 : List ℕ := [1,2,65536,131072,4,8,262144,524288,16,32,1048576,2097152,64,128,4194304,8388608,256,512,16777216,33554432,1024,2048,67108864,134217728,4096,8192,268435456,536870912,16384,32768,1073741824,2147483648]
def c5_2_s19 : List ℕ := [0,1,16,17,2,3,18,19,8,9,24,25,10,11,26,27,4,5,20,21,6,7,22,23,12,13,28,29,14,15,30,31]
def c5_2_p19 : List ℕ := [1,2,65536,131072,4,8,262144,524288,256,512,16777216,33554432,1024,2048,67108864,134217728,16,32,1048576,2097152,64,128,4194304,8388608,4096,8192,268435456,536870912,16384,32768,1073741824,2147483648]
def c5_2_s20 : List ℕ := [0,1,16,17,4,5,20,21,2,3,18,19,6,7,22,23,8,9,24,25,12,13,28,29,10,11,26,27,14,15,30,31]
def c5_2_p20 : List ℕ := [1,2,65536,131072,16,32,1048576,2097152,4,8,262144,524288,64,128,4194304,8388608,256,512,16777216,33554432,4096,8192,268435456,536870912,1024,2048,67108864,134217728,16384,32768,1073741824,2147483648]
def c5_2_s21 : List ℕ := [0,1,16,17,4,5,20,21,8,9,24,25,12,13,28,29,2,3,18,19,6,7,22,23,10,11,26,27,14,15,30,31]
def c5_2_p21 : List ℕ := [1,2,65536,131072,16,32,1048576,2097152,256,512,16777216,33554432,4096,8192,268435456,536870912,4,8,262144,524288,64,128,4194304,8388608,1024,2048,67108864,134217728,16384,32768,1073741824,2147483648]
def c5_2_s22 : List ℕ := [0,1,16,17,8,9,24,25,2,3,18,19,10,11,26,27,4,5,20,21,12,13,28,29,6,7,22,23,14,15,30,31]
def c5_2_p22 : List ℕ := [1,2,65536,131072,256,512,16777216,33554432,4,8,262144,524288,1024,2048,67108864,134217728,16,32,1048576,2097152,4096,8192,268435456,536870912,64,128,4194304,8388608,16384,32768,1073741824,2147483648]
def c5_2_s23 : List ℕ := [0,1,16,17,8,9,24,25,4,5,20,21,12,13,28,29,2,3,18,19,10,11,26,27,6,7,22,23,14,15,30,31]
def c5_2_p23 : List ℕ := [1,2,65536,131072,256,512,16777216,33554432,16,32,1048576,2097152,4096,8192,268435456,536870912,4,8,262144,524288,1024,2048,67108864,134217728,64,128,4194304,8388608,16384,32768,1073741824,2147483648]
def c5_2_idx : Array (List ℕ) := Array.mk [c5_2_s0,c5_2_s1,c5_2_s2,c5_2_s3,c5_2_s4,c5_2_s5,c5_2_s6,c5_2_s7,c5_2_s8,c5_2_s9,c5_2_s10,c5_2_s11,c5_2_s12,c5_2_s13,c5_2_s14,c5_2_s15,c5_2_s16,c5_2_s17,c5_2_s18,c5_2_s19,c5_2_s20,c5_2_s21,c5_2_s22,c5_2_s23]
def c5_2_pow : Array (List ℕ) := Array.mk [c5_2_p0,c5_2_p1,c5_2_p2,c5_2_p3,c5_2_p4,c5_2_p5,c5_2_p6,c5_2_p7,c5_2_p8,c5_2_p9,c5_2_p10,c5_2_p11,c5_2_p12,c5_2_p13,c5_2_p14,c5_2_p15,c5_2_p16,c5_2_p17,c5_2_p18,c5_2_p19,c5_2_p20,c5_2_p21,c5_2_p22,c5_2_p23]
def c5_2_inv : Array ℕ := Array.mk [0,1,2,4,3,5,6,7,12,18,13,19,8,10,14,20,16,22,9,11,15,21,17,23]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_G_valid : (List.range 24).all (symValid 32 24 c5_2_idx c5_2_pow c5_2_inv c5_2_goal) = true := by decide +kernel
def c5_2_cfMasks : Array (BitVec 32) := Array.mk []
def c5_2_cfB0s : Array ℕ := Array.mk []
def c5_2_cfStocks : Array (List (BitVec 32)) := Array.mk []
def c5_2_cfLBs : Array ℕ := Array.mk []
theorem c5_2_cof_sound (c fuel : ℕ) (hc : c < 0) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_2_cfLBs[c]?.getD 0) fuel (c5_2_cfMasks[c]?.getD 0) (c5_2_cfB0s[c]?.getD 0) (c5_2_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_2_goal fuel nxt.toFinset := by
  omega
def c5_2_L2 : Array W5Node := Array.mk [
([0xffffff0,u1,u0],[(u13,u4,u2),(0xf0000000,u13,u3),(u12,u4,u2),(0xfffffff0,u3,u12),(0xffffff0,0xf0000000,0xfffffff0)],[],[]),
([u1,0xc00cc00c,0xffff0ff0],[(u20,u3,u4),(u18,u3,u4),(0xff00ff0,u20,u18),(0xffff0ff0,0xff00ff0,u2),(0xc00cc00c,0xff00ff0,u0)],[],[])
]
def c5_2_L3 : Array W5Node := Array.mk [
([u26,u0,u3,u4],[(u8,u1,u2),(u10,u8,u1),(u24,u8,u2),(u26,u10,u24)],[],[]),
([u1,u21,u4,u40],[(u28,u1,u3),(u40,u28,u2),(u17,u1,u3),(u21,u0,u17)],[],[]),
([u1,u0,u3,0xffaaaa00],[(u8,u1,u2),(u34,u8,u4),(u22,u1,u2),(0xffaaaa00,u34,u22)],[],[]),
([u1,u15,0xffa0ffa0,u2],[(u28,u1,u3),(0xffa0ffa0,u28,u4),(u14,u3,u2),(u15,u14,u0)],[],[]),
([u1,0xc8c8f8f8,u4,u2],[(u7,u1,u0),(u41,u7,u3),(u19,u0,u2),(0xc8c8f8f8,u19,u41)],[],[]),
([u1,u15,u4,u40],[(u28,u1,u3),(u40,u28,u2),(u14,u3,u40),(u15,u14,u0)],[],[]),
([u25,u26,u3,u4],[(u8,u1,u2),(u25,u8,u0),(u22,u1,u2),(u26,u8,u22)],[],[]),
([u1,u21,u4,u42],[(u17,u1,u3),(0xf000f0,u3,u4),(u42,0xf000f0,u2),(u21,u0,u17)],[],[]),
([u1,u21,u4,u43],[(u17,u1,u3),(u31,u3,u0),(u43,u31,u2),(u21,u0,u17)],[],[]),
([u1,0xc2c2c2c2,u4,u2],[(0xa0a0a0a,u1,u3),(0xcececece,0xa0a0a0a,u0),(u27,u0,u3),(0xc2c2c2c2,u27,0xcececece)],[],[]),
([0x44448888,u26,u3,u4],[(u10,u1,u2),(u24,u1,u2),(u26,u10,u24),(0x44448888,u26,u0)],[],[]),
([0x55aa,0x55aa55aa,u0,u3],[(0xaa00aa,u1,u4),(u45,u1,u4),(0x55aa55aa,0xaa00aa,u45),(0x55aa,0x55aa55aa,u2)],[],[]),
([u1,0xaaffff00,u0,u3],[(u45,u1,u4),(0x55000000,u45,u2),(u12,u4,u2),(0xaaffff00,0x55000000,u12)],[],[]),
([u29,u35,u4,u2],[(u6,u0,u3),(u35,u1,u6),(u9,u0,u3),(u29,u1,u9)],[],[]),
([u1,0xc888c888,u18,u2],[(u20,u3,u4),(0xfaaafaaa,u1,u20),(u18,u3,u4),(0xc888c888,u0,0xfaaafaaa)],[],[]),
([u23,u1,u0,u3],[(u13,u4,u2),(0xff00,u13,u4),(u12,0xff00,u2),(u23,u13,u12)],[],[]),
([0xff0fff0,u1,u0,u2],[(u20,u3,u4),(0xf0000000,u20,u2),(u18,u3,u4),(0xff0fff0,0xf0000000,u18)],[],[]),
([u1,u46,u47,u2],[(u20,u3,u4),(u46,u20,u0),(u18,u3,u4),(u47,u0,u18)],[],[(9,0)]),
([u1,0xc000cccc,u18,u2],[(u20,u3,u4),(0xfff0000,u20,u2),(0xc000cccc,0xfff0000,u0),(u18,u3,u4)],[],[]),
([u1,0xc0c0fcfc,u4,u2],[(u6,u0,u3),(0x3f3f0000,u6,u2),(u9,u0,u3),(0xc0c0fcfc,0x3f3f0000,u9)],[],[]),
([0xfcfc,0x3f3f0000,u1,u4],[(u6,u0,u3),(0x3f3f0000,u6,u2),(u9,u0,u3),(0xfcfc,u2,u9)],[],[(8,0)]),
([u1,u6,u4,0xffffa8a8],[(u6,u0,u3),(u9,u0,u3),(u29,u1,u9),(0xffffa8a8,u29,u2)],[],[]),
([u23,u1,u0,0xf0fffff0],[(u13,u4,u2),(u12,u4,u2),(u23,u13,u12),(0xf0fffff0,u23,u3)],[],[(4,1)]),
([u23,u1,0xcc0000cc,u3],[(u13,u4,u2),(u12,u4,u2),(u23,u13,u12),(0xcc0000cc,u23,u0)],[],[(4,1)]),
([u1,u6,u4,0xffff3c3c],[(u6,u0,u3),(u9,u0,u3),(0x3c3c3c3c,u6,u9),(0xffff3c3c,0x3c3c3c3c,u2)],[],[]),
([u1,0xc00cc00c,u18,u2],[(u20,u3,u4),(u18,u3,u4),(0xff00ff0,u20,u18),(0xc00cc00c,0xff00ff0,u0)],[],[]),
([0xffffcc,u1,u0,u3],[(u13,u4,u2),(u12,u4,u2),(0xffffffcc,u12,u0),(0xffffcc,u13,0xffffffcc)],[],[]),
([u1,u6,u4,0xffff00fc],[(u6,u0,u3),(u9,u0,u3),(0xfc00fc,u9,u4),(0xffff00fc,0xfc00fc,u2)],[],[]),
([u5,0x33ff3300,u1,u3],[(u48,u4,u0),(u12,u4,u2),(0x33ff3300,u48,u12),(u5,u2,u0)],[],[(6,0)]),
([u1,u15,0xff30ff30,u2],[(u31,u3,u0),(0xff30ff30,u31,u4),(u14,u3,u2),(u15,u14,u0)],[],[]),
([u1,0xc0ccf0fc,u4,u2],[(0xf0f0,u3,u2),(u49,0xf0f0,u0),(0xf000f00,u3,u4),(0xc0ccf0fc,0xf000f00,u49)],[],[]),
([u1,u15,0xff00fff0,u2],[(0xf0f0,u3,u2),(0xff00fff0,0xf0f0,u4),(u14,u3,u2),(u15,u14,u0)],[],[]),
([u1,u15,u4,u42],[(0xf000f0,u3,u4),(u42,0xf000f0,u2),(u14,u3,u42),(u15,u14,u0)],[],[]),
([u1,u15,u4,u43],[(u31,u3,u0),(u43,u31,u2),(u14,u3,u43),(u15,u14,u0)],[],[]),
([u5,u1,u36,0xff33ff00],[(u19,u2,u0),(0xff33ff00,u19,u4),(u36,u19,u3),(u5,u0,u2)],[],[]),
([u23,u1,u0,0xf0f0fff0],[(0xff00,u4,u2),(0xf0f0fff0,0xff00,u3),(u30,u4,u2),(u23,0xff00,u30)],[],[]),
([u23,u1,0xcc00cccc,u3],[(u30,u2,u4),(0xcc00cccc,u30,u0),(0xff00,u2,u4),(u23,0xff00,u30)],[],[])
]
def c5_2_L4 : Array W5Node := Array.mk [
([u1,u0,u3,u4,u2],[(u8,u1,u2),(u10,u8,u1),(u1,u10,u8)],[],[]),
([u7,u11,u3,u4,u2],[(u7,u1,u0),(u37,u7,u1),(u11,u37,u0)],[],[]),
([u10,u24,u0,u3,u4],[(u8,u1,u2),(u10,u8,u1),(u24,u8,u2)],[],[(0,0)]),
([u16,u1,u3,u4,u32],[(u7,u1,u0),(u16,u7,u0),(u32,u7,u2)],[],[]),
([u25,u1,u3,u4,u2],[(u7,u1,u0),(0x88880000,u7,u2),(u25,0x88880000,u0)],[],[]),
([u1,u0,u3,u4,0xffff8080],[(u7,u1,u0),(0x80808080,u7,u3),(0xffff8080,0x80808080,u2)],[],[]),
([0x44cccccc,u1,u3,u4,u2],[(0xaa00aa00,u1,u4),(0xaa000000,0xaa00aa00,u2),(0x44cccccc,0xaa000000,u0)],[],[]),
([u1,u0,u3,u34,u22],[(u8,u1,u2),(u34,u8,u4),(u22,u1,u2)],[],[(0,2),(3,1),(13,1)]),
([u1,u6,u0,u4,u40],[(u28,u1,u3),(u40,u28,u2),(u6,u3,u0)],[],[]),
([u5,u1,u0,u3,u34],[(u8,u1,u2),(u34,u8,u4),(u5,u2,u0)],[],[(19,3),(23,4)]),
([u1,u21,u41,u4,u2],[(u7,u1,u0),(u41,u7,u3),(u21,u0,u41)],[],[]),
([u5,u1,0xeeeecccc,u3,u4],[(u8,u1,u2),(0xeeeecccc,u8,u0),(u5,u2,0xeeeecccc)],[],[(19,5),(22,5)]),
([u1,u0,u3,0xff88ff88,u32],[(u7,u1,u0),(u32,u7,u2),(0xff88ff88,u7,u4)],[],[]),
([u25,u1,u3,u34,u2],[(u8,u1,u2),(u34,u8,u4),(u25,u8,u0)],[],[]),
([u1,u6,0xecececec,u4,u2],[(u28,u1,u3),(0xecececec,u28,u0),(u6,u0,u3)],[],[]),
([u1,u21,u3,u4,u2],[(u7,u1,u0),(u41,u7,u3),(u21,u41,u0)],[],[]),
([u1,u0,u3,u4,0xffff0088],[(u7,u1,u0),(0x880088,u7,u4),(0xffff0088,0x880088,u2)],[],[]),
([u1,0xc4c4cccc,u3,u4,u2],[(u8,u1,u2),(0xa0a0000,u8,u3),(0xc4c4cccc,0xa0a0000,u0)],[],[]),
([u1,u0,u3,u4,u32],[(u7,u1,u0),(0x8888,u7,u2),(u32,0x8888,u2)],[],[]),
([u25,0x5050f0f0,u1,u4,u2],[(u8,u1,u2),(u25,u8,u0),(0x5050f0f0,u8,u3)],[],[]),
([u25,u8,u3,u4,u22],[(u8,u1,u2),(u25,u8,u0),(u22,u1,u2)],[],[(0,6)]),
([u26,u1,u0,u3,u4],[(u8,u1,u2),(u22,u1,u2),(u26,u8,u22)],[],[]),
([u7,u1,u38,u4,u2],[(u7,u1,u0),(u11,u1,u0),(u38,u11,u3)],[],[(6,1),(7,1),(16,2)]),
([u26,u0,u3,u4,u2],[(u8,u1,u2),(u22,u1,u2),(u26,u8,u22)],[],[]),
([u1,0xaaaacccc,u0,u3,u4],[(u8,u1,u2),(u5,u2,u0),(0xaaaacccc,u5,u8)],[],[]),
([u7,u1,u36,u4,u2],[(u7,u1,u0),(u19,u0,u2),(u36,u19,u3)],[],[(0,4),(6,3),(6,5)]),
([u10,u1,0xcccc8888,u3,u4],[(u22,u1,u2),(u10,u1,u2),(0xcccc8888,u0,u22)],[],[]),
([u29,u0,u17,u4,u2],[(u17,u1,u3),(u9,u3,u0),(u29,u1,u9)],[],[]),
([u1,u21,u9,u4,u2],[(u17,u1,u3),(u9,u3,u0),(u21,u0,u17)],[],[]),
([u1,u21,u4,u18,u2],[(u17,u1,u3),(u18,u3,u4),(u21,u0,u17)],[],[]),
([u1,0xcacacaca,u0,u4,u2],[(u17,u1,u3),(u31,u3,u0),(0xcacacaca,u31,u17)],[],[]),
([u1,u0,u3,u50,u22],[(u22,u1,u2),(u14,u2,u3),(u50,u14,u4)],[],[(3,7),(13,8),(16,4)]),
([u5,u1,u38,u4,u2],[(u11,u1,u0),(u5,u0,u2),(u38,u11,u3)],[],[(6,4),(7,7)]),
([u5,u1,0xeeee0000,u3,u4],[(u11,u1,u0),(u5,u0,u2),(0xeeee0000,u11,u2)],[],[(9,8),(11,8)]),
([u7,u38,u11,u4,u2],[(u11,u1,u0),(u38,u11,u3),(u7,u1,u0)],[],[]),
([0xeeee,u1,u0,u3,u4],[(u11,u1,u0),(0xeeee0000,u11,u2),(0xeeee,0xeeee0000,u11)],[],[]),
([u1,u21,u3,0xfa00fa00,u2],[(u17,u1,u3),(u21,u17,u0),(0xfa00fa00,u17,u4)],[],[]),
([0xeeee,u1,u0,u38,u4],[(u11,u1,u0),(u38,u11,u3),(0xeeee,u11,u2)],[],[]),
([u1,0xccc8ccc8,u3,u4,u2],[(u17,u1,u3),(0xfffafffa,u17,u4),(0xccc8ccc8,0xfffafffa,u0)],[],[]),
([0xfefe,u1,u0,u3,u4],[(u11,u1,u0),(0xfefefefe,u11,u3),(0xfefe,0xfefefefe,u2)],[],[]),
([0xeeee,0xee00ee,u1,u0,u3],[(u11,u1,u0),(0xeeee,u11,u2),(0xee00ee,u11,u4)],[],[]),
([u1,u0,u3,u4,0xffff0044],[(u44,u1,u4),(0x440044,u44,u0),(0xffff0044,0x440044,u2)],[],[]),
([u1,0xc8c8cccc,u3,u4,u2],[(u17,u1,u3),(0x5050000,u17,u2),(0xc8c8cccc,0x5050000,u0)],[],[]),
([u5,u1,0xcccceeee,u3,u4],[(u10,u1,u2),(0xcccceeee,u10,u0),(u5,u0,u2)],[],[(3,9)]),
([u1,0xc0c0c8c8,u3,u4,u2],[(u10,u1,u2),(0xf0f0fafa,u10,u3),(0xc0c0c8c8,0xf0f0fafa,u0)],[],[]),
([0xccee,u1,u0,u3,u4],[(0xaa00aa,u1,u4),(0xcceeccee,0xaa00aa,u0),(0xccee,0xcceeccee,u2)],[],[]),
([0xaa,u1,u0,u3,u13],[(u10,u1,u2),(0xaa,u10,u4),(u13,u4,u2)],[],[(16,9)]),
([u26,u0,u3,u4],[(u10,u1,u2),(u24,u1,u2),(u26,u10,u24)],[],[(0,10),(1,11),(4,11),(6,10),(8,10),(18,11)]),
([u10,u26,u0,u3,u4],[(u10,u1,u2),(u24,u1,u2),(u26,u10,u24)],[],[]),
([u16,0x66666666,u3,u4,u2],[(u37,u1,u0),(u16,u1,u0),(0x66666666,u37,u16)],[],[]),
([u10,0xaaaaeeee,u0,u3,u4],[(u10,u1,u2),(u5,u0,u2),(0xaaaaeeee,u5,u1)],[],[]),
([u10,u1,0xcccc00cc,u3,u4],[(u10,u1,u2),(0xff00,u4,u2),(0xcccc00cc,0xff00,u0)],[],[]),
([0x40404040,u1,u9,u4,u2],[(u16,u1,u0),(0x40404040,u16,u3),(u9,u0,u3)],[],[(16,12)]),
([u1,u0,u3,u4,0xffff88cc],[(u45,u1,u4),(0x88cc88cc,u45,u0),(0xffff88cc,0x88cc88cc,u2)],[],[]),
([0x4040cccc,u1,u3,u4,u2],[(0x50505050,u1,u3),(0xafaf0000,0x50505050,u2),(0x4040cccc,0xafaf0000,u0)],[],[]),
([u5,u1,0xbbbb0000,u3,u4],[(u16,u1,u0),(0xbbbb0000,u16,u2),(u5,u2,u0)],[],[(12,12)]),
([u16,0xa2a2a2a2,u3,u4,u2],[(u16,u1,u0),(u27,u0,u3),(0xa2a2a2a2,u27,u1)],[],[]),
([u16,u1,u3,u4,u51],[(u16,u1,u0),(0xcc00cc,u0,u4),(u51,0xcc00cc,u2)],[],[]),
([u7,u35,u3,u4,u2],[(u6,u3,u0),(u35,u1,u6),(u7,u1,u0)],[],[]),
([u1,u0,u3,0xffaaaaaa,u12],[(u13,u4,u2),(0xffaaaaaa,u1,u13),(u12,u4,u2)],[],[(0,2),(4,14),(16,13),(18,14)]),
([u1,0xc888c888,u3,u4,u2],[(u20,u3,u4),(0xfaaafaaa,u1,u20),(0xc888c888,0xfaaafaaa,u0)],[],[(0,14)]),
([0xeaea,u1,u0,u3,u4],[(u6,u0,u3),(u35,u1,u6),(0xeaea,u35,u2)],[],[]),
([u1,u6,u0,u4,u43],[(u6,u3,u0),(u31,u6,u3),(u43,u31,u2)],[],[]),
([u1,u6,u9,u4,u2],[(u6,u0,u3),(u27,u6,u0),(u9,u27,u3)],[],[(16,15)]),
([u5,u19,u1,u3,u4],[(u33,u0,u2),(u5,u33,u0),(u19,u33,u2)],[],[(12,15)]),
([u1,u0,u3,u4,u51],[(u48,u0,u4),(0xcc00cc,u48,u0),(u51,0xcc00cc,u2)],[],[]),
([u1,u15,u3,u4,u2],[(0xf0f00000,u2,u3),(u14,0xf0f00000,u2),(u15,u14,u0)],[],[]),
([u1,u46,u0,u18,u2],[(u20,u3,u4),(u46,u20,u0),(u18,u3,u4)],[],[(0,17),(21,16)]),
([u1,u0,u3,u4,0xffff00c0],[(u6,u0,u3),(0xc000c0,u6,u4),(0xffff00c0,0xc000c0,u2)],[],[]),
([u1,0xc0cccccc,u3,u4,u2],[(u13,u4,u2),(0xf000000,u13,u3),(0xc0cccccc,0xf000000,u0)],[],[]),
([u1,u0,u3,u4,0xffff0ccc],[(u20,u3,u4),(0xccc0ccc,u20,u0),(0xffff0ccc,0xccc0ccc,u2)],[],[]),
([u1,0xc000cccc,u3,u4,u2],[(u20,u3,u4),(0xfff0000,u20,u2),(0xc000cccc,0xfff0000,u0)],[],[(0,18)]),
([u5,0x33ff0000,u1,u3,u4],[(u48,u0,u4),(0x33ff0000,u48,u2),(u5,u2,u0)],[],[(7,16)]),
([0xcccccc,u1,u0,u3,u12],[(u13,u4,u2),(0xcccccc,u13,u0),(u12,u4,u2)],[],[(18,18),(22,19),(22,20)]),
([u29,u1,u6,u4,u2],[(u6,u0,u3),(u9,u0,u3),(u29,u1,u9)],[],[(0,13),(0,21),(1,21),(16,2)]),
([u23,u1,u0,u3],[(u13,u4,u2),(u12,u4,u2),(u23,u13,u12)],[],[(0,22),(0,23),(6,22),(6,23)]),
([u23,u1,u0,u3,u13],[(u13,u4,u2),(u12,u4,u2),(u23,u13,u12)],[],[(16,24),(22,24)]),
([u23,u1,u0,u3,u12],[(u13,u4,u2),(u12,u4,u2),(u23,u13,u12)],[],[(4,25),(18,25)]),
([u1,u6,u4,u47,u2],[(u6,u0,u3),(u9,u0,u3),(u47,u9,u4)],[],[(0,17),(16,26)]),
([0xfcfc,u1,u6,u4,u2],[(u6,u0,u3),(u9,u0,u3),(0xfcfc,u9,u2)],[],[(0,19),(0,20),(1,27)]),
([u23,u1,u0,u3,u4],[(u13,u4,u2),(u12,u4,u2),(u23,u13,u12)],[],[]),
([0xccffcc,u1,u0,u3,u2],[(u13,u4,u2),(0xffccffcc,u4,u0),(0xccffcc,u13,0xffccffcc)],[],[(21,28)]),
([u5,u1,u6,u4,u39],[(u6,u3,u0),(u39,u3,u2),(u5,u0,u2)],[],[(2,28)]),
([u1,u6,u49,u4,u2],[(u6,u3,u0),(0xf0f0,u3,u2),(u49,0xf0f0,u0)],[],[]),
([u1,u6,u0,u4,u42],[(u6,u3,u0),(0xf000f0,u3,u4),(u42,0xf000f0,u2)],[],[]),
([u1,u0,u3,u4,0xffffa8a8],[(u9,u0,u3),(u29,u1,u9),(0xffffa8a8,u29,u2)],[],[(0,21)]),
([0x444444cc,u1,u3,u4,u2],[(u12,u4,u2),(0xaaaaaa00,u1,u12),(0x444444cc,0xaaaaaa00,u0)],[],[]),
([u1,u15,u4,u2,u39],[(u39,u2,u3),(u14,u2,u3),(u15,u14,u0)],[],[]),
([u1,u15,u9,u4,u2],[(u9,u3,u0),(u14,u3,u2),(u15,u14,u0)],[],[]),
([u1,u15,u4,u18,u2],[(u18,u3,u4),(u14,u3,u2),(u15,u14,u0)],[],[]),
([u5,0x33333030,u1,u3,u4],[(u39,u2,u3),(u5,u2,u0),(0x33333030,u0,u39)],[],[(12,26)]),
([u1,u0,u3,u4,0xffff00fc],[(u9,u0,u3),(0xfc00fc,u9,u4),(0xffff00fc,0xfc00fc,u2)],[],[(0,27)]),
([u1,0xc0c0c0cc,u3,u4,u2],[(u12,u4,u2),(0xf0f0f00,u12,u3),(0xc0c0c0cc,0xf0f0f00,u0)],[],[]),
([u1,u0,u3,u4,0xffff000c],[(u18,u3,u4),(0xc000c,u18,u0),(0xffff000c,0xc000c,u2)],[],[]),
([u1,0xccc0cccc,u3,u4,u2],[(u18,u3,u4),(0xf0000,u18,u2),(0xccc0cccc,0xf0000,u0)],[],[]),
([u5,u1,u0,u3,u50],[(u14,u2,u3),(u50,u14,u4),(u5,u2,u0)],[],[(16,30),(19,29)]),
([u5,u1,u0,u3,0xff33ff00],[(u19,u2,u0),(0xff33ff00,u19,u4),(u5,u2,u0)],[],[(19,31),(22,19)]),
([u1,u15,0xf0f0fcfc,u4,u2],[(u5,u0,u2),(0xf0f0fcfc,u5,u3),(u15,u0,0xf0f0fcfc)],[],[]),
([u5,u1,0xccffcccc,u3,u4],[(u30,u2,u4),(0xccffcccc,u30,u0),(u5,u2,0xccffcccc)],[],[(19,32),(22,33)]),
([u1,u0,u3,0xff0cff0c,0xffff0c0c],[(u27,u0,u3),(0xffff0c0c,u27,u2),(0xff0cff0c,u27,u4)],[],[]),
([u1,u15,u3,u50,u2],[(u14,u2,u3),(u50,u14,u4),(u15,u14,u0)],[],[(6,34)]),
([u5,u19,u1,u3,0xff00ffcc],[(u5,u0,u2),(0xff00ffcc,u5,u4),(u19,u0,u2)],[],[(12,35),(21,34)]),
([u5,u1,0xccff0000,u3,u4],[(u52,u4,u0),(0xccff0000,u52,u2),(u5,0xccff0000,u0)],[],[(9,29),(9,33)]),
([u5,u1,0xc0f0c0f0,u4,u2],[(u52,u4,u0),(0xc0f0c0f0,u52,u3),(u5,u0,u2)],[],[(1,30),(7,32)]),
([u5,u1,u36,u4,u2],[(u19,u2,u0),(u36,u19,u3),(u5,u0,u2)],[],[(0,19),(6,31)]),
([u1,u15,0xf000ff00,u3,u2],[(u14,u2,u3),(u15,u14,u0),(0xf000ff00,u14,u4)],[],[]),
([u5,u19,u1,u36,u4],[(u19,u2,u0),(u36,u19,u3),(u5,u2,u0)],[],[(0,34),(12,36)]),
([u5,u30,u52,u1,u3],[(u30,u2,u4),(u5,u2,u0),(u52,u0,u4)],[],[(0,28),(15,28),(20,28)]),
([u5,0x3333cccc,u1,u3,u4],[(u5,u0,u2),(u19,u0,u2),(0x3333cccc,u5,u19)],[],[(12,35),(14,35),(18,36),(20,36)])
]
def c5_2_L5 : Array W5Node := Array.mk [
([u10,u8,u0,u3,u4,u2],[(u8,u1,u2),(u10,u8,u1)],[],[(0,0),(0,2),(9,1)]),
([u10,u1,u0,u3,u4,u2],[(u8,u1,u2),(u10,u8,u1)],[],[(0,2)]),
([u16,u7,u1,u3,u4,u2],[(u7,u1,u0),(u16,u7,u0)],[],[(0,0),(0,3),(1,3),(4,3),(18,2)]),
([u16,u1,u0,u3,u4,u2],[(u7,u1,u0),(u16,u7,u0)],[],[(18,2)]),
([0x80808080,u1,u0,u3,u4,u2],[(u7,u1,u0),(0x80808080,u7,u3)],[],[(0,5),(1,5),(4,4),(16,6),(17,6),(18,4)]),
([u1,u0,u3,u4,u32],[(u7,u1,u0),(u32,u7,u2)],[],[(0,3),(3,10),(6,8),(8,8),(18,7),(18,9),(20,9),(21,11)]),
([u7,u1,u0,u3,u4,u32],[(u7,u1,u0),(u32,u7,u2)],[],[(0,3),(0,12),(2,12),(18,13),(20,13),(21,4)]),
([u1,u0,0xecececec,u3,u4,u2],[(u28,u1,u3),(0xecececec,u28,u0)],[],[(0,14),(4,11),(6,15)]),
([0x8888,u1,u0,u3,u4,u2],[(u7,u1,u0),(0x8888,u7,u2)],[],[(0,18),(1,16),(4,16),(19,17),(22,17)]),
([u25,u1,u3,u4,u2],[(u8,u1,u2),(u25,u8,u0)],[],[]),
([u25,u8,u1,u3,u4,u2],[(u8,u1,u2),(u25,u8,u0)],[],[(0,13),(0,19),(0,20),(2,13),(2,19),(21,18)]),
([u25,u1,u0,u3,u4,u2],[(u8,u1,u2),(u25,u8,u0)],[],[]),
([u7,u1,u11,u3,u4,u2],[(u7,u1,u0),(u11,u1,u0)],[],[(0,22),(2,22),(3,22),(18,7),(18,21),(19,7),(22,7)]),
([u7,u0,u11,u3,u4,u2],[(u7,u1,u0),(u11,u1,u0)],[],[(18,23)]),
([u7,u1,u6,u3,u4,u2],[(u7,u1,u0),(u6,u0,u3)],[],[(0,15),(6,8),(6,14),(7,8)]),
([u5,u8,u1,u0,u3,u4],[(u8,u1,u2),(u5,u2,u0)],[],[(0,9),(0,11),(0,24),(2,9),(21,25),(23,25)]),
([u10,u1,u0,u3,u4,u22],[(u22,u1,u2),(u10,u1,u2)],[],[(0,0),(0,2),(0,26),(6,26),(8,26),(9,1)]),
([u16,u0,u11,u3,u4,u2],[(u11,u1,u0),(u16,u1,u0)],[],[(0,0),(18,2)]),
([u1,u0,u3,u4,u22,0xffffcccc],[(u22,u1,u2),(0xffffcccc,u2,u0)],[],[(0,18),(3,27),(3,28),(13,29),(16,29)]),
([u5,u1,u11,u3,u4,u2],[(u11,u1,u0),(u5,u0,u2)],[],[(0,32),(0,33),(2,32),(9,30),(19,31),(22,31)]),
([u1,u21,u3,u4,u2],[(u17,u1,u3),(u21,u17,u0)],[],[(0,10),(0,29),(1,29),(4,26),(6,22),(6,32),(7,32),(18,33)]),
([u1,u21,u3,u17,u4,u2],[(u17,u1,u3),(u21,u17,u0)],[],[(0,36),(1,36),(4,26),(6,34),(6,37),(7,37),(18,35)]),
([u1,u21,u0,u3,u4,u2],[(u17,u1,u3),(u21,u17,u0)],[],[(0,28),(4,18),(18,33)]),
([u1,u0,u3,0xfefefefe,u4,u2],[(u11,u1,u0),(0xfefefefe,u11,u3)],[],[(0,39),(1,39),(4,35),(8,38),(9,38),(18,35)]),
([0xeeee,u1,u0,u3,u4],[(u11,u1,u0),(0xeeee,u11,u2)],[],[]),
([0xeeee,u1,u0,u11,u3,u4],[(u11,u1,u0),(0xeeee,u11,u2)],[],[(0,37),(0,40),(2,37),(2,40),(9,15)]),
([0xeeee,u1,u0,u3,u4,u2],[(u11,u1,u0),(0xeeee,u11,u2)],[],[]),
([0x4444,u1,u0,u3,u4,u2],[(u22,u1,u2),(0x4444,u22,u0)],[],[(1,41),(3,15),(4,41),(19,42),(22,42)]),
([u7,u1,u0,u3,u4,u2],[(u37,u1,u0),(u7,u37,u1)],[],[(0,18),(1,18),(4,18),(18,4),(20,4),(21,4)]),
([u1,u0,0xcccceeee,u3,u4,u2],[(u10,u1,u2),(0xcccceeee,u10,u0)],[],[(0,35),(0,43),(1,45),(4,45),(6,44),(8,44)]),
([0xaa,u1,u0,u3,u4,u2],[(u10,u1,u2),(0xaa,u10,u4)],[],[(0,46)]),
([u1,0xc4c4c4c4,u0,u3,u4,u2],[(0xa0a0a0a,u1,u3),(0xc4c4c4c4,0xa0a0a0a,u0)],[],[]),
([u1,u0,u11,u3,u4,u2],[(u37,u1,u0),(u11,u37,u0)],[],[(0,35),(1,35),(4,35),(6,15),(8,15),(9,15)]),
([u10,u24,u0,u3,u4],[(u10,u1,u2),(u24,u1,u2)],[],[(0,47),(0,48),(9,49)]),
([u10,u24,u1,u0,u3,u4],[(u10,u1,u2),(u24,u1,u2)],[],[(0,21)]),
([u10,u24,u0,u3,u4,u2],[(u10,u1,u2),(u24,u1,u2)],[],[(0,23)]),
([u10,u1,u33,u0,u3,u4],[(u10,u1,u2),(u33,u0,u2)],[],[(3,30),(12,46)]),
([u10,u5,u1,u0,u3,u4],[(u10,u1,u2),(u5,u0,u2)],[],[(0,35),(0,43),(0,50),(12,51),(14,51)]),
([0x40404040,u1,u0,u3,u4,u2],[(u16,u1,u0),(0x40404040,u16,u3)],[],[(0,52)]),
([u1,u0,0xdcdcdcdc,u3,u4,u2],[(0x50505050,u1,u3),(0xdcdcdcdc,0x50505050,u0)],[],[]),
([0x8888cccc,u1,u0,u3,u4,u2],[(u24,u1,u2),(0x8888cccc,u24,u0)],[],[(1,53),(4,53),(19,54),(21,4),(21,55),(22,54)]),
([u16,u1,u3,u9,u4,u2],[(u16,u1,u0),(u9,u0,u3)],[],[(0,52),(18,24)]),
([u5,u16,u1,u3,u4,u2],[(u16,u1,u0),(u5,u0,u2)],[],[(0,4),(0,55),(1,57),(3,56),(4,57)]),
([u1,u0,u35,u3,u4,u2],[(u6,u0,u3),(u35,u1,u6)],[],[(0,15),(0,61),(1,61),(6,15),(6,58),(8,60),(9,60),(16,59)]),
([0xaaaaaa,u1,u0,u3,u4,u2],[(u13,u4,u2),(0xaaaaaa,u1,u13)],[],[]),
([u5,u1,u33,u3,u4,u2],[(u33,u0,u2),(u5,u33,u0)],[],[(0,0),(0,64),(3,63),(9,62),(11,62)]),
([u5,u1,u0,u3,u4,u2],[(u33,u0,u2),(u5,u33,u0)],[],[(0,64),(1,65),(4,65),(19,66),(22,66)]),
([u1,u46,u0,u3,u4,u2],[(u6,u0,u3),(u46,u6,u4)],[],[(0,67),(6,67),(8,67)]),
([u1,u0,u3,0xfcccfccc,u4,u2],[(u20,u3,u4),(0xfcccfccc,u20,u0)],[],[]),
([0xc0c0,u1,u0,u3,u4,u2],[(u6,u0,u3),(0xc0c0,u6,u2)],[],[(1,68),(5,66),(16,69),(19,66)]),
([0xcccccc,u1,u0,u3,u4,u2],[(u13,u4,u2),(0xcccccc,u13,u0)],[],[(0,73),(4,70),(18,71),(20,72),(21,72),(22,66),(23,66)]),
([u1,u6,u9,u4,u2],[(u6,u0,u3),(u9,u0,u3)],[],[(0,52),(0,74),(0,78),(0,79),(1,78),(1,79),(8,67),(9,67),(16,46),(16,59),(16,73),(16,75),(16,76),(16,77),(17,73)]),
([u1,u6,u0,u9,u4,u2],[(u6,u0,u3),(u9,u0,u3)],[],[(16,80)]),
([u1,u6,u0,u4,u18,u2],[(u6,u3,u0),(u18,u3,u4)],[],[(0,67),(0,78),(1,82),(22,81)]),
([u5,u1,u6,u3,u4,u2],[(u6,u0,u3),(u5,u0,u2)],[],[(0,66),(0,82),(2,72),(6,83),(7,84)]),
([u29,u1,u0,u3,u4,u2],[(u9,u0,u3),(u29,u1,u9)],[],[(0,27),(0,74),(0,85),(1,85),(4,18),(16,86),(17,86),(18,18)]),
([0x54545454,u1,u0,u3,u4,u2],[(u9,u0,u3),(0x54545454,u1,u9)],[],[]),
([u5,u1,u0,u3,u4,0xffffcccc],[(0xffffcccc,u0,u2),(u5,u0,u2)],[],[(0,0),(0,64),(3,63),(19,87),(22,87)]),
([u5,u1,u0,u3,u4,u39],[(u39,u2,u3),(u5,u2,u0)],[],[(0,82),(0,90),(12,65),(19,88),(22,89)]),
([u1,0xccc0ccc0,u0,u3,u4,u2],[(u18,u3,u4),(0xccc0ccc0,u18,u0)],[],[]),
([u1,u0,u3,u4,u47,u2],[(u9,u0,u3),(u47,u9,u4)],[],[(0,78),(2,78),(12,78)]),
([0xfcfc,u1,u0,u3,u4,u2],[(u9,u0,u3),(0xfcfc,u9,u2)],[],[(0,79),(1,91),(4,65),(11,90),(16,92),(18,65),(21,90)]),
([0xcc,u1,u0,u3,u4,u2],[(u12,u4,u2),(0xcc,u12,u0)],[],[(0,65),(1,65),(4,93),(18,94)]),
([u1,0xaaaaeeee,u0,u3,u4,u2],[(u5,u0,u2),(0xaaaaeeee,u5,u1)],[],[(0,35),(0,50)]),
([0x8888aaaa,u1,u0,u3,u4,u2],[(u19,u2,u0),(0x8888aaaa,u19,u1)],[],[(9,56),(21,4)]),
([u1,u6,u0,u3,u4,u2],[(u27,u0,u3),(u6,u27,u0)],[],[(0,63)]),
([u1,u0,u3,u4,u51],[(0xcc00cc,u0,u4),(u51,0xcc00cc,u2)],[],[(0,57),(3,97),(6,84),(8,62),(18,31),(18,95),(20,96),(21,98)]),
([u5,u1,u0,u3,0xff00ffcc,u2],[(u5,u0,u2),(0xff00ffcc,u5,u4)],[],[(0,101),(3,99),(9,62),(19,100),(22,66)]),
([u1,u0,u49,u3,u4,u2],[(0xf0f0,u3,u2),(u49,0xf0f0,u0)],[],[(0,83),(4,98),(6,66)]),
([u1,u15,u3,u4,u2],[(u14,u2,u3),(u15,u14,u0)],[],[(0,87),(0,89),(0,97),(4,51),(6,25),(6,104),(7,103),(18,102)]),
([u5,u1,u0,0xf0f03030,u4,u2],[(u5,u0,u2),(0xf0f03030,u5,u3)],[],[(4,65),(19,87),(19,100),(19,105),(21,106)]),
([u1,u15,u0,u3,u4,u2],[(u14,u2,u3),(u15,u14,u0)],[],[(0,88),(4,65),(18,102)]),
([u1,u0,u3,u9,u4,u2],[(u27,u0,u3),(u9,u27,u3)],[],[(0,63)]),
([u5,u30,u1,u0,u3,u4],[(u30,u2,u4),(u5,u2,u0)],[],[(0,98),(0,107),(1,81),(2,95),(15,102),(15,103)]),
([u5,u19,u1,u3,u4],[(u5,u0,u2),(u19,u0,u2)],[],[(0,101),(0,106),(0,108),(2,101),(2,106),(12,75),(21,101),(21,106),(21,108),(23,101),(23,106)]),
([u5,u19,u1,u0,u3,u4],[(u5,u0,u2),(u19,u0,u2)],[],[(0,96),(2,96),(12,80),(21,104),(23,104)])
]
def c5_2_L6 : Array W5Node := Array.mk [
([u7,u1,u0,u3,u4,u2],[(u7,u1,u0)],[],[(0,2),(0,3),(0,4),(0,5),(0,6),(0,8),(0,12),(0,13),(0,14),(1,5),(1,6),(1,8),(2,4),(2,14),(3,4),(3,14),(4,5),(4,6),(4,8),(6,7),(8,7),(9,7),(18,0),(18,1),(18,9),(18,10),(18,11),(18,15),(20,9),(20,10),(20,11),(20,15),(21,9),(21,10),(21,11),(21,15)]),
([u1,u0,u11,u3,u4,u2],[(u11,u1,u0)],[],[(0,3),(0,12),(0,13),(0,17),(0,19),(0,23),(0,24),(0,25),(0,26),(1,19),(1,24),(1,25),(1,26),(2,23),(3,23),(4,19),(4,24),(4,25),(4,26),(6,20),(6,21),(6,22),(8,20),(8,21),(8,22),(9,20),(9,21),(9,22),(18,1),(18,16),(18,18),(18,27),(20,18),(20,27),(21,18),(21,27)]),
([u10,u1,u0,u3,u4,u2],[(u10,u1,u2)],[],[(0,0),(0,8),(0,16),(0,29),(0,30),(0,33),(0,34),(0,35),(0,36),(0,37),(2,30),(3,31),(6,8),(6,29),(6,36),(6,37),(8,8),(8,29),(8,36),(8,37),(9,28),(9,32),(12,30),(13,31),(16,31)]),
([u16,u1,u0,u3,u4,u2],[(u16,u1,u0)],[],[(0,2),(0,17),(0,27),(0,28),(0,32),(0,38),(0,41),(0,42),(1,27),(1,42),(2,38),(2,41),(3,38),(3,41),(4,27),(4,42),(6,39),(8,39),(9,39),(18,33),(18,34),(18,35),(18,40),(20,40),(21,40)]),
([u1,u6,u0,u3,u4,u2],[(u6,u0,u3)],[],[(0,4),(0,14),(0,38),(0,43),(0,47),(0,49),(0,51),(0,52),(0,53),(0,54),(1,47),(1,49),(1,53),(1,54),(4,36),(4,45),(4,46),(6,14),(6,52),(6,53),(6,54),(7,53),(7,54),(8,48),(9,48),(16,44),(16,50),(17,50),(18,36),(18,45),(18,46)]),
([u1,u0,u3,u9,u4,u2],[(u9,u0,u3)],[],[(0,23),(0,41),(0,51),(0,52),(0,55),(0,56),(0,60),(0,61),(1,60),(1,61),(4,18),(4,46),(4,57),(6,41),(6,52),(8,53),(8,59),(9,53),(9,59),(10,58),(11,58),(14,53),(15,53),(16,30),(16,62),(17,62),(18,18),(18,46),(18,57),(20,58),(21,58)]),
([u5,u1,u0,u3,u4,u2],[(u5,u0,u2)],[],[(0,8),(0,15),(0,19),(0,27),(0,37),(0,42),(0,45),(0,49),(0,54),(0,57),(0,58),(0,62),(0,63),(0,67),(0,70),(0,73),(0,74),(0,75),(1,66),(2,49),(2,54),(2,58),(2,62),(2,67),(2,70),(2,73),(3,65),(3,72),(4,66),(6,68),(8,68),(18,73),(19,69),(19,71),(20,73),(21,64),(21,75),(22,69),(22,71)])
]
def c5_2_L7 : Array W5Node := Array.mk [
([u1,u0,u3,u4,u2],[],[],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,6),(2,4),(2,5),(3,4),(3,5),(4,2),(4,6),(6,0),(6,1),(6,3),(6,6),(7,6),(8,0),(8,1),(8,3),(8,6),(9,0),(9,1),(9,3),(9,6),(10,6),(11,6),(12,4),(12,5),(13,4),(13,5),(16,4),(16,5),(18,2),(18,6),(20,6),(21,6)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_2_0 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 2 c5_2_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_2_chk_2 : ∀ i < c5_2_L2.size, checkNodeW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 2 c5_2_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_2_L2.size = 2 := by decide +kernel
  exact checkBlockW5_at c5_2_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_3_0 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 3 c5_2_L3 c5_2_L2 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_3_1 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 3 c5_2_L3 c5_2_L2 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_3_2 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 3 c5_2_L3 c5_2_L2 32 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_2_chk_3 : ∀ i < c5_2_L3.size, checkNodeW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 3 c5_2_L3 c5_2_L2 i = true := by
  intro i hi
  have hsz : c5_2_L3.size = 37 := by decide +kernel
  have hi' : i < 37 := hsz ▸ hi
  by_cases h : i < 32
  ·
    by_cases h : i < 16
    ·
      exact checkBlockW5_at c5_2_chk_3_0 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_2_chk_3_1 i (by omega) (by omega)
  ·
    exact checkBlockW5_at c5_2_chk_3_2 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_4_0 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 4 c5_2_L4 c5_2_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_4_1 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 4 c5_2_L4 c5_2_L3 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_4_2 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 4 c5_2_L4 c5_2_L3 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_4_3 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 4 c5_2_L4 c5_2_L3 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_4_4 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 4 c5_2_L4 c5_2_L3 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_4_5 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 4 c5_2_L4 c5_2_L3 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_4_6 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 4 c5_2_L4 c5_2_L3 96 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_2_chk_4 : ∀ i < c5_2_L4.size, checkNodeW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 4 c5_2_L4 c5_2_L3 i = true := by
  intro i hi
  have hsz : c5_2_L4.size = 109 := by decide +kernel
  have hi' : i < 109 := hsz ▸ hi
  by_cases h : i < 64
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW5_at c5_2_chk_4_0 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_2_chk_4_1 i (by omega) (by omega)
    ·
      by_cases h : i < 48
      ·
        exact checkBlockW5_at c5_2_chk_4_2 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_2_chk_4_3 i (by omega) (by omega)
  ·
    by_cases h : i < 96
    ·
      by_cases h : i < 80
      ·
        exact checkBlockW5_at c5_2_chk_4_4 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_2_chk_4_5 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_2_chk_4_6 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_5_0 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 5 c5_2_L5 c5_2_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_5_1 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 5 c5_2_L5 c5_2_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_5_2 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 5 c5_2_L5 c5_2_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_5_3 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 5 c5_2_L5 c5_2_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_5_4 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 5 c5_2_L5 c5_2_L4 64 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_2_chk_5 : ∀ i < c5_2_L5.size, checkNodeW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 5 c5_2_L5 c5_2_L4 i = true := by
  intro i hi
  have hsz : c5_2_L5.size = 76 := by decide +kernel
  have hi' : i < 76 := hsz ▸ hi
  by_cases h : i < 48
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW5_at c5_2_chk_5_0 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_2_chk_5_1 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_2_chk_5_2 i (by omega) (by omega)
  ·
    by_cases h : i < 64
    ·
      exact checkBlockW5_at c5_2_chk_5_3 i (by omega) (by omega)
    ·
      exact checkBlockW5_at c5_2_chk_5_4 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_6_0 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 6 c5_2_L6 c5_2_L5 0 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_2_chk_6 : ∀ i < c5_2_L6.size, checkNodeW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 6 c5_2_L6 c5_2_L5 i = true := by
  intro i hi
  have hsz : c5_2_L6.size = 7 := by decide +kernel
  exact checkBlockW5_at c5_2_chk_6_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_2_chk_7_0 : checkBlockW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 7 c5_2_L7 c5_2_L6 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_2_chk_7 : ∀ i < c5_2_L7.size, checkNodeW5 c5_2_goal 24 c5_2_pow 0 c5_2_cfLBs c5_2_cfMasks c5_2_cfB0s c5_2_cfStocks 7 c5_2_L7 c5_2_L6 i = true := by
  intro i hi
  have hsz : c5_2_L7.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_2_chk_7_0 i (Nat.zero_le _) (by omega)
theorem c5_2_L2_sound : ∀ i < c5_2_L2.size, ¬ live (basicOps 32) c5_2_goal 2 (c5_2_L2[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_2_G_valid c5_2_cof_sound (fun j hj => by simp at hj) c5_2_chk_2
theorem c5_2_L3_sound : ∀ i < c5_2_L3.size, ¬ live (basicOps 32) c5_2_goal 3 (c5_2_L3[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_2_G_valid c5_2_cof_sound c5_2_L2_sound c5_2_chk_3
theorem c5_2_L4_sound : ∀ i < c5_2_L4.size, ¬ live (basicOps 32) c5_2_goal 4 (c5_2_L4[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_2_G_valid c5_2_cof_sound c5_2_L3_sound c5_2_chk_4
theorem c5_2_L5_sound : ∀ i < c5_2_L5.size, ¬ live (basicOps 32) c5_2_goal 5 (c5_2_L5[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_2_G_valid c5_2_cof_sound c5_2_L4_sound c5_2_chk_5
theorem c5_2_L6_sound : ∀ i < c5_2_L6.size, ¬ live (basicOps 32) c5_2_goal 6 (c5_2_L6[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_2_G_valid c5_2_cof_sound c5_2_L5_sound c5_2_chk_6
theorem c5_2_L7_sound : ∀ i < c5_2_L7.size, ¬ live (basicOps 32) c5_2_goal 7 (c5_2_L7[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_2_G_valid c5_2_cof_sound c5_2_L6_sound c5_2_chk_7
set_option maxRecDepth 100000 in
theorem c5_2_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_2_goal ws) = [rows5] := by decide +kernel
theorem c5_2_top_match : sameSet (rows5.map (actB 32 (c5_2_pow[0]?.getD []))) (c5_2_L7[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_2_no_build : ¬ build (basicOps 32) c5_2_goal 7 rows5.toFinset :=
  no_build_of_top c5_2_G_valid (by decide) c5_2_sublists c5_2_top_match (c5_2_L7_sound 0 (by decide))

def c5_3_goal : BitVec 32 := 0xeaa8a8a8
def c5_3_idxs4 : List ℕ := [8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_3_no_build : ¬ build (basicOps 32) c5_3_goal 6 rows5.toFinset :=
  no_build5_of_proj4 5 b4_0_goal (by decide) b4_0_no_build c5_3_goal c5_3_idxs4 3 17 25 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

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

def v0 : BitVec 64 := 0xaaaaaaaaaaaaaaaa
def v1 : BitVec 64 := 0xffff0000ffff0000
def v2 : BitVec 64 := 0xff00ff00ff00ff00
def v3 : BitVec 64 := 0xf0f0f0f0f0f0f0f0
def v4 : BitVec 64 := 0xffffffff00000000
def v5 : BitVec 64 := 0xeeeeeeeeeeeeeeee
def v6 : BitVec 64 := 0xcccccccccccccccc
def v7 : BitVec 64 := 0xfff0fff0fff0fff0
def v8 : BitVec 64 := 0xff000000ff0000
def v9 : BitVec 64 := 0xffff000000000000
def v10 : BitVec 64 := 0xfafafafafafafafa
def v11 : BitVec 64 := 0xffaaffaaffaaffaa
def v12 : BitVec 64 := 0xfefefefefefefefe
def v13 : BitVec 64 := 0x5555000055550000
def v14 : BitVec 64 := 0xfffafffafffafffa
def v15 : BitVec 64 := 0x55000000550000
def v16 : BitVec 64 := 0xf0f0f0f00000000
def v17 : BitVec 64 := 0xffeeffeeffeeffee
def v18 : BitVec 64 := 0xff000000000000
def v19 : BitVec 64 := 0xfa00fa00fa00fa
def v20 : BitVec 64 := 0xee00ee00ee00ee
def v21 : BitVec 64 := 0xf0000000f0000
def v22 : BitVec 64 := 0x1111000011110000
def v23 : BitVec 64 := 0xf0f00000f0f0000
def v24 : BitVec 64 := 0x5555000000000000
def v25 : BitVec 64 := 0xf0f00000ffff0000
def v26 : BitVec 64 := 0xeeee0000eeee0000
def v27 : BitVec 64 := 0xffffaaaaaaaaaaaa
def v28 : BitVec 64 := 0xfff00000fff00000
def v29 : BitVec 64 := 0xfe00fe00fe00fe
def v30 : BitVec 64 := 0xff00ff00000000
def v31 : BitVec 64 := 0xaaffaaaaaaffaaaa
def v32 : BitVec 64 := 0xffaa0000ffaa0000
def v33 : BitVec 64 := 0xf0f000000000000
def v34 : BitVec 64 := 0xff0fff00ff0fff00
def v35 : BitVec 64 := 0xfefe0000fefe0000
def v36 : BitVec 64 := 0xfafa0000fafa0000
def v37 : BitVec 64 := 0xf0fff0f0f0fff0f0
def v38 : BitVec 64 := 0xff55ff00ff55ff00
def v39 : BitVec 64 := 0xffffff00ff00ff00
def v40 : BitVec 64 := 0x5454545454545454
def v41 : BitVec 64 := 0x5550555055505550
def v42 : BitVec 64 := 0xaaaa0000ffff0000
def v43 : BitVec 64 := 0x5555555500000000
def v44 : BitVec 64 := 0xeee0eee0eee0eee0
def v45 : BitVec 64 := 0xffee0000ffee0000
def v46 : BitVec 64 := 0xfefefefe
def v47 : BitVec 64 := 0xfffff0f0f0f0f0f0
def v48 : BitVec 64 := 0xf0a0f0a0f0a0f0a
def v49 : BitVec 64 := 0xbbbbaaaabbbbaaaa
def v50 : BitVec 64 := 0xff0fff00ff00ff00
def v51 : BitVec 64 := 0xf5f5f0f0f5f5f0f0
def v52 : BitVec 64 := 0xff00ffff00000000
def v53 : BitVec 64 := 0xfff00ff0f0f0000
def v54 : BitVec 64 := 0xf0fef0fef0fef0fe
def v55 : BitVec 64 := 0xffffeeeeeeeeeeee
def v56 : BitVec 64 := 0xfff0fff0fff0
def v57 : BitVec 64 := 0xfe00fe00fe00fe00
def v58 : BitVec 64 := 0xf0e0f0e0f0e0f0e0
def v59 : BitVec 64 := 0xfffefffefffefffe
def v60 : BitVec 64 := 0xeeffeeeeeeffeeee
def v61 : BitVec 64 := 0xaaaaffff00000000
def v62 : BitVec 64 := 0xf0fff0f0f0f0f0f0
def v63 : BitVec 64 := 0xff000000ffff0000
def v64 : BitVec 64 := 0xe000e000e000e
def v65 : BitVec 64 := 0x54005400540054
def v66 : BitVec 64 := 0xfffffafafafafafa
def v67 : BitVec 64 := 0x5544554455445544
def v68 : BitVec 64 := 0x11000000110000
def v69 : BitVec 64 := 0xe0e0e0e0e0e0e0e
def v70 : BitVec 64 := 0xf1f10000f1f10000
def v71 : BitVec 64 := 0xeeee000000000000
def v72 : BitVec 64 := 0x1111000000000000
def v73 : BitVec 64 := 0x1110111011101110
def v74 : BitVec 64 := 0xfffaaaaafffaaaaa
def v75 : BitVec 64 := 0xaaffaaaaaaaaaaaa
def v76 : BitVec 64 := 0xff00aa00aa00aa
def v77 : BitVec 64 := 0xf0a0f0a0ffaaffaa
def v78 : BitVec 64 := 0x505000005050000
def v79 : BitVec 64 := 0xfff5fff0fff5fff0
def v80 : BitVec 64 := 0xaaa0aaa0fff0fff0
def v81 : BitVec 64 := 0xf000000000000
def v82 : BitVec 64 := 0xfffffff0fff0fff0
def v83 : BitVec 64 := 0xf000f0f0f0f0f0f0

def g6_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def g6_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648,4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808]
def g6_s1 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def g6_p1 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808]
def g6_s2 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31,32,33,34,35,40,41,42,43,36,37,38,39,44,45,46,47,48,49,50,51,56,57,58,59,52,53,54,55,60,61,62,63]
def g6_p2 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768,65536,131072,262144,524288,16777216,33554432,67108864,134217728,1048576,2097152,4194304,8388608,268435456,536870912,1073741824,2147483648,4294967296,8589934592,17179869184,34359738368,1099511627776,2199023255552,4398046511104,8796093022208,68719476736,137438953472,274877906944,549755813888,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,72057594037927936,144115188075855872,288230376151711744,576460752303423488,4503599627370496,9007199254740992,18014398509481984,36028797018963968,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808]
def g6_s3 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,32,33,34,35,40,41,42,43,36,37,38,39,44,45,46,47,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31,48,49,50,51,56,57,58,59,52,53,54,55,60,61,62,63]
def g6_p3 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768,4294967296,8589934592,17179869184,34359738368,1099511627776,2199023255552,4398046511104,8796093022208,68719476736,137438953472,274877906944,549755813888,17592186044416,35184372088832,70368744177664,140737488355328,65536,131072,262144,524288,16777216,33554432,67108864,134217728,1048576,2097152,4194304,8388608,268435456,536870912,1073741824,2147483648,281474976710656,562949953421312,1125899906842624,2251799813685248,72057594037927936,144115188075855872,288230376151711744,576460752303423488,4503599627370496,9007199254740992,18014398509481984,36028797018963968,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808]
def g6_idx : Array (List ℕ) := Array.mk [g6_s0,g6_s1,g6_s2,g6_s3]
def g6_pow : Array (List ℕ) := Array.mk [g6_p0,g6_p1,g6_p2,g6_p3]
def g6_inv : Array ℕ := Array.mk [0,1,2,3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_G_valid : (List.range 4).all (symValid 64 4 g6_idx g6_pow g6_inv goal6) = true := by decide +kernel

def g6_m0 : BitVec 64 := 0xffff0000ffff0000

def g6_st0 : List (BitVec 64) := [0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff000000000000]

def g6_ix0 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_0 : g6_ix0.length = 32 ∧ (∀ idx ∈ g6_ix0, idx < 64) ∧ (∀ idx ∈ g6_ix0, g6_m0.getLsbD idx = true) ∧ projS 32 g6_ix0 goal6 = c5_0_goal ∧ g6_st0.all (fun w => rows5.contains (projS 32 g6_ix0 w)) = true := by decide +kernel

def g6_m1 : BitVec 64 := 0xffffffff00000000

def g6_st1 : List (BitVec 64) := [0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000]

def g6_ix1 : List ℕ := [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_1 : g6_ix1.length = 32 ∧ (∀ idx ∈ g6_ix1, idx < 64) ∧ (∀ idx ∈ g6_ix1, g6_m1.getLsbD idx = true) ∧ projS 32 g6_ix1 goal6 = c5_0_goal ∧ g6_st1.all (fun w => rows5.contains (projS 32 g6_ix1 w)) = true := by decide +kernel

def g6_m2 : BitVec 64 := 0xf0f0f0f0f0f0f0f

def g6_st2 : List (BitVec 64) := [0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]

def g6_ix2 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,32,33,34,35,40,41,42,43,48,49,50,51,56,57,58,59]

set_option maxRecDepth 100000 in

theorem g6_cspec_2 : g6_ix2.length = 32 ∧ (∀ idx ∈ g6_ix2, idx < 64) ∧ (∀ idx ∈ g6_ix2, g6_m2.getLsbD idx = true) ∧ projS 32 g6_ix2 goal6 = c5_1_goal ∧ g6_st2.all (fun w => rows5.contains (projS 32 g6_ix2 w)) = true := by decide +kernel

def g6_m3 : BitVec 64 := 0xff00ff00ff00ff

def g6_st3 : List (BitVec 64) := [0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]

def g6_ix3 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,32,33,34,35,36,37,38,39,48,49,50,51,52,53,54,55]

set_option maxRecDepth 100000 in

theorem g6_cspec_3 : g6_ix3.length = 32 ∧ (∀ idx ∈ g6_ix3, idx < 64) ∧ (∀ idx ∈ g6_ix3, g6_m3.getLsbD idx = true) ∧ projS 32 g6_ix3 goal6 = c5_1_goal ∧ g6_st3.all (fun w => rows5.contains (projS 32 g6_ix3 w)) = true := by decide +kernel

def g6_m4 : BitVec 64 := 0x3333333333333333

def g6_st4 : List (BitVec 64) := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]

def g6_ix4 : List ℕ := [0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_4 : g6_ix4.length = 32 ∧ (∀ idx ∈ g6_ix4, idx < 64) ∧ (∀ idx ∈ g6_ix4, g6_m4.getLsbD idx = true) ∧ projS 32 g6_ix4 goal6 = c5_2_goal ∧ g6_st4.all (fun w => rows5.contains (projS 32 g6_ix4 w)) = true := by decide +kernel

def g6_m5 : BitVec 64 := 0x5555555555555555

def g6_st5 : List (BitVec 64) := [0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]

def g6_ix5 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_5 : g6_ix5.length = 32 ∧ (∀ idx ∈ g6_ix5, idx < 64) ∧ (∀ idx ∈ g6_ix5, g6_m5.getLsbD idx = true) ∧ projS 32 g6_ix5 goal6 = c5_3_goal ∧ g6_st5.all (fun w => rows5.contains (projS 32 g6_ix5 w)) = true := by decide +kernel

def g6_cfMasks : Array (BitVec 64) := Array.mk [g6_m0,g6_m1,g6_m2,g6_m3,g6_m4,g6_m5]

def g6_cfB0s : Array ℕ := Array.mk [16,32,0,0,0,0]

def g6_cfStocks : Array (List (BitVec 64)) := Array.mk [g6_st0,g6_st1,g6_st2,g6_st3,g6_st4,g6_st5]

def g6_cfLBs : Array ℕ := Array.mk [7,7,7,7,8,7]

theorem g6_cof_sound (c fuel : ℕ) (hc : c < 6) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) (hnd : nxt.Nodup) (hchk : checkCofClose64 (g6_cfLBs[c]?.getD 0) fuel (g6_cfMasks[c]?.getD 0) (g6_cfB0s[c]?.getD 0) (g6_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose64_sound_aux goal6 7 g6_ix0 g6_cspec_0.1 g6_cspec_0.2.1 g6_m0 g6_cspec_0.2.2.1 16 g6_st0 c5_0_goal (by decide) g6_cspec_0.2.2.2.1 g6_cspec_0.2.2.2.2 c5_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose64_sound_aux goal6 7 g6_ix1 g6_cspec_1.1 g6_cspec_1.2.1 g6_m1 g6_cspec_1.2.2.1 32 g6_st1 c5_0_goal (by decide) g6_cspec_1.2.2.2.1 g6_cspec_1.2.2.2.2 c5_0_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose64_sound_aux goal6 7 g6_ix2 g6_cspec_2.1 g6_cspec_2.2.1 g6_m2 g6_cspec_2.2.2.1 0 g6_st2 c5_1_goal (by decide) g6_cspec_2.2.2.2.1 g6_cspec_2.2.2.2.2 c5_1_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose64_sound_aux goal6 7 g6_ix3 g6_cspec_3.1 g6_cspec_3.2.1 g6_m3 g6_cspec_3.2.2.1 0 g6_st3 c5_1_goal (by decide) g6_cspec_3.2.2.2.1 g6_cspec_3.2.2.2.2 c5_1_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose64_sound_aux goal6 8 g6_ix4 g6_cspec_4.1 g6_cspec_4.2.1 g6_m4 g6_cspec_4.2.2.1 0 g6_st4 c5_2_goal (by decide) g6_cspec_4.2.2.2.1 g6_cspec_4.2.2.2.2 c5_2_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose64_sound_aux goal6 7 g6_ix5 g6_cspec_5.1 g6_cspec_5.2.1 g6_m5 g6_cspec_5.2.2.1 0 g6_st5 c5_3_goal (by decide) g6_cspec_5.2.2.2.1 g6_cspec_5.2.2.2.2 c5_3_no_build fuel hist nxt hnd hchk
  | c + 6 => omega

def g6_L4 : Array W6Node := Array.mk [
([v44,v10,v17,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v17,v5,v2),(v7,v3,v2),(v44,v5,v7)],[],[]),
([v5,v10,v45,v7,v4],[(v5,v0,v6),(v10,v0,v3),(v17,v5,v2),(v7,v3,v2),(v45,v17,v1)],[],[]),
([v19,v48,v5,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v14,v11,v3),(v19,v2,v14),(v48,v3,v14)],[],[]),
([v0,v44,v3,v45,v4],[(v5,v0,v6),(v17,v5,v2),(v7,v2,v3),(v44,v5,v7),(v45,v17,v1)],[],[]),
([v0,v6,v25,v52,v7],[(v7,v3,v2),(v16,v3,v4),(v25,v16,v1),(v8,v2,v1),(v52,v8,v4)],[],[]),
([v53,v0,v6,v7,v9],[(v7,v2,v3),(v30,v2,v4),(v23,v3,v1),(v53,v30,v23),(v9,v1,v4)],[],[]),
([v56,v8,v16,v0,v6],[(v7,v2,v3),(v8,v2,v1),(v16,v3,v4),(v9,v1,v4),(v56,v7,v9)],[],[])
]

def g6_L5 : Array W6Node := Array.mk [
([v5,v3,v54,v11,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v20,v5,v2),(v54,v20,v3)],[0,1],[]),
([v64,v5,v3,v11,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v20,v5,v2),(v64,v20,v3)],[],[]),
([v5,v10,v17,v7,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v17,v5,v2),(v7,v3,v2)],[2],[(0,0),(0,1),(1,1)]),
([v29,v5,v3,v11,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v12,v5,v3),(v29,v2,v12)],[],[]),
([v65,v5,v3,v2,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v12,v5,v3),(v65,v11,v12)],[],[]),
([v5,v3,v10,v2,v45,v4],[(v5,v0,v6),(v10,v0,v3),(v17,v5,v2),(v45,v17,v1)],[],[(0,1)]),
([v20,v19,v5,v3,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v20,v5,v2),(v19,v10,v2)],[],[]),
([v5,v3,v11,0xffeeff00ffeeff00,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v26,v5,v1),(0xffeeff00ffeeff00,v26,v2)],[],[]),
([v5,v3,0xff11ff00ff11ff00,v11,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v22,v5,v1),(0xff11ff00ff11ff00,v22,v2)],[],[]),
([v5,v3,0xfbfbfafafbfbfafa,v2,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v22,v5,v1),(0xfbfbfafafbfbfafa,v22,v10)],[],[]),
([v44,v5,v3,v11,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v7,v2,v3),(v44,v5,v7)],[0,1,3],[]),
([v19,v5,v10,v7,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v7,v3,v2),(v19,v2,v10)],[],[]),
([v8,v5,v10,v7,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v7,v3,v2),(v8,v2,v1)],[0],[]),
([v19,v5,v3,v14,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v14,v11,v3),(v19,v2,v14)],[],[(0,2)]),
([v19,v5,v3,v11,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v14,v11,v3),(v19,v2,v14)],[],[(0,2)]),
([0xe0e4e0e4e0e4e0e4,v5,v3,v2,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v48,v11,v3),(0xe0e4e0e4e0e4e0e4,v48,v5)],[],[]),
([v5,v3,v38,v11,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v15,v11,v1),(v38,v15,v2)],[],[]),
([v5,v3,v34,v11,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v23,v3,v1),(v34,v23,v2)],[],[]),
([v5,v3,v11,v1,v39,v4],[(v5,v0,v6),(v11,v0,v2),(v9,v1,v4),(v39,v2,v9)],[],[]),
([v5,v3,v2,v1,v66,v4],[(v5,v0,v6),(v10,v0,v3),(v9,v1,v4),(v66,v10,v9)],[],[]),
([0xfafafafafafa,v5,v3,v2,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v9,v1,v4),(0xfafafafafafa,v10,v9)],[],[]),
([v5,v3,0xf5f4f5f4f5f4f5f4,v2,v1,v4],[(v5,v0,v6),(v17,v5,v2),(v67,v0,v17),(0xf5f4f5f4f5f4f5f4,v67,v3)],[],[]),
([v20,v67,v5,v3,v1,v4],[(v5,v0,v6),(v17,v5,v2),(v67,v0,v17),(v20,v5,v2)],[],[]),
([v40,v5,v2,v7,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v40,v0,v12),(v7,v3,v2)],[],[]),
([v40,v5,v3,v57,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v40,v0,v12),(v57,v12,v2)],[],[]),
([v29,v40,v5,v3,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v40,v0,v12),(v29,v12,v2)],[],[]),
([v40,v5,v3,v35,v2,v4],[(v5,v0,v6),(v12,v5,v3),(v40,v0,v12),(v35,v12,v1)],[],[]),
([v46,v40,v5,v3,v2,v1],[(v5,v0,v6),(v12,v5,v3),(v40,v0,v12),(v46,v12,v4)],[],[]),
([v20,v0,v5,v3,v45,v4],[(v5,v0,v6),(v17,v5,v2),(v20,v5,v2),(v45,v17,v1)],[],[]),
([v0,v44,v3,v17,v1,v4],[(v5,v0,v6),(v17,v5,v2),(v7,v2,v3),(v44,v5,v7)],[],[(0,0),(0,3),(1,3)]),
([v0,v5,v3,v45,v7,v4],[(v5,v0,v6),(v17,v5,v2),(v7,v2,v3),(v45,v17,v1)],[],[(0,1),(0,3)]),
([v29,v0,v5,v3,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v57,v12,v2),(v29,v57,v12)],[],[]),
([v20,v0,v5,v58,v1,v4],[(v5,v0,v6),(v17,v5,v2),(v58,v17,v3),(v20,v2,v17)],[],[]),
([v0,v5,v58,v2,v45,v4],[(v5,v0,v6),(v17,v5,v2),(v58,v17,v3),(v45,v17,v1)],[3],[]),
([v46,v0,v5,v3,v57,v1],[(v5,v0,v6),(v12,v5,v3),(v57,v12,v2),(v46,v12,v4)],[],[]),
([0x5554555455545554,v5,v3,v2,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v59,v12,v2),(0x5554555455545554,v0,v59)],[],[]),
([v0,v5,v3,v2,0xfffe0000fffe0000,v4],[(v5,v0,v6),(v12,v5,v3),(v59,v12,v2),(0xfffe0000fffe0000,v59,v1)],[],[]),
([v65,v29,v5,v3,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v29,v12,v2),(v65,v29,v0)],[],[]),
([v29,v0,v5,v3,v35,v4],[(v5,v0,v6),(v12,v5,v3),(v29,v12,v2),(v35,v12,v1)],[],[]),
([v46,v29,v0,v5,v3,v1],[(v5,v0,v6),(v12,v5,v3),(v29,v12,v2),(v46,v12,v4)],[],[]),
([v0,v5,v3,v35,0xfefefefe00000000,v2],[(v5,v0,v6),(v12,v5,v3),(v35,v12,v1),(0xfefefefe00000000,v12,v4)],[],[]),
([v46,v0,v5,v3,v35,v2],[(v5,v0,v6),(v12,v5,v3),(v35,v12,v1),(v46,v12,v4)],[],[]),
([v0,v5,v3,v35,v2,v4],[(v5,v0,v6),(v12,v5,v3),(0xfefe0000fefe,v12,v1),(v35,0xfefe0000fefe,v12)],[],[]),
([v46,0xfefe0000fefe,v0,v5,v3,v2],[(v5,v0,v6),(v12,v5,v3),(v46,v12,v4),(0xfefe0000fefe,v12,v1)],[],[]),
([0xaabbaaaaaabbaaaa,v5,v3,v2,v1,v4],[(v5,v0,v6),(v17,v5,v2),(v68,v17,v1),(0xaabbaaaaaabbaaaa,v68,v0)],[],[]),
([v0,v5,v3,0xff01ff00ff01ff00,v1,v4],[(v5,v0,v6),(v12,v5,v3),(0x101000001010000,v12,v1),(0xff01ff00ff01ff00,0x101000001010000,v2)],[],[]),
([v0,v5,v3,0xfefe0000ffff0000,v2,v4],[(v5,v0,v6),(v12,v5,v3),(0x101010100000000,v12,v4),(0xfefe0000ffff0000,0x101010100000000,v1)],[],[]),
([0x5054505450545054,v5,v3,v2,v1,v4],[(v5,v0,v6),(v20,v5,v2),(v54,v20,v3),(0x5054505450545054,v0,v54)],[],[]),
([v0,v5,v3,0xf0fe0000f0fe0000,v2,v4],[(v5,v0,v6),(v20,v5,v2),(v54,v20,v3),(0xf0fe0000f0fe0000,v54,v1)],[],[]),
([v5,v3,0xfbfbaaaafbfbaaaa,v2,v1,v4],[(v5,v0,v6),(v69,v5,v3),(v70,v69,v1),(0xfbfbaaaafbfbaaaa,v0,v70)],[],[]),
([v20,v0,v60,v3,v1,v4],[(v5,v0,v6),(v20,v5,v2),(v8,v2,v1),(v60,v8,v5)],[],[]),
([v49,v26,v5,v3,v2,v4],[(v5,v0,v6),(v26,v5,v1),(v22,v26,v1),(v49,v22,v0)],[],[]),
([v0,v5,v3,0xffeeff00ff00ff00,v1,v4],[(v5,v0,v6),(v26,v5,v1),(v71,v26,v4),(0xffeeff00ff00ff00,v71,v2)],[],[]),
([v26,v5,v3,v2,v27,v4],[(v5,v0,v6),(v26,v5,v1),(v9,v1,v4),(v27,v0,v9)],[1],[]),
([v0,v26,v3,v2,v55,v4],[(v5,v0,v6),(v26,v5,v1),(v9,v1,v4),(v55,v5,v9)],[],[]),
([0xbb00aa00bb00aa,v5,v3,v2,v1,v4],[(v5,v0,v6),(v22,v5,v1),(v49,v22,v0),(0xbb00aa00bb00aa,v49,v2)],[],[]),
([v8,v49,v5,v3,v2,v4],[(v5,v0,v6),(v22,v5,v1),(v49,v22,v0),(v8,v2,v1)],[],[]),
([0xbbbbaaaaaaaaaaaa,v5,v3,v2,v1,v4],[(v5,v0,v6),(v22,v5,v1),(v72,v22,v4),(0xbbbbaaaaaaaaaaaa,v72,v0)],[],[]),
([v22,v0,0xe0e0eeeee0e0eeee,v3,v2,v4],[(v5,v0,v6),(v22,v5,v1),(v23,v3,v1),(0xe0e0eeeee0e0eeee,v23,v5)],[],[]),
([v19,v5,v3,v7,v1,v4],[(v5,v0,v6),(v7,v2,v3),(v14,v0,v7),(v19,v2,v14)],[],[]),
([0x111f0000111f0000,v0,v5,v3,v2,v4],[(v5,v0,v6),(v7,v3,v2),(v44,v5,v7),(0x111f0000111f0000,v44,v1)],[],[]),
([0xbbbabbbabbbabbba,v5,v3,v2,v1,v4],[(v5,v0,v6),(v7,v3,v2),(v73,v5,v7),(0xbbbabbbabbbabbba,v73,v0)],[],[]),
([v5,v3,v2,v74,v1,v4],[(v5,v0,v6),(v7,v3,v2),(v28,v7,v1),(v74,v0,v28)],[],[]),
([0x4455444444554444,v5,v3,v2,v1,v4],[(v5,v0,v6),(v8,v2,v1),(v60,v8,v5),(0x4455444444554444,v0,v60)],[],[]),
([v75,v5,v3,v2,v1,v4],[(v5,v0,v6),(v8,v2,v1),(v18,v8,v4),(v75,v18,v0)],[],[]),
([v0,v5,v3,v50,v1,v4],[(v5,v0,v6),(v23,v3,v1),(v33,v23,v4),(v50,v33,v2)],[],[]),
([v8,v5,v3,v2,v27,v4],[(v5,v0,v6),(v8,v2,v1),(v9,v1,v4),(v27,v0,v9)],[1],[]),
([v76,v5,v3,v2,v1,v4],[(v5,v0,v6),(v9,v1,v4),(v27,v0,v9),(v76,v2,v27)],[],[]),
([0x5555444444444444,v5,v3,v2,v1,v4],[(v5,v0,v6),(v9,v1,v4),(v55,v5,v9),(0x5555444444444444,v0,v55)],[],[]),
([0xff00ee00ee00ee,v0,v5,v3,v1,v4],[(v5,v0,v6),(v9,v1,v4),(v55,v5,v9),(0xff00ee00ee00ee,v2,v55)],[],[]),
([v0,v6,v77,v7,v1,v4],[(v11,v0,v2),(v7,v2,v3),(v16,v3,v4),(v77,v16,v11)],[],[]),
([v8,v0,v6,v36,v7,v4],[(v10,v0,v3),(v7,v3,v2),(v8,v2,v1),(v36,v10,v1)],[],[]),
([v19,v41,v6,v3,v1,v4],[(v11,v0,v2),(v14,v11,v3),(v41,v0,v14),(v19,v2,v14)],[],[]),
([v19,v48,v0,v6,v1,v4],[(v11,v0,v2),(v14,v11,v3),(v19,v2,v14),(v48,v3,v14)],[],[(0,2)]),
([v0,v6,v3,0xf0f50000ffff0000,v2,v4],[(v11,v0,v2),(v48,v11,v3),(0xf0a0f0a00000000,v48,v4),(0xf0f50000ffff0000,0xf0a0f0a00000000,v1)],[],[]),
([v31,v6,v3,v2,v32,v4],[(v11,v0,v2),(v32,v11,v1),(v15,v32,v1),(v31,v15,v0)],[],[]),
([v0,v6,v3,v34,v32,v4],[(v11,v0,v2),(v32,v11,v1),(v23,v3,v1),(v34,v23,v2)],[],[]),
([v0,v6,v3,v32,v39,v4],[(v11,v0,v2),(v32,v11,v1),(v9,v1,v4),(v39,v2,v9)],[],[]),
([v31,v6,v3,v38,v1,v4],[(v11,v0,v2),(v15,v11,v1),(v31,v15,v0),(v38,v15,v2)],[],[]),
([v0,v6,v3,0xff05ff00ff00ff00,v1,v4],[(v10,v0,v3),(v78,v10,v1),(0x505000000000000,v78,v4),(0xff05ff00ff00ff00,0x505000000000000,v2)],[],[]),
([v0,v6,v3,0xfaff0000fafa0000,v2,v4],[(v10,v0,v3),(v30,v2,v4),(0xfafffafffafafafa,v30,v10),(0xfaff0000fafa0000,0xfafffafffafafafa,v1)],[],[]),
([0x3331333033313330,v0,v3,v2,v1,v4],[(v13,v0,v1),(v51,v13,v3),(v79,v51,v2),(0x3331333033313330,v6,v79)],[],[]),
([v0,v6,v3,v38,v32,v4],[(v13,v0,v1),(v15,v13,v2),(v32,v15,v1),(v38,v13,v2)],[],[]),
([v42,v6,v3,v2,v27,v4],[(v13,v0,v1),(v24,v13,v4),(v27,v24,v0),(v42,v24,v1)],[],[]),
([v42,v0,v61,v6,v3,v2],[(v13,v0,v1),(v24,v13,v4),(v42,v24,v1),(v61,v24,v4)],[0],[]),
([0x555f0000000f0000,v0,v6,v3,v2,v4],[(v43,v0,v4),(v7,v3,v2),(v80,v43,v7),(0x555f0000000f0000,v80,v1)],[],[]),
([v8,0xaaa0fff0aaa0fff0,v0,v6,v3,v4],[(v13,v0,v1),(v7,v2,v3),(0xaaa0fff0aaa0fff0,v13,v7),(v8,v2,v1)],[],[]),
([v8,v0,v6,v25,v7,v4],[(v7,v3,v2),(v16,v3,v4),(v25,v16,v1),(v8,v2,v1)],[],[(0,4)]),
([v53,v0,v6,v7,v1,v4],[(v7,v2,v3),(v30,v2,v4),(v23,v3,v1),(v53,v30,v23)],[],[(0,5)]),
([v8,v16,v0,v6,v7,v9],[(v7,v2,v3),(v8,v2,v1),(v16,v3,v4),(v9,v1,v4)],[],[(0,6),(1,5)]),
([v56,v8,v0,v6,v3,v4],[(v7,v2,v3),(v8,v2,v1),(v9,v1,v4),(v56,v7,v9)],[],[(0,6)]),
([v0,v6,v3,v34,v28,v4],[(v7,v2,v3),(v28,v7,v1),(v21,v28,v1),(v34,v21,v2)],[],[]),
([v0,v6,v37,v34,v1,v4],[(v7,v2,v3),(v21,v7,v1),(v34,v21,v2),(v37,v21,v3)],[],[]),
([v0,v6,v3,v50,v1,v4],[(v7,v2,v3),(v21,v7,v1),(v81,v21,v4),(v50,v81,v2)],[],[]),
([0x3333333033303330,v0,v3,v2,v1,v4],[(v7,v3,v2),(v9,v1,v4),(v82,v7,v9),(0x3333333033303330,v6,v82)],[],[]),
([v0,v6,v3,0xffafff00ffaaff00,v1,v4],[(v16,v3,v4),(0xafafafafaaaaaaaa,v16,v0),(0xafaf0000aaaa0000,0xafafafafaaaaaaaa,v1),(0xffafff00ffaaff00,0xafaf0000aaaa0000,v2)],[],[]),
([v0,v6,v25,v3,v50,v4],[(v23,v3,v1),(v33,v23,v4),(v50,v33,v2),(v25,v33,v1)],[],[]),
([v0,v6,v83,v1,v39,v4],[(v8,v2,v1),(v18,v8,v4),(v83,v18,v3),(v39,v18,v2)],[],[]),
([v0,v6,v25,v2,v47,v4],[(v23,v3,v1),(v33,v23,v4),(v47,v33,v3),(v25,v33,v1)],[],[]),
([v0,v6,v25,v3,0xf0f0ffff00000000,v2],[(v23,v3,v1),(v33,v23,v4),(v25,v33,v1),(0xf0f0ffff00000000,v33,v4)],[],[]),
([v0,v6,v25,v3,v2,v52],[(v16,v3,v4),(v25,v16,v1),(v8,v2,v1),(v52,v8,v4)],[],[(0,4)]),
([v53,v0,v6,v3,v2,v9],[(v30,v2,v4),(v23,v3,v1),(v53,v30,v23),(v9,v1,v4)],[],[(0,5)])
]

def g6_L6 : Array W6Node := Array.mk [
([v20,v5,v3,v11,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v20,v5,v2)],[0,1,3,4],[(0,0),(0,1)]),
([v5,v3,v10,v2,v17,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v17,v5,v2)],[0,1,2,3],[(0,2),(0,5),(1,5),(2,3),(2,4)]),
([v20,v5,v3,v10,v2,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v20,v5,v2)],[2,3,4],[(0,6),(2,1)]),
([v26,v5,v3,v10,v2,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v26,v5,v1)],[0,2],[(2,7)]),
([v22,v5,v3,v10,v2,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v22,v5,v1)],[0,2],[(0,9),(2,8)]),
([v5,v3,v11,v7,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v7,v2,v3)],[0,1,2,3,5],[(0,1),(0,10),(2,2),(2,11),(2,12),(3,12)]),
([v5,v3,v2,v14,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v14,v10,v2)],[2,3,4],[(0,13),(2,13)]),
([v5,v3,v10,v2,v14,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v14,v10,v2)],[3],[(0,13),(2,14)]),
([v19,v5,v3,v2,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v19,v10,v2)],[2,3,5],[(0,6),(0,13),(2,15)]),
([v19,v5,v3,v10,v2,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v19,v10,v2)],[3,5],[(0,11),(0,13)]),
([v5,v3,v36,v10,v2,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v36,v10,v1)],[0,5],[]),
([v15,v5,v3,v2,v11,v1,v4],[(v5,v0,v6),(v11,v0,v2),(v15,v11,v1)],[0],[(0,16)]),
([v8,v5,v3,v10,v2,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v8,v2,v1)],[0,2],[(0,12),(2,17)]),
([v5,v3,v10,v2,v9,v1,v4],[(v5,v0,v6),(v10,v0,v3),(v9,v1,v4)],[0,1,2],[(0,19),(0,20),(2,18)]),
([v40,v5,v3,v2,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v40,v0,v12)],[2,4],[(0,4),(0,23),(2,21),(2,22)]),
([v40,v5,v3,v12,v2,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v40,v0,v12)],[4],[(0,24),(0,25),(0,26),(0,27),(1,26),(1,27),(2,22)]),
([v20,v0,v5,v3,v17,v1,v4],[(v5,v0,v6),(v17,v5,v2),(v20,v5,v2)],[2,3,4],[(0,22),(0,28),(1,28)]),
([v0,v5,v3,v17,v7,v1,v4],[(v5,v0,v6),(v17,v5,v2),(v7,v2,v3)],[2],[(0,2),(0,29),(0,30),(1,30),(2,23)]),
([v0,v5,v58,v2,v17,v1,v4],[(v5,v0,v6),(v17,v5,v2),(v58,v17,v3)],[3],[(0,32),(0,33),(1,33),(2,24),(2,31),(2,34),(3,34)]),
([v0,v5,v3,v2,v59,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v59,v12,v2)],[0,1],[(0,31),(0,35),(0,36),(1,36),(2,31)]),
([v29,v0,v5,v3,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v29,v12,v2)],[4,5],[(0,37)]),
([v29,v0,v5,v3,v12,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v29,v12,v2)],[3],[(0,25),(0,38),(0,39),(1,38),(1,39)]),
([v29,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v29,v12,v2)],[5],[(0,3),(0,4)]),
([v0,v5,v3,v35,v2,v4],[(v5,v0,v6),(v12,v5,v3),(v35,v12,v1)],[2,4,5],[(2,5),(2,28),(2,30)]),
([v0,v5,v3,v35,v12,v2,v4],[(v5,v0,v6),(v12,v5,v3),(v35,v12,v1)],[0],[(0,26),(0,38),(0,40),(0,41),(2,28),(2,33)]),
([v0,v5,v3,v35,v2,v1,v4],[(v5,v0,v6),(v12,v5,v3),(v35,v12,v1)],[],[]),
([v46,v0,v5,v3,v12,v2,v1],[(v5,v0,v6),(v12,v5,v3),(v46,v12,v4)],[],[(0,27),(0,34),(0,39),(0,41),(0,43),(1,42)]),
([v68,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(v17,v5,v2),(v68,v17,v1)],[1,2],[(0,44),(2,42),(2,45),(3,46)]),
([v0,v5,v3,v54,v2,v1,v4],[(v5,v0,v6),(v20,v5,v2),(v54,v20,v3)],[0,1,2,5],[(0,0),(0,47),(0,48),(1,48)]),
([v64,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(v20,v5,v2),(v64,v20,v3)],[2,4],[(0,1),(2,1)]),
([0xee000000ee0000,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(v20,v5,v2),(0xee000000ee0000,v20,v1)],[],[]),
([v0,v5,v3,v70,v2,v1,v4],[(v5,v0,v6),(v69,v5,v3),(v70,v69,v1)],[5],[(0,49)]),
([v20,v8,v0,v5,v3,v1,v4],[(v5,v0,v6),(v20,v5,v2),(v8,v2,v1)],[0],[(0,50)]),
([v0,v5,v3,0xfefef0f0fefef0f0,v2,v1,v4],[(v5,v0,v6),(v26,v5,v1),(0xfefef0f0fefef0f0,v26,v3)],[2],[(2,7)]),
([v22,v0,v26,v5,v3,v2,v4],[(v5,v0,v6),(v26,v5,v1),(v22,v26,v1)],[0,4],[(0,51)]),
([v0,v71,v5,v3,v2,v1,v4],[(v5,v0,v6),(v26,v5,v1),(v71,v26,v4)],[2,3,4,5],[(0,52),(2,52)]),
([0x11110000ffff0000,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(0xeeeeeeee00000000,v5,v4),(0x11110000ffff0000,0xeeeeeeee00000000,v1)],[],[]),
([v0,v26,v5,v3,v2,v9,v4],[(v5,v0,v6),(v26,v5,v1),(v9,v1,v4)],[1],[(0,53),(0,54)]),
([v49,v5,v3,v2,v1,v4],[(v5,v0,v6),(v22,v5,v1),(v49,v22,v0)],[0,4],[(0,9),(0,51),(0,55),(0,56),(2,9),(2,55),(2,56)]),
([v22,v49,v5,v3,v2,v1,v4],[(v5,v0,v6),(v22,v5,v1),(v49,v22,v0)],[0,4],[(0,51)]),
([v0,v5,v3,0xf1f1f0f0f1f1f0f0,v2,v1,v4],[(v5,v0,v6),(v22,v5,v1),(0xf1f1f0f0f1f1f0f0,v22,v3)],[5],[(0,9),(2,8)]),
([v72,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(v22,v5,v1),(v72,v22,v4)],[],[(0,57)]),
([v0,0xeeee0000ffff0000,v5,v3,v2,v1,v4],[(v5,v0,v6),(0x1111111100000000,v5,v4),(0xeeee0000ffff0000,0x1111111100000000,v1)],[],[]),
([v8,v22,v0,v5,v3,v2,v4],[(v5,v0,v6),(v22,v5,v1),(v8,v2,v1)],[3],[(0,56),(2,58)]),
([v5,v3,v2,v7,v14,v1,v4],[(v5,v0,v6),(v7,v3,v2),(v14,v0,v7)],[2,5],[(0,59),(2,59)]),
([v0,v44,v5,v3,v2,v1,v4],[(v5,v0,v6),(v7,v3,v2),(v44,v5,v7)],[0,1,2,3,4,5],[(0,10),(0,29),(0,60),(1,60),(2,10)]),
([v73,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(v7,v3,v2),(v73,v5,v7)],[],[(0,61)]),
([v8,v0,v5,v3,v7,v1,v4],[(v5,v0,v6),(v7,v2,v3),(v8,v2,v1)],[0,2],[(0,12)]),
([v0,v5,v3,v2,v28,v1,v4],[(v5,v0,v6),(v7,v3,v2),(v28,v7,v1)],[5],[(0,62)]),
([v21,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(v7,v3,v2),(v21,v7,v1)],[],[]),
([v0,v5,v60,v3,v2,v1,v4],[(v5,v0,v6),(v8,v2,v1),(v60,v8,v5)],[0],[(0,50),(0,63)]),
([v0,0xe0e0e0e0eeeeeeee,v5,v3,v2,v1,v4],[(v5,v0,v6),(v16,v3,v4),(0xe0e0e0e0eeeeeeee,v16,v5)],[2],[(1,58)]),
([v0,v5,v3,v37,v2,v1,v4],[(v5,v0,v6),(v8,v2,v1),(v37,v8,v3)],[2],[(2,17)]),
([v18,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(v8,v2,v1),(v18,v8,v4)],[2,5],[(0,64),(2,65)]),
([v0,v5,v25,v3,v2,v1,v4],[(v5,v0,v6),(v16,v3,v4),(v25,v16,v1)],[],[]),
([v8,v0,v5,v3,v2,v9,v4],[(v5,v0,v6),(v8,v2,v1),(v9,v1,v4)],[1,3],[(0,66)]),
([v5,v3,v2,v1,v27,v4],[(v5,v0,v6),(v9,v1,v4),(v27,v0,v9)],[0,1,4,5],[(0,19),(0,53),(0,66),(0,67),(1,53),(1,66),(2,19),(2,66),(2,67),(3,66)]),
([v5,v3,v2,v9,v1,v27,v4],[(v5,v0,v6),(v9,v1,v4),(v27,v0,v9)],[0,1,5],[]),
([v0,v5,v3,v2,v1,v55,v4],[(v5,v0,v6),(v9,v1,v4),(v55,v5,v9)],[0,1,2,3],[(0,54),(0,68),(0,69),(1,54),(2,69)]),
([0xeeeeeeeeeeee,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(v9,v1,v4),(0xeeeeeeeeeeee,v5,v9)],[4],[]),
([v0,v5,v3,v2,v1,v47,v4],[(v5,v0,v6),(v9,v1,v4),(v47,v3,v9)],[5],[(0,19),(2,18)]),
([v41,v6,v3,v11,v7,v1,v4],[(v11,v0,v2),(v7,v2,v3),(v41,v0,v7)],[5],[]),
([v19,v0,v6,v10,v7,v1,v4],[(v10,v0,v3),(v7,v3,v2),(v19,v2,v10)],[3],[(0,11)]),
([v8,v0,v6,v10,v7,v1,v4],[(v10,v0,v3),(v7,v3,v2),(v8,v2,v1)],[0],[(0,12),(0,71),(3,70)]),
([v0,v6,v3,v32,v7,v1,v4],[(v11,v0,v2),(v7,v2,v3),(v32,v11,v1)],[2],[(2,71)]),
([v15,v0,v6,v3,v7,v1,v4],[(v11,v0,v2),(v7,v2,v3),(v15,v11,v1)],[2],[]),
([v41,v6,v3,v2,v14,v1,v4],[(v10,v0,v3),(v14,v10,v2),(v41,v0,v14)],[4],[(0,72),(2,72)]),
([v19,v0,v6,v3,v14,v1,v4],[(v11,v0,v2),(v14,v11,v3),(v19,v2,v14)],[4],[(0,13),(0,72),(0,73)]),
([v0,v6,v3,v2,0xfffa0000fffa0000,v1,v4],[(v10,v0,v3),(v14,v10,v2),(0xfffa0000fffa0000,v14,v1)],[],[]),
([0x5000000050000,v0,v6,v3,v2,v1,v4],[(v10,v0,v3),(v14,v10,v2),(0x5000000050000,v14,v1)],[],[]),
([v41,v6,v3,v10,v2,v1,v4],[(v10,v0,v3),(v14,v10,v2),(v41,v0,v14)],[4,5],[(0,72)]),
([v19,v0,v6,v3,v11,v1,v4],[(v11,v0,v2),(v14,v11,v3),(v19,v2,v14)],[4,5],[(0,14),(0,73)]),
([0xfa000000fa0000,v0,v6,v3,v2,v1,v4],[(v10,v0,v3),(v19,v10,v2),(0xfa000000fa0000,v19,v1)],[1,5],[(3,74)]),
([v0,v6,v3,0xf0f50000f0f50000,v2,v1,v4],[(v11,v0,v2),(v48,v11,v3),(0xf0f50000f0f50000,v48,v1)],[],[]),
([v0,v6,v3,v2,0xfffaf0f0fffaf0f0,v1,v4],[(v11,v0,v2),(v32,v11,v1),(0xfffaf0f0fffaf0f0,v32,v3)],[],[]),
([v15,v0,v6,v3,v2,v32,v4],[(v11,v0,v2),(v32,v11,v1),(v15,v32,v1)],[4],[(0,75)]),
([v0,v6,v3,0xfafa000000000000,v2,v1,v4],[(v10,v0,v3),(v36,v10,v1),(0xfafa000000000000,v36,v4)],[5],[]),
([0x550000ffff0000,v0,v6,v3,v2,v1,v4],[(v11,v0,v2),(0xffaaffaa00000000,v11,v4),(0x550000ffff0000,0xffaaffaa00000000,v1)],[],[]),
([v8,v0,v6,v3,v36,v2,v4],[(v10,v0,v3),(v36,v10,v1),(v8,v2,v1)],[3],[(0,71),(2,76)]),
([v0,v6,v3,v36,v2,v9,v4],[(v10,v0,v3),(v36,v10,v1),(v9,v1,v4)],[1,5],[(2,77)]),
([v15,v31,v6,v3,v2,v1,v4],[(v11,v0,v2),(v15,v11,v1),(v31,v15,v0)],[4],[(0,75),(0,78)]),
([v0,v6,v3,0xf0f5f0f0f0f5f0f0,v2,v1,v4],[(v11,v0,v2),(v15,v11,v1),(0xf0f5f0f0f0f5f0f0,v15,v3)],[],[]),
([v15,v0,v6,v3,v38,v1,v4],[(v11,v0,v2),(v15,v11,v1),(v38,v15,v2)],[4],[(0,78)]),
([0x55000000000000,v0,v6,v3,v2,v1,v4],[(v11,v0,v2),(v15,v11,v1),(0x55000000000000,v15,v4)],[2],[(2,79)]),
([v0,v6,v3,0xfafa0000ffff0000,v2,v1,v4],[(v10,v0,v3),(0x505050500000000,v10,v4),(0xfafa0000ffff0000,0x505050500000000,v1)],[],[]),
([v31,v6,v3,v2,v11,v1,v4],[(v11,v0,v2),(v15,v11,v1),(v31,v15,v0)],[4,5],[(0,75)]),
([v0,v6,v3,v38,v11,v1,v4],[(v11,v0,v2),(v15,v11,v1),(v38,v15,v2)],[4,5],[(0,16)]),
([v0,v6,v3,v34,v11,v1,v4],[(v11,v0,v2),(v23,v3,v1),(v34,v23,v2)],[5],[(0,17)]),
([v0,v6,v3,0xfafffafafafffafa,v2,v1,v4],[(v10,v0,v3),(v8,v2,v1),(0xfafffafafafffafa,v8,v10)],[1,3],[(1,80)]),
([v0,v6,v77,v3,v2,v1,v4],[(v11,v0,v2),(v16,v3,v4),(v77,v16,v11)],[],[(0,70)]),
([v0,v6,v3,v11,v1,v39,v4],[(v11,v0,v2),(v9,v1,v4),(v39,v2,v9)],[5],[(0,18),(0,77),(1,77)]),
([v0,v6,v3,v2,v1,v66,v4],[(v10,v0,v3),(v9,v1,v4),(v66,v10,v9)],[0,1],[(0,19)]),
([0xfafafafafafa,v0,v6,v3,v2,v1,v4],[(v10,v0,v3),(v9,v1,v4),(0xfafafafafafa,v10,v9)],[],[(0,20)]),
([v0,v6,v3,v2,v79,v1,v4],[(v13,v0,v1),(v51,v13,v3),(v79,v51,v2)],[4],[(0,81)]),
([0xf500f000f500f0,v0,v6,v3,v2,v1,v4],[(v13,v0,v1),(v51,v13,v3),(0xf500f000f500f0,v51,v2)],[0],[]),
([v0,v6,v3,0xf5f50000f0f00000,v2,v1,v4],[(v43,v0,v4),(0xf5f5f5f5f0f0f0f0,v43,v3),(0xf5f50000f0f00000,0xf5f5f5f5f0f0f0f0,v1)],[],[]),
([0xaa000000ff0000,v0,v6,v3,v2,v1,v4],[(v43,v0,v4),(0xff55ff55ff00ff00,v43,v2),(0xaa000000ff0000,0xff55ff55ff00ff00,v1)],[5],[]),
([v8,v13,v0,v6,v3,v38,v4],[(v13,v0,v1),(v38,v13,v2),(v8,v2,v1)],[3],[]),
([v13,v31,v6,v3,v2,v1,v4],[(v13,v0,v1),(v15,v13,v2),(v31,v15,v0)],[0,4,5],[(0,78)]),
([v13,v0,v6,v3,v36,v2,v4],[(v13,v0,v1),(v78,v13,v3),(v36,v78,v1)],[4,5],[(2,82)]),
([v24,v6,v3,v2,v1,v27,v4],[(v13,v0,v1),(v24,v13,v4),(v27,v24,v0)],[0,4],[(0,83),(1,83)]),
([v0,v6,v3,0xf5f5f0f0f0f0f0f0,v2,v1,v4],[(v13,v0,v1),(v24,v13,v4),(0xf5f5f0f0f0f0f0f0,v24,v3)],[],[]),
([v24,v42,v0,v6,v3,v2,v4],[(v13,v0,v1),(v24,v13,v4),(v42,v24,v1)],[0,4],[(0,83),(0,84)]),
([v8,v24,v0,v6,v3,v2,v4],[(v13,v0,v1),(v24,v13,v4),(v8,v2,v1)],[1,3],[]),
([v13,v6,v3,v2,v1,v27,v4],[(v13,v0,v1),(v24,v13,v4),(v27,v24,v0)],[0,4,5],[(1,83)]),
([v13,v42,v0,v6,v3,v2,v4],[(v13,v0,v1),(v24,v13,v4),(v42,v24,v1)],[4,5],[(0,84)]),
([v0,v6,v3,0xfafaf0f0fffff0f0,v2,v1,v4],[(v43,v0,v4),(v42,v43,v1),(0xfafaf0f0fffff0f0,v42,v3)],[],[]),
([v8,v0,v61,v6,v3,v2,v4],[(v13,v0,v1),(v61,v13,v4),(v8,v2,v1)],[],[]),
([0x5550000055500000,v0,v6,v3,v2,v1,v4],[(v13,v0,v1),(v7,v3,v2),(0x5550000055500000,v13,v7)],[],[]),
([v80,v0,v6,v3,v2,v1,v4],[(v43,v0,v4),(v7,v3,v2),(v80,v43,v7)],[0,2,3,5],[(0,85),(1,86),(3,86)]),
([v8,v13,v0,v6,v3,v7,v4],[(v13,v0,v1),(v7,v2,v3),(v8,v2,v1)],[2],[(0,86)]),
([v21,v13,v0,v6,v3,v2,v4],[(v13,v0,v1),(v7,v3,v2),(v21,v7,v1)],[5],[]),
([v8,v13,v31,v6,v3,v2,v4],[(v13,v0,v1),(v8,v2,v1),(v31,v8,v0)],[0,5],[]),
([v13,v0,v6,v3,v37,v2,v4],[(v13,v0,v1),(v8,v2,v1),(v37,v8,v3)],[2],[]),
([0x55ff00ff55550000,v0,v6,v3,v2,v1,v4],[(v13,v0,v1),(v30,v2,v4),(0x55ff00ff55550000,v30,v13)],[3],[]),
([0x5050000055550000,v0,v6,v3,v2,v1,v4],[(v13,v0,v1),(v16,v3,v4),(0x5050000055550000,v16,v13)],[],[]),
([v13,v0,v6,v25,v3,v2,v4],[(v13,v0,v1),(v16,v3,v4),(v25,v16,v1)],[5],[]),
([v19,v0,v6,v3,v7,v1,v4],[(v7,v2,v3),(v14,v0,v7),(v19,v2,v14)],[2,4],[(0,59),(0,72)]),
([v0,0xaaaf0000aaaf0000,v6,v3,v2,v1,v4],[(v7,v3,v2),(v41,v0,v7),(0xaaaf0000aaaf0000,v41,v1)],[5],[]),
([v0,v31,v6,v3,v7,v1,v4],[(v7,v2,v3),(v8,v2,v1),(v31,v8,v0)],[2],[]),
([v8,v0,v6,v37,v7,v1,v4],[(v7,v2,v3),(v8,v2,v1),(v37,v8,v3)],[2,3],[]),
([v18,v0,v6,v3,v7,v1,v4],[(v7,v2,v3),(v8,v2,v1),(v18,v8,v4)],[2],[]),
([v0,v6,v25,v2,v7,v1,v4],[(v7,v3,v2),(v16,v3,v4),(v25,v16,v1)],[3],[(0,87)]),
([v8,v16,v0,v6,v7,v1,v4],[(v7,v2,v3),(v8,v2,v1),(v16,v3,v4)],[],[(0,87),(0,89),(1,88),(3,87)]),
([v8,v0,v6,v3,v28,v7,v4],[(v7,v2,v3),(v8,v2,v1),(v28,v7,v1)],[0],[]),
([v8,v0,v6,v3,v7,v9,v4],[(v7,v2,v3),(v8,v2,v1),(v9,v1,v4)],[2],[(0,89),(0,90)]),
([v0,v6,v3,v2,v74,v1,v4],[(v7,v3,v2),(v28,v7,v1),(v74,v0,v28)],[],[(0,62)]),
([v21,v0,v6,v3,v2,v28,v4],[(v7,v3,v2),(v28,v7,v1),(v21,v28,v1)],[4],[(2,91)]),
([v0,v6,v3,v2,0xfff0000000000000,v1,v4],[(v7,v3,v2),(v28,v7,v1),(0xfff0000000000000,v28,v4)],[],[]),
([0xf0000ffff0000,v0,v6,v3,v2,v1,v4],[(v7,v3,v2),(0xfff0fff000000000,v7,v4),(0xf0000ffff0000,0xfff0fff000000000,v1)],[],[]),
([v0,0xaaafaaaaaaafaaaa,v6,v3,v2,v1,v4],[(v7,v3,v2),(v21,v7,v1),(0xaaafaaaaaaafaaaa,v21,v0)],[],[]),
([v21,v0,v6,v3,v34,v1,v4],[(v7,v2,v3),(v21,v7,v1),(v34,v21,v2)],[4],[(0,92)]),
([v81,v0,v6,v3,v2,v1,v4],[(v7,v3,v2),(v21,v7,v1),(v81,v21,v4)],[],[(0,93),(2,93)]),
([v0,v6,v3,v2,0xfff00000ffff0000,v1,v4],[(v7,v3,v2),(0xf000f00000000,v7,v4),(0xfff00000ffff0000,0xf000f00000000,v1)],[],[]),
([v21,v0,v6,v3,v2,v9,v4],[(v7,v3,v2),(v21,v7,v1),(v9,v1,v4)],[1],[]),
([v0,v6,v3,v34,v7,v1,v4],[(v7,v2,v3),(v21,v7,v1),(v34,v21,v2)],[2,4],[]),
([v0,v6,v3,v2,v1,v82,v4],[(v7,v3,v2),(v9,v1,v4),(v82,v7,v9)],[2,4],[(0,94)]),
([v56,v0,v6,v3,v2,v1,v4],[(v7,v3,v2),(v9,v1,v4),(v56,v7,v9)],[0,1,2,3],[(0,90),(1,90),(2,90),(3,90)]),
([0xaf00aa00af00aa,v0,v6,v3,v2,v1,v4],[(v23,v3,v1),(0xafafaaaaafafaaaa,v23,v0),(0xaf00aa00af00aa,0xafafaaaaafafaaaa,v2)],[],[]),
([v0,0xaaff0000aaaa0000,v6,v3,v2,v1,v4],[(v30,v2,v4),(0xaaffaaffaaaaaaaa,v30,v0),(0xaaff0000aaaa0000,0xaaffaaffaaaaaaaa,v1)],[2,5],[(2,95)]),
([v8,v0,v6,v3,v38,v1,v4],[(v8,v2,v1),(v15,v8,v0),(v38,v15,v2)],[0,4],[(0,78)]),
([v8,v0,v6,v3,v2,v32,v4],[(v8,v2,v1),(v15,v8,v0),(v32,v15,v1)],[0,4],[(0,75)]),
([0x5055505050555050,v0,v6,v3,v2,v1,v4],[(v8,v2,v1),(v37,v8,v3),(0x5055505050555050,v0,v37)],[],[]),
([v0,v6,v3,0xf0ff0000f0f00000,v2,v1,v4],[(v30,v2,v4),(0xf0fff0fff0f0f0f0,v30,v3),(0xf0ff0000f0f00000,0xf0fff0fff0f0f0f0,v1)],[0],[]),
([0xf0000000ff0000,v0,v6,v3,v2,v1,v4],[(v16,v3,v4),(0xff0fff0fff00ff00,v16,v2),(0xf0000000ff0000,0xff0fff0fff00ff00,v1)],[2],[]),
([v0,v6,v3,v37,v2,v9,v4],[(v8,v2,v1),(v37,v8,v3),(v9,v1,v4)],[1,2],[]),
([v8,v0,v6,v3,v34,v1,v4],[(v8,v2,v1),(v21,v8,v3),(v34,v21,v2)],[0,4],[(0,92)]),
([v8,v0,v6,v3,v2,v28,v4],[(v8,v2,v1),(v21,v8,v3),(v28,v21,v1)],[0,4],[(2,91)]),
([v0,v75,v6,v3,v2,v1,v4],[(v8,v2,v1),(v18,v8,v4),(v75,v18,v0)],[],[(0,64)]),
([v0,v6,v3,v50,v1,v4],[(v23,v3,v1),(v33,v23,v4),(v50,v33,v2)],[4],[(0,65)]),
([v18,v0,v6,v62,v2,v1,v4],[(v8,v2,v1),(v18,v8,v4),(v62,v18,v3)],[2],[(2,96),(3,96)]),
([v0,v6,v3,v62,v2,v1,v4],[(v8,v2,v1),(v18,v8,v4),(v62,v18,v3)],[],[]),
([v18,v0,v6,v83,v2,v1,v4],[(v8,v2,v1),(v18,v8,v4),(v83,v18,v3)],[],[(0,97),(2,93)]),
([v18,v0,v6,v3,v1,v39,v4],[(v8,v2,v1),(v18,v8,v4),(v39,v18,v2)],[4],[(0,97),(2,98),(3,98)]),
([v18,v0,v6,v3,v63,v2,v4],[(v8,v2,v1),(v18,v8,v4),(v63,v18,v1)],[4],[(2,96),(2,98),(2,99)]),
([v8,v0,v6,v62,v2,v1,v4],[(v8,v2,v1),(v18,v8,v4),(v62,v18,v3)],[0,1],[(3,96)]),
([v8,v0,v6,v3,v1,v39,v4],[(v8,v2,v1),(v18,v8,v4),(v39,v18,v2)],[0,4],[(3,98)]),
([v8,v0,v6,v3,v63,v2,v4],[(v8,v2,v1),(v18,v8,v4),(v63,v18,v1)],[0,4],[(2,99)]),
([v0,v6,v3,0xfafaaaaaffffaaaa,v2,v1,v4],[(v16,v3,v4),(v25,v16,v1),(0xfafaaaaaffffaaaa,v0,v25)],[0],[]),
([v0,v6,v3,v2,0xfff0f0f0fffff0f0,v1,v4],[(v30,v2,v4),(v63,v30,v1),(0xfff0f0f0fffff0f0,v63,v3)],[],[]),
([v8,v0,v6,v25,v3,v2,v4],[(v16,v3,v4),(v25,v16,v1),(v8,v2,v1)],[3],[(0,87),(0,100)]),
([v8,v0,v6,v3,v2,v52,v9],[(v8,v2,v1),(v52,v8,v4),(v9,v1,v4)],[1],[]),
([v53,v0,v6,v3,v2,v1,v4],[(v30,v2,v4),(v23,v3,v1),(v53,v30,v23)],[],[(0,88),(0,101)]),
([v8,v16,v0,v6,v3,v2,v9],[(v8,v2,v1),(v16,v3,v4),(v9,v1,v4)],[0,1,2,3],[(0,89),(1,101)]),
([v8,v0,v6,v3,v2,v27,v4],[(v8,v2,v1),(v9,v1,v4),(v27,v0,v9)],[1,5],[(0,66)]),
([v8,v0,v6,v3,v9,v39,v4],[(v8,v2,v1),(v9,v1,v4),(v39,v2,v9)],[3],[]),
([v76,v0,v6,v3,v2,v1,v4],[(v9,v1,v4),(v27,v0,v9),(v76,v2,v27)],[],[(0,67)]),
([v42,v0,v6,v3,v2,v9,v4],[(v9,v1,v4),(v24,v0,v9),(v42,v24,v1)],[0,4],[(0,83)]),
([0x5555505050505050,v0,v6,v3,v2,v1,v4],[(v9,v1,v4),(v47,v3,v9),(0x5555505050505050,v0,v47)],[],[]),
([0xff00f000f000f0,v0,v6,v3,v2,v1,v4],[(v9,v1,v4),(v47,v3,v9),(0xff00f000f000f0,v2,v47)],[0,1,3],[]),
([v0,v6,v3,v50,v9,v1,v4],[(v9,v1,v4),(v33,v3,v9),(v50,v33,v2)],[0],[]),
([v0,v6,v25,v3,v2,v9,v4],[(v9,v1,v4),(v33,v3,v9),(v25,v33,v1)],[0,4],[(0,98)])
]

def g6_L7 : Array W6Node := Array.mk [
([v5,v3,v10,v2,v1,v4],[(v5,v0,v6),(v10,v0,v3)],[0,1,2,3,4,5],[(0,1),(0,2),(0,3),(0,4),(0,6),(0,7),(0,8),(0,9),(0,10),(0,12),(0,13),(1,3),(1,4),(1,10),(1,12),(2,0),(2,5),(2,11),(3,11)]),
([v0,v5,v3,v12,v2,v1,v4],[(v5,v0,v6),(v12,v5,v3)],[0,1,2,3,4,5],[(0,14),(0,15),(0,19),(0,20),(0,21),(0,22),(0,23),(0,24),(0,25),(0,26),(1,23),(1,24),(1,25),(1,26),(2,1),(2,16),(2,17),(2,18),(2,27),(3,27)]),
([v20,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(v20,v5,v2)],[0,1,2,3,4,5],[(0,0),(0,2),(0,16),(0,28),(0,29),(0,30),(0,32),(1,30),(1,32),(2,31),(3,31)]),
([v0,v26,v5,v3,v2,v1,v4],[(v5,v0,v6),(v26,v5,v1)],[0,1,2,3,4,5],[(0,3),(0,30),(0,33),(0,34),(0,35),(0,37),(1,36),(2,3),(2,30),(2,33)]),
([v22,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(v22,v5,v1)],[0,1,2,3,4,5],[(0,4),(0,27),(0,34),(0,38),(0,39),(0,40),(0,41),(0,43),(1,42),(2,4),(2,27),(2,40),(2,43)]),
([v0,v5,v3,v2,v7,v1,v4],[(v5,v0,v6),(v7,v3,v2)],[0,1,2,3,4,5],[(0,5),(0,6),(0,17),(0,19),(0,29),(0,44),(0,45),(0,46),(0,47),(0,48),(0,49),(1,47),(1,48),(1,49),(2,5),(2,17),(2,47),(3,47)]),
([v8,v0,v5,v3,v2,v1,v4],[(v5,v0,v6),(v8,v2,v1)],[0,1,2,3,4,5],[(0,12),(0,27),(0,30),(0,32),(0,43),(0,47),(0,49),(0,50),(0,52),(0,53),(0,55),(3,51),(3,54)]),
([v0,v5,v3,v2,v9,v1,v4],[(v5,v0,v6),(v9,v1,v4)],[0,1,2,3,4,5],[(0,13),(0,35),(0,37),(0,41),(0,53),(0,55),(0,56),(0,57),(0,58),(0,59),(0,60),(1,37),(1,55),(2,13),(2,53),(2,55),(2,60),(3,55)]),
([v0,v6,v3,v11,v7,v1,v4],[(v11,v0,v2),(v7,v2,v3)],[0,1,2,3,4,5],[(0,5),(0,61),(0,64),(0,65),(1,64),(1,65),(2,62),(2,63),(3,63)]),
([v0,v6,v3,v2,v14,v1,v4],[(v10,v0,v3),(v14,v10,v2)],[0,1,2,3,4,5],[(0,6),(0,66),(0,67),(0,68),(0,69),(1,68),(1,69),(2,67)]),
([v0,v6,v3,v10,v2,v14,v1,v4],[(v10,v0,v3),(v14,v10,v2)],[3,5],[(0,7),(0,67),(0,70),(2,71)]),
([v19,v0,v6,v3,v2,v1,v4],[(v10,v0,v3),(v19,v10,v2)],[0,1,2,3,4,5],[(0,8),(0,67),(0,72),(1,72),(2,73),(3,73)]),
([v19,v0,v6,v3,v10,v2,v1,v4],[(v10,v0,v3),(v19,v10,v2)],[3,5],[(0,9),(0,62),(0,67)]),
([v0,v6,v3,v36,v2,v1,v4],[(v10,v0,v3),(v36,v10,v1)],[0,1,2,3,4,5],[(0,72),(0,76),(0,78),(0,79),(2,64),(2,74),(2,75),(3,77)]),
([v0,v6,v3,v36,v10,v2,v1,v4],[(v10,v0,v3),(v36,v10,v1)],[0,5],[(0,10),(2,75)]),
([v15,v0,v6,v3,v2,v1,v4],[(v11,v0,v2),(v15,v11,v1)],[0,1,2,3,4,5],[(0,65),(0,69),(0,75),(0,80),(0,81),(0,82),(0,83),(3,84)]),
([v15,v0,v6,v3,v2,v11,v1,v4],[(v11,v0,v2),(v15,v11,v1)],[0,5],[(0,11),(0,75),(0,85),(0,86)]),
([v8,v0,v6,v3,v10,v2,v1,v4],[(v10,v0,v3),(v8,v2,v1)],[0,2,5],[(0,12),(0,63),(0,69),(0,72),(0,78),(0,88),(2,87),(3,89)]),
([v0,v6,v3,v10,v2,v9,v1,v4],[(v10,v0,v3),(v9,v1,v4)],[0,1,2,5],[(0,13),(0,76),(0,79),(0,91),(0,92),(1,79),(2,83),(2,90)]),
([v0,v6,v3,v51,v2,v1,v4],[(v13,v0,v1),(v51,v13,v3)],[0,1,2,3,4,5],[(0,93),(0,94),(1,95),(2,82),(3,96)]),
([v13,v0,v6,v3,v51,v2,v1,v4],[(v13,v0,v1),(v51,v13,v3)],[2,5],[(2,82),(2,97)]),
([v15,v13,v0,v6,v3,v2,v1,v4],[(v13,v0,v1),(v15,v13,v2)],[0,3,5],[(0,82),(0,98),(2,99)]),
([v24,v0,v6,v3,v2,v1,v4],[(v13,v0,v1),(v24,v13,v4)],[0,1,2,3,4,5],[(0,83),(0,100),(0,101),(0,102),(0,103),(1,102),(1,103),(2,83),(2,101),(2,103),(3,103)]),
([v24,v13,v0,v6,v3,v2,v1,v4],[(v13,v0,v1),(v24,v13,v4)],[0,1,5],[(0,104),(0,105),(1,102)]),
([v42,v0,v6,v3,v2,v1,v4],[(v43,v0,v4),(v42,v43,v1)],[0,1,2,3,4,5],[(0,96),(0,102),(0,106),(1,107),(2,96),(2,106),(3,107)]),
([v13,v0,v61,v6,v3,v2,v1,v4],[(v13,v0,v1),(v61,v13,v4)],[0,1,5],[(1,102)]),
([v13,v0,v6,v3,v2,v7,v1,v4],[(v13,v0,v1),(v7,v3,v2)],[0,2,3,5],[(0,65),(0,69),(0,93),(0,108),(0,110),(0,111),(1,109),(2,65),(2,110)]),
([v8,v13,v0,v6,v3,v2,v4],[(v13,v0,v1),(v8,v2,v1)],[0,1,2,3,4,5],[(0,97),(0,103),(0,107),(0,110),(0,111),(0,112),(0,113)]),
([v8,v43,v0,v6,v3,v2,v1,v4],[(v43,v0,v4),(v8,v2,v1)],[0,1,5],[(0,83),(0,96),(0,103),(1,114),(3,115),(3,116)]),
([v0,v6,v3,v2,v7,v14,v1,v4],[(v7,v3,v2),(v14,v0,v7)],[2,5],[(0,44),(0,66),(0,117),(2,117)]),
([v41,v0,v6,v3,v2,v1,v4],[(v7,v3,v2),(v41,v0,v7)],[0,1,2,3,4,5],[(0,66),(0,108),(0,118),(1,108),(1,118)]),
([v41,v0,v6,v3,v2,v7,v1,v4],[(v7,v3,v2),(v41,v0,v7)],[2,3,5],[(0,61),(0,66),(2,61)]),
([v8,v0,v6,v3,v7,v1,v4],[(v7,v2,v3),(v8,v2,v1)],[0,2,3,4],[(0,47),(0,63),(0,65),(0,110),(0,119),(0,120),(0,121),(0,123),(0,124),(0,125),(3,122)]),
([v0,v6,v3,v2,v28,v1,v4],[(v7,v3,v2),(v28,v7,v1)],[0,1,2,3,4,5],[(0,48),(0,108),(0,126),(0,127),(0,128),(1,129)]),
([v0,v6,v3,v2,v28,v7,v1,v4],[(v7,v3,v2),(v28,v7,v1)],[0,2,3],[(0,124),(0,127),(2,124)]),
([v21,v0,v6,v3,v2,v1,v4],[(v7,v3,v2),(v21,v7,v1)],[0,1,2,3,4,5],[(0,49),(0,69),(0,111),(0,127),(0,130),(0,131),(0,132),(0,134),(1,133),(2,131)]),
([v21,v0,v6,v3,v2,v7,v1,v4],[(v7,v3,v2),(v21,v7,v1)],[0,2,3],[(0,127),(0,135),(2,135)]),
([v0,v6,v3,v2,v7,v9,v1,v4],[(v7,v3,v2),(v9,v1,v4)],[0,1,2,3],[(0,121),(0,125),(0,128),(0,132),(0,134),(0,136),(0,137),(1,125),(1,134),(2,121),(2,125),(3,125)]),
([v0,v31,v6,v3,v2,v1,v4],[(v8,v2,v1),(v31,v8,v0)],[0,1,2,3,4,5],[(0,80),(0,88),(0,119),(1,139),(2,138),(3,115)]),
([v8,v0,v31,v6,v3,v2,v1,v4],[(v8,v2,v1),(v31,v8,v0)],[0,3,5],[(0,80),(0,112)]),
([v15,v8,v0,v6,v3,v2,v1,v4],[(v8,v2,v1),(v15,v8,v0)],[0,5],[(0,80),(0,140),(0,141)]),
([v0,v6,v3,v37,v2,v1,v4],[(v8,v2,v1),(v37,v8,v3)],[0,1,2,3,4,5],[(0,52),(0,88),(0,113),(0,142),(0,145),(1,143),(2,87),(2,131),(3,144)]),
([v8,v0,v6,v3,v37,v2,v1,v4],[(v8,v2,v1),(v37,v8,v3)],[0,2,3],[(0,120),(2,131)]),
([v21,v8,v0,v6,v3,v2,v1,v4],[(v8,v2,v1),(v21,v8,v3)],[0,2,3],[(0,146),(0,147),(2,131)]),
([v18,v0,v6,v3,v2,v1,v4],[(v8,v2,v1),(v18,v8,v4)],[0,1,2,3,4,5],[(0,53),(0,83),(0,121),(0,132),(0,148),(0,150),(0,151),(0,152),(0,153),(0,154),(1,154),(2,149)]),
([v18,v8,v0,v6,v3,v2,v1,v4],[(v8,v2,v1),(v18,v8,v4)],[0,1,2],[(0,155),(0,156),(0,157),(1,154)]),
([v0,v6,v25,v3,v2,v1,v4],[(v16,v3,v4),(v25,v16,v1)],[0,1,2,3,4,5],[(0,54),(0,115),(0,116),(0,122),(0,144),(0,158),(0,160),(2,154),(2,159)]),
([v8,v0,v6,v3,v2,v52,v1,v4],[(v8,v2,v1),(v52,v8,v4)],[0,1,3],[(0,161),(1,154)]),
([v8,v16,v0,v6,v3,v2,v1,v4],[(v8,v2,v1),(v16,v3,v4)],[0,1],[(0,123),(0,132),(0,144),(0,160),(0,163),(1,162),(3,144),(3,160)]),
([v8,v0,v6,v3,v2,v9,v4],[(v8,v2,v1),(v9,v1,v4)],[0,1,2,3,4,5],[(0,55),(0,103),(0,125),(0,134),(0,145),(0,161),(0,163),(0,164),(0,165)]),
([v0,v6,v3,v2,v1,v27,v4],[(v9,v1,v4),(v27,v0,v9)],[0,1,2,3,4,5],[(0,56),(0,91),(0,100),(0,164),(0,166),(1,164),(2,91),(2,164),(2,166),(3,164)]),
([v0,v6,v3,v2,v9,v1,v27,v4],[(v9,v1,v4),(v27,v0,v9)],[0,1,5],[(0,57),(0,100)]),
([v24,v0,v6,v3,v2,v9,v1,v4],[(v9,v1,v4),(v24,v0,v9)],[0,1,5],[(0,100),(0,167),(1,167)]),
([v0,v6,v3,v2,v1,v47,v4],[(v9,v1,v4),(v47,v3,v9)],[0,1,2,3,4,5],[(0,60),(0,91),(0,136),(0,168),(0,169),(2,90),(2,153)]),
([v0,v6,v3,v2,v9,v1,v47,v4],[(v9,v1,v4),(v47,v3,v9)],[0,1,2],[(2,153),(2,165),(3,165)]),
([v18,v0,v6,v3,v2,v9,v1,v4],[(v9,v1,v4),(v18,v2,v9)],[0,2,3],[(0,153),(2,170),(2,171),(3,171)])
]

def g6_L8 : Array W6Node := Array.mk [
([v0,v5,v3,v2,v1,v4],[(v5,v0,v6)],[0,1,2,3,4,5],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,3),(1,4),(1,6),(2,0),(2,1),(2,2),(2,6),(3,6)]),
([v0,v6,v3,v10,v2,v1,v4],[(v10,v0,v3)],[0,1,2,3,4,5],[(0,0),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,17),(0,18),(1,13),(1,14),(1,17),(2,8),(2,15),(2,16),(3,15),(3,16)]),
([v13,v0,v6,v3,v2,v1,v4],[(v13,v0,v1)],[0,1,2,3,4,5],[(0,15),(0,19),(0,20),(0,21),(0,22),(0,23),(0,25),(0,26),(0,27),(1,24),(1,28),(2,15),(2,19),(2,20),(2,21),(2,27),(3,28)]),
([v0,v6,v3,v2,v7,v1,v4],[(v7,v3,v2)],[0,1,2,3,4,5],[(0,5),(0,8),(0,9),(0,26),(0,29),(0,30),(0,31),(0,32),(0,33),(0,34),(0,35),(0,36),(0,37),(1,26),(1,32),(1,33),(1,34),(1,35),(1,36),(2,8),(2,32),(3,32)]),
([v8,v0,v6,v3,v2,v1,v4],[(v8,v2,v1)],[0,1,2,3,4,5],[(0,6),(0,15),(0,17),(0,27),(0,28),(0,32),(0,35),(0,38),(0,39),(0,40),(0,41),(0,42),(0,43),(0,44),(0,45),(0,47),(0,48),(0,49),(3,46)]),
([v0,v6,v3,v2,v9,v1,v4],[(v9,v1,v4)],[0,1,2,3,4,5],[(0,7),(0,18),(0,22),(0,37),(0,44),(0,49),(0,50),(0,51),(0,52),(0,53),(0,54),(0,55),(1,49),(2,18),(2,44),(2,49),(2,53),(2,54),(2,55),(3,49)])
]

def g6_L9 : Array W6Node := Array.mk [
([v0,v6,v3,v2,v1,v4],[],[0,1,2,3,4,5],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,4),(2,1),(2,4),(3,4)])
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_4_0 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 (Array.mk []) 0 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_4 : ∀ i < g6_L4.size, checkNodeW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 (Array.mk []) i = true := by
  intro i hi
  have hsz : g6_L4.size = 7 := by decide +kernel
  exact checkBlockW6_at g6_chk_4_0 i (Nat.zero_le _) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_0 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_1 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_2 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_3 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_4 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_5 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_6 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 96 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_5 : ∀ i < g6_L5.size, checkNodeW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 i = true := by
  intro i hi
  have hsz : g6_L5.size = 102 := by decide +kernel
  have hi' : i < 102 := hsz ▸ hi
  by_cases h : i < 64
  ·
    by_cases h : i < 32
    ·
      by_cases h : i < 16
      ·
        exact checkBlockW6_at g6_chk_5_0 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_5_1 i (by omega) (by omega)
    ·
      by_cases h : i < 48
      ·
        exact checkBlockW6_at g6_chk_5_2 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_5_3 i (by omega) (by omega)
  ·
    by_cases h : i < 96
    ·
      by_cases h : i < 80
      ·
        exact checkBlockW6_at g6_chk_5_4 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_5_5 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_5_6 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_0 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_1 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_2 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_3 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_4 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_5 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_6 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_7 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_8 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_9 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_10 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 160 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_6 : ∀ i < g6_L6.size, checkNodeW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 i = true := by
  intro i hi
  have hsz : g6_L6.size = 172 := by decide +kernel
  have hi' : i < 172 := hsz ▸ hi
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
      by_cases h : i < 160
      ·
        exact checkBlockW6_at g6_chk_6_9 i (by omega) (by omega)
      ·
        exact checkBlockW6_at g6_chk_6_10 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_0 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_1 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_2 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_3 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 48 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_7 : ∀ i < g6_L7.size, checkNodeW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 i = true := by
  intro i hi
  have hsz : g6_L7.size = 56 := by decide +kernel
  have hi' : i < 56 := hsz ▸ hi
  by_cases h : i < 32
  ·
    by_cases h : i < 16
    ·
      exact checkBlockW6_at g6_chk_7_0 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_7_1 i (by omega) (by omega)
  ·
    by_cases h : i < 48
    ·
      exact checkBlockW6_at g6_chk_7_2 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_7_3 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_0 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_8 : ∀ i < g6_L8.size, checkNodeW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 i = true := by
  intro i hi
  have hsz : g6_L8.size = 6 := by decide +kernel
  exact checkBlockW6_at g6_chk_8_0 i (Nat.zero_le _) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_9_0 : checkBlockW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_9 : ∀ i < g6_L9.size, checkNodeW6 goal6 4 g6_pow 6 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 i = true := by
  intro i hi
  have hsz : g6_L9.size = 1 := by decide +kernel
  exact checkBlockW6_at g6_chk_9_0 i (Nat.zero_le _) (by omega)

theorem g6_L4_sound : ∀ i < g6_L4.size, ¬ live (basicOps 64) goal6 4 (g6_L4[i]?.getD ([], [], [], [])).1.toFinset :=

  level_sound_W6 (by decide) g6_G_valid g6_cof_sound (fun j hj => by simp at hj) g6_chk_4

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

set_option maxRecDepth 100000 in

theorem g6_sublists : rows6.sublists.filter (fun ws => cover 64 jumps6 goal6 ws) = [rows6] := by decide +kernel

theorem g6_top_match : sameSet (rows6.map (actB 64 (g6_pow[0]?.getD []))) (g6_L9[0]?.getD ([], [], [], [])).1 = true := by decide +kernel

theorem g6_no_build : ¬ build (basicOps 64) goal6 9 rows6.toFinset :=

  no_build_of_top g6_G_valid (by decide) g6_sublists g6_top_match (g6_L9_sound 0 (by decide))

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
  Nat.testBit (4277071594 * 2 ^ 32 + 4008373984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
theorem sample6_ok : ∀ k : Fin 64, F (fun i => (rows6.getD i.val 0)[k.val]) = goal6[k.val] := by decide +kernel

def idxs64 : List ℕ := List.range 64
theorem idxs64_spec : idxs64.length = 64 ∧ ∀ idx ∈ idxs64, idx < 64 := by decide
theorem projS64_goal6 : projS 64 idxs64 goal6 = goal6 := by decide +kernel
theorem projS64_rows6_sub : rows6.all (fun w => projS 64 idxs64 w == 0 || rows6.contains (projS 64 idxs64 w)) = true := by decide +kernel

theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) :
    9 < binaryCost gs := by
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
  ⟨.or, [0, 1]⟩,
  ⟨.and, [2, 3]⟩,
  ⟨.or, [7, 6]⟩,
  ⟨.and, [8, 4]⟩,
  ⟨.and, [9, 5]⟩,
  ⟨.or, [10, 0]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.and, [12, 6]⟩,
  ⟨.or, [9, 5]⟩,
  ⟨.and, [14, 11]⟩,
  ⟨.or, [15, 13]⟩
]

theorem wfits : Monotone2 ⟨wg, 16⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 16⟩ (List.ofFn x) = F x := by
  decide +kernel

end PEqualNP.Outside.L_meta_37701_aux

open PEqualNP.Outside.L_meta_37701_aux in
theorem PEqualNP.Outside.L_meta_37701 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4008373984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4008373984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
    have hl : (⟨wg, 16⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = 11 := rfl
    exact ⟨⟨wg, 16⟩, wfits, by omega, weval⟩
  · refine ⟨C, fun g hg => ⟨?_, (hfan g hg).2⟩, hsz, hev⟩
    have hf := (hfan g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf ⊢
    rcases hf with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
