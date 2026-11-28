import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37503_aux

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

def goal6 : BitVec 64 := 0xfeeaeeeaeeeae8e8

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

def b4_0_goal : BitVec 16 := 0xeee8
def b4_0_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_0_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_0_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_0_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_0_s2 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_0_p2 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_0_s3 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_0_p3 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_0_idx : Array (List ℕ) := Array.mk [b4_0_s0,b4_0_s1,b4_0_s2,b4_0_s3]
def b4_0_pow : Array (List ℕ) := Array.mk [b4_0_p0,b4_0_p1,b4_0_p2,b4_0_p3]
def b4_0_inv : Array ℕ := Array.mk [0,1,2,3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_G_valid : (List.range 4).all (symValid 16 4 b4_0_idx b4_0_pow b4_0_inv b4_0_goal) = true := by decide +kernel
def b4_0_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfff0],[])
]
def b4_0_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfff0],[]),
([0xaaaa,0xcccc,0xf0f0,0xfff0],[]),
([0xf0,0xaaaa,0xcccc,0xff00],[(0,0)])
]
def b4_0_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,1),(1,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_2_0 : checkBlockP 16 jumps4 b4_0_goal 4 b4_0_pow 2 b4_0_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_2 : ∀ i < b4_0_L2.size, checkNodeP 16 jumps4 b4_0_goal 4 b4_0_pow 2 b4_0_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_0_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_0_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_3_0 : checkBlockP 16 jumps4 b4_0_goal 4 b4_0_pow 3 b4_0_L3 b4_0_L2 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_3 : ∀ i < b4_0_L3.size, checkNodeP 16 jumps4 b4_0_goal 4 b4_0_pow 3 b4_0_L3 b4_0_L2 i = true := by
  intro i hi
  have hsz : b4_0_L3.size = 3 := by decide +kernel
  exact checkBlockP_at b4_0_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_0_chk_4_0 : checkBlockP 16 jumps4 b4_0_goal 4 b4_0_pow 4 b4_0_L4 b4_0_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_0_chk_4 : ∀ i < b4_0_L4.size, checkNodeP 16 jumps4 b4_0_goal 4 b4_0_pow 4 b4_0_L4 b4_0_L3 i = true := by
  intro i hi
  have hsz : b4_0_L4.size = 1 := by decide +kernel
  exact checkBlockP_at b4_0_chk_4_0 i (Nat.zero_le _) (by omega)
theorem b4_0_L2_sound : ∀ i < b4_0_L2.size, ¬ live (basicOps 16) b4_0_goal 2 (b4_0_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid (fun j hj => by simp at hj) b4_0_chk_2
theorem b4_0_L3_sound : ∀ i < b4_0_L3.size, ¬ live (basicOps 16) b4_0_goal 3 (b4_0_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L2_sound b4_0_chk_3
theorem b4_0_L4_sound : ∀ i < b4_0_L4.size, ¬ live (basicOps 16) b4_0_goal 4 (b4_0_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_0_G_valid b4_0_L3_sound b4_0_chk_4
set_option maxRecDepth 100000 in
theorem b4_0_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_0_goal ws) = [rows4] := by decide +kernel
theorem b4_0_top_match : sameSet (rows4.map (actB 16 (b4_0_pow[0]?.getD []))) (b4_0_L4[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_0_no_build : ¬ build (basicOps 16) b4_0_goal 4 rows4.toFinset :=
  no_build_of_top b4_0_G_valid (by decide) b4_0_sublists b4_0_top_match (b4_0_L4_sound 0 (by decide))

def b4_1_goal : BitVec 16 := 0xeaa8
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
([0x55aa,0xcccc,0xf0f0],[]),
([0xff0,0xaaaa,0xcccc],[])
]
def b4_1_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
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
def b4_1_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x8888,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(1,0),(4,1),(5,1)]),
([0xaaaa,0xcccc,0xeeee,0xf0f0,0xff00],[(0,3),(1,3),(2,2),(3,2)]),
([0xaa,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,4)]),
([0x4444,0xaaaa,0xcccc,0xf0f0,0xff00],[(4,4)]),
([0xaaaa,0xc0c0,0xcccc,0xf0f0,0xff00],[(0,5)]),
([0xaaaa,0xcccc,0xf0f0,0xfcfc,0xff00],[(0,5)]),
([0xcc,0xaaaa,0xcccc,0xf0f0,0xff00],[(0,8),(1,6),(4,7)])
]
def b4_1_L5 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,4),(1,5),(1,6),(2,0),(2,1),(2,3),(2,6),(3,0),(3,1),(3,3),(3,6),(4,2),(4,4),(4,5),(4,6),(5,6)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_2_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 2 b4_1_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_2 : ∀ i < b4_1_L2.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 2 b4_1_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_1_L2.size = 2 := by decide +kernel
  exact checkBlockP_at b4_1_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_3_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 3 b4_1_L3 b4_1_L2 0 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_3 : ∀ i < b4_1_L3.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 3 b4_1_L3 b4_1_L2 i = true := by
  intro i hi
  have hsz : b4_1_L3.size = 9 := by decide +kernel
  exact checkBlockP_at b4_1_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_4_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 4 b4_1_L4 b4_1_L3 0 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_4 : ∀ i < b4_1_L4.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 4 b4_1_L4 b4_1_L3 i = true := by
  intro i hi
  have hsz : b4_1_L4.size = 7 := by decide +kernel
  exact checkBlockP_at b4_1_chk_4_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_5_0 : checkBlockP 16 jumps4 b4_1_goal 6 b4_1_pow 5 b4_1_L5 b4_1_L4 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_5 : ∀ i < b4_1_L5.size, checkNodeP 16 jumps4 b4_1_goal 6 b4_1_pow 5 b4_1_L5 b4_1_L4 i = true := by
  intro i hi
  have hsz : b4_1_L5.size = 1 := by decide +kernel
  exact checkBlockP_at b4_1_chk_5_0 i (Nat.zero_le _) (by omega)
theorem b4_1_L2_sound : ∀ i < b4_1_L2.size, ¬ live (basicOps 16) b4_1_goal 2 (b4_1_L2[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid (fun j hj => by simp at hj) b4_1_chk_2
theorem b4_1_L3_sound : ∀ i < b4_1_L3.size, ¬ live (basicOps 16) b4_1_goal 3 (b4_1_L3[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L2_sound b4_1_chk_3
theorem b4_1_L4_sound : ∀ i < b4_1_L4.size, ¬ live (basicOps 16) b4_1_goal 4 (b4_1_L4[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L3_sound b4_1_chk_4
theorem b4_1_L5_sound : ∀ i < b4_1_L5.size, ¬ live (basicOps 16) b4_1_goal 5 (b4_1_L5[i]?.getD ([], [])).1.toFinset :=
  level_sound_P (by decide) b4_1_G_valid b4_1_L4_sound b4_1_chk_5
set_option maxRecDepth 100000 in
theorem b4_1_sublists : rows4.sublists.filter (fun ws => cover 16 jumps4 b4_1_goal ws) = [rows4] := by decide +kernel
theorem b4_1_top_match : sameSet (rows4.map (actB 16 (b4_1_pow[0]?.getD []))) (b4_1_L5[0]?.getD ([], [])).1 = true := by decide +kernel
theorem b4_1_no_build : ¬ build (basicOps 16) b4_1_goal 5 rows4.toFinset :=
  no_build_of_top b4_1_G_valid (by decide) b4_1_sublists b4_1_top_match (b4_1_L5_sound 0 (by decide))

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

def u0 : BitVec 32 := 0xf0f0f0f0
def u1 : BitVec 32 := 0xff00ff00
def u2 : BitVec 32 := 0xffff0000
def u3 : BitVec 32 := 0xaaaaaaaa
def u4 : BitVec 32 := 0xcccccccc
def u5 : BitVec 32 := 0xeeeeeeee
def u6 : BitVec 32 := 0xfff0fff0
def u7 : BitVec 32 := 0xffffff00
def u8 : BitVec 32 := 0xff000000
def u9 : BitVec 32 := 0xfafafafa
def u10 : BitVec 32 := 0xf000f000
def u11 : BitVec 32 := 0xf0f0
def u12 : BitVec 32 := 0xffff00
def u13 : BitVec 32 := 0xfffffff0
def u14 : BitVec 32 := 0xffaaffaa
def u15 : BitVec 32 := 0x30303030
def u16 : BitVec 32 := 0xfff0
def u17 : BitVec 32 := 0xfffff0f0
def u18 : BitVec 32 := 0xffffcccc
def u19 : BitVec 32 := 0xffffaaaa
def u20 : BitVec 32 := 0xfefefefe
def u21 : BitVec 32 := 0xfafa
def u22 : BitVec 32 := 0xfcfcfcfc
def u23 : BitVec 32 := 0xeeee
def u24 : BitVec 32 := 0xff0000
def u25 : BitVec 32 := 0xff00
def u26 : BitVec 32 := 0xf0f0000
def u27 : BitVec 32 := 0xf000f0
def u28 : BitVec 32 := 0x32323232
def u29 : BitVec 32 := 0xfffafffa
def u30 : BitVec 32 := 0x33003300
def u31 : BitVec 32 := 0xffffeeee
def u32 : BitVec 32 := 0xf0f0fff0
def u33 : BitVec 32 := 0xfffff0
def u34 : BitVec 32 := 0x33303330
def u35 : BitVec 32 := 0xf0fffff0
def u36 : BitVec 32 := 0xffccffcc
def u37 : BitVec 32 := 0xeee0eee0
def u38 : BitVec 32 := 0xffeeffee
def u39 : BitVec 32 := 0xf0fff0
def u40 : BitVec 32 := 0xfefe
def u41 : BitVec 32 := 0xffff00f0
def u42 : BitVec 32 := 0xf0f0f00
def u43 : BitVec 32 := 0xfcccfccc
def u44 : BitVec 32 := 0xf000f00
def u45 : BitVec 32 := 0xfff00000
def u46 : BitVec 32 := 0xaaaafafa
def u47 : BitVec 32 := 0x55550000
def u48 : BitVec 32 := 0xfaaafaaa
def u49 : BitVec 32 := 0xf0e0f0e0
def u50 : BitVec 32 := 0xeeee0000
def u51 : BitVec 32 := 0xf00000f0
def u52 : BitVec 32 := 0xff0fff00
def u53 : BitVec 32 := 0xe0e0e0e0
def u54 : BitVec 32 := 0xf0f000
def u55 : BitVec 32 := 0x333300
def u56 : BitVec 32 := 0xff00ff0
def u57 : BitVec 32 := 0xf0f0f000
def u58 : BitVec 32 := 0xfffffafa
def u59 : BitVec 32 := 0x33330000
def u60 : BitVec 32 := 0x55005500
def u61 : BitVec 32 := 0xf0fff0f0
def u62 : BitVec 32 := 0xffffeee0
def u63 : BitVec 32 := 0xffff3030
def u64 : BitVec 32 := 0xaaffffaa
def u65 : BitVec 32 := 0xfffffcfc
def u66 : BitVec 32 := 0xccccfcfc
def u67 : BitVec 32 := 0xffcccccc
def u68 : BitVec 32 := 0xf000fff0
def u69 : BitVec 32 := 0xf000f0f0
def u70 : BitVec 32 := 0xf3f0f3f0
def u71 : BitVec 32 := 0xf0a0f0a0
def u72 : BitVec 32 := 0xbabababa
def u73 : BitVec 32 := 0xfff0f0f0

def c5_0_goal : BitVec 32 := 0xfeeeeee8
def c5_0_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
def c5_0_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_0_s1 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31]
def c5_0_p1 : List ℕ := [1,2,4,8,16,32,64,128,65536,131072,262144,524288,1048576,2097152,4194304,8388608,256,512,1024,2048,4096,8192,16384,32768,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648]
def c5_0_s2 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15,16,17,18,19,24,25,26,27,20,21,22,23,28,29,30,31]
def c5_0_p2 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768,65536,131072,262144,524288,16777216,33554432,67108864,134217728,1048576,2097152,4194304,8388608,268435456,536870912,1073741824,2147483648]
def c5_0_s3 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27,4,5,6,7,12,13,14,15,20,21,22,23,28,29,30,31]
def c5_0_p3 : List ℕ := [1,2,4,8,256,512,1024,2048,65536,131072,262144,524288,16777216,33554432,67108864,134217728,16,32,64,128,4096,8192,16384,32768,1048576,2097152,4194304,8388608,268435456,536870912,1073741824,2147483648]
def c5_0_s4 : List ℕ := [0,1,2,3,16,17,18,19,4,5,6,7,20,21,22,23,8,9,10,11,24,25,26,27,12,13,14,15,28,29,30,31]
def c5_0_p4 : List ℕ := [1,2,4,8,65536,131072,262144,524288,16,32,64,128,1048576,2097152,4194304,8388608,256,512,1024,2048,16777216,33554432,67108864,134217728,4096,8192,16384,32768,268435456,536870912,1073741824,2147483648]
def c5_0_s5 : List ℕ := [0,1,2,3,16,17,18,19,8,9,10,11,24,25,26,27,4,5,6,7,20,21,22,23,12,13,14,15,28,29,30,31]
def c5_0_p5 : List ℕ := [1,2,4,8,65536,131072,262144,524288,256,512,1024,2048,16777216,33554432,67108864,134217728,16,32,64,128,1048576,2097152,4194304,8388608,4096,8192,16384,32768,268435456,536870912,1073741824,2147483648]
def c5_0_s6 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15,16,18,17,19,20,22,21,23,24,26,25,27,28,30,29,31]
def c5_0_p6 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768,65536,262144,131072,524288,1048576,4194304,2097152,8388608,16777216,67108864,33554432,134217728,268435456,1073741824,536870912,2147483648]
def c5_0_s7 : List ℕ := [0,2,1,3,4,6,5,7,16,18,17,19,20,22,21,23,8,10,9,11,12,14,13,15,24,26,25,27,28,30,29,31]
def c5_0_p7 : List ℕ := [1,4,2,8,16,64,32,128,65536,262144,131072,524288,1048576,4194304,2097152,8388608,256,1024,512,2048,4096,16384,8192,32768,16777216,67108864,33554432,134217728,268435456,1073741824,536870912,2147483648]
def c5_0_s8 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15,16,18,17,19,24,26,25,27,20,22,21,23,28,30,29,31]
def c5_0_p8 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768,65536,262144,131072,524288,16777216,67108864,33554432,134217728,1048576,4194304,2097152,8388608,268435456,1073741824,536870912,2147483648]
def c5_0_s9 : List ℕ := [0,2,1,3,8,10,9,11,16,18,17,19,24,26,25,27,4,6,5,7,12,14,13,15,20,22,21,23,28,30,29,31]
def c5_0_p9 : List ℕ := [1,4,2,8,256,1024,512,2048,65536,262144,131072,524288,16777216,67108864,33554432,134217728,16,64,32,128,4096,16384,8192,32768,1048576,4194304,2097152,8388608,268435456,1073741824,536870912,2147483648]
def c5_0_s10 : List ℕ := [0,2,1,3,16,18,17,19,4,6,5,7,20,22,21,23,8,10,9,11,24,26,25,27,12,14,13,15,28,30,29,31]
def c5_0_p10 : List ℕ := [1,4,2,8,65536,262144,131072,524288,16,64,32,128,1048576,4194304,2097152,8388608,256,1024,512,2048,16777216,67108864,33554432,134217728,4096,16384,8192,32768,268435456,1073741824,536870912,2147483648]
def c5_0_s11 : List ℕ := [0,2,1,3,16,18,17,19,8,10,9,11,24,26,25,27,4,6,5,7,20,22,21,23,12,14,13,15,28,30,29,31]
def c5_0_p11 : List ℕ := [1,4,2,8,65536,262144,131072,524288,256,1024,512,2048,16777216,67108864,33554432,134217728,16,64,32,128,1048576,4194304,2097152,8388608,4096,16384,8192,32768,268435456,1073741824,536870912,2147483648]
def c5_0_idx : Array (List ℕ) := Array.mk [c5_0_s0,c5_0_s1,c5_0_s2,c5_0_s3,c5_0_s4,c5_0_s5,c5_0_s6,c5_0_s7,c5_0_s8,c5_0_s9,c5_0_s10,c5_0_s11]
def c5_0_pow : Array (List ℕ) := Array.mk [c5_0_p0,c5_0_p1,c5_0_p2,c5_0_p3,c5_0_p4,c5_0_p5,c5_0_p6,c5_0_p7,c5_0_p8,c5_0_p9,c5_0_p10,c5_0_p11]
def c5_0_inv : Array ℕ := Array.mk [0,1,2,4,3,5,6,7,8,10,9,11]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_G_valid : (List.range 12).all (symValid 32 12 c5_0_idx c5_0_pow c5_0_inv c5_0_goal) = true := by decide +kernel
def c5_0_m0 : BitVec 32 := 0xf0f0f0f
def c5_0_st0 : List (BitVec 32) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]
def c5_0_ix0 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_0 : c5_0_ix0.length = 16 ∧ (∀ idx ∈ c5_0_ix0, idx < 32) ∧ (∀ idx ∈ c5_0_ix0, c5_0_m0.getLsbD idx = true) ∧ projS 16 c5_0_ix0 c5_0_goal = b4_0_goal ∧ c5_0_st0.all (fun w => rows4.contains (projS 16 c5_0_ix0 w)) = true := by decide +kernel
def c5_0_m1 : BitVec 32 := 0x55555555
def c5_0_st1 : List (BitVec 32) := [0x44444444,0x50505050,0x55005500,0x55550000]
def c5_0_ix1 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_1 : c5_0_ix1.length = 16 ∧ (∀ idx ∈ c5_0_ix1, idx < 32) ∧ (∀ idx ∈ c5_0_ix1, c5_0_m1.getLsbD idx = true) ∧ projS 16 c5_0_ix1 c5_0_goal = b4_1_goal ∧ c5_0_st1.all (fun w => rows4.contains (projS 16 c5_0_ix1 w)) = true := by decide +kernel
def c5_0_m2 : BitVec 32 := 0x33333333
def c5_0_st2 : List (BitVec 32) := [0x22222222,0x30303030,0x33003300,0x33330000]
def c5_0_ix2 : List ℕ := [0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_2 : c5_0_ix2.length = 16 ∧ (∀ idx ∈ c5_0_ix2, idx < 32) ∧ (∀ idx ∈ c5_0_ix2, c5_0_m2.getLsbD idx = true) ∧ projS 16 c5_0_ix2 c5_0_goal = b4_1_goal ∧ c5_0_st2.all (fun w => rows4.contains (projS 16 c5_0_ix2 w)) = true := by decide +kernel
def c5_0_m3 : BitVec 32 := 0xffff
def c5_0_st3 : List (BitVec 32) := [0xaaaa,0xcccc,0xf0f0,0xff00]
def c5_0_ix3 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_3 : c5_0_ix3.length = 16 ∧ (∀ idx ∈ c5_0_ix3, idx < 32) ∧ (∀ idx ∈ c5_0_ix3, c5_0_m3.getLsbD idx = true) ∧ projS 16 c5_0_ix3 c5_0_goal = b4_0_goal ∧ c5_0_st3.all (fun w => rows4.contains (projS 16 c5_0_ix3 w)) = true := by decide +kernel
def c5_0_m4 : BitVec 32 := 0xff00ff
def c5_0_st4 : List (BitVec 32) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]
def c5_0_ix4 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23]
set_option maxRecDepth 100000 in
theorem c5_0_cspec_4 : c5_0_ix4.length = 16 ∧ (∀ idx ∈ c5_0_ix4, idx < 32) ∧ (∀ idx ∈ c5_0_ix4, c5_0_m4.getLsbD idx = true) ∧ projS 16 c5_0_ix4 c5_0_goal = b4_0_goal ∧ c5_0_st4.all (fun w => rows4.contains (projS 16 c5_0_ix4 w)) = true := by decide +kernel
def c5_0_cfMasks : Array (BitVec 32) := Array.mk [c5_0_m0,c5_0_m1,c5_0_m2,c5_0_m3,c5_0_m4]
def c5_0_cfB0s : Array ℕ := Array.mk [0,0,0,0,0]
def c5_0_cfStocks : Array (List (BitVec 32)) := Array.mk [c5_0_st0,c5_0_st1,c5_0_st2,c5_0_st3,c5_0_st4]
def c5_0_cfLBs : Array ℕ := Array.mk [5,6,6,5,5]
theorem c5_0_cof_sound (c fuel : ℕ) (hc : c < 5) (hist : List (BitVec 32 × BitVec 32 × BitVec 32)) (nxt : List (BitVec 32)) (hnd : nxt.Nodup) (hchk : checkCofClose32 (c5_0_cfLBs[c]?.getD 0) fuel (c5_0_cfMasks[c]?.getD 0) (c5_0_cfB0s[c]?.getD 0) (c5_0_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 32) c5_0_goal fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix0 c5_0_cspec_0.1 c5_0_cspec_0.2.1 c5_0_m0 c5_0_cspec_0.2.2.1 0 c5_0_st0 b4_0_goal (by decide) c5_0_cspec_0.2.2.2.1 c5_0_cspec_0.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose32_sound_aux c5_0_goal 6 c5_0_ix1 c5_0_cspec_1.1 c5_0_cspec_1.2.1 c5_0_m1 c5_0_cspec_1.2.2.1 0 c5_0_st1 b4_1_goal (by decide) c5_0_cspec_1.2.2.2.1 c5_0_cspec_1.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose32_sound_aux c5_0_goal 6 c5_0_ix2 c5_0_cspec_2.1 c5_0_cspec_2.2.1 c5_0_m2 c5_0_cspec_2.2.2.1 0 c5_0_st2 b4_1_goal (by decide) c5_0_cspec_2.2.2.2.1 c5_0_cspec_2.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix3 c5_0_cspec_3.1 c5_0_cspec_3.2.1 c5_0_m3 c5_0_cspec_3.2.2.1 0 c5_0_st3 b4_0_goal (by decide) c5_0_cspec_3.2.2.2.1 c5_0_cspec_3.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose32_sound_aux c5_0_goal 5 c5_0_ix4 c5_0_cspec_4.1 c5_0_cspec_4.2.1 c5_0_m4 c5_0_cspec_4.2.2.1 0 c5_0_st4 b4_0_goal (by decide) c5_0_cspec_4.2.2.2.1 c5_0_cspec_4.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | c + 5 => omega
def c5_0_L2 : Array W5Node := Array.mk [
([u3,u43,u62],[(u5,u4,u3),(u10,u0,u1),(u43,u4,u10),(u6,u0,u1),(u37,u5,u6),(u62,u37,u2)],[],[]),
([u3,u4,0xf00f0ff0],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u54,u12,u0),(u35,u12,u0),(0xf00f0ff0,u54,u35)],[],[])
]
def c5_0_L3 : Array W5Node := Array.mk [
([u37,u9,u36,u2],[(u5,u4,u3),(u36,u4,u1),(u9,u3,u0),(u6,u0,u1),(u37,u5,u6)],[],[]),
([u5,u0,0xffaacc88,u7],[(u5,u4,u3),(u18,u4,u2),(u14,u3,u1),(u7,u1,u2),(0xffaacc88,u14,u18)],[],[]),
([u3,u4,u49,0xffffee00],[(u5,u3,u4),(0xee00ee00,u5,u1),(0xffffee00,0xee00ee00,u2),(u38,u5,u1),(u49,u0,u38)],[],[]),
([u3,u4,u0,0xffeeee00],[(u5,u3,u4),(u50,u5,u2),(0xffeeff00,u50,u1),(u31,u5,u2),(0xffeeee00,0xffeeff00,u31)],[],[]),
([u3,u4,0xf0e0ffe0,u2],[(u5,u3,u4),(u38,u5,u1),(u25,u1,u2),(u32,u25,u0),(0xf0e0ffe0,u32,u38)],[],[]),
([u3,u4,0xf00ef00e,u2],[(u5,u3,u4),(0xee00ee,u5,u1),(0xf0fef0fe,0xee00ee,u0),(u27,u0,u1),(0xf00ef00e,u27,0xf0fef0fe)],[],[]),
([u3,u37,u43,u2],[(u5,u4,u3),(u10,u0,u1),(u43,u4,u10),(u6,u0,u1),(u37,u5,u6)],[],[(0,0)]),
([u3,u4,u10,u62],[(u5,u3,u4),(u10,u0,u1),(u6,u0,u1),(u37,u5,u6),(u62,u37,u2)],[],[(0,0),(6,0)]),
([u3,u43,u18,u13],[(u18,u4,u2),(u7,u2,u1),(u10,u1,u0),(u43,u4,u10),(u13,u0,u7)],[0],[]),
([u33,u3,u4,u9],[(u9,u3,u0),(u17,u0,u2),(u8,u2,u1),(u13,u1,u17),(u33,u8,u13)],[],[]),
([0xffff30,u3,u4,u0],[(u15,u4,u0),(u63,u15,u2),(u8,u2,u1),(0xffffff30,u1,u63),(0xffff30,u8,0xffffff30)],[],[]),
([u33,u15,u3,u4],[(u15,u4,u0),(u17,u0,u2),(u8,u2,u1),(u13,u1,u17),(u33,u8,u13)],[],[]),
([u3,u64,u4,u35],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u64,u12,u3),(u35,u12,u0)],[],[]),
([u12,u3,u4,0xf0f3f3f0],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u55,u12,u4),(0xf0f3f3f0,u55,u0)],[],[]),
([u12,u3,u4,0xf0a0a0f0],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(0x555500,u12,u3),(0xf0a0a0f0,0x555500,u0)],[],[]),
([u55,u3,u4,u35],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u55,u12,u4),(u35,u12,u0)],[],[]),
([u12,u3,u4,u51],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u54,u12,u0),(u51,u54,u0)],[],[]),
([u54,u3,u4,u35],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u54,u12,u0),(u35,u12,u0)],[],[(0,1)]),
([u3,u4,u51,u35],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u35,u12,u0),(u51,u12,u35)],[],[]),
([u12,u3,u4,u35],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(0xf0f00,u12,u0),(u35,0xf0f00,u0)],[],[]),
([0xff0,u3,u4,0xf00f0000],[(u10,u0,u1),(u6,u0,u1),(u56,u10,u6),(0xff0,u56,u2),(0xf00f0000,u56,u2)],[],[(0,1)]),
([u33,u3,u4,u0],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(0xf0,u0,u7),(u33,0xf0,u12)],[],[]),
([u33,u3,u4,u57],[(u8,u1,u2),(u7,u1,u2),(u57,u7,u0),(u13,u7,u0),(u33,u8,u13)],[],[]),
([0xffff0,u3,u4,u10],[(u10,u0,u1),(u6,u0,u1),(u45,u6,u2),(u13,u6,u2),(0xffff0,u45,u13)],[],[]),
([u16,0xfff0ff0,u3,u4],[(u10,u0,u1),(u6,u0,u1),(u13,u6,u2),(0xfff0ff0,u10,u13),(u16,u2,u13)],[0],[]),
([u16,u3,u4,0xf00ff000],[(u10,u0,u1),(u6,u0,u1),(u16,u6,u2),(0xf0000,u6,u2),(0xf00ff000,0xf0000,u10)],[],[]),
([u16,0xfff00f0,u3,u4],[(u10,u0,u1),(u17,u0,u2),(0xfff00f0,u10,u17),(u13,0xfff00f0,u1),(u16,u2,u13)],[0],[]),
([0xffffff0,u3,u4],[(u44,u1,u0),(u24,u1,u2),(u11,u2,u0),(0xfff0f00,u24,u44),(0xffffff0,u11,0xfff0f00)],[],[]),
([u39,0xffffff0,u3,u4],[(u25,u1,u2),(u27,u1,u0),(u26,u0,u2),(u39,u27,u25),(0xffffff0,u26,u39)],[],[])
]
def c5_0_L4 : Array W5Node := Array.mk [
([u5,u0,u1,u19,u65],[(u5,u3,u4),(u19,u3,u2),(u18,u4,u2),(u65,u0,u18)],[1],[]),
([u21,u5,u22,u1,u2],[(u5,u4,u3),(u22,u4,u0),(u9,u3,u0),(u21,u2,u9)],[],[]),
([u5,u0,u14,u18,u7],[(u5,u4,u3),(u18,u4,u2),(u14,u3,u1),(u7,u1,u2)],[],[(0,1),(4,0)]),
([u5,u0,0xfac8fac8,u1,u2],[(u5,u4,u3),(u36,u4,u1),(u9,u3,u0),(0xfac8fac8,u9,u36)],[1,2],[(3,1)]),
([u3,u5,u0,u36,0xffffee00],[(u5,u4,u3),(u36,u4,u1),(0xee00ee00,u5,u1),(0xffffee00,0xee00ee00,u2)],[],[]),
([u3,u37,u0,u36,u2],[(u5,u4,u3),(u36,u4,u1),(u6,u1,u0),(u37,u5,u6)],[2],[(0,0)]),
([u46,u5,u22,u1,u2],[(u5,u4,u3),(u22,u4,u0),(u11,u0,u2),(u46,u11,u3)],[],[]),
([u3,u5,u0,u52,u18],[(u5,u4,u3),(u18,u4,u2),(u26,u2,u0),(u52,u26,u1)],[],[]),
([u3,u4,u0,0xffeeff00,u31],[(u5,u3,u4),(u50,u5,u2),(0xffeeff00,u50,u1),(u31,u5,u2)],[],[(0,3),(1,2)]),
([0x1111eeee,u3,u4,u0,u1],[(u5,u3,u4),(u50,u5,u2),(u31,u5,u2),(0x1111eeee,u50,u31)],[1],[]),
([u3,u4,u53,0xfe00fe00,u2],[(u5,u3,u4),(u53,u5,u0),(u20,u5,u0),(0xfe00fe00,u20,u1)],[],[(2,2),(3,3)]),
([u28,0x54545454,u0,u1,u2],[(u5,u4,u3),(u20,u5,u0),(u28,u4,u20),(0x54545454,u3,u20)],[],[]),
([u23,0x33332222,u3,u0,u1],[(u5,u4,u3),(u31,u5,u2),(0x33332222,u4,u31),(u23,u2,u31)],[],[]),
([u23,u3,u4,0xf0f0e0e0,u1],[(u5,u3,u4),(u31,u5,u2),(u23,u2,u31),(0xf0f0e0e0,u0,u31)],[],[]),
([u3,u4,0xf0eef0ee,u0,u2],[(u5,u3,u4),(u38,u5,u1),(u44,u1,u0),(0xf0eef0ee,u44,u38)],[],[]),
([u3,u4,u0,u52,u31],[(u5,u3,u4),(u31,u5,u2),(u26,u2,u0),(u52,u26,u1)],[0],[(4,4)]),
([u40,u3,u4,u0,u1],[(u5,u3,u4),(u20,u5,u0),(0xfefe0000,u20,u2),(u40,0xfefe0000,u20)],[],[]),
([u3,u4,u49,u1,0xffee0000],[(u5,u3,u4),(u38,u5,u1),(u49,u38,u0),(0xffee0000,u38,u2)],[],[]),
([u40,u3,u4,u0,0xfe00fe00],[(u5,u3,u4),(u20,u5,u0),(0xfe00fe00,u20,u1),(u40,u20,u2)],[],[]),
([0xfffe,u3,u4,u0,u1],[(u5,u3,u4),(u20,u5,u0),(0xfffefffe,u20,u1),(0xfffe,0xfffefffe,u2)],[],[]),
([u40,0xfe00fe,u3,u4,u0],[(u5,u3,u4),(u20,u5,u0),(u40,u20,u2),(0xfe00fe,u20,u1)],[],[]),
([u11,u3,u4,0xf0f0fefe,u1],[(u5,u3,u4),(u23,u5,u2),(0xf0f0fefe,u23,u0),(u11,u0,u2)],[],[(1,5)]),
([0xf0fe,u3,u4,u0,u1],[(u5,u3,u4),(0xee00ee,u5,u1),(0xf0fef0fe,0xee00ee,u0),(0xf0fe,0xf0fef0fe,u2)],[],[]),
([0xee,u3,u4,u0,u8],[(u5,u3,u4),(u23,u5,u2),(0xee,u23,u1),(u8,u1,u2)],[],[(4,5)]),
([u23,u3,u66,u0,u1],[(u5,u4,u3),(u23,u5,u2),(u11,u0,u2),(u66,u11,u4)],[],[]),
([u23,u3,u4,0xf0f000f0,u1],[(u5,u3,u4),(u23,u5,u2),(u25,u1,u2),(0xf0f000f0,u25,u0)],[],[]),
([u3,u5,u0,u67,u7],[(u5,u4,u3),(u8,u1,u2),(u67,u4,u8),(u7,u1,u2)],[],[(4,6)]),
([u3,u4,u0,0xffeeeeee,u7],[(u5,u3,u4),(u8,u1,u2),(0xffeeeeee,u5,u8),(u7,u1,u2)],[0],[(0,3)]),
([0xfeee,u3,u4,u0,u1],[(u5,u3,u4),(u10,u0,u1),(0xfeeefeee,u5,u10),(0xfeee,0xfeeefeee,u2)],[],[]),
([u3,u4,u37,u10,u2],[(u5,u3,u4),(u10,u0,u1),(u6,u0,u1),(u37,u5,u6)],[],[(0,6),(0,7),(3,3),(6,6)]),
([u12,u3,u4,u5,u0],[(u5,u3,u4),(u8,u1,u2),(u7,u1,u2),(u12,u8,u7)],[1],[]),
([u3,u4,u0,u1,u62],[(u5,u3,u4),(u6,u0,u1),(u37,u5,u6),(u62,u37,u2)],[],[(0,7)]),
([u3,0xaaaafcfc,u4,u0,u1],[(u18,u4,u2),(u47,u3,u2),(u65,u18,u0),(0xaaaafcfc,u47,u65)],[],[]),
([u28,u3,u4,u1,u41],[(u9,u3,u0),(u28,u4,u9),(u27,u0,u1),(u41,u27,u2)],[],[]),
([u3,u4,u0,0xffaacc88,u7],[(u14,u3,u1),(u18,u4,u2),(u7,u1,u2),(0xffaacc88,u14,u18)],[],[(0,1)]),
([u3,u0,u43,u18,u7],[(u18,u4,u2),(u7,u2,u1),(u10,u1,u0),(u43,u4,u10)],[0],[(0,8)]),
([u39,u3,u4,u9,u2],[(u9,u3,u0),(u6,u0,u1),(u8,u1,u2),(u39,u8,u6)],[],[]),
([u3,u4,u10,u19,u13],[(u19,u3,u2),(u7,u2,u1),(u10,u1,u0),(u13,u0,u7)],[0],[(3,9),(6,8)]),
([u3,u4,0xf0a0ffaa,u6,u2],[(u14,u3,u1),(u6,u1,u0),(u26,u0,u2),(0xf0a0ffaa,u26,u14)],[],[]),
([u11,u42,u3,u4,u14],[(u14,u3,u1),(u7,u1,u2),(u11,u2,u0),(u42,u0,u7)],[],[(2,9)]),
([u21,0x55555050,u4,u0,u1],[(u9,u3,u0),(u17,u0,u2),(0x55555050,u3,u17),(u21,u9,u2)],[],[]),
([u3,u4,0xf0a0ffa0,u32,u2],[(u14,u3,u1),(u25,u1,u2),(u32,u25,u0),(0xf0a0ffa0,u32,u14)],[],[]),
([u3,u4,0xf0a0ffa0,u0,u2],[(u14,u3,u1),(u25,u1,u2),(u32,u25,u0),(0xf0a0ffa0,u32,u14)],[],[]),
([u21,u3,u4,u0,u52],[(u9,u3,u0),(u26,u0,u2),(u52,u26,u1),(u21,u9,u2)],[],[]),
([0x33ffcc,u3,u4,u0,u1],[(u36,u4,u1),(0xffcc0000,u36,u2),(0xffffffcc,u2,u36),(0x33ffcc,0xffcc0000,0xffffffcc)],[2],[]),
([u21,0xf0f0a0a,u3,u4,u1],[(u19,u3,u2),(u58,u19,u0),(u21,u2,u58),(0xf0f0a0a,u0,u58)],[],[]),
([0x33333332,u3,u0,u1,u2],[(u9,u3,u0),(u29,u9,u1),(0xfffffffa,u29,u2),(0x33333332,u4,0xfffffffa)],[],[]),
([u21,u3,u4,u61,u1],[(u9,u3,u0),(u21,u9,u2),(u24,u1,u2),(u61,u24,u0)],[],[]),
([u21,u3,u4,u0,0xff05ff00],[(u9,u3,u0),(u21,u9,u2),(0x5050000,u9,u2),(0xff05ff00,0x5050000,u1)],[],[]),
([u3,u0,u22,u67,u7],[(u22,u4,u0),(u8,u1,u2),(u67,u4,u8),(u7,u1,u2)],[0],[(4,8)]),
([0xfafafa,u3,u4,u0,u7],[(u9,u3,u0),(u8,u1,u2),(0xfafafa,u8,u9),(u7,u1,u2)],[],[]),
([u12,u3,u4,u0,u9],[(u9,u3,u0),(u8,u1,u2),(u7,u1,u2),(u12,u8,u7)],[1],[]),
([0x30ff30,u3,u4,u0,u2],[(u15,u4,u0),(0xff30ff30,u15,u1),(u8,u1,u2),(0x30ff30,u8,0xff30ff30)],[],[]),
([u3,u4,u10,0xfff3fff0,u2],[(u59,u4,u2),(0xff33ff00,u59,u1),(u10,u1,u0),(0xfff3fff0,u0,0xff33ff00)],[],[(3,10)]),
([u11,0xf0f0300,u3,u4,u1],[(u30,u4,u1),(0xffff3300,u30,u2),(u11,u2,u0),(0xf0f0300,u0,0xffff3300)],[],[(2,10)]),
([u39,u15,u3,u4,u2],[(u15,u4,u0),(u6,u0,u1),(u8,u1,u2),(u39,u8,u6)],[3],[]),
([u15,u3,u4,u8,u13],[(u15,u4,u0),(u17,u0,u2),(u8,u2,u1),(u13,u1,u17)],[0],[(0,11)]),
([u11,u42,u30,u3,u4],[(u30,u4,u1),(u7,u1,u2),(u11,u2,u0),(u42,u0,u7)],[],[(2,11)]),
([0x3030fff0,u3,u4,u1,u2],[(u15,u4,u0),(u6,u0,u1),(u16,u6,u2),(0x3030fff0,u16,u15)],[],[]),
([0xaaa0fff0,u3,u4,u10,u2],[(u47,u3,u2),(u10,u0,u1),(u6,u0,u1),(0xaaa0fff0,u47,u6)],[3],[]),
([u12,u15,u3,u4,u0],[(u15,u4,u0),(u8,u1,u2),(u7,u1,u2),(u12,u8,u7)],[],[]),
([0x32223222,u3,u4,u6,u2],[(u10,u0,u1),(u48,u3,u10),(0x32223222,u4,u48),(u6,u0,u1)],[],[]),
([u34,u3,u43,u6,u2],[(u10,u0,u1),(u43,u4,u10),(u6,u0,u1),(u34,u4,u6)],[],[]),
([u3,u4,u0,0xffaaaaaa,u13],[(u8,u1,u2),(0xffaaaaaa,u3,u8),(u7,u1,u2),(u13,u0,u7)],[0],[(10,8)]),
([u16,u3,u4,u48,u2],[(u10,u0,u1),(u48,u3,u10),(u6,u0,u1),(u16,u2,u6)],[],[]),
([u55,u3,u4,u0,u7],[(u8,u1,u2),(u67,u4,u8),(u7,u1,u2),(u55,u67,u7)],[0],[]),
([u12,u3,u4,u0,0xffffffaa],[(u8,u1,u2),(u7,u1,u2),(0xffffffaa,u3,u7),(u12,u8,u7)],[],[]),
([0xffffaa,u3,u4,u0,u7],[(u8,u1,u2),(u7,u1,u2),(0xffffffaa,u3,u7),(0xffffaa,u8,0xffffffaa)],[1],[]),
([u12,0x33333300,u3,u4,u0],[(u8,u1,u2),(u7,u1,u2),(0x33333300,u4,u7),(u12,u8,u7)],[],[]),
([u12,u3,u64,u4,u0],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u64,u12,u3)],[1],[(0,12)]),
([u55,u12,u3,u4,u0],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u55,u12,u4)],[2],[(0,13),(0,15),(6,14)]),
([u54,u12,u3,u4,u0],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u54,u12,u0)],[],[(0,16),(0,17)]),
([u12,u3,u4,u35],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u35,u12,u0)],[],[(0,12),(0,15),(0,16),(0,18),(6,12),(6,15)]),
([u12,u3,u4,u0,u35],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u35,u12,u0)],[],[(0,17),(0,18)]),
([0xff0,u56,u3,u4,u2],[(u10,u0,u1),(u6,u0,u1),(u56,u10,u6),(0xff0,u56,u2)],[],[(0,20),(3,19)]),
([u12,u3,u4,u51],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u51,u12,u0)],[],[(0,18),(0,19)]),
([u12,u3,u4,u51,u0],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u51,u12,u0)],[],[(0,18),(4,20)]),
([u3,u64,u4,u0,u7],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u64,u12,u3)],[1],[]),
([u12,u3,u4,u35,u7],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u35,u12,u0)],[0,4],[]),
([u12,u3,u4,u51,u7],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u51,u12,u0)],[],[]),
([u12,u3,u4,u57,u0],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u57,u0,u7)],[],[]),
([u12,u3,u4,u0,u13],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(u13,u0,u7)],[0],[]),
([0xf0,u12,u3,u4,u0],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7),(0xf0,u0,u7)],[],[(0,21)]),
([u16,u56,u3,u4,u2],[(u10,u0,u1),(u6,u0,u1),(u56,u10,u6),(u16,u2,u6)],[0,3],[]),
([u16,u3,u4,u10,u2],[(u10,u0,u1),(u6,u0,u1),(u45,u6,u2),(u16,u45,u6)],[3],[]),
([u3,u4,u10,u45,u13],[(u10,u0,u1),(u6,u0,u1),(u45,u6,u2),(u13,u6,u2)],[0],[(0,23),(3,22)]),
([u33,u3,u4,u0],[(u8,u1,u2),(u7,u1,u2),(u13,u7,u0),(u33,u8,u13)],[4],[(0,9),(0,11),(6,9),(6,11)]),
([u33,u3,u4,u0,u13],[(u8,u1,u2),(u7,u1,u2),(u13,u7,u0),(u33,u8,u13)],[0],[(4,24)]),
([u16,u3,u4,u10,u13],[(u10,u0,u1),(u6,u0,u1),(u13,u6,u2),(u16,u2,u13)],[0],[(0,24)]),
([u33,u3,u4,u0,u7],[(u8,u1,u2),(u7,u1,u2),(u13,u7,u0),(u33,u8,u13)],[4],[(0,22),(4,24)]),
([u3,u4,u68,u2],[(u10,u0,u1),(u6,u0,u1),(u16,u6,u2),(u68,u16,u10)],[],[]),
([u16,u3,u4,u68,u2],[(u10,u0,u1),(u6,u0,u1),(u16,u6,u2),(u68,u16,u10)],[0],[]),
([u3,u4,u10,u2,u13],[(u10,u0,u1),(u6,u0,u1),(u16,u6,u2),(u13,u16,u2)],[0],[(3,21)]),
([u3,u4,u68,u6,u2],[(u10,u0,u1),(u6,u0,u1),(u16,u6,u2),(u68,u16,u10)],[],[]),
([0xf0,u42,u3,u4,u8],[(u8,u1,u2),(u7,u1,u2),(u42,u7,u0),(0xf0,u7,u0)],[],[(4,23),(4,25)]),
([u3,u4,0xf00ff000,u6,u2],[(u10,u0,u1),(u6,u0,u1),(0xf0000,u6,u2),(0xf00ff000,0xf0000,u10)],[0],[(0,25)]),
([u39,u3,u4,u0,u13],[(u8,u1,u2),(u6,u1,u0),(u39,u8,u6),(u13,u39,u2)],[4],[(4,26)]),
([u39,u3,u4,u0,u17],[(u8,u1,u2),(u6,u1,u0),(u39,u8,u6),(u17,u0,u2)],[3],[]),
([u33,u3,u4,u0,u6],[(u8,u1,u2),(u6,u1,u0),(u13,u2,u6),(u33,u8,u13)],[4],[]),
([u16,u3,u4,u10,u17],[(u10,u0,u1),(u17,u0,u2),(u13,u1,u17),(u16,u2,u13)],[],[(0,26)]),
([u16,0xff00f0,u3,u4,u0],[(u17,u0,u2),(u6,u0,u1),(u16,u2,u6),(0xff00f0,u1,u17)],[],[(0,21)]),
([u16,u33,u3,u4,u0],[(u6,u1,u0),(u24,u1,u2),(u16,u2,u6),(u33,u24,u16)],[3],[]),
([u16,u3,u4,u0,u52],[(u6,u0,u1),(u26,u0,u2),(u52,u26,u1),(u16,u2,u6)],[],[]),
([u33,u3,u4,u0,u1],[(u6,u1,u0),(u24,u1,u2),(u16,u2,u6),(u33,u24,u16)],[4],[]),
([0xffff0,u3,u4,u0,u1],[(u6,u0,u1),(u45,u6,u2),(u13,u2,u6),(0xffff0,u45,u13)],[],[(0,23)]),
([u3,u46,u4,u61,u1],[(u11,u0,u2),(u46,u11,u3),(u24,u1,u2),(u61,u24,u0)],[],[]),
([u11,u42,u3,u4,u1],[(u24,u2,u1),(u7,u24,u1),(u11,u2,u0),(u42,u0,u7)],[],[(2,21)]),
([u11,0xfff0f00,u3,u4],[(u44,u1,u0),(u24,u1,u2),(u11,u2,u0),(0xfff0f00,u24,u44)],[0],[(0,27),(5,28)])
]
def c5_0_L5 : Array W5Node := Array.mk [
([u5,u0,u1,u19,u18],[(u5,u4,u3),(u18,u4,u2),(u19,u3,u2)],[1,2,3],[(0,0),(2,0),(3,1),(5,1),(6,0),(8,0),(9,1),(11,1)]),
([u5,u0,u9,u22,u1,u2],[(u5,u4,u3),(u22,u4,u0),(u9,u3,u0)],[0,1,2],[]),
([u28,u5,u0,u9,u1,u2],[(u5,u3,u4),(u9,u3,u0),(u28,u4,u9)],[1,2],[]),
([u5,u0,u9,u1,u36,u2],[(u5,u4,u3),(u36,u4,u1),(u9,u3,u0)],[],[(0,3),(3,2),(4,0),(7,0)]),
([u3,u53,u5,u22,u1,u2],[(u5,u4,u3),(u22,u4,u0),(u53,u5,u0)],[2],[(2,4),(3,4)]),
([u23,u3,u5,u0,u1,u18],[(u5,u4,u3),(u18,u4,u2),(u23,u5,u2)],[2,3],[]),
([u3,u5,u0,u1,u18,u17],[(u5,u4,u3),(u18,u4,u2),(u17,u2,u0)],[],[(1,5),(2,2),(6,0)]),
([u11,u3,u5,u22,u1,u2],[(u5,u4,u3),(u22,u4,u0),(u11,u0,u2)],[],[(0,6),(5,7)]),
([u3,u5,u0,u1,0xfffcfffc,u2],[(u5,u4,u3),(u22,u4,u0),(0xfffcfffc,u22,u1)],[1],[(1,0),(4,0)]),
([u21,u4,u5,u0,u1,u2],[(u5,u3,u4),(u9,u3,u0),(u21,u9,u2)],[2],[(0,1)]),
([u23,u3,u4,u0,u1,u2],[(u5,u3,u4),(u50,u5,u2),(u23,u50,u5)],[],[]),
([u3,u4,u5,u0,u1,0xffffe0e0],[(u5,u3,u4),(u53,u5,u0),(0xffffe0e0,u53,u2)],[0,1],[(2,4),(4,8),(8,4)]),
([0x1010f0f0,u3,u4,u5,u1,u2],[(u5,u3,u4),(u50,u5,u2),(0x1010f0f0,u50,u0)],[1],[]),
([u3,u4,u53,u20,u1,u2],[(u5,u3,u4),(u53,u5,u0),(u20,u5,u0)],[],[(0,10),(1,10),(4,8),(4,9),(5,8)]),
([u28,u3,u0,u20,u1,u2],[(u5,u4,u3),(u20,u5,u0),(u28,u4,u20)],[1],[(0,11),(4,12)]),
([u23,u3,u4,u0,u1,u31],[(u5,u3,u4),(u31,u5,u2),(u23,u2,u31)],[1],[(0,12),(0,13),(2,13),(6,12)]),
([u3,u4,u0,u1,u31,u17],[(u5,u3,u4),(u31,u5,u2),(u17,u2,u0)],[0,4],[]),
([u11,u3,u4,u20,u1,u2],[(u5,u3,u4),(u20,u5,u0),(u11,u0,u2)],[3,4],[(3,14),(5,15)]),
([u3,u4,u49,u1,u38,u2],[(u5,u3,u4),(u38,u5,u1),(u49,u38,u0)],[],[(0,17),(1,13),(2,18),(4,16)]),
([u3,u4,u0,u1,0xfffefffe,u2],[(u5,u3,u4),(u20,u5,u0),(0xfffefffe,u20,u1)],[3],[(0,19),(1,16),(4,16)]),
([u40,u3,u4,u0,u1],[(u5,u3,u4),(u20,u5,u0),(u40,u20,u2)],[],[]),
([u40,u3,u4,u0,u20,u1],[(u5,u3,u4),(u20,u5,u0),(u40,u20,u2)],[3],[(0,18),(0,20)]),
([u40,u3,u4,u0,u1,u2],[(u5,u3,u4),(u20,u5,u0),(u40,u20,u2)],[],[]),
([u28,u3,u5,u0,u1,u2],[(u5,u4,u3),(u20,u5,u0),(u28,u4,u20)],[1],[(4,12)]),
([u3,u4,u5,u49,u1,u2],[(u5,u3,u4),(u38,u5,u1),(u49,u38,u0)],[1],[(1,13),(2,10)]),
([u40,u3,u4,u5,u0,u1],[(u5,u3,u4),(u20,u5,u0),(u40,u20,u2)],[1],[]),
([u3,u4,u0,0xf0f0fefe,u1,u2],[(u5,u3,u4),(u23,u5,u2),(0xf0f0fefe,u23,u0)],[4],[(0,16),(0,21),(1,22)]),
([0xee,u3,u4,u0,u1,u2],[(u5,u3,u4),(u23,u5,u2),(0xee,u23,u1)],[],[(0,23)]),
([u3,u4,u0,u20,u1,u2],[(u5,u3,u4),(0xe0e0e0e,u5,u0),(u20,0xe0e0e0e,u0)],[3,4],[(0,16),(1,16)]),
([u23,u3,u4,0xf0f00000,u0,u1],[(u5,u3,u4),(u23,u5,u2),(0xf0f00000,u0,u2)],[],[(1,14),(2,23)]),
([u23,u11,u3,u4,u0,u1],[(u5,u3,u4),(u23,u5,u2),(u11,u0,u2)],[],[(0,16),(0,21),(0,24),(2,25),(6,24)]),
([u23,0x11110000,u3,u4,u0,u1],[(u5,u3,u4),(u23,u5,u2),(0x11110000,u5,u2)],[1],[(0,9)]),
([u3,0xdcdcdcdc,u5,u0,u1,u2],[(u5,u4,u3),(0x10101010,u5,u0),(0xdcdcdcdc,0x10101010,u4)],[1],[]),
([u3,u5,u0,u43,u1,u2],[(u5,u4,u3),(u10,u0,u1),(u43,u4,u10)],[1,4],[(3,26)]),
([u3,u4,u0,0xfeeefeee,u1,u2],[(u5,u3,u4),(u10,u0,u1),(0xfeeefeee,u5,u10)],[0,3,4],[(0,28),(3,27)]),
([0xeeeeee,u3,u4,u0,u1,u2],[(u5,u3,u4),(u8,u1,u2),(0xeeeeee,u5,u8)],[],[]),
([u3,u4,u5,u10,u6,u2],[(u5,u3,u4),(u10,u0,u1),(u6,u0,u1)],[0,1],[(0,29),(3,23),(3,26),(3,27),(3,30),(9,26)]),
([u3,u4,u37,u0,u1,u2],[(u5,u3,u4),(u6,u0,u1),(u37,u5,u6)],[0,1,2,3,4],[(0,5),(0,29),(0,31),(6,5),(8,5)]),
([0x11101110,u3,u4,u0,u1,u2],[(u5,u3,u4),(u6,u0,u1),(0x11101110,u5,u6)],[],[]),
([u3,u66,u5,u0,u1,u2],[(u5,u4,u3),(u11,u0,u2),(u66,u11,u4)],[1],[(0,24),(6,6)]),
([u3,u4,0xeeeefefe,u0,u1,u2],[(u5,u3,u4),(u11,u0,u2),(0xeeeefefe,u11,u5)],[],[(0,16)]),
([u3,u4,0xe0e0eeee,u0,u1,u2],[(u5,u3,u4),(u26,u2,u0),(0xe0e0eeee,u26,u5)],[0],[]),
([u3,u4,u5,u0,u1,u41],[(u5,u3,u4),(u27,u0,u1),(u41,u27,u2)],[0,1],[(4,7),(4,15),(10,7)]),
([u3,u4,u5,u69,u1,u2],[(u5,u3,u4),(u24,u2,u1),(u69,u24,u0)],[1,4],[(1,25)]),
([u11,u26,u3,u4,u5,u1],[(u5,u3,u4),(u11,u0,u2),(u26,u0,u2)],[1],[(2,30)]),
([u28,u3,u9,u22,u1,u2],[(u22,u4,u0),(u9,u3,u0),(u28,u4,u9)],[0],[]),
([u3,u4,u0,u1,u19,u65],[(u18,u4,u2),(u19,u3,u2),(u65,u0,u18)],[1],[(0,0)]),
([u21,u3,u4,u22,u1,u2],[(u9,u3,u0),(u22,u4,u0),(u21,u2,u9)],[],[(0,1)]),
([u28,u3,u0,u22,u1,u2],[(u22,u4,u0),(u9,u3,u0),(u28,u4,u9)],[1],[(0,11)]),
([u3,0xaaaacccc,u4,u0,u1,u18],[(u18,u4,u2),(u47,u3,u2),(0xaaaacccc,u47,u18)],[2,3],[]),
([u3,u4,u0,u70,u14,u2],[(u14,u3,u1),(u30,u4,u1),(u70,u30,u0)],[1],[]),
([u15,u3,u4,u1,u29,u2],[(u9,u3,u0),(u15,u4,u0),(u29,u9,u1)],[],[(10,32)]),
([u21,u15,u3,u4,u1,u2],[(u9,u3,u0),(u15,u4,u0),(u21,u9,u2)],[],[]),
([u23,u3,u4,u0,u1,u19],[(u19,u3,u2),(u31,u4,u19),(u23,u2,u31)],[1],[(0,12)]),
([u3,u4,u49,u1,u14,u2],[(u14,u3,u1),(u38,u4,u14),(u49,u38,u0)],[1],[]),
([u40,u3,u4,u0,u9,u1],[(u9,u3,u0),(u20,u4,u9),(u40,u20,u2)],[1],[]),
([u3,u4,u0,0xf3f2f3f2,u1,u2],[(u14,u3,u1),(0x33223322,u4,u14),(0xf3f2f3f2,0x33223322,u0)],[],[]),
([0x3232,u3,u4,u0,u1,u2],[(u9,u3,u0),(u28,u4,u9),(0x3232,u28,u2)],[],[]),
([u28,u3,u4,u1,u6,u2],[(u9,u3,u0),(u28,u4,u9),(u6,u0,u1)],[4],[]),
([u11,u28,u3,u4,u1,u2],[(u9,u3,u0),(u28,u4,u9),(u11,u0,u2)],[],[(1,33)]),
([u3,u4,u0,u14,u18,u7],[(u14,u3,u1),(u18,u4,u2),(u7,u1,u2)],[],[(0,2),(0,34)]),
([u3,u4,u0,0xfac8fac8,u1,u2],[(u9,u3,u0),(u36,u4,u1),(0xfac8fac8,u9,u36)],[1,2],[(0,3),(3,34)]),
([u3,u4,u0,u1,u63,u19],[(u19,u3,u2),(u15,u4,u0),(u63,u15,u2)],[1],[]),
([u3,u4,u0,0xfbfafbfa,u1,u2],[(u9,u3,u0),(u30,u4,u1),(0xfbfafbfa,u30,u9)],[],[]),
([0xa8a8fcfc,u3,u4,u0,u1,u2],[(u22,u4,u0),(u47,u3,u2),(0xa8a8fcfc,u47,u22)],[1],[]),
([u15,u3,u4,u1,u19,u17],[(u19,u3,u2),(u15,u4,u0),(u17,u0,u2)],[0],[]),
([u34,u3,u0,u36,u6,u2],[(u36,u4,u1),(u6,u1,u0),(u34,u4,u6)],[2],[]),
([u34,u3,u4,u0,u14,u2],[(u14,u3,u1),(u6,u1,u0),(u34,u4,u6)],[1],[]),
([u3,u4,u10,u0,u19,u7],[(u19,u3,u2),(u7,u2,u1),(u10,u1,u0)],[0],[(0,37),(5,36),(6,35)]),
([u11,u3,u4,u0,u14,u7],[(u14,u3,u1),(u7,u1,u2),(u11,u2,u0)],[0,4],[(0,39),(5,38)]),
([u3,u4,u71,u14,u6,u2],[(u14,u3,u1),(u6,u1,u0),(u71,u0,u14)],[],[]),
([u21,u3,u4,u9,u1,u17],[(u9,u3,u0),(u17,u0,u2),(u21,u2,u9)],[3],[]),
([u3,u4,u0,u1,u19,u13],[(u19,u3,u2),(u17,u2,u0),(u13,u1,u17)],[0,1,4],[(0,37)]),
([u16,u3,u4,u0,u14,u2],[(u14,u3,u1),(u6,u1,u0),(u16,u2,u6)],[0,4],[(5,39)]),
([u34,u3,u0,u22,u1,u2],[(u22,u4,u0),(u6,u0,u1),(u34,u4,u6)],[1],[(7,40)]),
([u21,u3,u4,u0,u1,u17],[(u9,u3,u0),(u17,u0,u2),(u21,u9,u2)],[0,1],[(0,40)]),
([u3,u46,u4,u22,u1,u2],[(u22,u4,u0),(u11,u0,u2),(u46,u11,u3)],[],[(0,6)]),
([u3,u4,0xf0aaf0aa,u0,u14,u2],[(u14,u3,u1),(u44,u1,u0),(0xf0aaf0aa,u44,u14)],[4],[]),
([u3,u4,u0,u52,u19],[(u19,u3,u2),(u26,u2,u0),(u52,u26,u1)],[0,1,3,4],[(0,15),(3,33),(4,41),(6,7)]),
([u3,u4,u0,u32,u14,u2],[(u14,u3,u1),(u25,u1,u2),(u32,u25,u0)],[0],[(0,42)]),
([u3,u4,u0,u1,u19,u17],[(u19,u3,u2),(u26,u2,u0),(u17,u26,u0)],[0,1],[]),
([u11,u3,u4,u9,u1,u7],[(u9,u3,u0),(u11,u0,u2),(u7,u1,u2)],[4],[]),
([u11,u24,u3,u4,u9,u1],[(u9,u3,u0),(u11,u0,u2),(u24,u1,u2)],[],[(1,36)]),
([u3,u66,u0,u1,u2,u18],[(u18,u4,u2),(u11,u2,u0),(u66,u11,u4)],[1,2],[]),
([u3,u4,u0,u9,u1,0xffff0f00],[(u9,u3,u0),(u44,u0,u1),(0xffff0f00,u44,u2)],[0,1,4],[(1,43)]),
([u3,u4,u69,u1,u14,u2],[(u14,u3,u1),(u24,u1,u2),(u69,u24,u0)],[1],[]),
([u3,u4,u0,u1,u29,u2],[(u14,u3,u1),(u27,u1,u0),(u29,u27,u14)],[],[]),
([u11,0xf0f0a0a,u3,u4,u1,u2],[(u19,u3,u2),(u11,u2,u0),(0xf0f0a0a,u0,u19)],[1],[(5,43)]),
([u21,u3,u4,u0,u1,u2],[(u9,u3,u0),(0xfafa0000,u9,u2),(u21,0xfafa0000,u9)],[],[]),
([u3,u4,u71,u1,u29,u2],[(u14,u3,u1),(u71,u14,u0),(u29,u0,u14)],[1],[(11,44)]),
([u34,u3,u0,u1,0xfffcfffc,u2],[(u22,u4,u0),(0xfffcfffc,u22,u1),(u34,u4,0xfffcfffc)],[1],[(7,40),(10,40)]),
([0x33323332,u3,u4,u0,u1,u2],[(u9,u3,u0),(u29,u9,u1),(0x33323332,u4,u29)],[],[]),
([u21,u3,u4,u0,u1,u58],[(u19,u3,u2),(u58,u19,u0),(u21,u2,u58)],[1],[(0,40),(0,45)]),
([u3,u4,u0,u1,u2,0xfffffffa],[(u9,u3,u0),(u29,u9,u1),(0xfffffffa,u29,u2)],[2],[(0,46)]),
([0xfffa,u3,u4,u0,u1,u2],[(u9,u3,u0),(u29,u9,u1),(0xfffa,u29,u2)],[],[]),
([u21,u3,u4,u0,u1,u19],[(u19,u3,u2),(u58,u19,u0),(u21,u2,u58)],[1],[(0,45)]),
([u3,0xaaaafefe,u4,u0,u1,u2],[(u22,u4,u0),(0xfcfc,u22,u2),(0xaaaafefe,0xfcfc,u3)],[1],[]),
([u3,u4,u0,0xf0f0fffa,u1,u2],[(u14,u3,u1),(0xffaa,u14,u2),(0xf0f0fffa,0xffaa,u0)],[4],[]),
([0xfa,u3,u4,u0,u1,u2],[(u9,u3,u0),(u21,u9,u2),(0xfa,u21,u1)],[],[]),
([u21,u3,u4,u0,u1,u7],[(u9,u3,u0),(u21,u9,u2),(u7,u1,u2)],[4],[]),
([u11,0xf0a0f0a,u3,u4,u1,u2],[(u14,u3,u1),(0xf0a0f0a,u14,u0),(u11,u2,u0)],[],[(4,47)]),
([0x3030,0xf0f0c0c,u3,u4,u1,u2],[(u18,u4,u2),(0xf0f0c0c,u18,u0),(0x3030,u18,u0)],[2],[(4,44),(11,48)]),
([u3,u4,u0,u9,u1,0xffff0500],[(u9,u3,u0),(0x5000500,u9,u1),(0xffff0500,0x5000500,u2)],[1,4],[(1,48)]),
([u3,u4,0xf0a0f0f0,u1,u14,u2],[(u14,u3,u1),(0x550000,u14,u2),(0xf0a0f0f0,0x550000,u0)],[1],[]),
([u3,u4,u0,u1,u63,u18],[(u18,u4,u2),(0x3030,u18,u0),(u63,0x3030,u2)],[0,1,2],[]),
([u3,u0,u43,u1,u2,u18],[(u18,u4,u2),(u10,u0,u1),(u43,u4,u10)],[0,3],[(0,35),(2,35),(3,49)]),
([u3,u4,u0,u1,u19,0xfffff000],[(u19,u3,u2),(u10,u0,u1),(0xfffff000,u10,u2)],[1],[]),
([u3,u4,u0,u1,0xfffafafa,u2],[(u9,u3,u0),(u8,u1,u2),(0xfffafafa,u8,u9)],[],[]),
([0xfafafa,u3,u4,u0,u1,u2],[(u9,u3,u0),(u8,u1,u2),(0xfafafa,u8,u9)],[],[(0,50)]),
([u3,u4,u10,u6,u2,u19],[(u19,u3,u2),(u10,u0,u1),(u6,u0,u1)],[0,1,3],[(0,37),(3,50),(3,51),(9,49)]),
([u3,u4,u0,0xfafafa00,u1,u2],[(u9,u3,u0),(u7,u1,u2),(0xfafafa00,u9,u7)],[1],[]),
([0x3330,u3,u4,u0,u1,u2],[(u18,u4,u2),(u6,u0,u1),(0x3330,u18,u6)],[0,4],[]),
([u3,u4,u0,u1,u41,u19],[(u19,u3,u2),(u27,u0,u1),(u41,u27,u2)],[0,1],[(5,47)]),
([u3,u4,u0,0xfafafffa,u1,u2],[(u9,u3,u0),(u25,u1,u2),(0xfafafffa,u25,u9)],[4],[]),
([u3,u4,0xf0a0ffaa,u0,u1,u2],[(u14,u3,u1),(u26,u2,u0),(0xf0a0ffaa,u26,u14)],[1],[(0,38)]),
([u11,u26,u3,u4,u1,u14],[(u14,u3,u1),(u11,u0,u2),(u26,u0,u2)],[1],[(2,51)]),
([0xbaba,u3,u4,u0,u1,u2],[(u15,u4,u0),(u72,u15,u3),(0xbaba,u72,u2)],[],[]),
([u3,u72,u4,u1,u6,u2],[(u15,u4,u0),(u72,u15,u3),(u6,u0,u1)],[4],[]),
([u15,u3,u4,0xf5f0f5f0,u1,u2],[(u60,u3,u1),(0xf5f0f5f0,u60,u0),(u15,u4,u0)],[],[]),
([0x31303130,u3,u4,u0,u1,u2],[(u60,u3,u1),(0xf5f0f5f0,u60,u0),(0x31303130,u4,0xf5f0f5f0)],[],[]),
([u3,u4,u10,u0,0xff33ff00,u2],[(u59,u4,u2),(0xff33ff00,u59,u1),(u10,u1,u0)],[],[(0,53),(5,52)]),
([u11,u3,u4,u0,u1,0xffff3300],[(u30,u4,u1),(0xffff3300,u30,u2),(u11,u2,u0)],[4],[(0,54)]),
([u3,u4,u0,u1,0xfff3fff0,u2],[(u59,u4,u2),(0xf3f3f0f0,u59,u0),(0xfff3fff0,0xf3f3f0f0,u1)],[],[(0,53)]),
([0xf3f0,u3,u4,u0,u1,u2],[(u30,u4,u1),(u70,u30,u0),(0xf3f0,u70,u2)],[0,4],[(5,54)]),
([0x73507350,u3,u4,u0,u1,u2],[(u30,u4,u1),(0x50505050,u3,u0),(0x73507350,u30,0x50505050)],[],[]),
([u15,u60,u3,u4,u6,u2],[(u15,u4,u0),(u60,u3,u1),(u6,u0,u1)],[0],[]),
([u3,0xaaaaf0f0,u4,u0,u1,u17],[(u47,u3,u2),(u17,u2,u0),(0xaaaaf0f0,u47,u17)],[0,3,4],[]),
([u15,0x55505550,u3,u4,u1,u2],[(u15,u4,u0),(u6,u0,u1),(0x55505550,u3,u6)],[],[]),
([u15,u3,u4,u8,u1,u17],[(u15,u4,u0),(u17,u0,u2),(u8,u2,u1)],[0,4],[(0,56),(1,55)]),
([u11,u30,u3,u4,u0,u7],[(u30,u4,u1),(u7,u1,u2),(u11,u2,u0)],[0,4],[(0,57)]),
([u15,u3,u4,u1,u2,u13],[(u15,u4,u0),(u6,u0,u1),(u13,u6,u2)],[0],[(0,56)]),
([u16,u15,u3,u4,u1,u2],[(u15,u4,u0),(u6,u0,u1),(u16,u6,u2)],[0,3],[(0,58),(3,57)]),
([u3,u4,u0,0xf333f000,u1,u2],[(u59,u4,u2),(u10,u0,u1),(0xf333f000,u59,u10)],[],[]),
([u15,u3,u4,u1,u73,u2],[(u15,u4,u0),(u8,u1,u2),(u73,u0,u8)],[],[]),
([u15,u3,u4,u0,u8,u7],[(u15,u4,u0),(u8,u1,u2),(u7,u1,u2)],[0],[(0,56),(0,60),(4,53),(10,59)]),
([0xaaa0fff0,u3,u4,u0,u1,u2],[(u47,u3,u2),(u6,u0,u1),(0xaaa0fff0,u47,u6)],[0,1,3,4],[(0,59)]),
([0x3030ff30,u3,u4,u0,u1,u2],[(u15,u4,u0),(u25,u1,u2),(0x3030ff30,u25,u15)],[0,2],[]),
([u15,u3,u4,u32,u1,u2],[(u15,u4,u0),(u25,u1,u2),(u32,u25,u0)],[0],[]),
([u11,u26,u30,u3,u4,u1],[(u30,u4,u1),(u11,u0,u2),(u26,u0,u2)],[2],[(2,60)]),
([0x32223222,u3,u4,u0,u1,u2],[(u10,u0,u1),(u48,u3,u10),(0x32223222,u4,u48)],[],[(0,61)]),
([u3,u4,u0,0xffaaaaaa,u7],[(u8,u1,u2),(0xffaaaaaa,u3,u8),(u7,u1,u2)],[0,1,4],[(0,27),(0,63),(4,61),(4,64),(6,26),(6,49),(6,65),(10,62)]),
([u3,u4,u0,u48,u2,u7],[(u10,u1,u0),(u48,u3,u10),(u7,u1,u2)],[0,3],[(3,63),(6,35)]),
([0xfaaa,u3,u4,u0,u1,u2],[(u10,u0,u1),(u48,u3,u10),(0xfaaa,u48,u2)],[],[]),
([0x33303030,u3,u4,u0,u1,u2],[(u8,u1,u2),(u73,u8,u0),(0x33303030,u4,u73)],[],[]),
([u3,u4,u10,u6,u29,u2],[(u10,u0,u1),(u6,u0,u1),(u29,u3,u6)],[1],[(3,66),(3,67)]),
([u34,u3,u4,u10,u6,u2],[(u10,u0,u1),(u6,u0,u1),(u34,u4,u6)],[2],[(0,62),(3,65),(3,68)]),
([u12,u3,u4,u0],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7)],[1,2],[(0,30),(0,51),(0,60),(0,69),(0,70),(0,71),(0,72),(0,73),(0,75),(0,76),(4,74),(6,51),(6,60),(6,69),(6,70)]),
([u12,u3,u4,u0,u7],[(u8,u1,u2),(u7,u1,u2),(u12,u8,u7)],[0,1,2,4],[(0,65),(0,66),(0,68),(0,77),(0,78),(0,79),(0,80),(0,81),(0,82),(4,83),(6,65),(6,66),(6,68),(6,77)]),
([u3,u4,u10,u45,u6,u2],[(u10,u0,u1),(u6,u0,u1),(u45,u6,u2)],[0,3],[(0,84),(0,85),(3,80)]),
([u3,u4,u10,u2,u13],[(u10,u0,u1),(u6,u0,u1),(u13,u6,u2)],[0,3],[(0,37),(0,84),(0,88),(3,56),(3,63),(3,86),(3,87),(6,37),(9,56),(9,63)]),
([u3,u4,u10,u6,u2,u13],[(u10,u0,u1),(u6,u0,u1),(u13,u6,u2)],[0],[(0,85),(0,88),(3,81),(3,89)]),
([u16,u3,u4,u10,u2],[(u10,u0,u1),(u6,u0,u1),(u16,u6,u2)],[0,3],[(0,64),(0,88),(0,90),(0,91),(0,92),(6,64)]),
([u16,u3,u4,u10,u6,u2],[(u10,u0,u1),(u6,u0,u1),(u16,u6,u2)],[0,3],[(0,83),(0,88),(0,93),(3,94)]),
([0xf0,u3,u4,u0,u8,u7],[(u8,u1,u2),(u7,u1,u2),(0xf0,u7,u0)],[0],[(0,82),(0,94),(4,92),(4,95)]),
([u39,u3,u4,u0,u2],[(u8,u1,u2),(u6,u1,u0),(u39,u8,u6)],[3,4],[(0,36),(0,55),(0,96),(0,97),(6,36),(6,55)]),
([u39,u3,u4,u0,u6,u2],[(u8,u1,u2),(u6,u1,u0),(u39,u8,u6)],[0,3,4],[(0,96)]),
([u3,u4,u10,u2,u17,u7],[(u10,u1,u0),(u7,u1,u2),(u17,u0,u2)],[0,4],[(3,97),(5,97)]),
([u3,u4,u10,u2,u17,u13],[(u10,u0,u1),(u17,u0,u2),(u13,u1,u17)],[0],[(0,99),(3,96),(3,98)]),
([u3,0xbbbabbba,u4,u0,u1,u2],[(u6,u0,u1),(u34,u4,u6),(0xbbbabbba,u34,u3)],[],[]),
([u3,u4,u0,0xf3f3f3f0,u1,u2],[(u7,u1,u2),(0x33333300,u4,u7),(0xf3f3f3f0,0x33333300,u0)],[],[]),
([u16,u3,u4,u0,u1,u17],[(u17,u0,u2),(u6,u0,u1),(u16,u2,u6)],[0,1,3],[(0,100)]),
([u3,u4,u0,u1,u2,u13],[(u6,u0,u1),(u17,u0,u2),(u13,u6,u17)],[0,4],[]),
([u3,u46,u4,u0,u1,u7],[(u7,u2,u1),(u11,u2,u0),(u46,u11,u3)],[4],[]),
([u11,u42,u3,u4,u1],[(u7,u2,u1),(u11,u2,u0),(u42,u0,u7)],[0],[(0,39),(0,57),(2,86),(4,101),(6,39),(6,57)]),
([u11,u42,u3,u4,u1,u7],[(u7,u2,u1),(u11,u2,u0),(u42,u0,u7)],[0,3],[(4,98)]),
([u3,u4,u0,u1,u41,u7],[(u7,u1,u2),(u27,u1,u0),(u41,u27,u2)],[0,1,4],[(4,102)]),
([u11,u42,u3,u4,u1,u2],[(u7,u2,u1),(u11,u2,u0),(u42,u0,u7)],[0,3],[(4,103),(5,102)]),
([u16,u3,u4,u0,u1,u2],[(u6,u0,u1),(u45,u6,u2),(u16,u45,u6)],[0,3,4],[(0,84)]),
([u3,u4,u57,u1,u2,u13],[(u7,u1,u2),(u57,u7,u0),(u13,u0,u7)],[0],[(4,85),(4,104)]),
([0x33333330,u3,u4,u0,u1,u2],[(u6,u0,u1),(u13,u6,u2),(0x33333330,u4,u13)],[],[]),
([u16,u3,u4,u0,u1,u13],[(u17,u2,u0),(u13,u17,u1),(u16,u2,u13)],[0,1,4],[(0,88),(0,100),(2,100)]),
([u3,0xaaaafffa,u4,u0,u1,u2],[(u6,u0,u1),(u16,u6,u2),(0xaaaafffa,u16,u3)],[],[]),
([u16,u3,u4,u0,0xff00fff0,u2],[(u6,u1,u0),(u16,u6,u2),(0xff00fff0,u16,u1)],[0,3],[]),
([0xf0,u42,u3,u4,u1,u2],[(u7,u1,u2),(u42,u7,u0),(0xf0,u7,u0)],[],[(0,94),(4,102),(4,104),(5,102)]),
([0x22223232,u3,u4,u0,u1,u2],[(u11,u0,u2),(u46,u11,u3),(0x22223232,u46,u4)],[],[]),
([0xaafa,u3,u4,u0,u1,u2],[(u27,u0,u1),(0xaafaaafa,u27,u3),(0xaafa,0xaafaaafa,u2)],[],[]),
([u11,u3,0xafaaafaa,u4,u1,u2],[(u44,u1,u0),(0xafaaafaa,u44,u3),(u11,u2,u0)],[],[(4,105)]),
([u3,u4,u0,u1,u41,0xffffaafa],[(u27,u0,u1),(u41,u27,u2),(0xffffaafa,u3,u41)],[0,1],[(5,47)]),
([0x30303330,u3,u4,u32,u1,u2],[(u25,u1,u2),(u32,u25,u0),(0x30303330,u4,u32)],[0,2,4],[]),
([u11,u3,u4,u61,u1],[(u24,u2,u1),(u61,u24,u0),(u11,u2,u61)],[0,4],[(0,105),(6,105)]),
([u3,u4,u0,u1,u41,u13],[(u27,u0,u1),(u41,u27,u2),(u13,u1,u41)],[0,4],[(4,102)]),
([0x30303330,u3,u4,u0,u1,u2],[(u25,u1,u2),(u32,u25,u0),(0x30303330,u4,u32)],[2],[]),
([u11,u3,u4,u32,u1,u2],[(u25,u1,u2),(u32,u25,u0),(u11,u0,u2)],[0,3,4],[]),
([u34,u3,u4,u0,u1,u2],[(u27,u0,u1),(u6,u27,u1),(u34,u4,u6)],[],[]),
([u11,u3,u4,u0,u1,u7],[(u24,u2,u1),(u7,u24,u1),(u11,u2,u0)],[0,4],[(0,106)]),
([u11,u24,u44,u3,u4],[(u24,u2,u1),(u11,u2,u0),(u44,u0,u1)],[0,3,4],[(0,107),(3,107),(4,107)])
]
def c5_0_L6 : Array W5Node := Array.mk [
([u3,u5,u0,u22,u1,u2],[(u5,u4,u3),(u22,u4,u0)],[0,1,2],[(0,1),(0,4),(0,7),(0,8),(1,7),(1,8),(2,3),(3,3),(4,0),(4,5),(4,6),(5,6),(6,2),(6,9),(7,9)]),
([u3,u4,u53,u5,u0,u1,u2],[(u5,u3,u4),(u53,u5,u0)],[0,1,2],[(0,4),(0,11),(0,13),(1,11),(4,10),(4,12),(5,12),(6,4)]),
([u3,u4,u0,u20,u1,u2],[(u5,u3,u4),(u20,u5,u0)],[1,2,3,4],[(0,14),(0,17),(0,19),(0,20),(0,21),(0,22),(1,17),(1,19),(1,20),(1,21),(1,22),(2,18),(3,18),(4,10),(4,15),(4,16),(5,16),(6,14)]),
([u3,u4,u5,u0,u20,u1,u2],[(u5,u3,u4),(u20,u5,u0)],[0,1],[(0,13),(0,23),(0,25),(1,25),(2,24),(3,24),(4,15),(6,23)]),
([u23,u3,u4,u0,u1,u2],[(u5,u3,u4),(u23,u5,u2)],[0,1,2,4],[(0,15),(0,26),(0,27),(0,29),(0,30),(2,26),(2,27),(2,29),(2,30),(3,28)]),
([u23,u3,u4,u5,u0,u1,u2],[(u5,u3,u4),(u23,u5,u2)],[1,2,3],[(0,5),(0,15),(0,31),(6,5)]),
([0x10101010,u3,u4,u5,u0,u1,u2],[(u5,u3,u4),(0x10101010,u5,u0)],[0,1],[(0,28),(0,32),(4,31),(6,32)]),
([u3,u4,u5,u10,u0,u1,u2],[(u5,u3,u4),(u10,u0,u1)],[0,1,2,4],[(0,33),(0,34),(0,36),(1,29),(3,35),(4,29),(6,33)]),
([u3,u4,u5,u0,u1,u6,u2],[(u5,u3,u4),(u6,u0,u1)],[0,1,2,4],[(0,8),(0,19),(0,36),(0,37),(0,38),(1,6),(1,16),(3,27),(4,6),(4,16),(6,8),(7,6),(10,6)]),
([u11,u3,u4,u5,u0,u1,u2],[(u5,u3,u4),(u11,u0,u2)],[0,1,2,3],[(0,7),(0,17),(0,30),(0,39),(0,40),(0,44),(1,42),(4,43),(5,41),(6,7),(6,39)]),
([u3,u4,u0,u1,u19,u18],[(u19,u3,u2),(u18,u4,u2)],[1,2,3],[(0,0),(0,46),(2,46),(3,45),(3,47),(5,47),(6,46),(8,46),(9,45),(9,47),(11,47)]),
([u3,u4,u0,u9,u22,u1,u2],[(u9,u3,u0),(u22,u4,u0)],[0,1,2],[(0,1),(0,48),(6,48)]),
([u15,u3,u4,u9,u1,u2],[(u9,u3,u0),(u15,u4,u0)],[0,1,2],[(0,51),(0,52),(1,51),(1,52),(2,50),(3,50),(10,49)]),
([u3,u4,u0,u9,u20,u1,u2],[(u9,u3,u0),(u20,u4,u9)],[1,2],[(0,14),(0,55),(1,55),(2,54),(3,54),(4,53),(6,48)]),
([u28,u3,u4,u0,u1,u2],[(u9,u3,u0),(u28,u4,u9)],[1,2,3,4],[(0,14),(0,48),(0,57),(0,58),(0,59),(1,57),(1,58),(1,59),(2,56),(3,56)]),
([u28,u3,u4,u0,u9,u1,u2],[(u9,u3,u0),(u28,u4,u9)],[0,1,2],[(0,2),(0,14),(0,45)]),
([u3,u4,u0,u9,u1,u36,u2],[(u9,u3,u0),(u36,u4,u1)],[0,1,2,4],[(0,3),(0,19),(0,61),(1,57),(3,60),(4,46),(7,46),(10,57)]),
([u15,u3,u4,u0,u1,u14,u2],[(u14,u3,u1),(u15,u4,u0)],[0,1,2,4],[(0,51),(1,62),(1,65),(2,63),(10,64)]),
([u3,u4,u0,u1,u19,u17],[(u19,u3,u2),(u17,u2,u0)],[0,1,3,4],[(0,16),(0,46),(0,65),(0,72),(1,67),(1,70),(1,73),(2,68),(3,58),(4,60),(4,69),(5,71),(6,6),(7,66)]),
([u3,u4,u0,u9,u1,u6,u2],[(u9,u3,u0),(u6,u0,u1)],[0,1,4],[(1,75),(6,74)]),
([u11,u3,u4,u9,u1,u2],[(u9,u3,u0),(u11,u0,u2)],[0,1,3,4],[(0,17),(0,59),(0,81),(0,82),(2,79),(3,77),(5,78),(5,80),(6,7),(6,76)]),
([u11,u3,u4,u0,u1,u2,u19],[(u19,u3,u2),(u11,u2,u0)],[0,1,3],[(0,80),(0,87),(1,86),(3,84),(4,85),(6,83)]),
([u3,u4,u71,u0,u1,u14,u2],[(u14,u3,u1),(u71,u14,u0)],[0,1,4],[(0,70),(0,89),(4,88)]),
([u3,u4,u0,u1,u29,u2],[(u9,u3,u0),(u29,u9,u1)],[1,2,3],[(0,19),(0,51),(0,91),(0,93),(0,94),(1,88),(1,92),(2,51),(4,88),(4,92),(6,8),(6,90),(7,46),(10,46)]),
([u3,u4,u0,u9,u1,u29,u2],[(u9,u3,u0),(u29,u9,u1)],[1,4],[(1,92),(2,89),(4,95),(6,74)]),
([u21,u3,u4,u0,u1,u2],[(u9,u3,u0),(u21,u9,u2)],[0,1,2,4],[(0,9),(0,47),(0,52),(0,57),(0,75),(0,92),(0,98),(0,99),(1,86),(2,97),(3,100),(5,87),(6,96)]),
([u21,u3,u4,u0,u9,u1,u2],[(u9,u3,u0),(u21,u9,u2)],[1,3],[(0,71),(0,92),(11,101)]),
([0x3030,u3,u4,u0,u1,u2,u18],[(u18,u4,u2),(0x3030,u18,u0)],[0,2],[(0,83),(0,101),(0,104),(7,86),(9,102),(10,103)]),
([u3,u4,u10,u0,u1,u2,u19],[(u19,u3,u2),(u10,u0,u1)],[0,1,3],[(0,68),(0,106),(0,109),(2,68),(3,107),(3,108),(6,105)]),
([u3,u4,u0,u9,u1,u2,u7],[(u9,u3,u0),(u7,u1,u2)],[0,1,3,4],[(0,81),(0,93),(0,98),(0,99),(0,110),(1,81),(1,99),(4,72),(4,109),(10,111)]),
([u11,u3,u4,u0,u1,u14,u2],[(u14,u3,u1),(u11,u0,u2)],[0,1,4],[(0,69),(0,100),(0,115),(1,112),(2,113),(4,82),(5,114)]),
([u3,u72,u4,u0,u1,u2],[(u15,u4,u0),(u72,u15,u3)],[0,1,2,3,4],[(0,116),(0,117),(1,116),(1,117),(2,63),(3,63)]),
([u3,u4,u0,u70,u1,u2],[(u30,u4,u1),(u70,u30,u0)],[0,1,2,3,4],[(0,50),(0,63),(0,123),(1,122),(3,120),(4,62),(5,121),(6,118),(6,119)]),
([u15,u60,u3,u4,u0,u1,u2],[(u15,u4,u0),(u60,u3,u1)],[0,1,2,4],[(0,118),(0,125),(2,124),(8,118)]),
([u15,u3,u4,u1,u6,u2],[(u15,u4,u0),(u6,u0,u1)],[0,2,3,4],[(0,51),(0,117),(0,125),(0,127),(0,130),(0,131),(1,65),(1,128),(3,129),(10,126)]),
([u15,u3,u4,u0,u8,u1,u2],[(u15,u4,u0),(u8,u1,u2)],[0,2,3,4],[(0,128),(0,133),(0,134),(1,128),(4,120),(4,132),(5,120)]),
([u15,u3,u4,u0,u1,u2,u7],[(u15,u4,u0),(u7,u1,u2)],[0,2],[(0,130),(0,134),(4,122),(10,135)]),
([u11,u30,u3,u4,u0,u1,u2],[(u30,u4,u1),(u11,u0,u2)],[0,2,3,4],[(0,121),(0,129),(0,138),(2,136),(2,137)]),
([u3,u4,u0,u48,u1,u2],[(u10,u0,u1),(u48,u3,u10)],[0,1,2,3,4],[(0,34),(0,139),(0,141),(0,142),(2,141),(3,107),(3,140),(6,33),(6,105)]),
([u3,u4,u0,u1,u73,u2],[(u8,u1,u2),(u73,u8,u0)],[0,1,2,3,4],[(0,107),(0,133),(0,143),(4,106),(6,107),(6,133),(6,143),(10,106)]),
([u3,u4,u10,u6,u2],[(u10,u0,u1),(u6,u0,u1)],[0,1,2,3],[(0,36),(0,109),(0,144),(0,145),(0,148),(0,149),(0,150),(0,151),(0,152),(3,134),(3,140),(3,146),(3,147),(3,153),(6,109),(6,144),(6,145),(9,134),(9,140)]),
([u3,u4,u10,u0,u2,u7],[(u10,u1,u0),(u7,u1,u2)],[0,3,4],[(0,68),(0,141),(0,149),(0,156),(2,157),(3,128),(5,154),(5,155),(6,68),(6,141),(9,128)]),
([u3,u4,u0,u1,u6,u29,u2],[(u6,u0,u1),(u29,u3,u6)],[1],[(0,144),(1,75),(4,75),(6,90)]),
([u34,u3,u4,u0,u1,u2],[(u6,u0,u1),(u34,u4,u6)],[0,1,2,3,4],[(0,38),(0,67),(0,74),(0,90),(0,111),(0,158),(2,67),(2,74),(3,159),(6,127),(8,127)]),
([u34,u3,u4,u0,u1,u6,u2],[(u6,u0,u1),(u34,u4,u6)],[0,2,4],[(0,66),(0,90),(0,145),(2,66)]),
([u3,u4,u0,u1,u6,u2,u17],[(u6,u0,u1),(u17,u0,u2)],[0,3,4],[(0,160),(0,161),(1,160),(4,156)]),
([u11,u3,u4,u0,u1,u7],[(u7,u2,u1),(u11,u2,u0)],[0,3,4],[(0,69),(0,81),(0,129),(0,162),(0,163),(0,164),(6,69),(6,81),(6,129),(6,162)]),
([u11,u3,u4,u0,u1,u2,u7],[(u7,u2,u1),(u11,u2,u0)],[0,3,4],[(0,161),(0,166),(1,165)]),
([u3,u4,u57,u0,u1,u2,u7],[(u7,u1,u2),(u57,u7,u0)],[0],[(0,168),(4,148),(4,167)]),
([u3,u4,u0,u1,u2,u13],[(u6,u0,u1),(u13,u6,u2)],[0,1,2,3,4],[(0,72),(0,93),(0,130),(0,149),(0,167),(0,169),(0,170),(1,72),(1,149),(1,167),(1,170),(2,130),(3,130),(4,72),(4,149),(4,167),(4,170),(6,72),(6,93),(6,130),(6,169),(7,72),(8,130),(9,130),(10,72)]),
([u3,u4,u0,u1,u6,u2,u13],[(u6,u0,u1),(u13,u6,u2)],[0,3,4],[(0,150),(0,170),(1,157),(1,160),(3,168),(4,157),(4,160)]),
([u16,u3,u4,u0,u1,u2],[(u6,u0,u1),(u16,u6,u2)],[0,1,2,3,4],[(0,73),(0,111),(0,131),(0,151),(0,160),(0,161),(0,170),(0,171),(0,172),(2,73),(2,131),(2,160),(2,172),(3,163),(3,166),(5,163),(5,166),(6,73),(6,111),(6,131),(6,171),(8,73),(8,131)]),
([u16,u3,u4,u0,u1,u6,u2],[(u6,u0,u1),(u16,u6,u2)],[0,3,4],[(0,152),(0,170),(3,164),(3,173),(5,164)]),
([0xf0,u3,u4,u0,u1,u2,u7],[(u7,u1,u2),(0xf0,u7,u0)],[0],[(0,153),(0,161),(0,165),(0,173),(1,165)]),
([u3,u46,u4,u0,u1,u2],[(u11,u0,u2),(u46,u11,u3)],[0,1,2,4],[(0,40),(0,76),(0,162),(0,174),(1,86),(1,175),(2,113),(3,176),(6,39),(6,83)]),
([u3,u4,u0,u1,u41],[(u27,u0,u1),(u41,u27,u2)],[0,1,2,4],[(0,42),(0,177),(0,180),(1,172),(2,84),(3,178),(4,78),(5,179),(6,177),(8,84),(9,178),(10,78)]),
([u3,u4,u0,u32,u1,u2],[(u25,u1,u2),(u32,u25,u0)],[0,1,2,3,4],[(0,79),(0,113),(0,137),(0,161),(0,167),(0,181),(0,182),(1,179),(4,112),(4,165),(6,79),(6,113),(6,137),(6,181),(10,112)]),
([u3,u4,u69,u1,u2],[(u24,u2,u1),(u69,u24,u0)],[0,1,2,3,4],[(0,43),(0,85),(6,85)]),
([u3,u4,u0,u1,u6,u2],[(u27,u0,u1),(u6,u27,u1)],[0,1,2,3,4],[(0,86),(0,161),(0,167),(0,183),(1,80),(3,184),(4,80),(5,184),(6,86),(6,183),(7,80),(10,80)]),
([u11,u24,u3,u4,u0,u1],[(u24,u2,u1),(u11,u2,u0)],[0,3,4],[(0,82),(0,179),(0,184),(0,185),(1,154),(3,176),(6,82),(9,176)]),
([u11,u26,u3,u4,u1],[(u11,u0,u2),(u26,u0,u2)],[0,1,2,3],[(0,44),(0,115),(0,138),(2,146),(6,115),(6,138)]),
([u11,u25,u3,u4,u0,u1,u2],[(u11,u0,u2),(u25,u1,u2)],[0,3,4],[(0,167),(0,182),(0,184),(2,182),(2,184)])
]
def c5_0_L7 : Array W5Node := Array.mk [
([u3,u4,u5,u0,u1,u2],[(u5,u3,u4)],[0,1,2,3,4],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(1,4),(1,5),(1,7),(1,8),(1,9),(2,0),(2,1),(2,2),(2,3),(2,6),(2,9),(3,0),(3,1),(3,2),(3,3),(3,6),(3,9),(4,4),(4,5),(4,7),(4,8),(4,9),(5,9),(6,0),(8,0),(9,0)]),
([u3,u4,u0,u9,u1,u2],[(u9,u3,u0)],[0,1,2,3,4],[(0,2),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,19),(0,20),(0,23),(0,24),(0,25),(0,26),(0,29),(1,16),(1,19),(1,20),(1,23),(1,24),(1,25),(1,26),(2,17),(2,22),(2,30),(3,17),(3,22),(3,30),(4,10),(4,18),(4,21),(4,28),(5,18),(5,21),(6,0),(10,27),(11,27)]),
([u15,u3,u4,u0,u1,u2],[(u15,u4,u0)],[0,1,2,3,4],[(0,12),(0,17),(0,31),(0,33),(0,34),(0,35),(0,36),(1,17),(1,33),(1,34),(2,32),(2,37),(3,32),(3,37)]),
([u3,u4,u10,u0,u1,u2],[(u10,u0,u1)],[0,1,2,3,4],[(0,7),(0,28),(0,38),(0,40),(0,41),(2,41),(3,35),(3,39),(6,28),(6,38),(9,35)]),
([u3,u4,u0,u1,u6,u2],[(u6,u0,u1)],[0,1,2,3,4],[(0,8),(0,19),(0,23),(0,34),(0,40),(0,42),(0,43),(0,44),(0,45),(0,49),(0,50),(0,51),(0,52),(1,18),(2,19),(2,34),(2,45),(3,29),(3,36),(3,41),(3,46),(3,47),(3,48),(3,53),(4,18),(5,41),(5,46),(5,47),(6,19),(6,23),(6,34),(6,42),(6,43),(6,44),(7,18),(8,19),(8,34),(9,29),(9,36),(10,18)]),
([u11,u3,u4,u0,u1,u2],[(u11,u0,u2)],[0,1,2,3,4],[(0,9),(0,20),(0,21),(0,30),(0,37),(0,46),(0,47),(0,54),(0,59),(0,60),(0,61),(1,55),(1,58),(2,56),(4,57),(4,59),(6,20),(6,21),(6,30),(6,37),(6,54)])
]
def c5_0_L8 : Array W5Node := Array.mk [
([u3,u4,u0,u1,u2],[],[1,2],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,1),(2,2),(2,5),(3,1),(3,2),(3,5),(4,3),(4,4),(4,5),(5,5),(6,1),(6,2),(8,1),(8,2),(9,1),(9,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_2_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 2 c5_0_L2 (Array.mk []) 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_2 : ∀ i < c5_0_L2.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 2 c5_0_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : c5_0_L2.size = 2 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_3_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 3 c5_0_L3 c5_0_L2 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_3_1 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 3 c5_0_L3 c5_0_L2 16 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_3 : ∀ i < c5_0_L3.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 3 c5_0_L3 c5_0_L2 i = true := by
  intro i hi
  have hsz : c5_0_L3.size = 29 := by decide +kernel
  have hi' : i < 29 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockW5_at c5_0_chk_3_0 i (by omega) (by omega)
  ·
    exact checkBlockW5_at c5_0_chk_3_1 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_1 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_2 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_3 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_4 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_5 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_4_6 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 96 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_4 : ∀ i < c5_0_L4.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 4 c5_0_L4 c5_0_L3 i = true := by
  intro i hi
  have hsz : c5_0_L4.size = 108 := by decide +kernel
  have hi' : i < 108 := hsz ▸ hi
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
      exact checkBlockW5_at c5_0_chk_4_6 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_1 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_2 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_3 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_4 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_5 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_6 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_7 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_8 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_9 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_10 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_5_11 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 176 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_5 : ∀ i < c5_0_L5.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 5 c5_0_L5 c5_0_L4 i = true := by
  intro i hi
  have hsz : c5_0_L5.size = 186 := by decide +kernel
  have hi' : i < 186 := hsz ▸ hi
  by_cases h : i < 96
  ·
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
      by_cases h : i < 80
      ·
        by_cases h : i < 64
        ·
          exact checkBlockW5_at c5_0_chk_5_3 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_5_4 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_5_5 i (by omega) (by omega)
  ·
    by_cases h : i < 144
    ·
      by_cases h : i < 128
      ·
        by_cases h : i < 112
        ·
          exact checkBlockW5_at c5_0_chk_5_6 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_5_7 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_5_8 i (by omega) (by omega)
    ·
      by_cases h : i < 176
      ·
        by_cases h : i < 160
        ·
          exact checkBlockW5_at c5_0_chk_5_9 i (by omega) (by omega)
        ·
          exact checkBlockW5_at c5_0_chk_5_10 i (by omega) (by omega)
      ·
        exact checkBlockW5_at c5_0_chk_5_11 i (by omega) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_1 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_2 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_6_3 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 48 14 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_6 : ∀ i < c5_0_L6.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 6 c5_0_L6 c5_0_L5 i = true := by
  intro i hi
  have hsz : c5_0_L6.size = 62 := by decide +kernel
  have hi' : i < 62 := hsz ▸ hi
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_7_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 0 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_7 : ∀ i < c5_0_L7.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 7 c5_0_L7 c5_0_L6 i = true := by
  intro i hi
  have hsz : c5_0_L7.size = 6 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_7_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c5_0_chk_8_0 : checkBlockW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 8 c5_0_L8 c5_0_L7 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem c5_0_chk_8 : ∀ i < c5_0_L8.size, checkNodeW5 c5_0_goal 12 c5_0_pow 5 c5_0_cfLBs c5_0_cfMasks c5_0_cfB0s c5_0_cfStocks 8 c5_0_L8 c5_0_L7 i = true := by
  intro i hi
  have hsz : c5_0_L8.size = 1 := by decide +kernel
  exact checkBlockW5_at c5_0_chk_8_0 i (Nat.zero_le _) (by omega)
theorem c5_0_L2_sound : ∀ i < c5_0_L2.size, ¬ live (basicOps 32) c5_0_goal 2 (c5_0_L2[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound (fun j hj => by simp at hj) c5_0_chk_2
theorem c5_0_L3_sound : ∀ i < c5_0_L3.size, ¬ live (basicOps 32) c5_0_goal 3 (c5_0_L3[i]?.getD ([], [], [], [])).1.toFinset :=
  level_sound_W5 (by decide) c5_0_G_valid c5_0_cof_sound c5_0_L2_sound c5_0_chk_3
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
set_option maxRecDepth 100000 in
theorem c5_0_sublists : rows5.sublists.filter (fun ws => cover 32 jumps5 c5_0_goal ws) = [rows5] := by decide +kernel
theorem c5_0_top_match : sameSet (rows5.map (actB 32 (c5_0_pow[0]?.getD []))) (c5_0_L8[0]?.getD ([], [], [], [])).1 = true := by decide +kernel
theorem c5_0_no_build : ¬ build (basicOps 32) c5_0_goal 8 rows5.toFinset :=
  no_build_of_top c5_0_G_valid (by decide) c5_0_sublists c5_0_top_match (c5_0_L8_sound 0 (by decide))

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4008372456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
theorem sample6_ok : ∀ k : Fin 64, F (fun i => (rows6.getD i.val 0)[k.val]) = goal6[k.val] := by decide +kernel

def idx65 : List ℕ := [8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31,40,41,42,43,44,45,46,47,56,57,58,59,60,61,62,63]
theorem idx65_spec : idx65.length = 32 ∧ ∀ idx ∈ idx65, idx < 64 := by decide
theorem projS65_goal6 : projS 32 idx65 goal6 = c5_0_goal := by decide +kernel
theorem projS65_xv : projS 32 idx65 (rows6.getD 3 0) = 0 := by decide +kernel
theorem projS65_rows6_sub : rows6.all (fun w => projS 32 idx65 w == 0 || rows5.contains (projS 32 idx65 w)) = true := by decide +kernel
theorem xv_ess_only : rows6.all (fun w => w == rows6.getD 3 0 || w.getLsbD 18 == w.getLsbD 26) = true := by decide +kernel
theorem goal6_diff : goal6.getLsbD 18 ≠ goal6.getLsbD 26 := by decide
theorem ops6_diff (a b z : W6) (hz : z ∈ basicOps6 a b) (hd : z.getLsbD 18 ≠ z.getLsbD 26) :
    a.getLsbD 18 ≠ a.getLsbD 26 ∨ b.getLsbD 18 ≠ b.getLsbD 26 := by
  simp only [basicOps6, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail; obtain ⟨ha, hb⟩ := fail; apply hd
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
      show (18 : ℕ) < 64 by decide, show (26 : ℕ) < 64 by decide, decide_true, Bool.true_and, ha, hb]

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
  have hdt : t.getLsbD 18 ≠ t.getLsbD 26 := by
    rcases ht with rfl | rfl
    · exact goal6_diff
    · intro h
      have hgd := goal6_diff
      simp only [BitVec.getLsbD_not, show (18 : ℕ) < 64 by decide, show (26 : ℕ) < 64 by decide,
        decide_true, Bool.true_and] at h
      cases h1 : goal6.getLsbD 18 <;> cases h2 : goal6.getLsbD 26 <;>
        simp only [h1, h2, Bool.not_true, Bool.not_false] at h hgd <;>
        first | exact Bool.noConfusion h | exact hgd rfl
  obtain ⟨w, hw, hdw⟩ := live_separates (fun u : W6 => u.getLsbD 18 ≠ u.getLsbD 26) hdt ops6_diff hl
  have hw_eq : w = rows6.getD 3 0 := by
    have h1 := List.all_eq_true.mp xv_ess_only w (List.mem_toFinset.mp (hs hw))
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    exact h1.resolve_right hdw
  have hxv_mem : rows6.getD 3 0 ∈ s.filter (fun u => projS 32 idx65 u = 0) :=
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
  ⟨.or, [0, 2]⟩,
  ⟨.and, [6, 1]⟩,
  ⟨.and, [4, 5]⟩,
  ⟨.and, [8, 2]⟩,
  ⟨.or, [9, 1]⟩,
  ⟨.and, [10, 3]⟩,
  ⟨.or, [11, 0]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.or, [13, 2]⟩,
  ⟨.and, [14, 12]⟩,
  ⟨.or, [15, 7]⟩
]

theorem wfits : Monotone2 ⟨wg, 16⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 16⟩ (List.ofFn x) = F x := by
  decide +kernel

end PEqualNP.Outside.L_meta_37503_aux

open PEqualNP.Outside.L_meta_37503_aux in
theorem PEqualNP.Outside.L_meta_37503 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008372456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008372456) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
