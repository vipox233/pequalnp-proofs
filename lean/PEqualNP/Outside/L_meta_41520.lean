import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41520_aux

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

def goal6 : BitVec 64 := 0xfeeeeee8eeeaeae8

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

def b4_1_goal : BitVec 16 := 0xeee8
def b4_1_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_1_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_1_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_1_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_1_s2 : List ℕ := [0,2,1,3,4,6,5,7,8,10,9,11,12,14,13,15]
def b4_1_p2 : List ℕ := [1,4,2,8,16,64,32,128,256,1024,512,2048,4096,16384,8192,32768]
def b4_1_s3 : List ℕ := [0,2,1,3,8,10,9,11,4,6,5,7,12,14,13,15]
def b4_1_p3 : List ℕ := [1,4,2,8,256,1024,512,2048,16,64,32,128,4096,16384,8192,32768]
def b4_1_idx : Array (List ℕ) := Array.mk [b4_1_s0,b4_1_s1,b4_1_s2,b4_1_s3]
def b4_1_pow : Array (List ℕ) := Array.mk [b4_1_p0,b4_1_p1,b4_1_p2,b4_1_p3]
def b4_1_inv : Array ℕ := Array.mk [0,1,2,3]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_G_valid : (List.range 4).all (symValid 16 4 b4_1_idx b4_1_pow b4_1_inv b4_1_goal) = true := by decide +kernel
def b4_1_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfff0],[])
]
def b4_1_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xfff0],[]),
([0xaaaa,0xcccc,0xf0f0,0xfff0],[]),
([0xf0,0xaaaa,0xcccc,0xff00],[(0,0)])
]
def b4_1_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(0,2),(1,1),(1,2)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_2_0 : checkBlockP 16 jumps4 b4_1_goal 4 b4_1_pow 2 b4_1_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_2 : ∀ i < b4_1_L2.size, checkNodeP 16 jumps4 b4_1_goal 4 b4_1_pow 2 b4_1_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_1_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_1_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_3_0 : checkBlockP 16 jumps4 b4_1_goal 4 b4_1_pow 3 b4_1_L3 b4_1_L2 0 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_3 : ∀ i < b4_1_L3.size, checkNodeP 16 jumps4 b4_1_goal 4 b4_1_pow 3 b4_1_L3 b4_1_L2 i = true := by
  intro i hi
  have hsz : b4_1_L3.size = 3 := by decide +kernel
  exact checkBlockP_at b4_1_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_1_chk_4_0 : checkBlockP 16 jumps4 b4_1_goal 4 b4_1_pow 4 b4_1_L4 b4_1_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_1_chk_4 : ∀ i < b4_1_L4.size, checkNodeP 16 jumps4 b4_1_goal 4 b4_1_pow 4 b4_1_L4 b4_1_L3 i = true := by
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

def b4_4_goal : BitVec 16 := 0xa880
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
([0x8888,0xa0a0,0xff00],[])
]
def b4_4_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0x8888,0xaaaa,0xf0f0,0xff00],[(0,0),(1,0)]),
([0xaa,0xaaaa,0xcccc,0xf0f0],[])
]
def b4_4_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(1,1),(2,0),(3,0),(4,1)])
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

def b4_5_goal : BitVec 16 := 0xfeea
def b4_5_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
def b4_5_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768]
def b4_5_s1 : List ℕ := [0,1,2,3,8,9,10,11,4,5,6,7,12,13,14,15]
def b4_5_p1 : List ℕ := [1,2,4,8,256,512,1024,2048,16,32,64,128,4096,8192,16384,32768]
def b4_5_s2 : List ℕ := [0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15]
def b4_5_p2 : List ℕ := [1,2,16,32,4,8,64,128,256,512,4096,8192,1024,2048,16384,32768]
def b4_5_s3 : List ℕ := [0,1,4,5,8,9,12,13,2,3,6,7,10,11,14,15]
def b4_5_p3 : List ℕ := [1,2,16,32,256,512,4096,8192,4,8,64,128,1024,2048,16384,32768]
def b4_5_s4 : List ℕ := [0,1,8,9,2,3,10,11,4,5,12,13,6,7,14,15]
def b4_5_p4 : List ℕ := [1,2,256,512,4,8,1024,2048,16,32,4096,8192,64,128,16384,32768]
def b4_5_s5 : List ℕ := [0,1,8,9,4,5,12,13,2,3,10,11,6,7,14,15]
def b4_5_p5 : List ℕ := [1,2,256,512,16,32,4096,8192,4,8,1024,2048,64,128,16384,32768]
def b4_5_idx : Array (List ℕ) := Array.mk [b4_5_s0,b4_5_s1,b4_5_s2,b4_5_s3,b4_5_s4,b4_5_s5]
def b4_5_pow : Array (List ℕ) := Array.mk [b4_5_p0,b4_5_p1,b4_5_p2,b4_5_p3,b4_5_p4,b4_5_p5]
def b4_5_inv : Array ℕ := Array.mk [0,1,2,4,3,5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_5_G_valid : (List.range 6).all (symValid 16 6 b4_5_idx b4_5_pow b4_5_inv b4_5_goal) = true := by decide +kernel
def b4_5_L2 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xcccc,0xfafa,0xffaa],[])
]
def b4_5_L3 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xffaa],[(0,0),(2,0)]),
([0x4444,0xaaaa,0xf0f0,0xff00],[])
]
def b4_5_L4 : Array (List (BitVec 16) × List (ℕ × ℕ)) := Array.mk [
([0xaaaa,0xcccc,0xf0f0,0xff00],[(0,0),(0,1),(1,0),(2,1),(3,1),(4,0)])
]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_5_chk_2_0 : checkBlockP 16 jumps4 b4_5_goal 6 b4_5_pow 2 b4_5_L2 (Array.mk []) 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_5_chk_2 : ∀ i < b4_5_L2.size, checkNodeP 16 jumps4 b4_5_goal 6 b4_5_pow 2 b4_5_L2 (Array.mk []) i = true := by
  intro i hi
  have hsz : b4_5_L2.size = 1 := by decide +kernel
  exact checkBlockP_at b4_5_chk_2_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_5_chk_3_0 : checkBlockP 16 jumps4 b4_5_goal 6 b4_5_pow 3 b4_5_L3 b4_5_L2 0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_5_chk_3 : ∀ i < b4_5_L3.size, checkNodeP 16 jumps4 b4_5_goal 6 b4_5_pow 3 b4_5_L3 b4_5_L2 i = true := by
  intro i hi
  have hsz : b4_5_L3.size = 2 := by decide +kernel
  exact checkBlockP_at b4_5_chk_3_0 i (Nat.zero_le _) (by omega)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b4_5_chk_4_0 : checkBlockP 16 jumps4 b4_5_goal 6 b4_5_pow 4 b4_5_L4 b4_5_L3 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem b4_5_chk_4 : ∀ i < b4_5_L4.size, checkNodeP 16 jumps4 b4_5_goal 6 b4_5_pow 4 b4_5_L4 b4_5_L3 i = true := by
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

def c5_0_goal : BitVec 32 := 0xfffefeee
def c5_0_idxs4 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]
set_option maxRecDepth 100000 in
theorem c5_0_no_build : ¬ build (basicOps 32) c5_0_goal 5 rows5.toFinset :=
  no_build5_of_proj4 4 b4_5_goal (by decide) b4_5_no_build c5_0_goal c5_0_idxs4 0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

def c5_1_goal : BitVec 32 := 0xfeeeeeea
def c5_1_idxs4 : List ℕ := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28,30]
set_option maxRecDepth 100000 in
theorem c5_1_no_build : ¬ build (basicOps 32) c5_1_goal 6 rows5.toFinset :=
  no_build5_of_proj4 5 b4_0_goal (by decide) b4_0_no_build c5_1_goal c5_1_idxs4 0 0 1 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

def c5_2_goal : BitVec 32 := 0xeaa8aaa8
def c5_2_idxs4 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
set_option maxRecDepth 100000 in
theorem c5_2_no_build : ¬ build (basicOps 32) c5_2_goal 6 rows5.toFinset :=
  no_build5_of_proj4 5 b4_0_goal (by decide) b4_0_no_build c5_2_goal c5_2_idxs4 4 14 30 (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

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

def v0 : BitVec 64 := 0xf0f0f0f0f0f0f0f0
def v1 : BitVec 64 := 0xcccccccccccccccc
def v2 : BitVec 64 := 0xff00ff00ff00ff00
def v3 : BitVec 64 := 0xaaaaaaaaaaaaaaaa
def v4 : BitVec 64 := 0xffff0000ffff0000
def v5 : BitVec 64 := 0xffffffff00000000
def v6 : BitVec 64 := 0xff000000ff000000
def v7 : BitVec 64 := 0xf000f000f000f00
def v8 : BitVec 64 := 0xfcfcfcfcfcfcfcfc
def v9 : BitVec 64 := 0xffffff00ffffff00
def v10 : BitVec 64 := 0xeeeeeeeeeeeeeeee
def v11 : BitVec 64 := 0xfafafafafafafafa
def v12 : BitVec 64 := 0xffaaffaaffaaffaa
def v13 : BitVec 64 := 0xffff0000ffff00
def v14 : BitVec 64 := 0xc0c0c0c0c0c0c0c
def v15 : BitVec 64 := 0x3333cccc3333cccc
def v16 : BitVec 64 := 0xcccc0000cccc0000
def v17 : BitVec 64 := 0xffffffffaaaaaaaa
def v18 : BitVec 64 := 0x3300330033003300
def v19 : BitVec 64 := 0xffaaaaaaffaaaaaa
def v20 : BitVec 64 := 0xf0f00000f0f0000
def v21 : BitVec 64 := 0xffffccccffffcccc
def v22 : BitVec 64 := 0x5555555500000000
def v23 : BitVec 64 := 0xcc00cc00cc00cc00
def v24 : BitVec 64 := 0xffffaaaaffffaaaa
def v25 : BitVec 64 := 0xcccc0000cccc
def v26 : BitVec 64 := 0x3333000033330000
def v27 : BitVec 64 := 0xf0f0f000f0f0f00
def v28 : BitVec 64 := 0xffccffccffccffcc
def v29 : BitVec 64 := 0xc0c0c0c0c0c0c0c0
def v30 : BitVec 64 := 0xf0a0f0a0f0a0f0a
def v31 : BitVec 64 := 0x4444444444444444
def v32 : BitVec 64 := 0xf0f0f0f00000000
def v33 : BitVec 64 := 0xafaaafaaafaaafaa
def v34 : BitVec 64 := 0xfcfcfcfc00000000
def v35 : BitVec 64 := 0xfff0fff0fff0fff0
def v36 : BitVec 64 := 0xf0f0f0f000000000
def v37 : BitVec 64 := 0x33cc33cc33cc33cc
def v38 : BitVec 64 := 0xcccccccc00000000
def v39 : BitVec 64 := 0xfffff0f0fffff0f0
def v40 : BitVec 64 := 0xfcfcfc00fcfcfc
def v41 : BitVec 64 := 0xfff0f0f0fff0f0f0
def v42 : BitVec 64 := 0xfcfcfcfc
def v43 : BitVec 64 := 0x3030303030303030
def v44 : BitVec 64 := 0xe0e0e0e0e0e0e0e
def v45 : BitVec 64 := 0xff00ff0000000000
def v46 : BitVec 64 := 0xffffffffcccccccc
def v47 : BitVec 64 := 0x33330000333300
def v48 : BitVec 64 := 0xffccccccffcccccc
def v49 : BitVec 64 := 0x500050005000500
def v50 : BitVec 64 := 0xff000000ff00
def v51 : BitVec 64 := 0xcccccc00cccccc
def v52 : BitVec 64 := 0xffaaffaaaaaaaaaa
def v53 : BitVec 64 := 0x5500550055005500
def v54 : BitVec 64 := 0xccffffccccffffcc
def v55 : BitVec 64 := 0x3f003f003f003f00
def v56 : BitVec 64 := 0xf0f00000f0f0
def v57 : BitVec 64 := 0xee00ee00ee00ee00
def v58 : BitVec 64 := 0xeeaaeeaaeeaaeeaa
def v59 : BitVec 64 := 0xffff000000000000
def v60 : BitVec 64 := 0xcc3333cccc3333cc
def v61 : BitVec 64 := 0x33cc000033cc
def v62 : BitVec 64 := 0xcccccccc
def v63 : BitVec 64 := 0x3300cc003300cc00
def v64 : BitVec 64 := 0xffeeeeeeffeeeeee
def v65 : BitVec 64 := 0xf3f0f3f0f3f0f3f0
def v66 : BitVec 64 := 0xf0ff0000f0ff0000
def v67 : BitVec 64 := 0xcc330000cc330000
def v68 : BitVec 64 := 0xf0a0a0a0f0a0a0a
def v69 : BitVec 64 := 0xcc888888cc888888
def v70 : BitVec 64 := 0xfefefefefefefefe
def v71 : BitVec 64 := 0xeeeeaaaaeeeeaaaa
def v72 : BitVec 64 := 0xfc00fc00fc00fc00
def v73 : BitVec 64 := 0xfcfc0000fcfc
def v74 : BitVec 64 := 0xff000000ff0000
def v75 : BitVec 64 := 0xcfcccfcccfcccfcc
def v76 : BitVec 64 := 0xf000f000f000f000
def v77 : BitVec 64 := 0xcc003300cc003300
def v78 : BitVec 64 := 0xcc0000cccc0000cc
def v79 : BitVec 64 := 0xfcfcfcfca8a8a8a8
def v80 : BitVec 64 := 0xf000ff00f000ff00
def v81 : BitVec 64 := 0xf000f000ff00ff00
def v82 : BitVec 64 := 0xf3f3f0f0f3f3f0f0
def v83 : BitVec 64 := 0xeaeaeaeaeaeaeaea
def v84 : BitVec 64 := 0xf000f000f000f0
def v85 : BitVec 64 := 0xf0f0f0f0
def v86 : BitVec 64 := 0xcc00ff00cc00ff00
def v87 : BitVec 64 := 0x3322222233222222
def v88 : BitVec 64 := 0xa0a0a0a0a0a0a0a0
def v89 : BitVec 64 := 0x5555000055550000
def v90 : BitVec 64 := 0xf0ff0f00f0ff0f0
def v91 : BitVec 64 := 0xfcf0fcf0fcf0fcf0
def v92 : BitVec 64 := 0xaa00aa00aa00aa00
def v93 : BitVec 64 := 0xfcf0f3f0fcf0f3f0
def v94 : BitVec 64 := 0xf0f3f3f0f0f3f3f0
def v95 : BitVec 64 := 0xfffafafafffafafa
def v96 : BitVec 64 := 0xc0ccc0ccc0ccc0cc
def v97 : BitVec 64 := 0x404040404040404
def v98 : BitVec 64 := 0xff00ff00ff00
def v99 : BitVec 64 := 0x5454545454545454
def v100 : BitVec 64 := 0xc0c0ccccc0c0cccc
def v101 : BitVec 64 := 0xafafaaaaafafaaaa
def v102 : BitVec 64 := 0xff00ff00
def v103 : BitVec 64 := 0xf4f4f4f4f4f4f4f4
def v104 : BitVec 64 := 0xe0a0e0a0e0a0e0a
def v105 : BitVec 64 := 0xff00ff00aa00aa00
def v106 : BitVec 64 := 0xf0f0fcfcf0f0fcfc
def v107 : BitVec 64 := 0xfffffffff0f0f0f0
def v108 : BitVec 64 := 0x3333333300000000
def v109 : BitVec 64 := 0xcccc0000cccc00
def v110 : BitVec 64 := 0x5a5a5a5a5a5a5a5a
def v111 : BitVec 64 := 0x3f0f33003f0f3300
def v112 : BitVec 64 := 0xfcfcfc00fcfcfc00
def v113 : BitVec 64 := 0xcc00cc00cc00cc
def v114 : BitVec 64 := 0xf00ff000f00ff00
def v115 : BitVec 64 := 0x33003300ff00ff00
def v116 : BitVec 64 := 0xff00ff000f000f00
def v117 : BitVec 64 := 0x5050505050505050
def v118 : BitVec 64 := 0xaeaeaeaeaeaeaeae
def v119 : BitVec 64 := 0xf0fffff0f0fffff0
def v120 : BitVec 64 := 0xf0000000f000000
def v121 : BitVec 64 := 0xeeeeee00eeeeee
def v122 : BitVec 64 := 0xecececececececec
def v123 : BitVec 64 := 0xfefafefafefafefa
def v124 : BitVec 64 := 0xaaaa0000aaaa0000
def v125 : BitVec 64 := 0xfc00fcfcfc00fcfc
def v126 : BitVec 64 := 0xffff0f00ffff0f00
def v127 : BitVec 64 := 0xf0f00000f0f00000
def v128 : BitVec 64 := 0xf000f00ff00ff00
def v129 : BitVec 64 := 0xaaaa0000aaaa
def v130 : BitVec 64 := 0xf0f0f0f0a0a0a0a
def v131 : BitVec 64 := 0xff33ff00ff33ff00
def v132 : BitVec 64 := 0xff00ff00ff00ff0
def v133 : BitVec 64 := 0xf0f00000f0f00
def v134 : BitVec 64 := 0x3232323232323232
def v135 : BitVec 64 := 0xfafa0000fafa0000
def v136 : BitVec 64 := 0xfcfc0000fcfc0000
def v137 : BitVec 64 := 0x44444400444444
def v138 : BitVec 64 := 0x3f3f3f3f00000000
def v139 : BitVec 64 := 0xcf00cf00cf00cf00
def v140 : BitVec 64 := 0x3300ff003300ff00
def v141 : BitVec 64 := 0xf0f0f0f0c0c0c0c
def v142 : BitVec 64 := 0x2222222222222222
def v143 : BitVec 64 := 0x30c0f0f030c0f0f0
def v144 : BitVec 64 := 0xf0c0c0f0f0c0c0f0
def v145 : BitVec 64 := 0xffccccff00000000
def v146 : BitVec 64 := 0xffffff0003030300
def v147 : BitVec 64 := 0xeeee0000eeee0000
def v148 : BitVec 64 := 0xfcf8f8f8fcf8f8f8
def v149 : BitVec 64 := 0xfefaf0f0fefaf0f0
def v150 : BitVec 64 := 0xeeaa0000eeaa0000
def v151 : BitVec 64 := 0x3030c0c03030c0c
def v152 : BitVec 64 := 0xff33ffccff33ffcc
def v153 : BitVec 64 := 0xf00cfcc0f00cfcc
def v154 : BitVec 64 := 0xf0f0f0f0cccccccc
def v155 : BitVec 64 := 0xfffffff0f3f3f3f0
def v156 : BitVec 64 := 0xffffff0033333300
def v157 : BitVec 64 := 0xc0c0c000c0c0c00
def v158 : BitVec 64 := 0xcfcfcfcccfcfcfcc
def v159 : BitVec 64 := 0x303030003030300
def v160 : BitVec 64 := 0xc0c0c0ccc0c0c0cc
def v161 : BitVec 64 := 0xf0e0e0e0f0e0e0e
def v162 : BitVec 64 := 0x3322332233223322
def v163 : BitVec 64 := 0xee00aa00ee00aa00
def v164 : BitVec 64 := 0xcf0fcc00cf0fcc00
def v165 : BitVec 64 := 0xeaeeeaeeeaeeeaee
def v166 : BitVec 64 := 0xffeeffeeeeeeeeee
def v167 : BitVec 64 := 0xfaf0faf0faf0faf0
def v168 : BitVec 64 := 0xf0c0f0c0f0c0f0c
def v169 : BitVec 64 := 0xff0f0000ff0f0000
def v170 : BitVec 64 := 0xf0f0f0f0fff0fff0
def v171 : BitVec 64 := 0xa0a0a0a0a0a0a0a

def g6_s0 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def g6_p0 : List ℕ := [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648,4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808]
def g6_s1 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23,8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,48,49,50,51,52,53,54,55,40,41,42,43,44,45,46,47,56,57,58,59,60,61,62,63]
def g6_p1 : List ℕ := [1,2,4,8,16,32,64,128,65536,131072,262144,524288,1048576,2097152,4194304,8388608,256,512,1024,2048,4096,8192,16384,32768,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648,4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904,9223372036854775808]
def g6_idx : Array (List ℕ) := Array.mk [g6_s0,g6_s1]
def g6_pow : Array (List ℕ) := Array.mk [g6_p0,g6_p1]
def g6_inv : Array ℕ := Array.mk [0,1]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_G_valid : (List.range 2).all (symValid 64 2 g6_idx g6_pow g6_inv goal6) = true := by decide +kernel

def g6_m0 : BitVec 64 := 0x3333333300000000

def g6_st0 : List (BitVec 64) := [0x2222222200000000,0x3030303000000000,0x3300330000000000,0x3333000000000000]

def g6_ix0 : List ℕ := [32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_0 : g6_ix0.length = 16 ∧ (∀ idx ∈ g6_ix0, idx < 64) ∧ (∀ idx ∈ g6_ix0, g6_m0.getLsbD idx = true) ∧ projS 16 g6_ix0 goal6 = b4_0_goal ∧ g6_st0.all (fun w => rows4.contains (projS 16 g6_ix0 w)) = true := by decide +kernel

def g6_m1 : BitVec 64 := 0x5500550055005500

def g6_st1 : List (BitVec 64) := [0x4400440044004400,0x5000500050005000,0x5500000055000000,0x5500550000000000]

def g6_ix1 : List ℕ := [8,10,12,14,24,26,28,30,40,42,44,46,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_1 : g6_ix1.length = 16 ∧ (∀ idx ∈ g6_ix1, idx < 64) ∧ (∀ idx ∈ g6_ix1, g6_m1.getLsbD idx = true) ∧ projS 16 g6_ix1 goal6 = b4_0_goal ∧ g6_st1.all (fun w => rows4.contains (projS 16 g6_ix1 w)) = true := by decide +kernel

def g6_m2 : BitVec 64 := 0xcccccccccccccccc

def g6_st2 : List (BitVec 64) := [0x8888888888888888,0xc0c0c0c0c0c0c0c0,0xcc00cc00cc00cc00,0xcccc0000cccc0000,0xcccccccc00000000]

def g6_ix2 : List ℕ := [2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_2 : g6_ix2.length = 32 ∧ (∀ idx ∈ g6_ix2, idx < 64) ∧ (∀ idx ∈ g6_ix2, g6_m2.getLsbD idx = true) ∧ projS 32 g6_ix2 goal6 = c5_0_goal ∧ g6_st2.all (fun w => rows5.contains (projS 32 g6_ix2 w)) = true := by decide +kernel

def g6_m3 : BitVec 64 := 0xff00ff00000000

def g6_st3 : List (BitVec 64) := [0xaa00aa00000000,0xcc00cc00000000,0xf000f000000000,0xff000000000000]

def g6_ix3 : List ℕ := [32,33,34,35,36,37,38,39,48,49,50,51,52,53,54,55]

set_option maxRecDepth 100000 in

theorem g6_cspec_3 : g6_ix3.length = 16 ∧ (∀ idx ∈ g6_ix3, idx < 64) ∧ (∀ idx ∈ g6_ix3, g6_m3.getLsbD idx = true) ∧ projS 16 g6_ix3 goal6 = b4_1_goal ∧ g6_st3.all (fun w => rows4.contains (projS 16 g6_ix3 w)) = true := by decide +kernel

def g6_m4 : BitVec 64 := 0xf0f0f0f

def g6_st4 : List (BitVec 64) := [0xa0a0a0a,0xc0c0c0c,0xf000f00,0xf0f0000]

def g6_ix4 : List ℕ := [0,1,2,3,8,9,10,11,16,17,18,19,24,25,26,27]

set_option maxRecDepth 100000 in

theorem g6_cspec_4 : g6_ix4.length = 16 ∧ (∀ idx ∈ g6_ix4, idx < 64) ∧ (∀ idx ∈ g6_ix4, g6_m4.getLsbD idx = true) ∧ projS 16 g6_ix4 goal6 = b4_0_goal ∧ g6_st4.all (fun w => rows4.contains (projS 16 g6_ix4 w)) = true := by decide +kernel

def g6_m5 : BitVec 64 := 0xff00ff00ff00ff00

def g6_st5 : List (BitVec 64) := [0xaa00aa00aa00aa00,0xcc00cc00cc00cc00,0xf000f000f000f000,0xff000000ff000000,0xff00ff0000000000]

def g6_ix5 : List ℕ := [8,9,10,11,12,13,14,15,24,25,26,27,28,29,30,31,40,41,42,43,44,45,46,47,56,57,58,59,60,61,62,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_5 : g6_ix5.length = 32 ∧ (∀ idx ∈ g6_ix5, idx < 64) ∧ (∀ idx ∈ g6_ix5, g6_m5.getLsbD idx = true) ∧ projS 32 g6_ix5 goal6 = c5_1_goal ∧ g6_st5.all (fun w => rows5.contains (projS 32 g6_ix5 w)) = true := by decide +kernel

def g6_m6 : BitVec 64 := 0xffff0000ffff0000

def g6_st6 : List (BitVec 64) := [0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff000000000000]

def g6_ix6 : List ℕ := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]

set_option maxRecDepth 100000 in

theorem g6_cspec_6 : g6_ix6.length = 32 ∧ (∀ idx ∈ g6_ix6, idx < 64) ∧ (∀ idx ∈ g6_ix6, g6_m6.getLsbD idx = true) ∧ projS 32 g6_ix6 goal6 = c5_1_goal ∧ g6_st6.all (fun w => rows5.contains (projS 32 g6_ix6 w)) = true := by decide +kernel

def g6_m7 : BitVec 64 := 0xff00ff

def g6_st7 : List (BitVec 64) := [0xaa00aa,0xcc00cc,0xf000f0,0xff0000]

def g6_ix7 : List ℕ := [0,1,2,3,4,5,6,7,16,17,18,19,20,21,22,23]

set_option maxRecDepth 100000 in

theorem g6_cspec_7 : g6_ix7.length = 16 ∧ (∀ idx ∈ g6_ix7, idx < 64) ∧ (∀ idx ∈ g6_ix7, g6_m7.getLsbD idx = true) ∧ projS 16 g6_ix7 goal6 = b4_2_goal ∧ g6_st7.all (fun w => rows4.contains (projS 16 g6_ix7 w)) = true := by decide +kernel

def g6_m8 : BitVec 64 := 0x5555000055550000

def g6_st8 : List (BitVec 64) := [0x4444000044440000,0x5050000050500000,0x5500000055000000,0x5555000000000000]

def g6_ix8 : List ℕ := [16,18,20,22,24,26,28,30,48,50,52,54,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_8 : g6_ix8.length = 16 ∧ (∀ idx ∈ g6_ix8, idx < 64) ∧ (∀ idx ∈ g6_ix8, g6_m8.getLsbD idx = true) ∧ projS 16 g6_ix8 goal6 = b4_0_goal ∧ g6_st8.all (fun w => rows4.contains (projS 16 g6_ix8 w)) = true := by decide +kernel

def g6_m9 : BitVec 64 := 0x3333333333333333

def g6_st9 : List (BitVec 64) := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]

def g6_ix9 : List ℕ := [0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61]

set_option maxRecDepth 100000 in

theorem g6_cspec_9 : g6_ix9.length = 32 ∧ (∀ idx ∈ g6_ix9, idx < 64) ∧ (∀ idx ∈ g6_ix9, g6_m9.getLsbD idx = true) ∧ projS 32 g6_ix9 goal6 = c5_2_goal ∧ g6_st9.all (fun w => rows5.contains (projS 32 g6_ix9 w)) = true := by decide +kernel

def g6_m10 : BitVec 64 := 0xf000f000f000f

def g6_st10 : List (BitVec 64) := [0xa000a000a000a,0xc000c000c000c,0xf0000000f0000,0xf000f00000000]

def g6_ix10 : List ℕ := [0,1,2,3,16,17,18,19,32,33,34,35,48,49,50,51]

set_option maxRecDepth 100000 in

theorem g6_cspec_10 : g6_ix10.length = 16 ∧ (∀ idx ∈ g6_ix10, idx < 64) ∧ (∀ idx ∈ g6_ix10, g6_m10.getLsbD idx = true) ∧ projS 16 g6_ix10 goal6 = b4_3_goal ∧ g6_st10.all (fun w => rows4.contains (projS 16 g6_ix10 w)) = true := by decide +kernel

def g6_m11 : BitVec 64 := 0x505050505050505

def g6_st11 : List (BitVec 64) := [0x404040404040404,0x500050005000500,0x505000005050000,0x505050500000000]

def g6_ix11 : List ℕ := [0,2,8,10,16,18,24,26,32,34,40,42,48,50,56,58]

set_option maxRecDepth 100000 in

theorem g6_cspec_11 : g6_ix11.length = 16 ∧ (∀ idx ∈ g6_ix11, idx < 64) ∧ (∀ idx ∈ g6_ix11, g6_m11.getLsbD idx = true) ∧ projS 16 g6_ix11 goal6 = b4_4_goal ∧ g6_st11.all (fun w => rows4.contains (projS 16 g6_ix11 w)) = true := by decide +kernel

def g6_m12 : BitVec 64 := 0xffff00000000

def g6_st12 : List (BitVec 64) := [0xaaaa00000000,0xcccc00000000,0xf0f000000000,0xff0000000000]

def g6_ix12 : List ℕ := [32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47]

set_option maxRecDepth 100000 in

theorem g6_cspec_12 : g6_ix12.length = 16 ∧ (∀ idx ∈ g6_ix12, idx < 64) ∧ (∀ idx ∈ g6_ix12, g6_m12.getLsbD idx = true) ∧ projS 16 g6_ix12 goal6 = b4_1_goal ∧ g6_st12.all (fun w => rows4.contains (projS 16 g6_ix12 w)) = true := by decide +kernel

def g6_m13 : BitVec 64 := 0xc0c0c0c0c0c0c0c

def g6_st13 : List (BitVec 64) := [0x808080808080808,0xc000c000c000c00,0xc0c00000c0c0000,0xc0c0c0c00000000]

def g6_ix13 : List ℕ := [2,3,10,11,18,19,26,27,34,35,42,43,50,51,58,59]

set_option maxRecDepth 100000 in

theorem g6_cspec_13 : g6_ix13.length = 16 ∧ (∀ idx ∈ g6_ix13, idx < 64) ∧ (∀ idx ∈ g6_ix13, g6_m13.getLsbD idx = true) ∧ projS 16 g6_ix13 goal6 = b4_5_goal ∧ g6_st13.all (fun w => rows4.contains (projS 16 g6_ix13 w)) = true := by decide +kernel

def g6_m14 : BitVec 64 := 0xffff

def g6_st14 : List (BitVec 64) := [0xaaaa,0xcccc,0xf0f0,0xff00]

def g6_ix14 : List ℕ := [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]

set_option maxRecDepth 100000 in

theorem g6_cspec_14 : g6_ix14.length = 16 ∧ (∀ idx ∈ g6_ix14, idx < 64) ∧ (∀ idx ∈ g6_ix14, g6_m14.getLsbD idx = true) ∧ projS 16 g6_ix14 goal6 = b4_2_goal ∧ g6_st14.all (fun w => rows4.contains (projS 16 g6_ix14 w)) = true := by decide +kernel

def g6_m15 : BitVec 64 := 0x4444444444444444

def g6_st15 : List (BitVec 64) := [0x4040404040404040,0x4400440044004400,0x4444000044440000,0x4444444400000000]

def g6_ix15 : List ℕ := [2,6,10,14,18,22,26,30,34,38,42,46,50,54,58,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_15 : g6_ix15.length = 16 ∧ (∀ idx ∈ g6_ix15, idx < 64) ∧ (∀ idx ∈ g6_ix15, g6_m15.getLsbD idx = true) ∧ projS 16 g6_ix15 goal6 = b4_5_goal ∧ g6_st15.all (fun w => rows4.contains (projS 16 g6_ix15 w)) = true := by decide +kernel

def g6_m16 : BitVec 64 := 0xf0f0f0f00000000

def g6_st16 : List (BitVec 64) := [0xa0a0a0a00000000,0xc0c0c0c00000000,0xf000f0000000000,0xf0f000000000000]

def g6_ix16 : List ℕ := [32,33,34,35,40,41,42,43,48,49,50,51,56,57,58,59]

set_option maxRecDepth 100000 in

theorem g6_cspec_16 : g6_ix16.length = 16 ∧ (∀ idx ∈ g6_ix16, idx < 64) ∧ (∀ idx ∈ g6_ix16, g6_m16.getLsbD idx = true) ∧ projS 16 g6_ix16 goal6 = b4_1_goal ∧ g6_st16.all (fun w => rows4.contains (projS 16 g6_ix16 w)) = true := by decide +kernel

def g6_m17 : BitVec 64 := 0x5555555500000000

def g6_st17 : List (BitVec 64) := [0x4444444400000000,0x5050505000000000,0x5500550000000000,0x5555000000000000]

def g6_ix17 : List ℕ := [32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62]

set_option maxRecDepth 100000 in

theorem g6_cspec_17 : g6_ix17.length = 16 ∧ (∀ idx ∈ g6_ix17, idx < 64) ∧ (∀ idx ∈ g6_ix17, g6_m17.getLsbD idx = true) ∧ projS 16 g6_ix17 goal6 = b4_0_goal ∧ g6_st17.all (fun w => rows4.contains (projS 16 g6_ix17 w)) = true := by decide +kernel

def g6_m18 : BitVec 64 := 0xf0f00000f0f

def g6_st18 : List (BitVec 64) := [0xa0a00000a0a,0xc0c00000c0c,0xf0000000f00,0xf0f00000000]

def g6_ix18 : List ℕ := [0,1,2,3,8,9,10,11,32,33,34,35,40,41,42,43]

set_option maxRecDepth 100000 in

theorem g6_cspec_18 : g6_ix18.length = 16 ∧ (∀ idx ∈ g6_ix18, idx < 64) ∧ (∀ idx ∈ g6_ix18, g6_m18.getLsbD idx = true) ∧ projS 16 g6_ix18 goal6 = b4_3_goal ∧ g6_st18.all (fun w => rows4.contains (projS 16 g6_ix18 w)) = true := by decide +kernel

def g6_cfMasks : Array (BitVec 64) := Array.mk [g6_m0,g6_m1,g6_m2,g6_m3,g6_m4,g6_m5,g6_m6,g6_m7,g6_m8,g6_m9,g6_m10,g6_m11,g6_m12,g6_m13,g6_m14,g6_m15,g6_m16,g6_m17,g6_m18]

def g6_cfB0s : Array ℕ := Array.mk [32,8,2,32,0,8,16,0,16,0,0,0,32,2,0,2,32,32,0]

def g6_cfStocks : Array (List (BitVec 64)) := Array.mk [g6_st0,g6_st1,g6_st2,g6_st3,g6_st4,g6_st5,g6_st6,g6_st7,g6_st8,g6_st9,g6_st10,g6_st11,g6_st12,g6_st13,g6_st14,g6_st15,g6_st16,g6_st17,g6_st18]

def g6_cfLBs : Array ℕ := Array.mk [6,6,6,5,6,7,7,5,6,7,5,5,5,5,5,5,5,6,5]

theorem g6_cof_sound (c fuel : ℕ) (hc : c < 19) (hist : List (BitVec 64 × BitVec 64 × BitVec 64)) (nxt : List (BitVec 64)) (hnd : nxt.Nodup) (hchk : checkCofClose64 (g6_cfLBs[c]?.getD 0) fuel (g6_cfMasks[c]?.getD 0) (g6_cfB0s[c]?.getD 0) (g6_cfStocks[c]?.getD []) hist nxt = true) : ¬ live (basicOps 64) goal6 fuel nxt.toFinset := by
  match c with
  | 0 => exact checkCofClose64_16_sound_aux goal6 6 g6_ix0 g6_cspec_0.1 g6_cspec_0.2.1 g6_m0 g6_cspec_0.2.2.1 32 g6_st0 b4_0_goal (by decide) g6_cspec_0.2.2.2.1 g6_cspec_0.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 1 => exact checkCofClose64_16_sound_aux goal6 6 g6_ix1 g6_cspec_1.1 g6_cspec_1.2.1 g6_m1 g6_cspec_1.2.2.1 8 g6_st1 b4_0_goal (by decide) g6_cspec_1.2.2.2.1 g6_cspec_1.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 2 => exact checkCofClose64_sound_aux goal6 6 g6_ix2 g6_cspec_2.1 g6_cspec_2.2.1 g6_m2 g6_cspec_2.2.2.1 2 g6_st2 c5_0_goal (by decide) g6_cspec_2.2.2.2.1 g6_cspec_2.2.2.2.2 c5_0_no_build fuel hist nxt hnd hchk
  | 3 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix3 g6_cspec_3.1 g6_cspec_3.2.1 g6_m3 g6_cspec_3.2.2.1 32 g6_st3 b4_1_goal (by decide) g6_cspec_3.2.2.2.1 g6_cspec_3.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 4 => exact checkCofClose64_16_sound_aux goal6 6 g6_ix4 g6_cspec_4.1 g6_cspec_4.2.1 g6_m4 g6_cspec_4.2.2.1 0 g6_st4 b4_0_goal (by decide) g6_cspec_4.2.2.2.1 g6_cspec_4.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 5 => exact checkCofClose64_sound_aux goal6 7 g6_ix5 g6_cspec_5.1 g6_cspec_5.2.1 g6_m5 g6_cspec_5.2.2.1 8 g6_st5 c5_1_goal (by decide) g6_cspec_5.2.2.2.1 g6_cspec_5.2.2.2.2 c5_1_no_build fuel hist nxt hnd hchk
  | 6 => exact checkCofClose64_sound_aux goal6 7 g6_ix6 g6_cspec_6.1 g6_cspec_6.2.1 g6_m6 g6_cspec_6.2.2.1 16 g6_st6 c5_1_goal (by decide) g6_cspec_6.2.2.2.1 g6_cspec_6.2.2.2.2 c5_1_no_build fuel hist nxt hnd hchk
  | 7 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix7 g6_cspec_7.1 g6_cspec_7.2.1 g6_m7 g6_cspec_7.2.2.1 0 g6_st7 b4_2_goal (by decide) g6_cspec_7.2.2.2.1 g6_cspec_7.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 8 => exact checkCofClose64_16_sound_aux goal6 6 g6_ix8 g6_cspec_8.1 g6_cspec_8.2.1 g6_m8 g6_cspec_8.2.2.1 16 g6_st8 b4_0_goal (by decide) g6_cspec_8.2.2.2.1 g6_cspec_8.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 9 => exact checkCofClose64_sound_aux goal6 7 g6_ix9 g6_cspec_9.1 g6_cspec_9.2.1 g6_m9 g6_cspec_9.2.2.1 0 g6_st9 c5_2_goal (by decide) g6_cspec_9.2.2.2.1 g6_cspec_9.2.2.2.2 c5_2_no_build fuel hist nxt hnd hchk
  | 10 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix10 g6_cspec_10.1 g6_cspec_10.2.1 g6_m10 g6_cspec_10.2.2.1 0 g6_st10 b4_3_goal (by decide) g6_cspec_10.2.2.2.1 g6_cspec_10.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | 11 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix11 g6_cspec_11.1 g6_cspec_11.2.1 g6_m11 g6_cspec_11.2.2.1 0 g6_st11 b4_4_goal (by decide) g6_cspec_11.2.2.2.1 g6_cspec_11.2.2.2.2 b4_4_no_build fuel hist nxt hnd hchk
  | 12 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix12 g6_cspec_12.1 g6_cspec_12.2.1 g6_m12 g6_cspec_12.2.2.1 32 g6_st12 b4_1_goal (by decide) g6_cspec_12.2.2.2.1 g6_cspec_12.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 13 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix13 g6_cspec_13.1 g6_cspec_13.2.1 g6_m13 g6_cspec_13.2.2.1 2 g6_st13 b4_5_goal (by decide) g6_cspec_13.2.2.2.1 g6_cspec_13.2.2.2.2 b4_5_no_build fuel hist nxt hnd hchk
  | 14 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix14 g6_cspec_14.1 g6_cspec_14.2.1 g6_m14 g6_cspec_14.2.2.1 0 g6_st14 b4_2_goal (by decide) g6_cspec_14.2.2.2.1 g6_cspec_14.2.2.2.2 b4_2_no_build fuel hist nxt hnd hchk
  | 15 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix15 g6_cspec_15.1 g6_cspec_15.2.1 g6_m15 g6_cspec_15.2.2.1 2 g6_st15 b4_5_goal (by decide) g6_cspec_15.2.2.2.1 g6_cspec_15.2.2.2.2 b4_5_no_build fuel hist nxt hnd hchk
  | 16 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix16 g6_cspec_16.1 g6_cspec_16.2.1 g6_m16 g6_cspec_16.2.2.1 32 g6_st16 b4_1_goal (by decide) g6_cspec_16.2.2.2.1 g6_cspec_16.2.2.2.2 b4_1_no_build fuel hist nxt hnd hchk
  | 17 => exact checkCofClose64_16_sound_aux goal6 6 g6_ix17 g6_cspec_17.1 g6_cspec_17.2.1 g6_m17 g6_cspec_17.2.2.1 32 g6_st17 b4_0_goal (by decide) g6_cspec_17.2.2.2.1 g6_cspec_17.2.2.2.2 b4_0_no_build fuel hist nxt hnd hchk
  | 18 => exact checkCofClose64_16_sound_aux goal6 5 g6_ix18 g6_cspec_18.1 g6_cspec_18.2.1 g6_m18 g6_cspec_18.2.2.1 0 g6_st18 b4_3_goal (by decide) g6_cspec_18.2.2.2.1 g6_cspec_18.2.2.2.2 b4_3_no_build fuel hist nxt hnd hchk
  | c + 19 => omega

def g6_L3 : Array W6Node := Array.mk [
([v143,v3,v60,v5],[],[],[]),
([0x33ccffff00000000,v3,v60,v0],[],[],[]),
([v3,v60,v93,v5],[],[],[]),
([v3,v60,v144,v5],[],[],[]),
([v3,v60,v0,v145],[],[],[])
]

def g6_L4 : Array W6Node := Array.mk [
([v40,v3,v1,v0,v146],[],[],[]),
([v13,v3,v1,v94,v5],[],[],[]),
([v13,v14,0x3033333030333330,v3,v5],[],[],[]),
([v15,v3,v93,v2,v5],[],[],[]),
([v63,v15,v3,v93,v5],[],[],[]),
([v3,v60,v0,v5],[],[],[]),
([v63,v3,v60,v0,v5],[],[],[]),
([v15,v3,v60,v0,v5],[],[],[]),
([v63,0x3f33cfcc3f33cfcc,v3,v0,v5],[],[],[]),
([v3,v77,v60,v0,v5],[],[],[(1,0),(1,1)]),
([v61,v3,v67,0xfcf3f0f0fcf3f0f0,v5],[],[],[(1,2)]),
([v61,v143,v3,v67,v5],[],[],[(0,0)]),
([v61,0x33ccffff00000000,v3,v67,v0],[],[],[(0,1)]),
([v61,v37,v3,0xfcf3f0f0fcf3f0f0,v5],[],[],[]),
([v15,0x33ffccff00000000,v3,v93,v2],[],[],[]),
([v18,v3,v60,v0,v5],[],[],[]),
([0xfcfcf000fcfcf0,v27,v3,v1,v5],[],[],[]),
([v3,0xc3c3c3ccc3c3c3cc,v0,v6,v5],[],[],[]),
([v3,v60,v54,v0,v5],[],[],[]),
([v13,v3,v60,v0,v5],[],[],[]),
([v13,v3,v1,v94,0xffffffff00333300],[],[],[]),
([v13,v3,v1,v94,v145],[],[],[]),
([v47,v3,v78,v94,v5],[],[],[]),
([v13,v3,v1,v144,0xffffffff00333300],[],[],[]),
([v47,v3,v78,v144,v5],[],[],[(0,3)]),
([v47,v3,v78,v0,v145],[],[],[(0,4)]),
([v47,v3,v60,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[0],[(0,3),(0,4)]),
([v3,v60,v0,v6,v5],[],[],[])
]

set_option maxRecDepth 100000 in

def g6_L5 : Array W6Node := Array.mk [
([v10,v8,v2,v95,v4,v5],[],[],[]),
([v40,v10,v11,v2,v4,v5],[(v8,v1,v0),(v40,v8,v6)],[1],[]),
([v14,v68,v10,v2,v4,v5],[],[],[]),
([v44,0xafaaaaaaafaaaaaa,v1,v2,v4,v5],[],[],[]),
([v1,v57,v147,v0,v19,v5],[],[1],[]),
([v10,v148,v2,v19,v4,v5],[(v69,v1,v19),(v148,v69,v0)],[1],[]),
([0xaca8aca8aca8aca8,v1,v11,v2,v4,v5],[(v11,v3,v0)],[2],[]),
([v1,v58,v149,v2,v24,v5],[(v150,v58,v4),(v149,v150,v0)],[1],[]),
([v3,0xc3c3c6c6c3c3c6c6,v0,v2,v4,v5],[],[],[]),
([v3,v1,v79,v2,v41,v4],[],[],[]),
([v40,v3,v1,v0,v34,v9],[],[],[]),
([v42,v40,v3,v1,v0,v9],[],[],[(0,0)]),
([v3,v1,v0,v8,v6,v146],[],[3],[(0,0)]),
([0xfcfc0000fcfc00,v13,v3,v1,v0,v5],[],[],[]),
([v13,v3,v1,v0,0xfcfffffcfcfffffc,v5],[],[],[]),
([0x3030000030300,v13,v3,v1,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[0,4],[(0,1)]),
([v13,v3,v1,v0,0xfc0000fcfc0000fc,v5],[],[],[]),
([v68,v118,v1,v2,v4,v5],[],[],[]),
([v13,0xcffff0c0cffff0c,v3,v1,v0,v5],[],[],[]),
([0xf3f30000f3f300,v13,v3,v1,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[0,4],[(0,1)]),
([v13,v14,v3,v1,v119,v5],[],[],[(0,1),(0,2)]),
([v151,v15,v3,0xf3f3fcfcf3f3fcfc,v2,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21)],[5],[]),
([v15,v3,v0,0xf300fc00f300fc00,v2,v5],[],[],[]),
([0xc0003000c000300,v15,v3,v0,v2,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21)],[0,4],[(0,3)]),
([0x3000c0003000c00,v15,v3,v0,v2,v5],[],[],[]),
([v15,v3,v0,0xfc00f300fc00f300,v2,v5],[],[],[(0,3)]),
([v151,v15,v3,v2,v35,v5],[],[],[(0,3)]),
([v15,v3,v0,0xf3f0fcf0f3f0fcf0,v2,v5],[],[],[]),
([v63,v15,v3,v77,v0,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21)],[5],[(0,4)]),
([v15,v3,v77,v0,v2,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21)],[0,4,5],[(0,3)]),
([v63,v3,v0,v152,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21)],[0,1,5],[(0,5),(0,6)]),
([v63,v15,v3,v0,v152,v5],[],[],[(0,7)]),
([v63,v15,v3,v0,v35,v5],[],[],[]),
([v7,v63,v15,v3,v0,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21)],[4],[(0,8)]),
([0xf030f0c0f030f0c,v15,v3,v0,v2,v5],[],[],[]),
([v63,v15,v3,v0,v2,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21)],[5],[]),
([v15,v3,v0,0xf0f3f0fcf0f3f0fc,v2,v5],[],[],[]),
([v61,v3,v67,v0,v5],[(v23,v1,v2),(v28,v1,v2),(v37,v23,v28),(v61,v37,v4),(v67,v37,v4)],[0,6],[(0,5),(0,10),(0,11),(0,12),(1,9)]),
([v61,v37,v3,v67,v0,v5],[(v67,v37,v4)],[7],[(1,7)]),
([v61,v20,v37,v3,v0,v5],[(v23,v1,v2),(v28,v1,v2),(v37,v23,v28)],[4],[]),
([v15,v3,v93,v2,v5],[(v77,v15,v2),(v93,v77,v0)],[0,8],[(0,4),(1,13)]),
([v15,v3,v77,v93,v2,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21),(v77,v15,v2),(v93,v77,v0)],[0,4],[(0,4),(0,14),(1,10)]),
([v15,v3,v0,v93,v2,v5],[],[],[]),
([v143,v37,v3,v67,v4,v5],[(v23,v1,v2),(v28,v1,v2),(v37,v23,v28),(v67,v37,v4),(v143,v67,v0)],[0,4],[(0,11),(1,3)]),
([v15,0x33ffccff00000000,v3,v77,v0,v2],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21)],[0,4],[(0,14),(1,12)]),
([0x3330ccc03330ccc0,v15,v3,v0,v2,v5],[],[],[]),
([v15,v3,0xccc03330ccc03330,v0,v2,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21)],[0,4,5],[(0,3)]),
([v15,0x3f33cfcc3f33cfcc,v3,v0,v2,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21)],[4],[(0,8)]),
([0x3033c0cc3033c0cc,v15,v3,v0,v2,v5],[],[],[]),
([0xf03f0fc0f03f0fc,v3,v1,v0,v2,v5],[],[],[]),
([v63,v15,v3,v0,v131,v5],[(v25,v1,v4),(v26,v1,v4),(v15,v25,v26)],[5],[]),
([v63,v15,v3,v86,v0,v5],[(v25,v1,v4),(v26,v1,v4),(v15,v25,v26)],[5],[]),
([v61,v37,v3,0xccff0000ccff0000,v0,v5],[(0xccff0000ccff0000,v18,v4),(v61,v37,v4)],[5,7],[]),
([v18,0x33cc000033cc0000,v3,v0,0xffff33ccffff33cc,v5],[],[],[(0,15)]),
([v15,v3,0xcc00ffcccc00ffcc,v0,v2,v5],[],[],[]),
([v61,v18,v3,v67,v0,v5],[],[],[(0,15)]),
([v15,v3,v0,v2,0xff333300ff333300,v5],[],[],[]),
([v18,v37,v3,0xfcf3f0f0fcf3f0f0,v4,v5],[],[],[]),
([v153,v132,v3,v1,v4,v5],[],[],[]),
([0xf0f0f0033333300,v3,v1,v0,v2,v4],[(0xf0f0f0033333300,v154,v9)],[3],[]),
([v3,v1,v36,v2,v4,v155],[(v155,v0,v156)],[3],[]),
([0x6363666663636666,v3,v0,v2,v4,v5],[],[],[]),
([0x3366666633666666,v3,v0,v2,v4,v5],[(v69,v1,v19),(v64,v1,v19),(0x3366666633666666,v69,v64)],[1],[]),
([v13,v3,v54,v0,v48,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[5,9],[]),
([v13,v3,v78,v0,v48,v5],[(v48,v1,v6),(v78,v13,v1)],[5],[]),
([v47,v13,v3,v1,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[0,4,9],[(0,1)]),
([v51,v13,v3,v54,v0,v5],[(v51,v1,v6),(v54,v13,v1)],[5],[]),
([v27,v3,v1,0xfcfcfcf0fcfcfcf0,v6,v5],[],[],[(0,16)]),
([v157,v3,v158,v0,v6,v5],[],[],[(0,17)]),
([v27,v3,v1,0xf3f3f3f0f3f3f3f0,v6,v5],[],[],[]),
([v27,v3,v1,v0,0xff030300ff030300,v5],[],[],[]),
([v159,v3,v160,v0,v6,v5],[],[],[(0,17)]),
([v27,v3,v1,v0,0xffc0c0ccffc0c0cc,v5],[],[],[]),
([v13,v3,v1,v0,0xf0fcfcf0f0fcfcf0,v5],[],[],[]),
([v109,v3,v54,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9),(v109,v13,v1),(v54,v13,v1)],[1,9],[(0,5),(0,18)]),
([v109,v13,v3,v54,v0,v5],[],[],[(0,19)]),
([v47,v13,v3,v54,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[5,9],[]),
([v3,v1,v54,v0,v119,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[4,9,10],[]),
([v133,v3,v1,v54,v0,v5],[],[],[]),
([v13,0xc0f0f0c0c0f0f0c,v3,v1,v0,v5],[],[],[]),
([v13,v3,v1,v54,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[9],[]),
([v13,v3,v1,v94,v5],[(v47,v13,v1),(v94,v47,v0)],[1],[]),
([v47,v13,v3,v1,v94,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[4],[(0,20),(0,21),(0,22)]),
([v13,v3,v1,v0,v94,v5],[],[],[]),
([v47,v13,v3,v1,v144,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[4],[(0,1),(0,23),(0,24)]),
([v47,v13,v3,v1,v0,0xffffffff00333300],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[0,4],[(0,20),(0,23)]),
([v47,v13,v3,v1,v0,v145],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[0,4],[(0,21),(0,25)]),
([v47,v3,v78,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[0,9],[(0,5),(0,22),(0,24),(0,25),(0,26)]),
([v47,v13,v3,v78,v0,v5],[],[],[(0,19)]),
([v47,v3,v1,v0,v119,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[4],[]),
([v133,v47,v3,v1,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[4,9,10],[]),
([v13,v3,v1,v0,0xfcf0f0fcfcf0f0fc,v5],[],[],[]),
([v133,v13,v3,v1,v119,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[4,5],[]),
([v13,0x3033333030333330,v3,v1,v0,v5],[],[],[(0,1),(0,2)]),
([v13,v3,v1,0xcccfcfcccccfcfcc,v0,v5],[],[],[]),
([v13,v3,v1,v0,0xffcccc00ffcccc00,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[0],[]),
([v109,v3,v54,v0,v6,v5],[],[],[(0,27)]),
([v13,v3,v1,v94,v6,v5],[],[],[]),
([v13,v3,v1,v0,0xff333300ff333300,v5],[],[],[]),
([v47,v3,v78,v0,v6,v5],[],[],[(0,27)]),
([v3,0xc3c3c3ccc3c3c3cc,v0,v2,v4,v5],[],[],[(0,17)])
]

set_option maxRecDepth 100000 in

def g6_L6 : Array W6Node := Array.mk [
([v49,v10,v11,v8,v2,v4,v5],[(v11,v3,v0),(v8,v1,v0)],[1,2,4,9],[]),
([v10,v11,v8,v6,v2,v4,v5],[(v11,v3,v0),(v8,v1,v0)],[1,2,4,11],[(0,0),(0,1)]),
([v1,v10,v11,v2,v41,v4,v5],[(v11,v3,v0)],[2,10],[]),
([v1,v10,v0,v2,v95,v4,v5],[],[9],[(0,0)]),
([v10,v0,v8,v2,v19,v4,v5],[(v8,v1,v0)],[1],[(0,0)]),
([v3,v10,v8,v2,v41,v4,v5],[],[],[(0,0)]),
([v40,v3,v10,v0,v2,v4,v5],[(v8,v1,v0),(v40,v8,v6)],[1],[(0,1)]),
([v14,v10,v0,v2,v19,v4,v5],[(v14,v1,v0)],[1],[(0,2)]),
([v3,v1,v70,v2,v41,v4,v5],[(v6,v2,v4)],[3,4,12],[]),
([0xfefefe00fefefe,v3,v1,v0,v2,v4,v5],[(v70,v10,v0),(0xfefefe00fefefe,v70,v6)],[1,5,6],[]),
([v44,v7,v3,v96,v2,v4,v5],[],[2],[]),
([v44,v120,v3,v1,v2,v4,v5],[(v10,v3,v1)],[2,4],[(0,3)]),
([v44,v3,v1,v80,v2,v4,v5],[],[],[]),
([v44,v7,v3,v1,v6,v4,v5],[],[13],[]),
([v44,v3,v1,v81,v2,v4,v5],[],[],[]),
([0xe0e0e000e0e0e,v3,v1,v0,v2,v4,v5],[],[],[]),
([v121,v3,v1,v0,v2,v4,v5],[],[],[]),
([v3,v1,v10,0xfef0f0f0fef0f0f0,v2,v4,v5],[],[],[]),
([v3,v1,v57,v147,v0,v6,v5],[],[1,2,5,6],[(0,4)]),
([v1,v57,v10,v0,v19,v4,v5],[(v57,v10,v2)],[6,8],[(0,4)]),
([v1,v57,v10,v0,v52,v4,v5],[(v10,v3,v1),(v57,v10,v2),(v52,v3,v45)],[0,4],[]),
([v3,v1,0xe0e0eeeee0e0eeee,v0,v6,v2,v5],[],[5],[]),
([0xafaaaaaaafaaaaaa,v1,v10,v0,v2,v4,v5],[],[9],[(0,3)]),
([v3,v1,0xe0eeeeeee0eeeeee,v0,v2,v4,v5],[],[],[]),
([0xe00eeee0e00eeee,v3,v1,v0,v2,v4,v5],[],[],[]),
([v7,v1,v10,v0,v19,v4,v5],[(v10,v3,v1),(v7,v0,v2),(v19,v3,v6)],[6,12],[]),
([0xe0eeeee0000eeee,v3,v1,v0,v2,v4,v5],[],[],[]),
([v69,v10,v0,v2,v19,v4,v5],[(v69,v1,v19)],[1,5,6],[(0,5)]),
([v87,v10,v0,v2,v19,v4,v5],[(v87,v1,v19)],[1],[]),
([v68,v1,v10,v0,v2,v4,v5],[],[],[(0,2)]),
([v10,v0,v2,v19,v48,v4,v5],[(v48,v1,v6)],[1,3,9,12],[]),
([v51,v10,v0,v2,v19,v4,v5],[(v51,v1,v6)],[1,3,9,12],[]),
([v161,v3,v1,v6,v2,v4,v5],[(v64,v10,v6),(v161,v0,v64)],[1],[]),
([v3,v1,v0,0xf0fefefef0fefefe,v2,v4,v5],[],[0,4,5,6],[]),
([0x3322332222222222,v10,v0,v2,v52,v4,v5],[],[],[]),
([v3,v1,0xee00eeee0000eeee,v0,v2,v4,v5],[],[4],[]),
([v3,v1,v103,v2,v41,v4,v5],[(v6,v2,v4)],[4,9],[]),
([0xf4f4f400f4f4f4,v3,v1,v0,v2,v4,v5],[(v103,v31,v0),(0xf4f4f400f4f4f4,v103,v6)],[1],[]),
([v31,v3,v8,v2,v41,v4,v5],[],[],[]),
([v40,v31,v3,v0,v2,v4,v5],[(v8,v1,v0),(v40,v8,v6)],[1],[]),
([v97,v122,v11,v2,v4,v5],[(v88,v3,v0),(v11,v3,v0),(v97,v122,v11)],[1,2,4,5,6,8,9],[]),
([v110,0x8484848484848484,v1,v2,v4,v5],[(v88,v3,v0),(v11,v3,v0),(v110,v88,v11),(0x8484848484848484,v110,v1)],[1,4,5,6,8,9,13],[]),
([v97,v110,v1,v2,v4,v5],[(v88,v3,v0),(v11,v3,v0),(v110,v88,v11),(v97,v1,v11)],[1,2,4,5,6,8,9,13],[]),
([0xa4a4a4a4a4a4a4a4,v1,v11,v2,v4,v5],[(v88,v3,v0),(v11,v3,v0)],[2,4,9,13],[]),
([v33,v1,v11,v8,v2,v4,v5],[(v11,v3,v0)],[2],[(0,6)]),
([v3,v1,v8,v2,v95,v4,v5],[],[9],[(0,0)]),
([v40,v3,v1,v11,v2,v4,v5],[(v8,v1,v0),(v40,v8,v6)],[1],[(0,1)]),
([v49,v44,v3,v1,v2,v4,v5],[],[2,5],[]),
([v49,v3,v1,v0,0xfefe0000fefe0000,v2,v5],[],[],[]),
([v3,v1,v0,v2,0xff323232ff323232,v4,v5],[],[],[]),
([v134,v3,v1,v2,v41,v4,v5],[],[],[]),
([v104,v1,v58,v11,v2,v4,v5],[(v104,v58,v0)],[1,4],[]),
([v104,v3,v1,v123,v2,v4,v5],[],[5,10],[]),
([v104,v3,v1,v11,v2,v4,v5],[],[4,5],[]),
([v3,v1,v0,0xfeccfa00feccfa00,v2,v4,v5],[],[],[]),
([v3,v1,0xcd05cc00cd05cc00,v0,v2,v4,v5],[],[],[]),
([v3,v1,v65,v135,v2,v4,v5],[(v11,v3,v0)],[6],[]),
([v49,v3,v1,v82,v2,v4,v5],[],[2],[]),
([v3,v1,v0,0xfb33fa00fb33fa00,v2,v4,v5],[],[],[]),
([0x3705330037053300,v3,v1,v0,v2,v4,v5],[],[],[]),
([v68,v3,v1,v2,v95,v4,v5],[],[5,10],[]),
([v68,v3,v1,v11,v2,v4,v5],[],[4,5],[]),
([v14,0x5555aaaa5555aaaa,v1,v0,v2,v5],[(v124,v3,v4),(v24,v3,v4),(0x5555aaaa5555aaaa,v124,v24),(v14,v1,v0)],[0,1,4,5,8,9,11],[]),
([v30,v1,v83,v2,v4,v5],[(v12,v3,v2),(v30,v0,v12)],[0,4,5,9],[]),
([v55,v3,0xc0ff80aac0ff80aa,v1,v0,v4,v5],[],[],[]),
([v3,0xc080ffaac080ffaa,v1,v0,v2,v4,v5],[(v29,v1,v0),(0x3f3f00003f3f0000,v29,v4)],[5],[]),
([v30,v3,v1,0xcfcacfcacfcacfca,v2,v4,v5],[],[],[]),
([v7,v3,v1,v0,0xfca8fca8fca8fca8,v4,v5],[(v12,v3,v2)],[2,5],[]),
([0x302ffaa0302ffaa,v3,v1,v0,v2,v4,v5],[],[],[]),
([0xc08ffaa0c08ffaa,v3,v1,v0,v2,v4,v5],[],[],[]),
([v14,v30,v3,0xcfcecfcecfcecfce,v2,v4,v5],[],[],[]),
([0x3020ffaa3020ffaa,v3,v1,v0,v2,v4,v5],[],[],[]),
([v7,v3,v1,v82,v2,v24,v5],[(v24,v3,v4)],[5],[]),
([v111,v3,v1,v0,v12,v4,v5],[],[],[]),
([v3,v1,v0,v2,0xff33ff2233332222,v4,v5],[],[],[]),
([v98,v162,v3,v1,v0,v4,v5],[],[4],[]),
([v1,v163,v71,v0,v12,v4,v5],[(v163,v71,v2)],[1,6,8],[(1,7)]),
([v7,v1,v71,v0,v12,v4,v5],[(v7,v0,v2)],[6,8,12],[]),
([v30,v1,v71,v0,v2,v4,v5],[(v30,v0,v12)],[8],[]),
([0x3020f0a03020f0a,v3,v1,v0,v2,v4,v5],[],[],[]),
([v3,v1,v0,0xf3f2fffaf3f2fffa,v2,v4,v5],[],[],[]),
([v7,0x3322ffaa3322ffaa,v3,v1,v0,v4,v5],[],[],[]),
([v3,v1,v164,v0,v2,v24,v5],[(v20,v0,v4)],[3],[]),
([v3,v1,0xcf0fce0acf0fce0a,v0,v2,v4,v5],[],[],[]),
([v7,v3,v1,v82,v12,v4,v5],[],[],[]),
([v30,v3,v1,v82,v2,v4,v5],[],[5],[]),
([0xc080f0a0c080f0a,v3,v1,v0,v2,v4,v5],[],[],[]),
([v3,v1,v0,0xfcf8fffafcf8fffa,v2,v4,v5],[],[2],[]),
([v7,v3,v1,0xccff88aaccff88aa,v0,v4,v5],[],[],[]),
([v111,v3,v1,v0,v2,v24,v5],[],[13],[]),
([0x3f0f3b0a3f0f3b0a,v3,v1,v0,v2,v4,v5],[],[4],[]),
([v3,0xcc88ffaa0000ffaa,v1,v0,v2,v4,v5],[(v38,v1,v5),(0x33330000ffff0000,v38,v4)],[5],[]),
([v7,v1,v165,v0,v12,v4,v5],[(v96,v7,v1)],[11],[]),
([v7,v3,v1,0xf0a0ffaaf0a0ffaa,v0,v4,v5],[],[],[]),
([v30,v3,v1,0xfcf8fcf8fcf8fcf8,v2,v4,v5],[],[5],[]),
([0xc080c080c080c08,v3,0xcfcecfcecfcecfce,v0,v2,v4,v5],[],[],[(1,8)]),
([v30,v3,v1,0xf3f2f3f2f3f2f3f2,v2,v4,v5],[],[2,5],[]),
([0x302030203020302,v3,0xc0c4c0c4c0c4c0c4,v0,v2,v4,v5],[],[],[(1,8)]),
([v30,v1,v165,v0,v2,v4,v5],[(v12,v3,v2),(v30,v0,v12)],[9],[]),
([v30,v3,v1,v2,0xfffaf0f0fffaf0f0,v4,v5],[],[5,12],[]),
([v3,v1,0xf0a0ffaa0000ffaa,v0,v2,v4,v5],[],[],[]),
([0xf0affaa0000ffaa,v3,v1,v0,v2,v4,v5],[],[],[]),
([v53,v3,v1,0xcfcc0f00cfcc0f00,v0,v4,v5],[],[],[]),
([v7,v53,v3,v1,v82,v4,v5],[],[1],[]),
([v111,v89,v3,v1,v0,v2,v5],[],[],[]),
([v7,v3,v1,v0,v79,v2,v4],[(v79,v8,v17)],[4],[]),
([v3,v1,v0,0xfc00fc00a800a800,v79,v2,v4],[(v17,v3,v5),(v8,v1,v0),(v79,v8,v17)],[1,4,9],[]),
([0x300030057005700,v3,v1,v0,v79,v2,v4],[(v8,v1,v0),(v79,v8,v17)],[1],[]),
([v3,v1,v0,v79,v6,v2,v4],[(v8,v1,v0),(v79,v8,v17)],[1,4],[(0,9)]),
([v3,v1,v8,v2,v41,v4,v17],[(v17,v3,v5)],[9],[(0,9)]),
([v40,v3,v1,v0,v2,v4,v17],[(v8,v1,v0),(v40,v8,v6)],[1],[]),
([v7,v3,v1,v82,v2,v4,v17],[(v17,v3,v5)],[5],[]),
([v111,v3,v1,v0,v2,v4,v17],[],[4],[]),
([v3,v1,v0,v105,v2,v4,0xfffff0f0fafaf0f0],[(v17,v3,v5),(0xfffff0f0fafaf0f0,v0,0xffff0000aaaa0000)],[3,5],[]),
([v22,v3,v1,v8,v2,v41,v4],[(v22,v3,v5),(v6,v2,v4)],[4,9],[]),
([v40,v22,v3,v1,v0,v2,v4],[(v8,v1,v0),(v40,v8,v6)],[1],[]),
([v22,v3,v1,v164,v0,v2,v4],[],[],[]),
([v7,v22,v3,v1,v82,v2,v4],[(v22,v3,v5)],[5],[]),
([v111,v22,v3,v1,v0,v2,v4],[],[4],[]),
([0x1515150015151500,v1,v83,v0,v2,v4,v5],[],[0,4],[]),
([0x54545400545454,v3,v1,v0,v2,v4,v5],[(v8,v1,v0),(0x54545400545454,v99,v6)],[1],[]),
([v99,v3,v1,v2,v41,v4,v5],[(v6,v2,v4)],[4],[]),
([v3,0xaca8aca8aca8aca8,v1,v0,v2,v4,v5],[],[2,5],[(0,6)]),
([v3,v1,v0,v112,v2,v4,v5],[],[0,4],[]),
([v3,v1,v0,v72,v136,v9,v5],[(v8,v1,v0),(v136,v8,v4)],[5],[]),
([v73,v74,v3,v1,v0,v34,v2],[],[],[]),
([v42,v73,v74,v3,v1,v0,v2],[],[],[]),
([0x3030300ffffff00,v3,v1,v0,v2,v4],[(v8,v1,v0),(v34,v8,v5)],[1,5,6],[]),
([v3,v1,v34,v8,v2,v41,v4],[(v34,v8,v5)],[9],[]),
([v40,v3,v1,v0,v34,v2,v4],[],[4],[(0,10)]),
([v3,v1,v0,v34,v8,v6,v9],[(v34,v8,v5),(v6,v2,v4),(v9,v2,v4)],[0,10],[(0,10)]),
([0x3030300ffffff00,v3,v1,v0,v8,v2,v4],[(v8,v1,v0),(v34,v8,v5)],[0,5,6,7,14],[]),
([v3,v1,v0,v112,v34,v2,v4],[(v8,v1,v0),(v34,v8,v5)],[0,5],[]),
([v3,v1,v0,v125,v34,v2,v4],[],[],[]),
([v3,v1,v0,v2,v4,v146],[(v8,v1,v0),(v42,v8,v5)],[1,3,5,6],[]),
([v42,v27,v3,v1,v0,v2,v4],[(v27,v0,v9)],[3],[]),
([v42,v3,v1,v8,v2,v41,v4],[(v42,v8,v5),(v6,v2,v4)],[4,9],[]),
([v42,v40,v3,v1,v0,v2,v4],[],[],[(0,11)]),
([v42,v3,v1,v0,v8,v6,v9],[(v6,v2,v4),(v9,v2,v4)],[3,4],[(0,11),(0,12)]),
([v3,v1,v0,v8,v2,v4,v146],[(v8,v1,v0),(v42,v8,v5)],[3,4,5,6,12],[(0,12)]),
([v42,v3,v1,v0,v112,v2,v4],[(v8,v1,v0),(v42,v8,v5)],[4,5],[]),
([v42,v3,v1,v0,v125,v2,v4],[],[],[]),
([v3,v1,v0,0xfca8a8a8fca8a8a8,v2,v4,v5],[(v8,v1,v0),(0xfca8a8a8fca8a8a8,v8,v19)],[1,5,6,9],[]),
([v3,0xaafefefeaafefefe,v1,v0,v2,v4,v5],[(v8,v1,v0),(v40,v8,v6)],[1,5,6],[]),
([v40,v3,v1,v0,v9,v5],[(v8,v1,v0),(v40,v8,v6)],[1,5,10],[]),
([v40,v3,v1,v0,v8,v9,v5],[],[3],[(0,10),(0,11)]),
([v13,v3,v1,v0,v8,v5],[(v8,v1,v0),(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[0,1,4,9],[(0,13),(0,14),(0,15),(0,16)]),
([v3,v1,v0,0xfcfcfc0000000000,v112,v2,v4],[],[0],[]),
([0xfcfcfc00,v3,v1,v0,v112,v2,v4],[],[4],[]),
([v118,v1,v0,v2,v19,v4,v5],[(v14,v1,v0)],[1,3,9,12],[(0,17)]),
([0xaeaeae00aeaeae,v3,v1,v0,v2,v4,v5],[],[],[]),
([v14,v68,v3,v1,v2,v4,v5],[],[2],[(0,2),(0,17)]),
([v13,v14,v3,v1,v0,v5],[(v14,v1,v0),(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[0,1,4,9,10],[(0,18),(0,19),(0,20)]),
([v3,v1,v58,v149,v2,v4,v5],[(v23,v1,v2),(v150,v58,v4),(v149,v150,v0)],[0,1,8,12],[(0,7)]),
([0xbbaaffaabbaaffaa,v1,v71,v0,v2,v4,v5],[(0x1100550011005500,v71,v2)],[3,5,8,15],[]),
([v33,v1,v71,v0,v2,v4,v5],[(v7,v0,v2)],[8,9],[]),
([v3,v1,0xefafeeaaefafeeaa,v0,v2,v4,v5],[],[],[]),
([v3,v1,0xe0a0eeaae0a0eeaa,v0,v2,v4,v5],[],[4],[]),
([v15,v3,v0,0xf3f3fcfcf3f3fcfc,v2,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21),(0xf3f3fcfcf3f3fcfc,v15,v0)],[0,1,4,5,8,13],[(0,21),(0,22),(0,23)]),
([v151,v15,v3,v0,v2,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21),(v151,v15,v0)],[0,1,4,5,8,13],[(0,21),(0,24),(0,25),(0,26)]),
([v63,v15,v3,v0,v2,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21),(v63,v15,v2)],[0,1,4,5,8],[(0,24),(0,27),(0,28),(0,29),(0,30),(0,31),(0,32),(0,33)]),
([v15,v3,v0,v2,v152,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21),(v152,v15,v2)],[0,1,4,5],[(0,29),(0,30),(0,31),(0,34)]),
([v61,v37,v3,v0,v4,v5],[(v23,v1,v2),(v28,v1,v2),(v37,v23,v28),(v61,v37,v4)],[0,1,4,6,7],[(0,37),(0,38),(0,39),(1,35),(1,36)]),
([v15,v3,v77,v0,v2,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21),(v77,v15,v2)],[0,1,4,5,8,13,14],[(0,23),(0,28),(0,35),(0,40),(0,41),(0,42),(0,44),(1,37),(1,38),(1,43)]),
([v15,v3,v0,v2,v35,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21)],[0,1,4,5,13],[(0,26),(0,32),(0,45),(0,46)]),
([v7,v15,v3,v0,v2,v5],[(v16,v1,v4),(v21,v1,v4),(v15,v16,v21),(v7,v0,v2)],[0,1,4,5,8],[(0,23),(0,24),(0,33),(0,47),(0,48),(1,39)]),
([0x2322afaa2322afaa,v3,v1,v0,v2,v4,v5],[],[],[]),
([0x4505440045054400,v3,v1,v0,v2,v4,v5],[],[],[]),
([v3,v1,0xf0ccf0ccf0ccf0cc,v0,v4,v126,v5],[(v7,v0,v2)],[5,12],[]),
([0xf0cffcc0000ffcc,v3,v1,v0,v2,v4,v5],[],[],[]),
([v3,v1,0xf000fc00f000fc00,v0,0xfff0fffcfff0fffc,v4,v5],[],[],[(1,49)]),
([0xf000f0c0f000f0c,v3,v1,v106,v2,v4,v5],[],[5,6],[]),
([0xf0fc0000f0fc,0xf0300000f030000,v3,v1,v0,v2,v5],[(v113,v1,v2),(0xf0300000f030000,0xf0fcf0fcf0fcf0fc,v4)],[4],[(0,49)]),
([v3,v1,v106,v2,0xfff0f3f0fff0f3f0,v4,v5],[],[3,5],[]),
([v15,v3,v0,v2,v131,v5],[(v25,v1,v4),(v26,v1,v4),(v15,v25,v26),(v131,v26,v2)],[0,1,4,5,6,13],[(0,29),(0,50)]),
([v15,v3,v86,v0,v2,v5],[(v25,v1,v4),(v26,v1,v4),(v15,v25,v26),(v86,v26,v2)],[0,1,2,4,5,6,8,13],[(0,51),(1,52)]),
([v18,0x33cc000033cc0000,v37,v3,v0,v4,v5],[(v113,v1,v2),(v18,v1,v2),(v37,v113,v18),(0x33cc000033cc0000,v37,v4)],[5,6],[(0,53),(1,50),(1,51)]),
([v18,v37,v3,v0,v4,0xffff33ccffff33cc,v5],[],[],[(0,53),(1,54)]),
([v61,v18,v37,v3,v0,v4,v5],[(v113,v1,v2),(v18,v1,v2),(v37,v113,v18)],[0,2,5,6,7],[(0,52),(0,55)]),
([v18,v37,v3,v67,v0,v4,v5],[],[0,7,13],[(0,55),(0,57),(1,56)]),
([v153,v3,v1,v0,v2,v4,v5],[],[],[]),
([v56,v20,0xfcf00cc0fcf00cc,v3,v1,v2,v5],[],[],[(1,58)]),
([v25,v7,v132,v3,v1,v4,v5],[(v84,v0,v2),(v7,v0,v2),(v132,v84,v7)],[6,13],[]),
([v3,0xbfafbbaabfafbbaa,v1,v0,v2,v4,v5],[],[4],[]),
([v3,v33,v1,v82,v2,v4,v5],[],[],[]),
([0x1505110015051100,v3,v1,v0,v2,v4,v5],[],[],[]),
([0x8c88afaa8c88afaa,v3,v1,v0,v2,v4,v5],[],[],[]),
([0x33333333cccccccc,v3,v0,v2,v4,v9],[(v38,v1,v5),(v46,v1,v5),(0x33333333cccccccc,v38,v46),(v9,v2,v4)],[0,1,3,4,5,6],[]),
([v3,v1,v154,v0,v2,v4,v9],[],[3,16],[(0,59)]),
([v32,v3,v1,v0,v2,v4,0xffffff00cccccc00],[],[16],[]),
([0xf0f0f000c0c0c00,v3,v1,v0,v2,v4,v5],[],[],[]),
([v3,v1,v0,0xf0f0f0ffc0c0c0cc,v2,v4,v5],[],[9],[]),
([v3,v1,v0,v2,v4,0xfffffff0fcfcfcf0,v5],[],[0,5],[]),
([0xf0f0f0003030300,v3,v1,v0,v2,v4,v5],[(0xf0f0f0003030300,0xf0f0f0f0fcfcfcfc,v9)],[2,3,5,6],[]),
([v3,v1,v36,v0,v2,v4,v156],[],[3],[(0,59),(0,60)]),
([v62,0xf0f0f00ffffff00,v3,v1,v0,v2,v4],[(0xf0f0f00ffffff00,v36,v9)],[3],[(0,59)]),
([v3,v1,v0,v2,v4,v155,v5],[(v155,v0,v156)],[3,5],[(0,60)]),
([0xf0f0f00cfcfcfcc,v3,v1,v0,v2,v4,v5],[(v27,v0,v9)],[3],[]),
([v90,v3,0xc0c00c0cc0c00c0c,v1,v2,v5],[(v56,v0,v4),(v20,v0,v4),(v90,v56,v20),(0xc0c00c0cc0c00c0c,v90,v1)],[0,1,4,5,8,9,10,13],[]),
([v90,v3,v1,v2,0xff0ffff0ff0ffff0,v5],[(v56,v0,v4),(v20,v0,v4),(v90,v56,v20)],[1,4,5,9,10,13,16],[]),
([v25,v132,v3,v1,v4,v5],[],[],[]),
([v90,v3,v100,v1,v2,v5],[(v56,v0,v4),(v20,v0,v4),(v90,v56,v20),(v100,v20,v1)],[0,1,4,5,6,8,9,10,13],[]),
([v90,v3,v1,v2,0xff0fff00ff0fff00,v5],[(v56,v0,v4),(v20,v0,v4),(v90,v56,v20)],[1,4,5,6,9,10,13,16],[]),
([v3,v33,v1,0xfcf8fcf8fcf8fcf8,v2,v4,v5],[],[],[]),
([0x8c888c888c888c88,v3,0xefeeefeeefeeefee,v0,v2,v4,v5],[],[],[(1,61)]),
([0x4544454445444544,v33,v1,v0,v2,v4,v5],[],[2,5,11],[]),
([0x2322232223222322,0x4044404440444044,v3,v0,v2,v4,v5],[],[],[(1,61)]),
([v33,v1,v165,v0,v2,v4,v5],[],[1,5],[]),
([v3,v33,v1,v2,0xfffaf0f0fffaf0f0,v4,v5],[],[12],[]),
([v33,v1,v0,0xfaffaaaafaffaaaa,v2,v4,v5],[],[5,11,12],[]),
([0xf0fff000f0fff00,v3,v100,v1,v0,v2,v5],[(v20,v0,v4)],[2,3,6],[]),
([v3,v1,v0,0xfcfcfc00cccccc00,v2,v4,v5],[],[4],[]),
([0xf0f0f0ff0f0f0f0,v3,v1,v2,v4,v9],[(v36,v0,v5),(v107,v0,v5),(0xf0f0f0ff0f0f0f0,v36,v107),(v9,v2,v4)],[0,1,3,4,5,6,9],[]),
([v3,v1,0xcfcfcf00cccccc00,v0,v2,v4,v5],[],[],[]),
([v3,v1,v148,v2,v19,v4,v5],[(v69,v1,v19),(v148,v69,v0)],[1],[(0,5)]),
([v3,v69,v0,v2,v64,v4,v5],[(v69,v1,v19),(v64,v1,v19)],[1],[(0,62)]),
([0x5544444455444444,v1,v0,v2,v19,v4,v5],[(v64,v1,v19)],[1,2,5],[]),
([v161,v3,v1,v2,v19,v4,v5],[(v64,v1,v19),(v161,v0,v64)],[1],[]),
([0xaaeeeeeeaaeeeeee,v1,v0,v2,v19,v4,v5],[(v137,v1,v19)],[1,5,8],[]),
([v137,v87,v3,v0,v2,v4,v5],[(v137,v1,v19),(v87,v1,v19)],[1],[(0,62)]),
([v68,v3,v1,v0,v2,v4,0xffffffff0f0a0a0a],[],[4],[]),
([v68,v3,v1,v0,0xf0f5f5f500000000,v2,v4],[],[0],[]),
([v51,v87,v3,v0,v2,v4,v5],[(v51,v1,v6),(v87,v1,v19)],[1],[]),
([v13,v3,v1,v0,v48,v5],[(v6,v2,v4),(v48,v1,v6),(v9,v2,v4),(v13,v6,v9)],[0,1,3,4,5,7,9,10],[(0,63),(0,64)]),
([v51,v13,v3,v1,v0,v5],[(v6,v2,v4),(v51,v1,v6),(v9,v2,v4),(v13,v6,v9)],[0,1,4,5,9,10],[(0,65),(0,66)]),
([v157,v27,v3,v1,v0,v6,v5],[],[],[(0,67),(0,68)]),
([v27,v3,v1,v158,v0,v6,v5],[],[],[(0,68)]),
([v159,v27,v3,v1,v0,v6,v5],[(v6,v2,v4),(v9,v2,v4),(v27,v0,v9)],[3,4],[(0,69),(0,70),(0,71)]),
([v27,v3,v160,v1,v0,v6,v5],[(v6,v2,v4),(v9,v2,v4),(v27,v0,v9)],[3,4],[(0,71),(0,72)]),
([v109,v13,v3,v1,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9),(v109,v13,v1)],[0,1,4,9],[(0,65),(0,73),(0,74),(0,75)]),
([v13,v3,v1,v54,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9),(v54,v13,v1)],[0,1,4,9],[(0,14),(0,65),(0,74),(0,75),(0,76),(0,77),(0,78),(0,79)]),
([v47,v13,v3,v1,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9),(v47,v13,v1)],[0,1,3,4,7,9,10],[(0,15),(0,76),(0,80),(0,81),(0,82),(0,83),(0,84),(0,85),(0,86),(0,87),(0,88),(0,89),(0,90)]),
([v13,v3,v78,v1,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9),(v78,v13,v1)],[0,1,4,9],[(0,80),(0,87),(0,88),(0,91)]),
([v13,v3,v1,v0,v119,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9),(v119,v13,v0)],[0,1,3,4,9,10],[(0,14),(0,20),(0,77),(0,89),(0,92),(0,93)]),
([v133,v13,v3,v1,v0,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9),(v133,v13,v0)],[0,1,4,9,10],[(0,15),(0,78),(0,90),(0,92),(0,94)]),
([v109,v13,v3,v1,v0,v6,v5],[],[],[(0,95),(0,96)]),
([v13,v3,v1,v54,v0,v6,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9),(v54,v13,v1)],[5,9],[(0,63),(0,66),(0,96)]),
([v47,v13,v3,v1,v0,v6,v5],[],[3,7,10],[(0,97),(0,98),(0,99)]),
([v13,v3,v78,v1,v0,v6,v5],[(v6,v2,v4),(v9,v2,v4),(v13,v6,v9)],[3,5,7,9],[(0,64),(0,99)]),
([v27,v3,v1,0xfcfcfcf0fcfcfcf0,v2,v4,v5],[],[5,6],[(0,67)]),
([v157,v3,v158,v0,v2,v4,v5],[],[],[(0,68),(0,100)]),
([v27,v3,v1,0xf3f3f3f0f3f3f3f0,v2,v4,v5],[],[2,5],[(0,69)]),
([v27,v3,v1,v0,v2,v4,0xffffffff03030300],[(v27,v0,v9)],[3],[]),
([v159,v3,v160,v0,v2,v4,v5],[],[],[(0,71),(0,100)]),
([v27,v3,v1,v0,v2,v4,0xffffffffc0c0c0cc],[(v27,v0,v9)],[3],[]),
([v27,v3,v1,0xf0f0f0f0fffffff0,v2,v4,v5],[(v27,v0,v9)],[0,3,5,6],[]),
([0x5544554444444444,v1,v0,v2,v52,v4,v5],[],[2,4,5],[]),
([0xf0e0f0e0e0e0e0e,v3,v1,v2,v52,v4,v5],[(v52,v3,v45),(v166,v1,v52),(0xf0e0f0e0e0e0e0e,v0,v166)],[0,4],[])
]

set_option maxRecDepth 100000 in

def g6_L7 : Array W6Node := Array.mk [
([v10,v11,v8,v2,v4,v5],[(v10,v3,v1),(v11,v3,v0),(v8,v1,v0)],[0,1,2,4,5,6,8,9,11],[(0,0),(0,1),(1,0)]),
([v49,v1,v10,v0,v11,v2,v4,v5],[(v11,v3,v0),(v49,v11,v2)],[1,2,4,9],[(0,0)]),
([v1,v10,v0,v11,v6,v2,v4,v5],[(v11,v3,v0),(v6,v2,v4)],[1,2,4,8,9,11],[(0,1),(0,2),(0,3)]),
([v1,v10,v0,v11,v2,v4,v17],[(v11,v3,v0)],[0,1,2,4,5,6,8,9,13,15],[]),
([v22,v1,v10,v0,v11,v2,v4],[(v10,v3,v1)],[1,2,4,8,9,11,13,15],[]),
([v44,v3,v1,v11,v2,v4,v5],[(v10,v3,v1),(v44,v10,v0)],[1,2,4,5,6,8,9,11,13],[]),
([v44,v3,v1,v0,v2,v4,v17],[(v17,v3,v5),(v44,v10,v0)],[0,1,2,4,5,6,8,9],[]),
([v14,v22,v3,v10,v0,v2,v4],[(v22,v3,v5)],[0,1,2,4,5,6,9,13],[]),
([v44,v22,v3,v1,v0,v2,v4],[(v10,v3,v1),(v22,v3,v5),(v44,v10,v0)],[0,1,2,4,5,6,8,9],[]),
([v3,v10,v0,v8,v6,v2,v4,v5],[(v10,v3,v1),(v8,v1,v0)],[1,2,4],[(0,1),(0,4),(0,5),(0,6)]),
([v14,v3,v10,v0,v6,v2,v4,v5],[(v14,v1,v0)],[1,9,13],[(0,7)]),
([v3,v1,v0,0xfe00fe00fe00fe00,v4,v5],[],[0,1,2,3,4,8,9,13,15],[]),
([v3,v1,v0,v70,v6,v2,v4,v5],[(v10,v3,v1),(v70,v10,v0),(v6,v2,v4)],[0,1,2,3,4,5,6,12],[(0,8),(0,9)]),
([v44,v7,v3,v1,v2,v4,v5],[(v10,v3,v1),(v44,v10,v0)],[1,2,4,5,13],[(0,10),(0,11),(0,13),(1,12)]),
([v44,v32,v3,v1,v2,v4,v5],[(v10,v3,v1),(v44,v10,v0)],[0,2,4,17],[(0,14),(1,14)]),
([v44,v3,v1,v0,v6,v2,v4,v5],[(v44,v10,v0)],[1,3,4,5,6,12,13],[(0,11),(0,13),(0,15),(1,13)]),
([v3,v1,0xee000000ee000000,v10,v0,v2,v4,v5],[(v10,v3,v1)],[0,1,2,4,9],[(0,16),(0,17)]),
([0x1100ff001100ff00,v3,v1,v10,v0,v2,v4,v5],[(v147,v10,v4)],[1,2,3,5,6],[]),
([v3,v1,v57,v147,v0,v2,v4,v5],[(v10,v3,v1)],[1,2,3,5,6,12],[(0,18)]),
([v3,v1,v57,v10,v0,v6,v4,v5],[(v57,v10,v2)],[2,5,6,8],[(0,18),(0,19)]),
([v3,v1,v57,v10,v0,v45,v4,v5],[(v10,v3,v1),(v57,v10,v2)],[0,2,4,5],[(0,20)]),
([0x11001100ff00ff00,v3,v1,v10,v0,v2,v4,v5],[(0xeeeeeeee00000000,v10,v5)],[0,1,2,3,5,9],[]),
([v7,v3,v96,v10,v0,v2,v4,v5],[],[1,2,3,5,13],[(0,10)]),
([v3,v1,0xe0e0eeeee0e0eeee,v0,v2,v4,v5],[(v10,v3,v1),(0xe0e0eeeee0e0eeee,v20,v10)],[0,1,2,3,4,5,6,8,9,13],[(0,21)]),
([v7,v3,v1,0xe0eee0eee0eee0ee,v0,v2,v4,v5],[(v10,v3,v1),(0xe0eee0eee0eee0ee,v7,v10)],[1,2,4,5],[]),
([v120,v3,v1,v10,v0,v2,v4,v5],[(v10,v3,v1),(v120,v7,v4)],[0,1,2,3,4,9],[(0,11),(0,22),(0,23)]),
([v3,v1,v10,v80,v0,v2,v4,v5],[(v20,v0,v4),(v80,v20,v2)],[1,2,3,4,5,9],[(0,12),(1,24)]),
([v7,v3,v1,v10,v0,v6,v4,v5],[(v10,v3,v1),(v7,v0,v2),(v6,v2,v4)],[2,3,4,6,12],[(0,13),(0,25),(1,21)]),
([v3,v1,v10,v81,v0,v2,v4,v5],[(v32,v0,v5)],[2,3,4,5,9,16],[(0,14),(1,26)]),
([v1,v10,v0,v2,v19,v4,v5],[],[1,3,5,6,8,9,12],[(0,3),(0,4),(0,7),(0,19),(0,25),(0,27),(0,28),(0,29),(1,19),(1,25)]),
([v1,v10,v0,v6,v2,v19,v4,v5],[(v10,v3,v1),(v19,v3,v6)],[1,3,5,6,9,12],[(0,30),(0,31)]),
([v3,v10,v0,v6,v2,v48,v4,v5],[(v48,v1,v6)],[1,2,3,9,12],[(0,30)]),
([v51,v3,v10,v0,v6,v2,v4,v5],[(v51,v1,v6)],[1,2,3,12],[(0,31)]),
([v3,v1,v0,v6,v2,v64,v4,v5],[(v6,v2,v4),(v64,v10,v6)],[0,1,4,5,6],[(0,16),(0,32)]),
([v121,v3,v1,v0,v2,v4,v5],[(v121,v10,v6)],[0,1,2,4,5,6,9],[(0,15),(0,33)]),
([v121,v3,v1,v10,v0,v2,v4,v5],[],[1,2,3,9],[]),
([v121,v3,v1,v0,v6,v2,v4,v5],[(v121,v10,v6)],[1,2,5,6],[]),
([v3,v1,v10,v0,v2,v41,v4,v5],[],[1,2,4,9,10],[(0,2),(0,3),(0,5),(0,8),(0,15)]),
([v1,v10,v0,v2,v52,v4,v5],[(v10,v3,v1),(v45,v2,v5),(v52,v3,v45)],[0,1,3,4,5,8,9],[(0,20),(0,34)]),
([0xeeeeeeeeeeee,v3,v1,v0,v2,v4,v5],[(v10,v3,v1),(0xeeeeeeeeeeee,v10,v59)],[0,2,3,4,5,6,9],[]),
([0xeeeeeeeeeeee,v3,v1,v10,v0,v2,v4,v5],[(v10,v3,v1)],[2,4,9],[]),
([v98,v3,v1,v10,v0,v2,v4,v5],[(v59,v4,v5),(v98,v59,v2)],[0,1,2,3,4,5,6,9,12],[(1,35)]),
([v7,v3,v1,v0,v103,v2,v4,v5],[],[0,3,4,5,9,13],[]),
([v3,v1,v0,v103,v6,v2,v4,v5],[(v31,v3,v1),(v103,v31,v0),(v6,v2,v4)],[0,1,3,4,15],[(0,36),(0,37)]),
([v7,v31,v3,v0,v8,v2,v4,v5],[(v31,v3,v1)],[4,5,9,15],[]),
([v31,v3,v0,v8,v6,v2,v4,v5],[(v31,v3,v1),(v8,v1,v0)],[1,2,4],[(0,38),(0,39)]),
([v114,v31,v3,v1,v0,v2,v4,v5],[(v127,v0,v4)],[1,2,3,5,9,15],[]),
([v7,0x4f444f444f444f44,v3,v1,v0,v2,v4,v5],[(0x4f444f444f444f44,v7,v31)],[1,4,5,9],[]),
([v7,v31,v3,v75,v0,v2,v4,v5],[(v7,v0,v2),(v75,v7,v1)],[1,5,9,15],[]),
([v120,v31,v3,v1,v0,v2,v4,v5],[(v31,v3,v1),(v120,v7,v4)],[0,1,2,4,9,15],[]),
([v31,v3,v1,v80,v0,v2,v4,v5],[(v20,v0,v4),(v80,v20,v2)],[1,2,5,9,15],[]),
([v7,v31,v3,v1,v0,v6,v4,v5],[(v31,v3,v1),(v7,v0,v2)],[1,4,6,13,15],[]),
([v3,v1,v0,v6,v2,0xff444444ff444444,v4,v5],[(v6,v2,v4),(0xff444444ff444444,v31,v6)],[0,1,4,9],[]),
([v31,v3,v0,v6,v2,v48,v4,v5],[(v6,v2,v4),(v48,v1,v6)],[1,9,15],[]),
([v31,v3,v1,v0,v2,v41,v4,v5],[(v6,v2,v4),(v41,v0,v6)],[1,2,4,9,15],[(0,36),(0,38)]),
([v122,v11,v2,v4,v5],[(v11,v3,v0)],[1,2,4,8,11],[(0,40)]),
([v1,v122,v11,v2,v4,v5],[(v11,v3,v0)],[1,2,4,8,9,11],[(0,40)]),
([v110,v1,v2,v4,v5],[],[1,4,8,11,13],[(0,41)]),
([v110,v1,v11,v2,v4,v5],[],[1,2,4,8,11,13],[(0,42)]),
([v97,v88,v1,v11,v2,v4,v5],[(v88,v3,v0),(v11,v3,v0),(v97,v1,v11)],[1,4,5,6,8,9,11,13],[(0,40),(0,42),(0,43)]),
([v49,v3,v1,v11,v8,v2,v4,v5],[(v11,v3,v0),(v8,v1,v0)],[1,2,9],[(0,0),(0,44)]),
([v3,v1,v11,v8,v6,v2,v4,v5],[(v11,v3,v0),(v8,v1,v0)],[1,2,9,11],[(0,1),(0,45),(0,46)]),
([v99,v1,v0,v11,v2,v4,v5],[(v8,v1,v0)],[1,2,4,5,8,9,11,13,15],[]),
([v7,v3,v1,v11,v8,v2,v4,v5],[(v11,v3,v0),(v8,v1,v0)],[1,2,5,9,13],[(0,44)]),
([v49,v3,v1,v0,v70,v2,v4,v5],[(v11,v3,v0),(v49,v11,v2)],[1,2,3,4,5,8,9,17],[(0,47),(0,48)]),
([v3,v1,v0,v11,0xfe00fe00fe00fe00,v4,v5],[(v11,v3,v0),(v70,v1,v11),(0xfe00fe00fe00fe00,v70,v2)],[0,1,2,4,8,9,10,11,13],[(1,48)]),
([v97,v49,v3,v1,v0,v2,v4,v5],[],[1,2,3,5,9,13],[]),
([v134,v3,v1,v0,v6,v2,v4,v5],[(v134,v1,v11)],[1,2,3,4],[(0,49),(0,50)]),
([v1,v58,v0,v11,v2,v4,v5],[(v11,v3,v0),(v23,v1,v2)],[0,1,3,4,5,6,8,9,10,11],[(0,51)]),
([v3,v1,v11,v91,v2,v4,v5],[(v11,v3,v0),(v23,v1,v2),(v91,v23,v0)],[0,1,4,5,6,9,10,11],[]),
([v3,v1,v0,v123,v2,v4,v5],[(v23,v1,v2),(v123,v23,v11)],[0,1,2,4,5,6,8,9,10,12],[(0,52)]),
([v3,v1,v0,v11,v123,v2,v4,v5],[(v23,v1,v2)],[1,9,10,11,13],[(0,53)]),
([v3,v23,v1,v0,v135,v2,v4,v5],[(v23,v1,v2),(v135,v11,v4)],[1,8,9,11],[(1,54)]),
([v49,v3,v16,v1,v0,v2,v4,v5],[(v11,v3,v0),(v49,v11,v2)],[3,5,6,8,9,12],[(1,55)]),
([v3,v1,v65,v11,v2,v4,v5],[(v11,v3,v0),(v18,v1,v2),(v65,v18,v0)],[1,2,4,5,6,13],[(0,56),(1,57)]),
([v3,v1,v0,0xfbfafbfafbfafbfa,v2,v4,v5],[],[0,1,2,4,5,6,9,12,13,15],[]),
([v3,v1,v0,v11,0xfbfafbfafbfafbfa,v2,v4,v5],[],[1,2,13,15],[]),
([v18,v3,v1,v0,v135,v2,v4,v5],[(v18,v1,v2),(v135,v11,v4)],[1,2,3,4,5,6,8,11,12],[(0,56),(1,58)]),
([v49,v26,v3,v1,v0,v2,v4,v5],[(v49,v11,v2)],[2,3,4,8],[(0,57),(1,59)]),
([v33,v1,v0,v11,v2,v4,v5],[(v7,v0,v2),(v33,v7,v3)],[1,2,4,5,8,11,13],[(0,44)]),
([v49,0x505000005050000,v3,v1,v0,v2,v4,v5],[(v11,v3,v0)],[1,3,5,6,12],[]),
([v3,v1,v11,v2,v41,v4,v5],[(v11,v3,v0),(v6,v2,v4),(v41,v0,v6)],[1,2,3,4,5,6,8,10],[(0,2),(0,8),(0,50)]),
([v3,v1,v0,v2,v95,v4,v5],[(v95,v11,v6)],[0,1,2,4,5,6,9,10],[(0,3),(0,45),(0,60)]),
([v3,v1,v0,v11,v2,v95,v4,v5],[],[1,3,10],[(0,61)]),
([0x4040c0c04040c0c,v3,v1,0xfafaf0f0fafaf0f0,v2,v4,v5],[(v124,v3,v4),(0xfafaf0f0fafaf0f0,v124,v0),(0x4040c0c04040c0c,v1,0xfafaf0f0fafaf0f0)],[0,1,4,5,6,8,9,11],[]),
([v14,v3,v1,v167,v2,v4,v5],[(v92,v3,v2),(v167,v92,v0),(v14,v1,v0)],[0,1,2,4,5,6,8,9,11],[]),
([v14,v3,v1,v0,v2,0xffffaa00ffffaa00,v5],[(v92,v3,v2),(0xffffaa00ffffaa00,v92,v4),(v14,v1,v0)],[0,1,4,5,6,9,11],[]),
([v14,0x5500ff005500ff00,v3,v1,v0,v4,v5],[(v124,v3,v4),(0x5500ff005500ff00,v124,v2),(v14,v1,v0)],[0,1,4,6,8,9,11],[]),
([0x5555aaaa5555aaaa,v1,v0,v2,v5],[],[1,8,11,15,17],[(0,62)]),
([v14,v92,v1,v0,v12,v4,v5],[(v92,v3,v2),(v12,v3,v2),(v14,v1,v0)],[0,1,4,5,6,8,9,11],[(1,62)]),
([v1,v83,v0,v2,v12,v4,v5],[(v12,v3,v2),(v29,v1,v0),(v83,v3,v29)],[0,4,5,6,8,9,11,18],[(0,63)]),
([v55,v3,v1,v0,v12,v4,v5],[(v12,v3,v2),(v29,v1,v0),(v55,v29,v2)],[0,1,3,4,5,6,9,11,18],[]),
([0x3f2a3f2a3f2a3f2a,v3,v1,v0,v2,v4,v5],[(v29,v1,v0)],[0,1,2,4,5,6,8,9,10,11,12],[]),
([v55,v3,v1,v0,v4,v24,v5],[(v24,v3,v4),(v29,v1,v0),(v55,v29,v2)],[0,1,3,4,6,8,9,11,18],[(0,64)]),
([v55,v3,v1,v0,v2,v4,v24,v5],[(v29,v1,v0)],[1,3,5,6,12],[(1,65)]),
([v138,v3,v1,v0,v2,v12,v4],[(v12,v3,v2),(v29,v1,v0),(v138,v29,v5)],[0,1,4,5,6,8,9,11,18],[]),
([v30,v3,v29,v1,v2,v4,v5],[(v12,v3,v2),(v29,v1,v0),(v30,v0,v12)],[0,1,4,5,9],[(0,63),(0,66)]),
([v7,v3,v1,v0,v8,v12,v4,v5],[(v12,v3,v2),(v7,v0,v2)],[2,4,5,17],[(0,67)]),
([v30,v3,v1,v0,v8,v2,v4,v5],[(v12,v3,v2),(v30,v0,v12)],[2,4,5,9,17],[]),
([v3,v1,v0,0xfca8fca8fca8fca8,v2,v4,v5],[(v12,v3,v2),(v8,v1,v0),(0xfca8fca8fca8fca8,v8,v12)],[0,1,2,4,5,6,8,9,12],[(0,67)]),
([v3,v1,v0,v72,v2,v4,v24,v5],[(v8,v1,v0)],[1,3,5,6,12],[(1,68)]),
([v3,v1,v0,v34,v2,v12,v4],[(v12,v3,v2),(v8,v1,v0),(v34,v8,v5)],[1,2,4,5,6,8,9,15,18],[]),
([v3,v1,v0,0xf300f300f300f300,v12,v4,v5],[(v12,v3,v2),(v14,v1,v0)],[0,1,2,5,6,9,13],[]),
([v3,v1,v0,0xf300f300f300f300,v2,v4,v24,v5],[(v14,v1,v0)],[1,6,12,13],[(1,69)]),
([v14,v43,v3,v2,v12,v4,v5],[(v12,v3,v2),(v14,v1,v0),(v43,v1,v0)],[0,1,2,4,5,6,8,9,18],[]),
([v14,v7,v3,v1,v0,v12,v4,v5],[(v12,v3,v2)],[2,4,5,13],[]),
([v14,v30,v3,v1,v2,v4,v5],[(v12,v3,v2),(v14,v1,v0),(v30,v0,v12)],[0,1,2,5,9],[(0,70)]),
([v14,v30,v3,v1,v0,v2,v4,v5],[(v12,v3,v2)],[2,4,5,9,13],[]),
([v3,v1,v139,v0,v12,v4,v5],[(v12,v3,v2),(v43,v1,v0)],[1,2,4,5,6,11,18],[]),
([v3,v1,0xcf8acf8acf8acf8a,v0,v2,v4,v5],[(v12,v3,v2),(v43,v1,v0),(0xcf8acf8acf8acf8a,v43,v12)],[1,2,4,5,6,9,12],[]),
([v3,v1,v139,v0,v2,v4,v24,v5],[(v43,v1,v0)],[1,3,5,6,12],[(1,71)]),
([v3,v1,v0,v65,v12,v4,v5],[(v12,v3,v2),(v65,v18,v0)],[1,2,5,6,7,13],[(1,72)]),
([v30,v18,v3,v1,v0,v4,v5],[(v12,v3,v2)],[1,5,9,13],[]),
([v7,v26,v3,v1,v0,v2,v24,v5],[(v24,v3,v4),(v26,v1,v4)],[1,2,5],[(0,72),(1,73)]),
([v162,v3,v1,v0,v2,v59,v4,v5],[],[0,2,4,5],[(0,75),(1,74)]),
([v1,v58,v0,v2,v4,v24,v5],[(v24,v3,v4),(v23,v1,v2),(v58,v3,v23)],[0,1,3,5,6,9,12],[(1,76),(1,77),(1,78)]),
([v3,v1,v0,v91,v2,v4,v24,v5],[(v23,v1,v2),(v91,v23,v0)],[1,3,5,6,10,12],[(1,79)]),
([v140,v3,v1,v0,v12,v4,v5],[(v16,v1,v4),(v140,v16,v2)],[0,1,3,5,8,9,10],[]),
([0x3322ffaa3322ffaa,v3,v1,v0,v2,v4,v5],[(v16,v1,v4)],[0,1,2,4,5,6,9],[(0,79),(0,80),(0,81)]),
([v7,v3,v16,v1,v0,v12,v4,v5],[(v7,v0,v2)],[1,3,5,6,8,12],[(0,77),(0,81),(1,82)]),
([v30,v3,v16,v1,v0,v2,v4,v5],[(v30,v0,v12)],[1,5,8,9,10],[(0,78),(0,79),(1,83)]),
([v3,v1,v0,v65,v2,v4,v24,v5],[(v65,v18,v0)],[1,4,6,12,13],[(1,84),(1,85),(1,86)]),
([v3,v86,v1,v0,v12,v4,v5],[(v86,v26,v2)],[1,2,3,4,5,6,8,10,15],[]),
([v3,0xcc88ffaacc88ffaa,v1,v0,v2,v4,v5],[(v12,v3,v2),(0xcc88ffaacc88ffaa,v26,v12)],[0,1,2,4,5,6,8,9],[(0,86),(0,87),(1,88)]),
([v7,v18,v3,v1,v0,v4,v24,v5],[(v24,v3,v4),(v7,v0,v2)],[1,2,4,9,18],[(0,88)]),
([v7,v26,v3,v1,v0,v12,v4,v5],[(v12,v3,v2),(v7,v0,v2)],[2,3,4,5,8],[(0,84),(1,89)]),
([v30,v26,v3,v1,v0,v2,v4,v5],[(v12,v3,v2),(v30,v0,v12)],[2,4,8],[(0,85),(0,86),(1,90)]),
([v1,0xeeeeeeeeaaaaaaaa,v0,v2,v12,v4,v5],[(v12,v3,v2),(v38,v1,v5),(0xeeeeeeeeaaaaaaaa,v3,v38)],[0,3,4,5,6,7,8,9],[]),
([v115,v3,v1,v0,v12,v4,v5],[(v12,v3,v2),(v38,v1,v5),(v115,v38,v2)],[0,1,3,4,5,6,9],[]),
([0x33223322ffaaffaa,v3,v1,v0,v2,v4,v5],[(v12,v3,v2),(v38,v1,v5),(0x33223322ffaaffaa,v38,v12)],[0,1,2,4,5,6,8,9,12],[]),
([v115,v3,v1,v0,v2,v4,v24,v5],[(v38,v1,v5)],[0,1,3,4,5,6,12],[(1,91)]),
([v7,v3,v1,v75,v0,v12,v4,v5],[(v7,v0,v2)],[2,3,5],[]),
([v7,v3,v96,v1,v0,v12,v4,v5],[(v12,v3,v2),(v96,v7,v1)],[1,2,3,5,11,13],[(0,92)]),
([v7,v3,v1,v0,v66,v12,v4,v5],[(v7,v0,v2)],[5,6,8,11,12],[]),
([v7,v20,v3,v1,v0,v2,v24,v5],[(v24,v3,v4),(v20,v0,v4)],[3,4,5,6],[(1,93)]),
([0xc080c080c080c08,v30,v3,v1,v0,v2,v4,v5],[(v12,v3,v2)],[2,5,9,13],[(0,94),(0,95)]),
([v30,v3,v1,0xcfcecfcecfcecfce,v0,v2,v4,v5],[(v12,v3,v2),(v30,v0,v12)],[2,5,9],[(0,70),(0,95)]),
([0x302030203020302,v30,v3,v1,v0,v2,v4,v5],[(v12,v3,v2),(v30,v0,v12)],[2,4,9,17],[(0,96),(0,97)]),
([v30,v3,0xc0c4c0c4c0c4c0c4,v1,v0,v2,v4,v5],[(v12,v3,v2),(v30,v0,v12)],[2,4,5,9],[(0,97),(0,98)]),
([0xf000a000f000a00,0xf0f0a0a0f0f0a0a,v3,v1,v0,v2,v4,v5],[(v24,v3,v4),(0xf0f0a0a0f0f0a0a,v0,v24)],[1,3,4,5,6,17,18],[(1,99)]),
([v30,v3,v1,v0,0xf0f50000f0f50000,v2,v4,v5],[(v30,v0,v12)],[6,8,12],[]),
([v7,0xf0f0a0a0f0f0a0a,v3,v1,v0,v2,v4,v5],[],[3,4,5,6,18],[]),
([v114,v3,v1,v0,v12,v4,v5],[(v12,v3,v2),(v127,v0,v4),(v114,v127,v2)],[1,2,4,5,8,11,13],[]),
([0xf0affaa0f0affaa,v3,v1,v0,v2,v4,v5],[(v12,v3,v2),(0xf0affaa0f0affaa,v127,v12)],[1,2,4,5,6,8,9,13],[]),
([v3,v1,v80,v0,v12,v4,v5],[(v12,v3,v2),(v20,v0,v4),(v80,v20,v2)],[0,1,2,3,5,6,8,9,10],[]),
([v7,v3,v1,v0,v66,v2,v24,v5],[(v66,v7,v4)],[1,3,5,6],[]),
([v3,v1,0xf0a0ffaaf0a0ffaa,v0,v2,v4,v5],[(v12,v3,v2),(v20,v0,v4),(0xf0a0ffaaf0a0ffaa,v20,v12)],[0,1,2,4,5,6,9],[(0,93)]),
([v7,v3,v1,v0,0xf0ffa0aaf0ffa0aa,v2,v4,v5],[(0xf0ffa0aaf0ffa0aa,v7,v24)],[1,4,5,6],[]),
([v128,v3,v1,v0,v12,v4,v5],[(v12,v3,v2),(v36,v0,v5),(v128,v36,v2)],[1,2,4,5,6,11,12,13,17],[]),
([0xf0a0f0affaaffaa,v3,v1,v0,v2,v4,v5],[(v12,v3,v2),(0xf0a0f0affaaffaa,v36,v12)],[1,2,4,5,6,9,12,13,17],[]),
([v128,v3,v1,v0,v2,v4,v24,v5],[(v36,v0,v5)],[1,3,5,6,12],[(1,100)]),
([v3,v1,v81,v0,v2,v4,v24,v5],[(v32,v0,v5)],[0,1,4,6,12,16],[(1,101)]),
([v98,v3,v1,v0,v12,v4,v5],[(v12,v3,v2),(v59,v4,v5),(v98,v59,v2)],[1,2,3,4,5,8,17],[(0,75)]),
([0xffaaffaaffaa,v3,v1,v0,v2,v4,v5],[(v12,v3,v2),(v59,v4,v5),(0xffaaffaaffaa,v59,v12)],[0,1,2,4,5,6,7,9,17],[]),
([v129,v14,v89,v1,v0,v2,v5],[(v129,v3,v4),(v89,v3,v4),(v14,v1,v0)],[0,1,4,5,6,8,9,11],[(0,62)]),
([v53,v3,v1,v0,v136,v2,v4,v5],[(v8,v1,v0),(v136,v8,v4)],[1,3,5,6,8],[]),
([v53,v3,v1,v0,0xf3f30000f3f30000,v2,v4,v5],[(v14,v1,v0)],[1,3,5,8,13],[]),
([v53,v3,v1,v0,0xfcfcf0f0fcfcf0f0,v2,v4,v5],[(v16,v1,v4),(0xfcfcf0f0fcfcf0f0,v16,v0)],[1,3,4,5,8],[]),
([v7,v53,v3,v16,v1,v0,v4,v5],[(v16,v1,v4),(v7,v0,v2)],[1,3,4,6,8],[(0,102)]),
([v53,v3,v1,v0,v82,v2,v4,v5],[(v82,v26,v0)],[1,3,4,5,8,13],[(0,57),(0,103)]),
([v7,v18,v89,v3,v1,v0,v4,v5],[(v89,v3,v4),(v7,v0,v2)],[1,2,4,9,12],[]),
([v7,v26,v53,v3,v1,v0,v4,v5],[(v53,v3,v2),(v26,v1,v4),(v7,v0,v2)],[1,2,3,4,8],[(0,103),(1,104)]),
([0x55555555aaaaaaaa,v1,v0,v2,v4],[],[0,1,4,8],[]),
([v7,v3,v1,v0,v8,v2,v4,v17],[(v17,v3,v5)],[0,2,3,4,5,9],[(0,105)]),
([v3,v1,v0,v79,v2,v4],[(v8,v1,v0),(v79,v8,v17)],[0,1,2,4,8,9,11,15],[(0,105),(0,106),(0,107),(0,108),(1,105),(1,106),(1,107)]),
([v3,v1,v0,v8,v6,v2,v4,v17],[(v17,v3,v5),(v8,v1,v0)],[0,1,2,3,4],[(0,108),(0,109),(0,110)]),
([v3,v1,v0,v65,v2,v4,v17],[(v17,v3,v5),(v65,v18,v0)],[0,1,2,4,5,6,9,12,13],[(1,111)]),
([v7,v26,v3,v1,v0,v2,v4,v17],[(v17,v3,v5),(v7,v0,v2)],[0,1,2,3,4,5,13],[(0,111),(1,112)]),
([v7,v20,v3,v1,v0,v2,v4,v17],[(v17,v3,v5),(v7,v0,v2)],[1,3,4,5,6,12],[]),
([v130,v3,v1,v0,v105,v2,v4],[(v130,v0,v17)],[0,1,3,4,5,9,12,16],[]),
([v3,v1,v0,v2,v41,v4,v17],[(v17,v3,v5),(v41,v0,v6)],[0,1,2,3,4,5,6,8,9,10],[(0,109)]),
([v3,v1,v0,v2,0xfff0fff0faf0faf0,v4,v17],[(v17,v3,v5),(0xfff0fff0faf0faf0,v0,v105)],[0,1,2,3,4,5,6,9,12,16],[(1,113)]),
([v3,v1,v0,v105,v2,0xffff0000aaaa0000,v4],[(v105,v2,v17),(0xffff0000aaaa0000,v4,v17)],[0,1,3,4,5,6,8,9,12],[(0,113),(1,113)]),
([v22,v3,v1,v0,v8,v6,v2,v4],[(v22,v3,v5),(v8,v1,v0),(v6,v2,v4)],[1,2,3,4,17],[(0,114),(0,115)]),
([v22,v3,v118,v1,v0,v2,v4],[(v14,v1,v0),(v118,v14,v3)],[0,1,2,4,5,6,8,9],[]),
([v14,v22,v3,v1,v0,v6,v2,v4],[(v22,v3,v5),(v14,v1,v0),(v6,v2,v4)],[1,4,9,13],[]),
([v22,v3,v1,v0,v91,v2,v4],[(v23,v1,v2),(v91,v23,v0)],[0,1,2,4,5,6,8,9,12],[]),
([v7,v22,v3,v16,v1,v0,v2,v4],[(v22,v3,v5),(v16,v1,v4),(v7,v0,v2)],[3,4,5,6,8,9,12],[(1,116)]),
([v22,v3,v1,v0,v65,v2,v4],[(v22,v3,v5),(v18,v1,v2),(v65,v18,v0)],[0,1,2,4,5,6,9,12,13],[(1,117)]),
([v7,v26,v22,v3,v1,v0,v2,v4],[(v22,v3,v5),(v7,v0,v2)],[2,3,4,5,8,13],[(0,117),(1,118)]),
([v22,v3,v1,v0,v2,v41,v4],[(v22,v3,v5),(v6,v2,v4),(v41,v0,v6)],[1,2,3,4,5,6,8,9],[(0,114)]),
([v1,v83,v0,v2,0xffeaffeaffeaffea,v4,v5],[(v29,v1,v0),(v83,v3,v29),(0xffeaffeaffeaffea,v83,v2)],[0,4,5,6,9,10,11,18],[(0,63)]),
([v1,v83,v0,v2,v4,v9,v5],[(v29,v1,v0),(v83,v3,v29),(v9,v2,v4)],[0,4,5,6,9,10,11,18],[(0,119)]),
([v55,v3,0xbfaabfaabfaabfaa,v1,v0,v4,v5],[(v29,v1,v0),(v55,v29,v2),(0xbfaabfaabfaabfaa,v55,v3)],[0,1,3,4,5,6,8,9,11,18],[]),
([v55,v3,v1,v0,v4,0xffff3f00ffff3f00,v5],[(v29,v1,v0),(v55,v29,v2),(0xffff3f00ffff3f00,v55,v4)],[0,1,3,4,5,6,8,9],[]),
([v3,0xbfaabfaabfaabfaa,v1,v0,v2,v4,v5],[(v29,v1,v0)],[0,1,3,4,5,6,8,9,11,12],[]),
([v55,v3,v1,v0,v4,v9,v5],[(v29,v1,v0),(v55,v29,v2),(v9,v2,v4)],[0,1,3,4,5,6,9],[]),
([v3,v1,v0,v2,v4,v9,0xffffffffc0c0c0c0],[(v29,v1,v0),(0xffffffffc0c0c0c0,v29,v5),(v9,v2,v4)],[0,1,3,4,5,6,9],[]),
([v138,v3,v1,v0,v2,v4,v9],[(v29,v1,v0),(v138,v29,v5),(v9,v2,v4)],[0,1,4,5,6,9,10],[]),
([0x3f3f3f003f3f3f00,v3,v1,v0,v2,v4,v5],[(v29,v1,v0),(v9,v2,v4)],[0,1,2,4,5,6,9,10],[]),
([v7,v99,v3,v1,v0,v2,v4,v5],[(v99,v3,v8)],[0,1,2,3,4,5,9],[]),
([v99,v3,v1,v0,v6,v2,v4,v5],[(v8,v1,v0),(v99,v3,v8),(v6,v2,v4)],[0,1,3,4,15],[(0,120),(0,121)]),
([v3,v1,v8,v2,v35,v4,v39,v5],[],[4,9,10,18],[]),
([v42,v3,v1,v0,v2,v35,v4],[(v8,v1,v0),(v42,v8,v5)],[0,1,2,3,4,5,6,9,12],[]),
([v3,v33,v1,v0,v8,v2,v4,v5],[(v7,v0,v2),(v33,v7,v3)],[1,2,4,5,9,17],[(0,44),(0,122)]),
([v3,v1,v0,0xfeaafeaafeaafeaa,v2,v4,v5],[(v8,v1,v0)],[0,1,2,3,4,5,6,8,10,12,15],[]),
([v3,v1,v0,v72,v4,v9,v5],[(v8,v1,v0),(v72,v8,v2)],[1,2,3,5,6,10],[]),
([v3,v1,v0,v72,v136,v2,v4,v5],[(v8,v1,v0)],[3,5,6,12],[(0,123),(0,124)]),
([v73,v3,v1,v0,v72,v2,v4,v5],[(v8,v1,v0),(v72,v8,v2)],[3,5,6,18],[]),
([v3,v1,v0,v72,v8,v4,v9,v5],[(v8,v1,v0),(v72,v8,v2)],[2,3,5,6,7,10],[(0,124)]),
([v73,0xfc00fc00fc00fc,v3,v1,v0,v2,v4,v5],[(v8,v1,v0),(v73,v8,v4)],[5,6,10,18],[]),
([v73,v3,v1,v0,v34,v2,v4],[(v8,v1,v0),(v73,v8,v4),(v34,v8,v5)],[1,2,4,5,6,8,9,10],[(0,125)]),
([v42,v73,v3,v1,v0,v2,v4],[(v8,v1,v0),(v73,v8,v4),(v42,v8,v5)],[0,1,2,3,4,5,6,8,9,13],[(0,126)]),
([v73,v74,v3,v1,v0,v8,v2,v5],[],[2,5,12],[(0,125),(0,126)]),
([v3,v1,v0,0xfc00ff00fc00ff00,v4,v5],[],[0,2,3,4,6,8,9,13,15],[]),
([v3,v1,v0,0xfefefefeaaaaaaaa,v2,v4],[(v8,v1,v0),(v34,v8,v5),(0xfefefefeaaaaaaaa,v3,v34)],[1,2,4,7,8,9,14],[]),
([v3,v1,v0,v34,v2,v4,v9],[(v8,v1,v0),(v34,v8,v5),(v9,v2,v4)],[1,2,4,5,6,7,9],[(0,127)]),
([v3,v1,v0,v34,v8,v6,v2,v4],[(v34,v8,v5),(v6,v2,v4)],[0,2,4,10],[(0,128),(0,129),(0,130)]),
([v3,v1,v0,v34,v8,v2,v4,v9],[(v8,v1,v0),(v34,v8,v5),(v9,v2,v4)],[0,2,4,5,6,7,14],[(0,130),(0,131),(0,132)]),
([v50,v3,v1,v0,v34,v8,v2,v4],[(v34,v8,v5),(v50,v2,v4)],[0,2,6,10],[(1,125),(1,133)]),
([v42,v3,v1,v0,v2,v4,v9],[(v8,v1,v0),(v42,v8,v5)],[0,1,2,3,4,5,6,9],[(0,134),(0,135)]),
([v42,v3,v1,v0,v8,v6,v2,v4],[(v6,v2,v4)],[2,3,4],[(0,136),(0,137),(0,138)]),
([v42,v3,v1,v0,v8,v2,v4,v9],[(v8,v1,v0),(v42,v8,v5),(v9,v2,v4)],[0,2,3,4,5,6,12],[(0,138),(0,139),(0,140)]),
([v42,v50,v3,v1,v0,v8,v2,v4],[(v50,v2,v4)],[2,3,4,6],[(1,126),(1,141)]),
([v3,v1,v0,v8,v2,v19,v4,v5],[(v8,v1,v0),(v6,v2,v4)],[1,2,4,7,17],[(0,4),(0,45),(0,120),(0,142)]),
([v3,v1,v8,v2,v41,v4,v5],[],[3,4,7,9,10,12],[(0,5),(0,8),(0,38),(0,45),(0,109),(0,114),(0,121),(0,128),(0,136)]),
([v40,v3,v1,v0,v2,v4,v5],[(v8,v1,v0),(v40,v8,v6)],[0,1,2,4,5,6,9,10],[(0,6),(0,39),(0,46),(0,110),(0,115),(0,120),(0,143),(0,144)]),
([v40,v3,v1,v0,v8,v2,v4,v5],[],[3,4,9],[(0,129),(0,137),(0,145)]),
([v3,v1,v0,v8,v6,v9,v5],[(v8,v1,v0),(v6,v2,v4),(v9,v2,v4)],[0,1,3,4,5,7,9,10],[(0,130),(0,138),(0,144),(0,145),(0,146)]),
([v27,v3,v1,v0,v8,v2,v4,v5],[(v9,v2,v4)],[2,4,5,6,9,10,18],[(0,135)]),
([v3,v1,v0,v112,v2,v4,v5],[(v8,v1,v0)],[0,1,2,4,5,6,9],[(0,147),(0,148)]),
([v3,v1,v0,v112,v8,v2,v4,v5],[],[0,4,5],[(0,132),(0,140)]),
([v3,v1,v0,v125,v2,v4,v5],[(v8,v1,v0),(v74,v4,v2),(v125,v74,v8)],[0,1,2,3,4,5,6,9,18],[]),
([v3,v1,v0,v125,v8,v2,v4,v5],[(v74,v4,v2),(v125,v74,v8)],[5,9],[(0,133),(0,141)]),
([v50,v74,v3,v1,v0,v8,v5],[(v8,v1,v0),(v50,v2,v4),(v74,v2,v4)],[0,1,4,5,6,9],[(0,146)]),
([v3,v118,v1,v0,v6,v2,v4,v5],[(v14,v1,v0)],[1,3,5,6,12,13],[(0,149),(0,150)]),
([v3,v1,v0,v8,v2,v4,v9,v5],[(v9,v2,v4)],[0,2,3,4,5,6,10,12],[(0,123)]),
([v3,v1,v0,0xfbaafbaafbaafbaa,v2,v4,v5],[(v14,v1,v0)],[0,1,4,5,6,9,12,13],[]),
([v14,v43,v3,v2,v4,v9,v5],[(v14,v1,v0),(v43,v1,v0),(v9,v2,v4)],[0,1,2,4,5,6,9],[]),
([v14,v7,v3,v1,v2,v4,v39,v5],[],[5,10,13,18],[]),
([v14,v3,v33,v1,v0,v2,v4,v5],[(v14,v1,v0),(v33,v7,v3)],[1,2,4,5,9,13],[]),
([v14,v3,v1,v0,v2,v19,v4,v5],[(v14,v1,v0)],[1,4,9,10,13],[(0,7),(0,149),(0,151)]),
([v14,v3,v1,v0,v6,v9,v5],[(v14,v1,v0),(v6,v2,v4),(v9,v2,v4)],[0,1,3,4,5,9,10],[(0,152)]),
([v14,v27,v3,v1,v0,v2,v4,v5],[],[2,4,5,9,10],[]),
([v14,v3,v1,0xf0f0fff0f0f0fff0,v2,v4,v5],[(v14,v1,v0)],[0,2,3,6,8,9,10],[]),
([v50,v74,v14,v3,v1,v0,v5],[(v14,v1,v0),(v50,v2,v4),(v74,v2,v4)],[0,1,4,5,6,9,10],[(0,152)]),
([v3,v1,0xefaaefaaefaaefaa,v0,v2,v4,v5],[(0xefaaefaaefaaefaa,v3,v139)],[1,2,3,4,5,6,12],[]),
([v3,v1,0xcfcfcf00cfcfcf00,v0,v2,v4,v5],[(v43,v1,v0),(v9,v2,v4)],[1,2,4,5,6,9,10],[]),
([v3,v1,v58,v0,v123,v2,v4,v5],[(v123,v58,v0)],[0,1,4,5,10,15],[(0,52)]),
([v104,v3,v1,v0,v2,v4,v5],[(v104,v58,v0)],[0,1,4,5,6,9,10,12],[(0,52)]),
([v104,v3,v1,v58,v0,v2,v4,v5],[(v104,v58,v0)],[0,1,4,9,10],[(0,51),(0,52)]),
([v3,v1,v163,v71,v0,v2,v4,v5],[(v16,v1,v4),(v163,v71,v2)],[0,1,3,5,6,8,9,12,14,18],[(0,76),(1,153)]),
([0x1100550011005500,v3,v1,v71,v0,v2,v4,v5],[(v16,v1,v4),(0x1100550011005500,v71,v2)],[0,1,3,5,8],[(0,154)]),
([v7,v3,v1,v71,v0,v2,v4,v5],[(v16,v1,v4),(v7,v0,v2)],[0,1,3,5,6,8,12],[(0,77),(0,155),(1,156),(1,157)]),
([v3,v1,v91,v2,v4,v39,v5],[(v23,v1,v2),(v91,v23,v0),(v39,v0,v4)],[0,3,4,6,8,9,10,12],[]),
([v3,0xbbaaffaabbaaffaa,v1,v0,v2,v4,v5],[(v140,v16,v2)],[0,1,3,4,5,8,9,10],[]),
([v15,v3,v0,v2,v5],[],[0,8,13],[(0,158),(0,159),(0,160),(0,161),(0,163),(0,164),(0,165),(1,162)]),
([v3,v23,v0,v28,v4,v39,v5],[(v23,v1,v2),(v28,v1,v2),(v39,v0,v4)],[0,1,4,5,6,9,13],[(1,164)]),
([v7,v3,v16,v0,v2,v21,v5],[(v16,v1,v4),(v21,v1,v4),(v7,v0,v2)],[0,1,4,5,6,8,9],[(0,165)]),
([v3,v33,v16,v1,v0,v2,v4,v5],[(v7,v0,v2)],[1,3,5,8,9],[(0,155),(0,166),(1,156)]),
([v3,v1,v164,v0,v2,v4,v5],[(v23,v1,v2),(v20,v0,v4),(v164,v20,v23)],[0,1,2,3,4,5,6,9],[(0,82),(0,116),(0,156),(0,167),(1,102)]),
([v7,v3,v1,0xcfcc0f00cfcc0f00,v0,v2,v4,v5],[(v16,v1,v4),(0xcfcc0f00cfcc0f00,v7,v16)],[4,5,9,18],[]),
([v7,v3,v16,v1,v0,v2,v126,v5],[],[3,9,12,18],[]),
([v7,v3,v1,0xf0ccf0ccf0ccf0cc,v0,v4,v5],[(v7,v0,v2)],[1,2,3,4,5,12],[(0,168)]),
([v7,v3,v1,v0,v28,v4,v126,v5],[(v28,v1,v2),(v126,v7,v4)],[0,3,4,5,18],[(0,168)]),
([v7,v3,v1,v0,v66,v28,v4,v5],[(v7,v0,v2),(v66,v7,v4)],[3,4,5,12],[]),
([v168,v3,v1,v2,v4,v39,v5],[(v28,v1,v2),(v168,v0,v28),(v39,v0,v4)],[1,2,4,5,6,13],[]),
([0xffccffcc,v3,v1,v0,v2,v4,v39],[(v28,v1,v2),(v39,v0,v4),(0xffccffcc,v28,v5)],[0,1,2,4,5,6,9,13],[]),
([v3,v1,0xf0c0ffccf0c0ffcc,v0,v2,v4,v5],[(v28,v1,v2),(v20,v0,v4),(0xf0c0ffccf0c0ffcc,v20,v28)],[0,1,2,4,5,6,9,13],[]),
([v7,v3,v1,v0,0xf0ffc0ccf0ffc0cc,v2,v4,v5],[(v21,v1,v4),(0xf0ffc0ccf0ffc0cc,v7,v21)],[4,5,6,13],[]),
([v3,v1,v81,v0,v2,v4,v21,v5],[(v81,v32,v2)],[0,4,6,16],[(1,169)]),
([v98,v3,v1,v0,v28,v4,v5],[(v28,v1,v2),(v59,v4,v5)],[0,1,3,4,5,9,12],[]),
([0xffccffccffcc,v3,v1,v0,v2,v4,v5],[(v28,v1,v2),(v59,v4,v5),(0xffccffccffcc,v59,v28)],[0,1,2,4,5,6,9],[]),
([v3,v1,v0,v106,v2,v35,v4,v5],[],[3,5,6],[]),
([v7,v3,v1,v0,v106,v2,v4,v5],[],[3,4,5,6,18],[]),
([v3,v1,0xf000fc00f000fc00,v0,v106,v2,v4,v5],[],[3,5],[(0,170)]),
([v3,v1,v0,v106,v2,0xfff0fffcfff0fffc,v4,v5],[],[3,5],[(0,170),(0,171)]),
([0xf0fc0000f0fc,v3,v1,v0,0xf0fcf0fcf0fcf0fc,v2,v4,v5],[(v113,v1,v2)],[0,4,5,6,12],[(0,172)]),
([0xf0003000f000300,v3,v1,v0,v106,v2,v4,v5],[(v25,v1,v4)],[0,3,4,5,6,18],[(0,173),(1,172)]),
([v18,v37,v3,v0,v4,v5],[],[0,1,2,5,13],[(0,176),(0,177),(0,178),(0,179),(1,174),(1,175)]),
([v25,v26,v3,v0,v2,v131,v5],[(v25,v1,v4),(v26,v1,v4),(v131,v26,v2)],[0,1,2,4,5,6,13],[(0,174)]),
([v25,v26,v3,v86,v0,v2,v5],[(v25,v1,v4),(v26,v1,v4),(v86,v26,v2)],[0,1,2,4,5,6,8,13],[(0,175)]),
([v25,v26,v3,v0,v2,v35,v5],[(v25,v1,v4),(v26,v1,v4),(v35,v0,v2)],[0,1,2,4,5,6,13],[(0,164)]),
([v25,v7,v26,v3,v0,v2,v5],[(v25,v1,v4),(v26,v1,v4),(v7,v0,v2)],[0,1,2,4,5,6,8,13],[(0,165)]),
([v3,v1,0xf000fcccf000fccc,v0,v2,v4,v5],[(v25,v1,v4),(v76,v0,v2)],[0,1,3,4,5,6,8,9],[]),
([v25,v7,v3,v1,v0,v2,v4,v5],[],[3,5,6,12,13],[(0,180)]),
([0xccf0fc00ccf0fc,v3,v1,v0,v2,v4,v5],[(v113,v1,v2),(v56,v0,v4)],[0,1,4,5,6,9],[]),
([v25,v3,v1,v0,v2,v169,v5],[(v25,v1,v4),(v84,v0,v2)],[0,1,4,5,6,9,13],[]),
([v25,v3,v1,v0,v2,0xff0fff0f00000000,v4],[(v25,v1,v4),(v84,v0,v2),(0xff0fff0f00000000,v84,v5)],[1,4,5,6,9,13],[]),
([v25,v84,v7,v3,v1,v4,v5],[(v25,v1,v4),(v84,v0,v2),(v7,v0,v2)],[0,1,3,4,5,6,9,13,18],[(0,182),(1,181)]),
([v153,v3,v1,v0,v2,v4,v5],[(v7,v0,v2)],[0,1,4,5,6,8,9],[]),
([v7,v153,v3,v1,v0,v2,v4,v5],[],[4,5,6],[(1,181)]),
([v25,v3,v1,v0,v66,v2,v5],[(v7,v0,v2),(v66,v7,v4)],[0,3,6,8,9,12,18],[]),
([v25,v7,v3,v1,v0,v66,v2,v5],[],[3,6,18],[]),
([v7,v3,0xbbaabbaabbaabbaa,v1,v0,v4,v5],[(v7,v0,v2)],[1,2,3,4,5,11,12,13,15],[]),
([v7,v3,0xbbbbaaaabbbbaaaa,v1,v0,v2,v4,v5],[(v26,v1,v4)],[1,3,5,15],[(1,183)]),
([v7,v3,v1,v82,v2,v4,v5],[(v26,v1,v4)],[2,4,5,12,13,18],[(0,57),(0,72),(0,84),(0,103),(0,111),(0,117),(0,184)]),
([v3,v1,0xeeaaffaaeeaaffaa,v0,v2,v4,v5],[(v26,v1,v4),(v86,v26,v2)],[0,1,2,3,4,5,6,8,10],[]),
([v18,v3,v33,v1,v0,v4,v5],[(v33,v7,v3)],[1,3,5,9,13],[]),
([v111,v3,v1,v0,v2,v4,v5],[(v18,v1,v2),(v111,v20,v18)],[0,1,2,3,4,5,6,9,10,13],[(0,73),(0,89),(0,104),(0,112),(0,118),(0,183),(0,185)]),
([v7,0x3f330f003f330f00,v3,v1,v0,v2,v4,v5],[],[2,4,5,13],[]),
([v18,v3,v101,v1,v0,v2,v4,v5],[(v20,v0,v4),(v101,v20,v3)],[1,2,4],[(0,183),(1,184),(1,186)]),
([v3,0xbbaabbaaffaaffaa,v1,v0,v2,v4,v5],[(v38,v1,v5),(0xbbaabbaaffaaffaa,v115,v3)],[0,1,3,4,5,6,8,9,12],[]),
([v115,v3,v1,v0,v4,v9,v5],[(v38,v1,v5),(v115,v38,v2),(v9,v2,v4)],[0,1,3,4,5,6,9],[]),
([0x33333333cccccccc,v3,v0,v2,v4],[],[0,3,4,12,17],[(0,187)]),
([v3,v38,v0,v2,v4,v9,v46],[(v38,v1,v5),(v46,v1,v5),(v9,v2,v4)],[0,1,2,3,4,5,6,9],[(0,187)]),
([0x33333300ffffff00,v3,v1,v0,v2,v4,v5],[(v38,v1,v5),(v9,v2,v4)],[0,1,2,4,5,6,9],[]),
([v141,v3,v1,v2,v35,v4,v5],[(v46,v1,v5),(v141,v0,v46)],[0,1,2,3,4,5,6,13],[]),
([v3,v1,v154,v0,v2,v4],[(v32,v0,v5),(v154,v32,v46)],[2,3,4,9,12,16,17],[(0,188)]),
([v32,v3,v1,v0,v2,v4,v9,v46],[],[2,3,4,10,16,18],[(0,188),(0,189)]),
([v141,v3,v1,v0,v2,v4,v9,v5],[(v46,v1,v5),(v141,v0,v46)],[0,3,4,5,13],[(0,190)]),
([v27,v3,v1,v0,v2,v4,v5,v46],[(v9,v2,v4),(v27,v0,v9)],[0,2,3,4,5,6,10,18],[(0,190),(0,191)]),
([v3,v1,v0,0xff00ff00cc00cc00,v4,v9,v5],[(v46,v1,v5),(v9,v2,v4),(0xff00ff00cc00cc00,v2,v46)],[0,1,2,3,5,6,9,10],[]),
([v3,v1,v0,v2,v4,0xffffff00cccccc00,v5],[(v46,v1,v5),(v9,v2,v4)],[0,1,2,4,5,6,9],[(0,189),(0,190),(0,192)]),
([v3,v1,v0,0xf0f0f0f0fcfcfcfc,v2,v4,v9,v5],[(v9,v2,v4)],[0,3,4,5,6,16],[(0,193)]),
([v62,v108,v3,v0,v2,v4,v9],[(v62,v1,v5),(v108,v1,v5),(v9,v2,v4)],[1,2,3,4,5,6,9],[(0,187)]),
([v62,v3,v1,v36,v0,v2,v4,v9],[],[3,4,9],[(0,188),(0,194),(0,195)]),
([v3,v1,v0,v2,v4,v156,v5],[(v62,v1,v5),(v9,v2,v4)],[0,1,2,3,4,5,6,9],[(0,193),(0,194),(0,196)]),
([v62,v27,v3,v1,v0,v2,v4,v5],[(v9,v2,v4),(v27,v0,v9)],[0,3,4,9],[(0,193),(0,197)]),
([v3,0xafaaffaaafaaffaa,v1,v0,v2,v4,v5],[(v114,v127,v2),(0xafaaffaaafaaffaa,v114,v3)],[1,2,3,4,5,8,9,13],[]),
([v3,v1,v170,v2,v4,v39,v5],[(v39,v0,v4),(v102,v2,v5),(v170,v102,v0)],[0,3,4,6,8,9,16],[]),
([0xc0cccc00c0cccc,v3,v1,v0,v2,v169,v5],[(v84,v0,v2),(v169,v84,v4),(0xc0cccc00c0cccc,v1,v169)],[0,1,4,5,6,9,13],[]),
([v90,v3,v1,v2,v5],[],[4,8,10,13,18],[(0,198),(0,199),(1,200)]),
([v7,v132,v3,v1,v4,v5],[],[1,3,4,5,10,13,18],[(0,182),(1,201),(1,202)]),
([v56,v20,v3,v100,v1,v2,v5],[(v56,v0,v4),(v20,v0,v4),(v100,v20,v1)],[0,1,4,5,6,8,9,10,12,13],[(0,201)]),
([v56,v20,v3,v1,v2,0xff0fff00ff0fff00,v5],[(v56,v0,v4),(v20,v0,v4)],[1,4,5,6,9,10,12,13,16],[(0,202)]),
([0x8c888c888c888c88,v3,v33,v1,v0,v2,v4,v5],[(v33,v7,v3)],[2,4,5,9,13],[(0,203),(0,204)]),
([v3,v33,v1,0xefeeefeeefeeefee,v0,v2,v4,v5],[(v33,v7,v3)],[2,4,5,9],[(0,204),(0,205)]),
([0x2322232223222322,v3,v33,v1,v0,v2,v4,v5],[(v7,v0,v2),(v33,v7,v3)],[2,4,9,17],[(0,206)]),
([0x4040444440404444,v3,v101,v1,v0,v2,v4,v5],[(v101,v20,v3)],[2,4,6,9],[(1,206),(1,207)]),
([v3,0xaf00aa00af00aa00,v101,v1,v0,v2,v4,v5],[(v20,v0,v4),(v101,v20,v3)],[1,3,4,5,6,12,17],[(1,208)]),
([0x5000550050005500,v3,v101,v1,v0,v2,v4,v5],[(v20,v0,v4)],[1,3,5],[(1,209)]),
([v7,v3,v101,v1,v0,v2,v4,v5],[(v101,v20,v3)],[1,3,4,5,6,12],[]),
([v3,v33,v1,v75,v0,v2,v4,v5],[(v7,v0,v2),(v33,v7,v3)],[1,2,3,5,9,13],[(0,205)]),
([v3,v33,v96,v1,v0,v2,v4,v5],[],[1,2,3,4,5,9,13],[(0,207)]),
([v3,v33,v1,v0,v66,v2,v4,v5],[(v7,v0,v2)],[1,6,12],[(0,209)]),
([v3,v1,v75,v0,v2,v4,v126,v5],[(v7,v0,v2),(v75,v7,v1)],[0,2,3,4,6,9,18],[]),
([v3,v1,v75,v0,v66,v2,v4,v5],[(v7,v0,v2)],[2,6,9,12],[(0,180)]),
([v7,0x4544454445444544,v3,v1,v0,v2,v4,v5],[(v75,v7,v1)],[1,5,9,11],[(0,205)]),
([v50,v20,v3,v1,0xcfcfcccccfcfcccc,v0,v2,v5],[(v20,v0,v4)],[2,6,12],[]),
([v3,v100,v1,v0,v2,0xff0fff00ff0fff00,v4,v5],[(v100,v20,v1)],[0,4,5,9,10,12,13],[]),
([v3,v100,v1,v80,v0,v2,v4,v5],[(v20,v0,v4)],[2,3,4,5,9,12,13],[]),
([v7,v3,v1,v165,v0,v2,v4,v5],[(v96,v7,v1)],[1,2,4,5,11],[(0,92),(0,207)]),
([v50,v20,v3,v100,v1,v0,v2,v5],[(v20,v0,v4)],[3,5,6,12,13],[(0,210)]),
([v3,0xafaaaaaaafaaaaaa,v1,v0,v2,v4,v5],[(v7,v0,v2)],[0,1,2,3,4,5,6,7,8,9,10],[(0,22)]),
([v3,v1,v0,0xfaaaffaafaaaffaa,v2,v4,v5],[(v20,v0,v4),(v80,v20,v2)],[0,1,2,3,4,5,8,9],[]),
([v7,v3,v1,v0,0xfaffaaaafaffaaaa,v2,v4,v5],[(v66,v7,v4)],[1,5,6,11],[(0,209)]),
([v7,v3,v1,v0,v19,v4,v5],[(v7,v0,v2)],[1,2,3,4,5,6,8,10,11],[(0,25)]),
([v7,0xfff0f000fff0f00,v3,v1,v0,v4,v5],[(v7,v0,v2)],[1,2,3,4,5,12],[(1,210)]),
([v3,v1,v0,0xfcfcfcfccccccccc,v2,v4,v9,v5],[(v9,v2,v4)],[0,2,3,4,5,6,10,12],[(0,211)]),
([v3,0xafaaafaaffaaffaa,v1,v0,v2,v4,v5],[(0xafaaafaaffaaffaa,v128,v3)],[1,2,3,4,5,6,9,12,13,17],[]),
([0xf0f0f0ff0f0f0f0,v3,v1,v2,v4],[],[0,3,4,12,17],[(0,212)]),
([v3,v1,v36,v2,v4,v9,v107],[(v36,v0,v5),(v107,v0,v5),(v9,v2,v4)],[0,1,3,4,5,6,9],[(0,212)]),
([0xf0f0f00ffffff00,v3,v1,v0,v2,v4,v5],[(v36,v0,v5),(v9,v2,v4)],[1,2,4,5,6,9,10],[(0,195)]),
([v3,v1,v0,v116,v4,0xffffff00ffff0f00,v5],[(v85,v0,v5),(v116,v85,v2),(0xffffff00ffff0f00,v116,v4)],[0,1,3,4,5,6,8,9],[]),
([v3,v1,v0,v116,v4,v9,v5],[(v85,v0,v5),(v116,v85,v2),(v9,v2,v4)],[0,1,3,4,5,6,9],[]),
([v85,v32,v3,v1,v2,v4,v9],[(v85,v0,v5),(v32,v0,v5),(v9,v2,v4)],[0,1,3,4,5,6,9],[(0,212)]),
([v3,v1,v0,v2,v4,0xffffff000f0f0f00,v5],[(v85,v0,v5),(v9,v2,v4)],[0,1,2,3,4,5,6,9],[]),
([v3,v1,0xcfcfcfcfcccccccc,v0,v2,v4,v9,v5],[],[0,2,4,5,7],[(0,213)]),
([v3,v1,v0,0xfaaafaaaffaaffaa,v2,v4,v5],[(v32,v0,v5),(v81,v32,v2),(0xfaaafaaaffaaffaa,v3,v81)],[1,2,4,5,6,8,9,12,16,17],[]),
([v3,v1,v81,v0,v4,v9,v5],[(v32,v0,v5),(v81,v32,v2),(v9,v2,v4)],[1,4,5,6,16],[]),
([v3,v69,v1,v0,v2,v19,v4,v5],[(v69,v1,v19)],[1,2,3,5,6,7,9,10,12,17],[(0,27),(0,214),(0,215)]),
([v3,v1,v0,v2,v19,v64,v4,v5],[(v6,v2,v4),(v19,v3,v6),(v64,v1,v19)],[1,2,5,6,7,9,10,17],[(0,215),(0,216),(0,217)]),
([v137,v3,v1,v0,v2,v19,v4,v5],[(v137,v1,v19)],[1,2,9],[(0,218),(0,219)]),
([v87,v3,v1,v0,v2,v19,v4,v5],[(v87,v1,v19)],[1,2,3,9],[(0,28),(0,219)]),
([v3,v1,v0,v2,v19,v95,v4,v5],[(v95,v0,v19)],[1,4,10],[(0,60)]),
([v68,v3,v1,v0,v2,v4,v5],[(v68,v0,v19)],[0,1,2,4,5,6,8,9,10],[(0,29),(0,60),(0,151),(0,220),(0,221)]),
([v68,v3,v1,v0,v2,v19,v4,v5],[(v6,v2,v4),(v68,v0,v19)],[1,4,7,10,17],[(0,60)]),
([v3,v1,v0,v2,v19,v48,v4,v5],[(v6,v2,v4),(v48,v1,v6)],[1,2,7,9,17],[(0,30),(0,216)]),
([v51,v3,v1,v0,v2,v19,v4,v5],[(v51,v1,v6)],[1,2,9],[(0,31),(0,218),(0,222)]),
([v87,v3,v1,v0,v6,v2,v4,v5],[(v87,v1,v19)],[1,2,9],[(0,222)]),
([0x5544444455444444,v3,v1,v0,v6,v2,v4,v5],[(v6,v2,v4),(v48,v1,v6)],[0,1,4,9],[(0,216)]),
([v3,v1,v0,v6,v48,v9,v5],[(v6,v2,v4),(v48,v1,v6),(v9,v2,v4)],[0,1,3,4,5,7,9,10],[(0,223)]),
([v3,0xaaeeeeeeaaeeeeee,v1,v0,v6,v2,v4,v5],[(v51,v1,v6)],[1,2,5,6,8],[(0,218)]),
([v51,v3,v1,v0,v6,v9,v5],[(v6,v2,v4),(v51,v1,v6),(v9,v2,v4)],[0,1,3,4,5,9,10],[(0,224)]),
([v27,v3,v1,v0,v6,v5],[(v6,v2,v4),(v9,v2,v4),(v27,v0,v9)],[1,3,4,5,10],[(0,225),(0,226),(0,227),(0,228)]),
([v13,v3,v1,v0,v5],[],[1,3,7,10],[(0,146),(0,152),(0,229),(0,230),(0,231),(0,232),(0,233),(0,234)]),
([v13,v3,v1,v0,v6,v5],[],[1,3,5,10],[(0,223),(0,224),(0,235),(0,236),(0,237),(0,238)]),
([v157,v27,v3,v1,v0,v2,v4,v5],[],[2,9],[(0,225),(0,239),(0,240)]),
([v27,v3,v1,v158,v0,v2,v4,v5],[],[2,9],[(0,226),(0,240)]),
([v159,v27,v3,v1,v0,v2,v4,v5],[(v9,v2,v4)],[2,4,5,6,9,10,18],[(0,227),(0,241),(0,242),(0,243)]),
([v27,v3,v160,v1,v0,v2,v4,v5],[(v9,v2,v4)],[2,4,5,6,9],[(0,228),(0,243),(0,244)]),
([v27,v3,v1,v0,v2,v4,v5,0xffffffff0f0f0f00],[(v9,v2,v4),(v27,v0,v9)],[0,3,4,5,6],[]),
([0xf0f0f00,v27,v3,v1,v0,v2,v4,v5],[(v9,v2,v4),(v27,v0,v9)],[0,3,4],[(0,245)]),
([v3,v1,v0,v2,v52,v166,v4,v5],[(v45,v2,v5),(v52,v3,v45),(v166,v1,v52)],[0,2,4,5,8,9,14],[(0,246),(0,247)]),
([0x3322332222222222,v3,v1,v0,v2,v52,v4,v5],[(v52,v3,v45),(0x3322332222222222,v1,v52)],[0,2,4,9],[(0,34)]),
([v3,0xaaaaffaaffaaffaa,v1,v0,v2,v4,v5],[(v59,v4,v5),(0xaaaaffaaffaaffaa,v98,v3)],[1,2,3,4,5,8,9,17],[]),
([0xffffffff0000,v3,v1,v0,v2],[],[],[])
]

set_option maxRecDepth 100000 in

def g6_L8 : Array W6Node := Array.mk [
([v3,v1,0xf8f8f8f8f8f8f8f8,v2,v4,v5],[],[0,1,8,9],[]),
([v3,v1,v0,0xf8f8f8f8f8f8f8f8,v2,v4,v5],[],[0,1,2,4,5,6,8,9],[]),
([0x7070707070707070,v3,v1,v2,v4,v5],[],[0,1,4,9],[]),
([v3,v1,v0,v2,0xffff8888ffff8888,v5],[],[0,1,6,9],[]),
([0x7700770077007700,v3,v1,v0,v4,v5],[],[0,1,8,9],[]),
([v3,v1,v0,v2,v4,0xffffffff88888888],[],[0,1,4,8,9],[]),
([0x7777777700000000,v3,v1,v0,v2,v4],[],[0,1,4,9],[]),
([v1,v10,v0,v11,v2,v4,v5],[(v10,v3,v1),(v11,v3,v0)],[0,1,2,4,8,9,11,13],[(0,0),(0,1),(0,2),(1,1)]),
([v3,v1,v10,v0,v11,v2,v4,v5],[(v10,v3,v1),(v11,v3,v0)],[0,1,2,4,5,6,8,9,11,13,15],[(0,3),(0,4),(0,5)]),
([v171,v1,v10,v0,v2,v4,v5],[],[0,1,2,4,8,9,13],[]),
([v3,v1,v10,v0,v2,v4,v17],[],[0,1,2,4,5,6,8,9,13,15],[(0,3),(0,6)]),
([v22,v3,v1,v10,v0,v2,v4],[],[0,1,2,4,5,6,8,9,13,15,17],[(0,4),(0,7),(0,8)]),
([v3,v10,v0,v8,v2,v4,v5],[(v10,v3,v1),(v8,v1,v0)],[0,1,2,4,5,6,8,9,13,15],[(0,0),(0,9)]),
([v14,v3,v10,v0,v2,v4,v5],[(v14,v1,v0)],[0,1,2,4,5,6,8,9,13],[(0,7),(0,10)]),
([v3,v1,v0,v70,v2,v4,v5],[(v10,v3,v1),(v70,v10,v0)],[0,1,2,3,4,5,6,8,9,12,13,15],[(0,11),(0,12),(1,11)]),
([v44,v3,v1,v0,v2,v4,v5],[(v10,v3,v1),(v44,v10,v0)],[0,1,2,3,4,5,6,8,9,12,13],[(0,5),(0,6),(0,8),(0,13),(0,14),(0,15),(1,13)]),
([v3,v1,v57,v0,v2,v4,v5],[(v57,v10,v2)],[0,1,2,3,4,5,6,8,9,10,12,13],[]),
([v3,v1,v57,v10,v0,v2,v4,v5],[(v10,v3,v1),(v57,v10,v2)],[0,1,2,4,5,6,7,8,9,13],[(0,16),(0,18),(0,19),(0,20),(1,17)]),
([0x1100110011001100,v3,v1,v0,v2,v4,v5],[],[0,1,2,3,4,5,6,8,9,12,13],[]),
([v3,v1,0xeeeeeeee00000000,v10,v0,v2,v4,v5],[(v10,v3,v1),(0xeeeeeeee00000000,v10,v5)],[0,1,2,4,5,6,7,8,9,14],[(0,21),(1,21)]),
([v7,v3,v1,v10,v0,v2,v4,v5],[(v10,v3,v1),(v7,v0,v2)],[0,1,2,3,4,5,6,8,9,13,18],[(0,13),(0,22),(0,24),(0,25),(0,27),(1,23),(1,26)]),
([v32,v3,v1,v10,v0,v2,v4,v5],[(v10,v3,v1),(v32,v0,v5)],[0,1,2,3,4,5,6,8,9,12,13,16,17],[(0,14),(0,28),(1,28)]),
([v3,v1,v10,v0,v6,v2,v4,v5],[(v10,v3,v1),(v6,v2,v4)],[0,1,2,3,4,5,6,8,9,12],[(0,2),(0,9),(0,10),(0,12),(0,15),(0,16),(0,19),(0,25),(0,27),(0,29),(0,30),(0,31),(0,32),(0,33),(0,34),(0,35),(0,36),(0,37),(1,19),(1,27)]),
([v3,v1,v10,v0,v45,v2,v4,v5],[(v10,v3,v1),(v45,v2,v5)],[0,1,2,3,4,5,6,8,9,12],[(0,20),(0,38),(1,39),(1,40),(1,41)]),
([v3,v1,v10,v0,v2,v4,v5],[],[0,1,2,4,5,6,8,9,13],[]),
([v3,v1,v0,0xf2f2f2f2f2f2f2f2,v2,v4,v5],[(v142,v3,v1),(0xf2f2f2f2f2f2f2f2,v142,v0)],[0,1,2,4,5,6,8,9],[]),
([v3,v1,v0,v2,v4,0xffffffff22222222],[],[0,1,2,4,8,9],[]),
([v3,v1,0xdddddddd00000000,v0,v2,v4],[],[0,1,2,4,9],[]),
([v142,v31,v0,v2,v4,v5],[],[0,1,2,8,9],[]),
([v142,v1,v0,v11,v2,v4,v5],[],[0,1,2,4,8,9,11,13],[]),
([v3,v1,v0,v103,v2,v4,v5],[(v103,v31,v0)],[0,1,2,3,4,5,6,8,9,11,12,13,15],[(0,42),(0,43),(1,42)]),
([v3,0xbb00bb00bb00bb00,v1,v0,v2,v4,v5],[],[0,1,2,3,4,5,6,8,9,10,12,15],[]),
([v31,v3,v1,v0,v11,v2,v4,v5],[(v11,v3,v0)],[0,1,2,4,5,6,8,9,11,13,15],[]),
([v31,v117,v3,v1,v0,v2,v4,v5],[(v31,v3,v1)],[0,1,2,4,5,6,8,9,15],[]),
([v31,v22,v3,v1,v0,v2,v4],[],[0,1,4,5,6,8,9,15,17],[]),
([v31,v3,v0,v8,v2,v4,v5],[(v8,v1,v0)],[0,1,2,4,5,6,8,9,11,15],[(0,44),(0,45),(1,44)]),
([v31,v3,v1,v76,v0,v2,v4,v5],[(v31,v3,v1),(v76,v0,v2)],[0,1,4,5,6,8,9,15,18],[(1,46)]),
([v7,v31,v3,v1,v0,v2,v4,v5],[(v31,v3,v1),(v7,v0,v2)],[0,1,3,4,5,6,8,9,15,18],[(0,42),(0,44),(0,47),(0,48),(0,49),(0,51),(1,50)]),
([v31,v3,v1,v0,v6,v2,v4,v5],[(v31,v3,v1),(v6,v2,v4)],[0,1,3,4,5,6,8,9,15],[(0,43),(0,45),(0,49),(0,51),(0,52),(0,53),(0,54),(1,51)]),
([v3,v122,v0,v2,v4,v5],[],[1,2,4,8],[(0,55)]),
([v3,v1,v122,v0,v2,v4,v5],[],[1,2,4,5,6,8,9],[(0,56)]),
([0x4c4c4c4c4c4c4c4c,v3,v0,v2,v4,v5],[],[0,1,4,9],[]),
([v3,v1,v0,v2,0xffffa0a0ffffa0a0,v5],[],[1,4,6],[]),
([0x5f005f005f005f00,v3,v1,v0,v4,v5],[],[1,4,8],[]),
([v3,v1,v0,v2,v4,0xffffffffa0a0a0a0],[],[0,1,4],[]),
([0x5f5f5f5f00000000,v3,v1,v0,v2,v4],[],[0,1,4,8],[]),
([v88,v1,v11,v2,v4,v5],[],[1,4,8,11,13],[(0,55),(0,56),(0,57),(0,58),(0,59)]),
([v3,v1,v0,v11,v2,v4,v17],[],[0,1,4,5,6,8,9,11,15,17],[(0,3)]),
([v22,v3,v1,v0,v11,v2,v4],[(v22,v3,v5)],[1,4,5,6,8,9,11,15],[(0,4)]),
([v3,v1,v11,v8,v2,v4,v5],[(v11,v3,v0),(v8,v1,v0)],[0,1,2,4,5,6,8,9,11,15],[(0,0),(0,60),(0,61),(1,60)]),
([v3,v1,v0,v11,v8,v2,v4,v5],[(v8,v1,v0)],[1,2,4,5,6,8,9,10,11,13,17,18],[(0,62),(0,63),(1,63)]),
([v14,v3,v1,v0,v11,v2,v4,v5],[(v14,v1,v0)],[0,1,2,4,5,6,8,9,10,11,13,15,18],[]),
([v43,v3,v1,v11,v2,v4,v5],[(v43,v1,v0)],[1,2,4,5,6,8,9,10,11,15],[]),
([v3,v1,v0,v11,v70,v2,v4,v5],[(v70,v1,v11)],[0,1,2,4,5,6,8,9,10,11,13,17,18],[(0,5),(0,62),(0,64),(0,65),(1,64),(1,65)]),
([v97,v3,v1,v0,v11,v2,v4,v5],[(v11,v3,v0),(v97,v1,v11)],[0,1,2,4,5,6,8,9,10,11,13,15,18],[(0,59),(0,66),(1,66)]),
([v134,v3,v1,v0,v2,v4,v5],[(v11,v3,v0),(v134,v1,v11)],[0,1,2,3,4,5,6,8,9,11,12,13],[(0,67)]),
([v3,v23,v1,v0,v11,v2,v4,v5],[(v11,v3,v0),(v23,v1,v2)],[0,1,3,4,5,6,8,9,10,11,18],[(0,68),(0,69),(0,70),(0,71),(0,72),(1,73)]),
([v18,v3,v1,v0,v11,v2,v4,v5],[(v11,v3,v0),(v18,v1,v2)],[0,1,2,3,4,5,6,8,9,10,11,13,18],[(0,74),(0,75),(0,76),(0,77),(1,78)]),
([v7,v3,v1,v0,v11,v2,v4,v5],[(v11,v3,v0),(v7,v0,v2)],[1,4,5,6,8,9,10,11,13,18],[(0,63),(0,79)]),
([v3,v1,v0,0xfa00fa00fa00fa00,v2,v4,v5],[(0xfa00fa00fa00fa00,v11,v2)],[0,1,2,3,4,5,6,8,9,11,12,17],[(1,72),(1,77)]),
([v49,v3,v1,v0,v2,v4,v5],[(v49,v11,v2)],[0,1,2,3,4,5,6,8,9,10,11,12,17],[(0,73),(0,78)]),
([v49,v3,v1,v0,v11,v2,v4,v5],[(v11,v3,v0),(v49,v11,v2)],[0,1,4,5,6,8,9,10,11,13,17,18],[(0,1),(0,60),(0,64),(0,66),(0,79),(0,80)]),
([v3,v1,v0,v11,v6,v2,v4,v5],[(v11,v3,v0),(v6,v2,v4)],[0,1,3,4,5,6,8,9,10,11,13],[(0,2),(0,12),(0,61),(0,67),(0,81),(0,82),(0,83)]),
([v3,v1,0xcececececececece,v0,v2,v4,v5],[],[0,1,2,4,5,6,8,9,13],[]),
([v3,v1,v0,v11,v2,v4,v5],[],[1,2,4,5,6,8,9,11,13,15],[]),
([v3,v1,v0,v2,v4,0xffffffff0a0a0a0a],[],[0,1,4,8],[]),
([v3,v1,v0,0xf5f5f5f500000000,v2,v4],[],[0,1,4,8],[]),
([v171,v117,v1,v2,v4,v5],[],[1,4,8],[(0,57)]),
([v171,v14,v3,v1,v0,v2,v4,v5],[(v14,v1,v0)],[0,1,2,4,5,6,8,9,13],[]),
([v3,v1,0xdcdcdcdcdcdcdcdc,v0,v2,v4,v5],[(0xdcdcdcdcdcdcdcdc,v117,v1)],[0,1,2,3,4,5,6,8,9,10,12,15],[]),
([v3,0xaf00af00af00af00,v1,v0,v2,v4,v5],[(0xaf00af00af00af00,v117,v2)],[1,2,3,4,5,6,8,9,12,13,18],[]),
([v117,v3,v1,v0,v2,v4,v17],[],[0,1,4,5,6,8,9,15,17],[]),
([v117,v3,v1,v8,v2,v4,v5],[(v8,v1,v0)],[1,2,4,5,6,8,9,10,13,15],[]),
([v3,0xeecceecceecceecc,v0,v2,v4,v5],[],[1,2,5,8,13,17],[]),
([v3,v1,0xeecceecceecceecc,v0,v2,v4,v5],[],[0,1,2,4,5,6,8,9,13,17],[]),
([0x4444cccc4444cccc,v3,v0,v2,v4,v5],[],[0,1,6,8,9],[]),
([v3,v1,v167,v2,v4,v5],[],[1,5,8,11,15,17],[(1,84)]),
([v3,v1,v0,v167,v2,v4,v5],[],[0,1,2,4,5,6,8,9,11,15,17],[(0,85)]),
([0x5050f0f05050f0f0,v3,v1,v2,v4,v5],[],[1,4,6,8],[]),
([v3,v1,v0,v2,0xffffaa00ffffaa00,v5],[],[1,5,6,11,15,17],[(0,86)]),
([0x5500ff005500ff00,v3,v1,v0,v4,v5],[],[1,6,8,11,15,17],[(0,87)]),
([v3,v1,v0,v2,v4,0xffffffffaa00aa00],[],[0,1,4,5,8],[]),
([0x5555ffff00000000,v3,v1,v0,v2,v4],[],[0,1,4,6,8],[]),
([v92,v1,v0,v12,v4,v5],[],[1,5,8,11,15,17],[(0,89),(1,88)]),
([v14,v92,v3,v1,v0,v2,v4,v5],[(v92,v3,v2),(v14,v1,v0)],[0,1,4,5,6,8,9,11,13],[(0,85),(0,86),(0,89),(1,87)]),
([v3,v29,v1,v0,v2,v12,v4,v5],[(v12,v3,v2),(v29,v1,v0)],[0,1,4,5,6,8,9,11,17,18],[(0,90),(0,91),(0,92),(0,95),(0,96),(1,93),(1,94)]),
([v3,v1,v0,v8,v2,v12,v4,v5],[(v12,v3,v2),(v8,v1,v0)],[0,1,2,4,5,6,8,9,15,17,18],[(0,97),(0,98),(0,99),(0,101),(1,100)]),
([v14,v3,v1,v0,v2,v12,v4,v5],[(v12,v3,v2),(v14,v1,v0)],[0,1,4,5,6,8,9,13,15,18],[(0,89),(0,102),(0,104),(0,105),(0,106),(0,107),(1,103)]),
([v43,v3,v1,v0,v2,v12,v4,v5],[(v12,v3,v2),(v43,v1,v0)],[1,2,4,5,6,8,9,11,15,18],[(0,104),(0,108),(0,109),(1,110)]),
([v18,v3,v1,v0,v12,v4,v5],[(v12,v3,v2),(v18,v1,v2)],[0,1,2,5,6,7,8,9,13,15],[(0,111),(0,112),(1,113)]),
([v162,v3,v1,v0,v2,v4,v5],[(v12,v3,v2),(v162,v1,v12)],[0,1,2,4,5,6,8,9,12,13],[(0,114)]),
([v3,v23,v1,v0,v2,v4,v24,v5],[(v24,v3,v4),(v23,v1,v2)],[0,1,3,4,5,6,9],[(0,115),(0,116),(1,117),(1,118),(1,119),(1,120)]),
([v18,v3,v1,v0,v2,v4,v24,v5],[(v24,v3,v4),(v18,v1,v2)],[0,1,2,4,5,6,9,15],[(0,121),(0,124),(1,122),(1,123),(1,125),(1,126)]),
([v3,v38,v1,v0,v2,v12,v4,v5],[(v12,v3,v2),(v38,v1,v5)],[0,1,4,5,6,8,9,12,17],[(0,127),(0,128),(0,129),(1,130)]),
([v108,v3,v1,v0,v2,v12,v4,v5],[(v12,v3,v2),(v108,v1,v5)],[0,1,2,4,5,6,8,9,12,17],[]),
([v7,v3,v1,v0,v12,v4,v5],[(v12,v3,v2),(v7,v0,v2)],[1,3,4,5,6,8,11,13,15,17,18],[(0,97),(0,105),(0,119),(0,125),(0,131),(0,132),(0,133),(1,134)]),
([v30,v3,v1,v0,v2,v4,v5],[(v12,v3,v2),(v30,v0,v12)],[0,1,2,4,5,6,8,9,12,17],[(0,96),(0,98),(0,106),(0,107),(0,112),(0,120),(0,126),(0,135),(0,136),(0,137),(0,138),(0,140),(1,139),(1,141)]),
([v3,v1,v76,v0,v2,v4,v24,v5],[(v24,v3,v4),(v76,v0,v2)],[1,4,5,6,9,13,15],[(1,142),(1,143)]),
([v7,v3,v1,v0,v2,v4,v24,v5],[(v24,v3,v4),(v7,v0,v2)],[0,1,3,4,5,6,9,13,15],[(0,113),(0,124),(0,134),(0,141),(0,145),(0,147),(1,144),(1,146)]),
([v3,v1,v36,v0,v2,v12,v4,v5],[(v12,v3,v2),(v36,v0,v5)],[1,4,5,6,8,9,12,13,15,17],[(0,148),(0,149),(1,150)]),
([v32,v3,v1,v0,v2,v12,v4,v5],[(v12,v3,v2),(v32,v0,v5)],[0,1,4,5,6,7,8,9,12,13,15,16,17],[(1,151)]),
([v3,v1,v0,0xff00aa00ff00aa00,v2,v4,v5],[],[0,1,2,3,4,5,6,9,10,17],[]),
([v3,v1,v0,v45,v2,v4,v24,v5],[(v24,v3,v4),(v45,v2,v5)],[0,1,3,4,5,6,9,14,15,17],[(1,114),(1,152),(1,153)]),
([v3,v1,0xcccceeeecccceeee,v0,v2,v4,v5],[],[0,1,2,4,5,6,9,13,17],[]),
([v3,v1,v0,0xf0f0fafaf0f0fafa,v2,v4,v5],[],[0,1,2,4,5,6,9,11,15,17],[]),
([v3,v1,v0,v2,v4,0xffffffff0000aaaa],[],[0,1,4,6],[]),
([v3,v1,v0,v2,0xff55ff5500000000,v4],[],[0,1,4,5,8],[]),
([v129,v89,v1,v0,v2,v5],[],[1,6,8,11,15,17],[(0,88),(0,154)]),
([v129,v14,v3,v1,v0,v2,v4,v5],[(v129,v3,v4),(v14,v1,v0)],[0,1,4,5,6,9,11,13],[(0,154)]),
([0x5500000055000000,v3,v1,v0,v2,v4,v5],[],[0,1,2,3,4,5,6,8,9,10,12,17],[]),
([v53,v3,v1,v0,v8,v2,v4,v5],[(v8,v1,v0)],[0,1,2,3,4,5,6,7,8,9,10,15,17],[(0,155)]),
([v14,v53,v3,v1,v0,v2,v4,v5],[(v53,v3,v2),(v14,v1,v0)],[0,1,3,4,5,6,8,9,10,13,15],[(0,156),(1,154)]),
([v18,v53,v3,v1,v0,v4,v5],[],[0,1,2,3,5,6,8,9,10,13,15],[]),
([v53,v3,v16,v1,v0,v2,v4,v5],[(v53,v3,v2),(v16,v1,v4)],[0,1,3,4,5,6,8,9],[(0,73),(0,157),(0,158)]),
([v18,v89,v3,v1,v0,v2,v4,v5],[(v89,v3,v4),(v18,v1,v2)],[0,1,2,4,5,6,8,9,12,15],[(0,160),(1,78),(1,159),(1,161)]),
([v7,v53,v3,v1,v0,v4,v5],[(v7,v0,v2)],[1,3,4,5,6,8,10,13,15,17],[(0,158),(0,161)]),
([v7,v89,v3,v1,v0,v2,v4,v5],[(v89,v3,v4),(v7,v0,v2)],[0,1,3,4,5,6,8,9,12,13,15,18],[(0,160)]),
([v3,v1,0xeeeeeeeecccccccc,v0,v2,v4,v5],[],[0,1,2,4,5,6,8,9],[]),
([v22,v3,v1,v0,v2,v4],[],[0,1,4,8],[]),
([0xaaaaaaaa00000000,v1,v0,v2,v4,v17],[],[0,1,4],[(0,162)]),
([v22,v1,v0,v2,v4,v17],[],[0,1,3,4,8],[]),
([v3,v1,v0,v8,v2,v4,v17],[(v8,v1,v0)],[0,1,2,3,4,5,6,8,9,11,12,15],[(0,163),(0,164),(0,165),(1,163)]),
([v43,v3,v1,v0,v2,v4,v17],[(v17,v3,v5),(v43,v1,v0)],[0,1,2,3,4,5,6,8,9,10,11,12],[]),
([v18,v3,v1,v0,v2,v4,v17],[(v17,v3,v5),(v18,v1,v2)],[0,1,2,3,4,5,6,8,9,12,13,15],[(0,166),(1,167)]),
([v3,v1,v76,v0,v2,v4,v17],[(v17,v3,v5),(v76,v0,v2)],[0,1,4,5,6,8,9,12,13,15,16],[]),
([v7,v3,v1,v0,v2,v4,v17],[(v7,v0,v2)],[0,1,3,4,5,6,8,9,12,15,16],[(0,163),(0,167),(0,168)]),
([v3,v1,0xf0f0f0f0a0a0a0a0,v0,v2,v4,v17],[(0xf0f0f0f0a0a0a0a0,v0,v17)],[0,1,3,4,5,6,8,9,12,17],[]),
([v130,v3,v1,v0,v2,v4,v17],[(v130,v0,v17)],[0,1,3,4,5,6,8,9,12,16,17],[(0,169),(1,169)]),
([v3,v1,v0,v6,v2,v4,v17],[(v17,v3,v5),(v6,v2,v4)],[0,1,3,4,5,6,8,9,10,12,15],[(0,165),(0,170)]),
([v3,v1,v0,v105,v2,v4,v17],[(v105,v2,v17)],[0,1,3,4,5,6,8,9,12,16],[(0,169),(0,171),(0,172)]),
([v3,v1,v36,v0,v2,v4,v17],[(v36,v0,v5)],[0,1,3,4,5,6,8,9,12,17],[]),
([v32,v3,v1,v0,v2,v4,v17],[(v32,v0,v5)],[0,1,3,4,5,6,8,9,10,16,17,18],[]),
([v130,v3,v1,v0,v2,v4,v5],[(v130,v0,v17)],[0,1,2,3,4,5,6,8,9,12,16,17],[]),
([v3,v1,v0,v45,v2,v4,v17],[(v17,v3,v5)],[0,1,4,5,6,9,12,14],[]),
([v3,v1,v0,v105,v2,v4,v5],[],[0,1,2,3,4,5,6,7,8,9,10,12],[]),
([v3,v1,v0,0xf0f0f0f0fafafafa,v2,v4,v5],[],[0,1,2,4,5,6,8,9],[]),
([v3,v1,v0,v2,v4,v17],[],[0,1,4,8],[]),
([0xaaaaaaaa,v22,v1,v0,v2,v4],[],[0,1,4],[(0,162)]),
([v22,v3,v1,v0,v8,v2,v4],[(v8,v1,v0)],[0,1,2,4,5,6,7,8,9,14,15,17],[(0,173)]),
([v14,v22,v3,v1,v0,v2,v4],[(v14,v1,v0)],[0,1,4,5,6,7,8,9,14],[(0,7),(0,174),(0,175)]),
([v22,v3,v23,v1,v0,v2,v4],[(v23,v1,v2)],[0,1,4,5,6,8,9,14,17],[(0,176),(1,177)]),
([v18,v22,v3,v1,v0,v2,v4],[(v18,v1,v2)],[0,1,2,4,5,6,7,8,9,13,14,15,17],[(0,178),(1,179)]),
([v7,v22,v3,v1,v0,v2,v4],[(v22,v3,v5),(v7,v0,v2)],[1,3,4,5,6,7,8,9,14,15],[(0,177),(0,179)]),
([v22,v3,v1,v0,v6,v2,v4],[(v22,v3,v5)],[1,3,4,5,6,7,8,9,10,14,15,17],[(0,173),(0,175),(0,180)]),
([v1,v83,v0,v2,v4,v5],[],[0,4,9,10,11,18],[(0,181),(0,182),(1,181)]),
([v3,v1,v83,v0,v2,v4,v5],[(v29,v1,v0)],[0,1,2,3,4,5,6,8,9,10,11,12,18],[(0,90),(1,90)]),
([0x2a2a2a2a2a2a2a2a,v1,v0,v2,v4,v5],[],[0,1,4,9],[]),
([v3,v1,v0,v2,0xffffc0c0ffffc0c0,v5],[],[0,4,6,8,9],[]),
([v55,v3,v1,v0,v4,v5],[],[0,3,4,9,11,18],[(0,93),(0,183),(0,184)]),
([v55,v3,v1,v0,v2,v4,v5],[],[0,1,2,3,4,5,6,9,11,12,18],[(0,91),(0,94),(0,185),(0,186)]),
([v3,v1,v0,v2,v4,0xffffffffc0c0c0c0],[],[0,3,4,9,12,17],[(0,187)]),
([v138,v3,v1,v0,v2,v4],[],[0,4,9,10,11,18],[(0,95),(0,188),(1,95)]),
([v3,v29,v1,v0,v2,v4,v9,v5],[(v29,v1,v0),(v9,v2,v4)],[0,1,4,5,6,9,10],[(0,182),(0,186),(0,187),(0,188),(0,189),(1,186)]),
([v99,v3,v1,v0,v2,v4,v5],[(v8,v1,v0),(v99,v3,v8)],[0,1,2,3,4,5,6,8,9,11,12,15],[(0,62),(0,190),(0,191),(1,190)]),
([v3,v1,v0,v8,v2,v35,v4,v5],[(v8,v1,v0),(v35,v0,v2)],[1,2,4,5,6,9,10,13,18],[(0,192),(0,193)]),
([v7,v3,v1,v0,v8,v2,v4,v5],[(v8,v1,v0),(v7,v0,v2)],[1,2,3,4,5,6,9,10,13,18],[(0,44),(0,63),(0,97),(0,163),(0,190),(0,194)]),
([v3,v1,v0,v72,v2,v4,v5],[(v72,v8,v2)],[0,1,2,3,4,5,6,7,9,10,12,15],[(0,100),(0,195),(0,196),(1,155)]),
([v3,v1,v0,v72,v8,v2,v4,v5],[(v8,v1,v0)],[0,1,2,3,4,5,6,7,9,10,13,15,18],[(0,197),(0,198),(0,199)]),
([v73,v3,v1,v0,v8,v2,v4,v5],[(v8,v1,v0),(v73,v8,v4)],[0,1,2,4,5,6,8,9,10,12,13],[(0,198),(0,200),(0,201),(0,202),(0,203)]),
([0x300030003000300,v3,v1,v0,v2,v4,v5],[],[0,1,2,3,4,5,6,9,12,13,15],[(1,204)]),
([v3,v1,v0,v34,v2,v4],[(v34,v8,v5)],[2,4,7,9,14,15],[(0,101),(0,205),(0,206),(1,101)]),
([v3,v1,v0,v34,v8,v2,v4],[],[0,2,4,7,9,14,15],[(0,201),(0,207),(0,208),(0,209),(1,201),(1,209)]),
([v42,v3,v1,v0,v2,v4],[],[0,2,3,4,9,12,17],[(0,193),(0,210),(1,193)]),
([v42,v3,v1,v0,v8,v2,v4],[],[0,2,3,4,9,12,13,15,17],[(0,202),(0,211),(0,212),(0,213),(1,202),(1,213)]),
([v3,v1,v0,v8,v6,v2,v4,v5],[(v8,v1,v0),(v6,v2,v4)],[0,1,2,3,4,5,6,7,9,10,12],[(0,9),(0,12),(0,45),(0,61),(0,165),(0,173),(0,191),(0,207),(0,211),(0,214),(0,215),(0,216),(0,217),(0,218)]),
([v3,v1,v0,v8,v2,v4,v9,v5],[(v8,v1,v0),(v9,v2,v4)],[0,1,2,4,5,6,9],[(0,196),(0,199),(0,206),(0,208),(0,210),(0,212),(0,218),(0,219),(0,220),(0,221),(1,196),(1,199)]),
([v50,v3,v1,v0,v8,v2,v4,v5],[(v8,v1,v0),(v50,v2,v4)],[0,1,2,3,4,5,6,7,8,9,10],[(0,209),(0,213),(0,224),(1,203),(1,222),(1,223)]),
([v3,v118,v1,v0,v2,v4,v5],[(v14,v1,v0)],[0,1,2,3,4,5,6,8,9,12,13],[(0,174),(0,225)]),
([v3,v1,v0,v8,v2,v4,v5],[],[0,1,2,3,4,5,6,9,10,11,12,15,18],[(0,226)]),
([v3,v1,v0,0xf300f300f300f300,v2,v4,v5],[(v14,v1,v0)],[0,1,2,3,4,5,6,7,9,12,13],[(0,102),(0,103),(0,227),(1,156)]),
([v14,v43,v3,v2,v4,v5],[],[0,2,4,9,10,11,18],[(0,104),(0,228),(1,104)]),
([v14,v3,v1,v0,v2,v35,v4,v5],[(v14,v1,v0),(v35,v0,v2)],[0,1,4,5,6,9,10,13],[(1,229)]),
([v14,v7,v3,v1,v0,v2,v4,v5],[(v14,v1,v0),(v7,v0,v2)],[0,1,2,4,5,6,9,10,13,18],[(0,105),(0,229),(0,230)]),
([v14,v3,v1,v0,v6,v2,v4,v5],[(v14,v1,v0),(v6,v2,v4)],[0,1,3,4,5,6,9,10,12,13],[(0,10),(0,175),(0,225),(0,231),(0,232)]),
([v14,v3,v1,v0,v2,v4,v9,v5],[(v14,v1,v0),(v9,v2,v4)],[0,1,4,5,6,9,13],[(0,226),(0,228),(0,232),(0,233)]),
([v50,v14,v3,v1,v0,v2,v4,v5],[(v14,v1,v0),(v50,v2,v4)],[0,1,3,4,5,6,8,9,10,13],[(0,234),(0,235)]),
([v3,0xbabababababababa,v1,v0,v2,v4,v5],[(v43,v1,v0),(0xbabababababababa,v43,v3)],[1,2,3,4,5,6,8,9,10,11,12],[]),
([v3,v1,v139,v0,v2,v4,v5],[(v43,v1,v0),(v139,v43,v2)],[1,2,3,4,5,6,9,12,18],[(0,108),(0,110),(0,236)]),
([v43,v3,v1,v0,v2,v4,v9,v5],[(v43,v1,v0),(v9,v2,v4)],[0,1,2,4,5,6,9,10],[(0,226),(0,228),(0,237)]),
([v3,v1,v58,v0,v2,v4,v5],[(v23,v1,v2)],[0,1,2,4,5,6,8,9,10,12],[(0,68),(0,70),(0,115),(0,238),(0,239),(0,240),(1,241),(1,242),(1,243)]),
([v3,v1,v0,v91,v2,v4,v5],[(v91,v23,v0)],[0,1,2,3,4,5,6,9,10,12,13],[(0,69),(0,70),(0,116),(0,176),(0,244),(1,157)]),
([v18,v3,v1,v0,v2,v4,v5],[],[0,1,2,4,5,6,9,12,13],[]),
([v140,v3,v1,v0,v2,v4,v5],[(v140,v16,v2)],[0,1,2,3,4,5,6,7,8,9,10,12],[(0,117),(0,245)]),
([v3,v23,v0,v28,v4,v5],[],[0,1,5,9,13],[(0,247),(1,246),(1,248)]),
([v3,v23,v1,v0,v2,v4,v39,v5],[(v23,v1,v2),(v39,v0,v4)],[0,1,3,4,5,6,8,9,10,13,18],[(0,244),(0,247)]),
([v7,v3,v16,v1,v0,v2,v4,v5],[(v16,v1,v4),(v7,v0,v2)],[0,1,3,4,5,6,9,12,13,18],[(0,73),(0,119),(0,158),(0,177),(0,243),(0,248),(0,249),(0,251),(0,252),(1,250)]),
([v7,v3,v1,v0,v28,v4,v5],[(v28,v1,v2)],[0,1,2,3,4,5,9,13,18],[(0,253),(0,254),(0,255)]),
([v168,v3,v1,v0,v2,v4,v5],[(v28,v1,v2),(v168,v0,v28)],[0,1,2,4,5,6,9,12,13],[(0,256)]),
([v3,v1,v0,v2,v28,v4,v39,v5],[(v28,v1,v2),(v39,v0,v4)],[0,1,2,4,5,6,9,13,18],[(0,247),(0,256),(0,257)]),
([v7,v3,v1,v0,v2,v4,v21,v5],[(v21,v1,v4),(v7,v0,v2)],[0,1,2,3,4,5,6,8,9,13],[(0,248),(0,259),(1,258)]),
([v32,v3,v1,v0,v2,v28,v4,v5],[(v28,v1,v2),(v32,v0,v5)],[0,1,2,4,5,6,9,12,16],[(1,260)]),
([v3,v1,v0,0xff00cc00ff00cc00,v2,v4,v5],[],[0,1,2,3,4,5,6,8,9,10,13],[]),
([v3,v1,v0,v2,0xffccffcc00000000,v4],[(0xffccffcc00000000,v28,v5)],[1,2,4,5,9],[]),
([0xffccffcc,v3,v1,v0,v2,v4],[],[0,1,2,5,9,12,13],[(0,257)]),
([v3,v1,v0,v45,v2,v4,v21,v5],[(v21,v1,v4),(v45,v2,v5)],[0,1,2,3,4,5,6,8,9],[(1,261),(1,262)]),
([0xffff00000000,v3,v1,v0,v2,v28,v4,v5],[(v28,v1,v2),(0xffff00000000,v4,v5)],[0,1,2,4,5,6,9,12],[]),
([v3,v1,v0,v106,v2,v4,v5],[(v25,v1,v4)],[0,1,3,4,5,6,8,9],[(0,263),(0,264),(0,265),(0,266),(0,268),(1,267)]),
([v3,v1,v0,0xff003300ff003300,v2,v4,v5],[],[0,1,3,4,5,6,8,9,10],[]),
([v25,v26,v3,v0,v2,v5],[],[0,2,6,8,13],[(0,246),(0,270),(0,271),(0,272),(0,273),(1,269)]),
([v25,v3,v1,v76,v0,v2,v4,v5],[(v25,v1,v4),(v76,v0,v2)],[0,1,3,4,5,6,8,9,13],[(0,274),(0,275)]),
([v25,v3,v1,v0,v2,v35,v4,v5],[(v25,v1,v4),(v35,v0,v2)],[0,1,4,5,6,9,10],[(0,263),(0,272),(0,275)]),
([v25,v84,v3,v1,v0,v2,v4,v5],[(v25,v1,v4),(v84,v0,v2)],[0,1,4,5,6,9,13],[(0,277),(0,278),(0,279),(1,276)]),
([v25,v7,v3,v1,v0,v2,v4,v5],[(v25,v1,v4),(v7,v0,v2)],[0,1,3,4,5,6,8,9],[(0,264),(0,273),(0,279),(0,280),(0,281),(0,282),(0,283)]),
([v3,0xbbaabbaabbaabbaa,v1,v0,v2,v4,v5],[(v18,v1,v2),(0xbbaabbaabbaabbaa,v18,v3)],[0,1,2,4,5,6,7,8,9,12,13,15],[(0,75),(0,284),(1,285)]),
([v3,v1,v0,v65,v2,v4,v5],[(v65,v18,v0)],[0,1,2,3,4,5,6,7,9,10,12,13],[(0,74),(0,75),(0,111),(0,121),(0,166),(0,178),(1,159),(1,286)]),
([0x3300000033000000,v3,v1,v0,v2,v4,v5],[],[0,1,2,3,4,5,6,8,9,12,13,15],[]),
([v18,v3,v1,v0,v2,v4,0xffff3300ffff3300,v5],[(v18,v1,v2)],[0,1,2,3,4,5,6,8,9,12,13],[(1,270)]),
([v3,v86,v1,v0,v2,v4,v5],[(v86,v26,v2)],[0,1,2,3,4,5,6,7,8,9,10,12,13],[(0,122),(0,287)]),
([v18,v3,v1,0xccff0000ccff0000,v0,v2,v4,v5],[(v18,v1,v2)],[0,1,2,3,4,5,6,9,13,15],[(1,271)]),
([v18,v3,v1,v0,v35,v4,v5],[(v18,v1,v2),(v35,v0,v2)],[0,1,2,4,5,9,13,18],[]),
([v7,v18,v3,v1,v0,v4,v5],[],[0,1,2,3,4,5,7,9,13,18],[(0,124),(0,160),(0,284),(0,288)]),
([v18,v3,v1,v0,v2,v4,v39,v5],[(v18,v1,v2),(v39,v0,v4)],[0,1,2,3,4,5,6,8,9,13,18],[(1,272)]),
([v7,v26,v3,v1,v0,v2,v4,v5],[(v26,v1,v4)],[0,1,2,3,4,5,6,9,12,13,18],[(0,78),(0,113),(0,125),(0,161),(0,167),(0,179),(0,273),(0,285),(0,286),(0,290),(1,289),(1,291)]),
([v3,v1,0xeeeeeeeeaaaaaaaa,v0,v2,v4,v5],[(v38,v1,v5)],[0,1,2,3,4,5,6,7,8,9,12,14,17],[(0,127),(1,127)]),
([v115,v3,v1,v0,v2,v4,v5],[(v38,v1,v5)],[0,1,2,3,4,5,6,9,12,14],[(0,128),(0,130),(0,292),(0,293)]),
([v3,v38,v0,v2,v4,v46],[],[0,2,3,4,9,12,17],[(0,294),(0,295)]),
([v3,v38,v1,v0,v2,v4,v9,v5],[(v38,v1,v5),(v9,v2,v4)],[0,1,4,5,6,7,9],[(0,293),(0,295),(0,296),(1,293)]),
([v3,v1,v0,v2,v35,v4,v5,v46],[(v46,v1,v5),(v35,v0,v2)],[0,1,2,3,4,5,6,9,10,12,18],[(0,297)]),
([v32,v3,v1,v0,v2,v4,v46],[],[0,2,3,4,9,10,12,17,18],[(0,298),(0,299)]),
([v141,v3,v1,v0,v2,v4,v5],[],[0,1,2,3,4,5,6,9,12,13,17],[(0,297),(0,300),(1,297)]),
([v3,v1,v0,v2,v4,v9,v5,v46],[(v46,v1,v5),(v9,v2,v4)],[0,1,2,3,4,5,6,9],[(0,295),(0,299),(0,300),(0,301),(0,302),(0,303),(1,302)]),
([v3,v1,v0,0xff00ff00cc00cc00,v2,v4,v5],[],[0,1,2,3,4,5,6,9,10,12,17],[(0,302)]),
([v3,v1,v0,0xf0f0f0f0fcfcfcfc,v2,v4,v5],[],[0,1,2,3,4,5,6,9,12,16,17],[(0,304)]),
([v3,v1,v0,0xff00ff0033003300,v2,v4,v5],[],[0,1,2,3,4,5,6,7,9,10,12,17],[]),
([v62,v108,v3,v0,v2,v4],[],[2,3,4,9,12,17],[(0,294),(0,305)]),
([v62,v3,v1,v0,v2,v35,v4,v5],[(v62,v1,v5),(v35,v0,v2)],[0,1,3,4,5,6,9,10,12,18],[]),
([v62,v3,v1,v36,v0,v2,v4],[(v36,v0,v5)],[3,4,9,12,17],[(0,298),(0,306)]),
([v62,v3,v1,v0,v2,v4,v9,v5],[(v62,v1,v5),(v9,v2,v4)],[0,1,3,4,5,6,9],[(0,304),(0,305),(0,306),(0,307),(0,308)]),
([v62,v3,v1,v0,v45,v2,v4],[],[0,1,3,4,5,9,12,14,17],[]),
([v108,v3,v1,v0,v2,v4,v9,v5],[(v108,v1,v5),(v9,v2,v4)],[0,1,2,4,5,6,7,9],[(0,305)]),
([v3,v1,v0,0xfaaafaaafaaafaaa,v2,v4,v5],[(v76,v0,v2)],[1,2,4,5,6,8,9,11,12,13,18],[]),
([v3,v1,v0,0xfcccfcccfcccfccc,v2,v4,v5],[(0xfcccfcccfcccfccc,v1,v76)],[0,1,2,3,4,5,6,9,12,15],[]),
([v7,v3,v1,v0,v2,v4,v5],[],[1,2,3,4,5,6,9,12,13,18],[(0,275)]),
([v114,v3,v1,v0,v2,v4,v5],[(v114,v127,v2)],[1,2,3,4,5,6,8,9,12,13],[(0,46),(0,142),(0,309)]),
([0x3330333033303330,v3,v1,v0,v2,v4,v5],[(v35,v0,v2),(0x3330333033303330,v1,v35)],[0,1,2,4,5,6,9,12,13],[]),
([v3,v1,v0,v2,v35,v4,v39,v5],[(v35,v0,v2),(v39,v0,v4)],[1,4,5,6,9,10,13],[(0,192)]),
([v7,v3,v1,v0,v2,v4,v39,v5],[(v39,v0,v4),(v7,v0,v2)],[1,3,4,5,6,8,9,10,13,18],[(0,229)]),
([v3,v1,v0,v6,v2,v39,v5],[(v6,v4,v2)],[1,3,4,5,6,8,10,12,13],[]),
([v3,v1,v0,0xff00f000ff00f000,v2,v4,v5],[],[0,1,2,3,4,5,6,8,9,10],[]),
([v3,v1,v0,v2,v35,v4,v5,0xffffffffffff0000],[(v35,v0,v2),(0xffffffffffff0000,v4,v5)],[0,1,4,5,6,9,10],[]),
([v102,v3,v1,v0,v2,v4,v39,v5],[(v39,v0,v4),(v102,v2,v5)],[0,1,3,4,5,6,8,9,18],[(0,310)]),
([v3,v1,0xccccfcfcccccfcfc,v0,v2,v4,v5],[],[1,2,3,4,5,6,8,9],[]),
([v3,v1,v0,v2,0xffff00f0ffff00f0,v5],[],[1,4,5,6],[]),
([v3,v1,v0,0xff000f00ff000f00,v4,v5],[],[3,4,6,8,13],[(1,311)]),
([v3,v1,v0,0xff000f00ff000f00,v2,v4,v5],[],[1,2,3,4,5,6,8,9,13],[(1,277)]),
([v3,v1,v0,v2,v4,0xffffffff0000f0f0],[],[0,4,6,8],[]),
([v3,v1,v0,v2,0xff0fff0f00000000,v4],[],[1,4,5,13,18],[(0,278)]),
([v56,v20,v3,v1,v2,v5],[],[4,6,8,10,12,13],[(0,312),(0,314),(0,315),(1,279),(1,313)]),
([v3,v33,v1,v0,v2,v4,v5],[(v7,v0,v2),(v33,v7,v3)],[0,1,2,3,4,5,6,8,9,12,17],[(0,79),(0,194),(0,230),(0,249),(0,288),(0,316),(0,317),(0,318),(1,291),(1,319),(1,320),(1,321),(1,322)]),
([v7,v3,v33,v1,v0,v2,v4,v5],[(v7,v0,v2)],[0,1,3,4,5,6,8,9,10,13,17,18],[(0,323),(0,324),(0,325)]),
([v3,v1,v75,v0,v2,v4,v5],[(v75,v7,v1)],[0,1,2,3,4,5,6,9,12,13,15],[]),
([v7,v3,v1,v75,v0,v2,v4,v5],[(v7,v0,v2),(v75,v7,v1)],[0,1,2,3,4,5,6,7,9,13,18],[(0,48),(0,131),(0,323),(0,326),(0,327),(0,328),(1,329)]),
([v7,v3,v96,v1,v0,v2,v4,v5],[(v7,v0,v2),(v96,v7,v1)],[0,1,2,3,4,5,6,7,9,10,13,18],[(0,22),(0,132),(0,324),(0,332),(1,314),(1,330),(1,331),(1,333)]),
([v120,v3,v1,v0,v2,v4,v5],[(v7,v0,v2)],[0,1,2,3,4,5,6,7,8,9,10,12],[(0,25),(0,49),(0,334)]),
([v7,v3,v1,v0,v2,v4,v126,v5],[(v7,v0,v2)],[0,1,3,4,5,6,8,9,10,12,13],[(0,252),(0,254),(0,326),(1,315),(1,330)]),
([v3,v1,v80,v0,v2,v4,v5],[(v80,v20,v2)],[0,1,2,3,4,5,6,7,8,9,10,12],[(0,26),(0,50),(0,144),(0,335),(1,282)]),
([v7,v3,v1,v0,v66,v2,v4,v5],[(v7,v0,v2),(v66,v7,v4)],[0,1,3,4,5,6,7,9,10,12,13,18],[(0,133),(0,145),(0,255),(0,283),(0,325),(0,327),(0,336),(1,331)]),
([v7,v20,v3,v1,v0,v2,v4,v5],[(v7,v0,v2),(v20,v0,v4)],[1,3,4,5,6,9,10,12,13,18],[(0,134),(0,168),(0,322),(1,134),(1,322)]),
([v7,v3,v1,v0,v6,v4,v5],[(v7,v0,v2)],[1,3,4,5,6,7,8,10,12,13],[(0,27),(0,51),(0,337)]),
([v50,v20,v3,v1,v0,v2,v5],[(v50,v4,v2)],[1,3,4,5,6,8,10,12,13],[(0,329),(0,333),(1,338)]),
([v3,v1,v0,0xfafafafaaaaaaaaa,v2,v4,v5],[(v36,v0,v5),(0xfafafafaaaaaaaaa,v3,v36)],[0,1,2,3,4,5,6,8,9,10,11,12,13,17],[]),
([v3,v1,v0,0xfcfcfcfccccccccc,v2,v4,v5],[],[0,1,2,3,4,5,6,9,10,12,15,17,18],[(0,339)]),
([v128,v3,v1,v0,v2,v4,v5],[(v36,v0,v5),(v128,v36,v2)],[0,1,2,3,4,5,6,9,12,13,18],[(0,148),(0,150),(0,340)]),
([v3,v1,v36,v2,v4,v107],[],[0,3,4,12,17],[(0,341),(0,342)]),
([v3,v1,v36,v0,v2,v4,v9,v5],[(v36,v0,v5),(v9,v2,v4)],[0,1,4,5,6,9,10,13],[(0,306),(0,339),(0,342),(0,343)]),
([v3,v1,v0,v2,v4,v9,v5,v107],[(v107,v0,v5),(v9,v2,v4)],[0,1,3,4,5,6,9],[(0,342)]),
([v3,v1,v0,v2,0xffff0000fffff0f0,v5],[],[0,4,6,8],[]),
([v3,v1,v0,v116,v4,v5],[],[0,3,4,12,17],[(0,344)]),
([v3,v1,v0,v116,v2,v4,v5],[],[0,1,2,3,4,5,6,9,12,17],[(0,345)]),
([v85,v32,v3,v1,v2,v4],[],[0,3,4,12,17],[(0,341),(0,346)]),
([v85,v3,v1,v0,v2,v4,v9,v5],[(v85,v0,v5),(v9,v2,v4)],[0,1,3,4,5,6,9],[(0,345),(0,346),(0,347),(1,345)]),
([v3,0xafafafafaaaaaaaa,v1,v0,v2,v4,v5],[(v32,v0,v5)],[0,1,2,3,4,5,6,7,8,9,12,14,16,17],[]),
([v3,v1,0xcfcfcfcfcccccccc,v0,v2,v4,v5],[],[0,1,2,3,4,5,6,7,9,12,14,15,17],[(0,348)]),
([v3,v1,v81,v0,v2,v4,v5],[(v32,v0,v5),(v81,v32,v2)],[0,1,2,3,4,5,6,9,12,14,16],[(0,28),(0,151),(0,260),(0,349),(0,350)]),
([v32,v3,v1,v0,v2,v4,v9,v5],[(v32,v0,v5),(v9,v2,v4)],[0,1,4,5,6,7,9,13,16],[(0,299),(0,346),(0,348),(0,350),(1,350)]),
([v102,v32,v3,v1,v0,v2,v4],[(v32,v0,v5)],[0,1,3,4,5,9,16,17,18],[]),
([v3,v1,v0,v2,v19,v4,v5],[],[0,1,2,3,4,5,6,7,8,9,10,17],[(0,29),(0,82),(0,214),(0,231),(0,337),(0,351),(0,352),(0,353),(0,354),(0,355),(0,356),(0,357),(1,337)]),
([v3,v1,v0,v6,v2,v19,v4,v5],[(v6,v2,v4)],[0,1,3,4,5,6,8,9,10,12,17],[(0,30),(0,33),(0,358),(0,359),(0,360)]),
([v3,v1,v0,v2,v48,v4,v5],[(v48,v1,v6)],[0,1,2,3,4,5,6,8,9,12,13,15],[]),
([v3,v1,v0,v6,v2,v48,v4,v5],[(v6,v2,v4),(v48,v1,v6)],[0,1,2,3,4,5,6,7,9,10,12,13],[(0,31),(0,33),(0,53),(0,358),(0,361),(0,362)]),
([v51,v3,v1,v0,v6,v2,v4,v5],[(v6,v2,v4),(v51,v1,v6)],[0,1,2,3,4,5,6,7,9,10,12],[(0,32),(0,359),(0,363),(0,364)]),
([v3,v1,v0,v2,v41,v4,v5],[(v41,v0,v6)],[0,1,2,3,4,5,6,7,8,9,10,12],[(0,37),(0,54),(0,81),(0,82),(0,170),(0,180),(0,215)]),
([v3,v1,v0,v6,v9,v5],[],[1,3,5,7,10],[(0,218),(0,232),(0,362),(0,364),(0,365),(0,366),(0,367)]),
([0x3333330033333300,v3,v1,v0,v2,v4,v5],[],[0,1,2,4,5,6,9,13],[]),
([v27,v3,v1,v0,v2,v4,v5],[(v9,v2,v4)],[0,1,2,4,5,6,9],[(0,219),(0,233),(0,301),(0,308),(0,365),(0,368),(0,369),(0,370),(0,371),(0,372),(0,373)]),
([v3,v1,v0,v2,v4,0xffffff0000000000],[],[1,4,5,6],[]),
([0xffffff00,v3,v1,v0,v2,v4],[],[0,1,5,6],[]),
([v3,v1,0xccccffccccccffcc,v0,v2,v4,v5],[],[0,1,2,3,4,5,6,8,9,13],[]),
([v3,v1,v0,0xf0f0fff0f0f0fff0,v2,v4,v5],[(v50,v2,v4)],[0,1,2,3,4,5,6,8,9,10],[(0,234)]),
([v3,v1,v0,v6,v2,v4,v5],[],[0,1,2,3,4,5,6,9,10,12],[]),
([v50,v74,v3,v1,v0,v5],[],[1,3,5,6,7,10],[(0,224),(0,235),(0,366)]),
([v3,v1,v0,v2,v52,v4,v5],[(v45,v2,v5),(v52,v3,v45)],[0,1,2,4,5,6,8,9,12,14,17],[(0,38),(0,374),(0,375)]),
([v3,v1,v0,v2,0xffccffcccccccccc,v4,v5],[(0xffccffcccccccccc,v1,v45)],[0,1,2,3,4,5,6,9,12,15],[]),
([v98,v3,v1,v0,v2,v4,v5],[(v98,v59,v2)],[0,1,2,3,4,5,6,8,9,12],[(0,41),(0,152),(0,261),(0,376)]),
([v3,v1,v0,v45,v4,0xffffffffff00ff00],[],[0,1,4,5],[(1,377)]),
([v102,v3,v1,v0,v2,v59,v4],[(v59,v4,v5)],[0,1,3,4,5,6,8,9,17],[]),
([0xf0f0f0f0f000f00,v3,v1,v0,v2,v4,v5],[],[0,1,2,4,5,6,9,12,16],[]),
([v3,v1,v0,0xff00ff00ff000000,v2,v4,v5],[],[0,1,2,3,4,5,6,8,9,10],[]),
([v3,v1,v0,v170,v2,v4,v5],[(v170,v102,v0)],[0,1,2,3,4,5,6,9,12,16,17],[(0,310)]),
([v3,v1,v0,0xff00ff000000ff00,v2,v4,v5],[],[0,1,2,3,4,5,6,8,9,10,12,17],[]),
([v102,0xff00ff00000000,v3,v1,v0,v4],[],[0,1,4,5],[(1,377)]),
([v3,v1,0xccccffffcccccccc,v0,v2,v4,v5],[],[0,1,2,3,4,5,6,8,9],[]),
([v3,v1,v0,0xff000000ff00ff00,v2,v4,v5],[],[0,1,2,3,4,5,6,8,9],[])
]

def g6_L9 : Array W6Node := Array.mk [
([0x8888888888888888,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,8,9],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,3),(1,4)]),
([v3,v1,v10,v0,v2,v4,v5],[],[0,1,2,4,5,6,8,9,13,17],[(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(0,22),(0,23),(1,16),(1,17),(1,18),(1,20),(1,23)]),
([v142,v3,v1,v0,v2,v4,v5],[],[0,1,2,4,5,6,8,9,17],[(0,24),(0,25),(0,26),(0,27),(0,28),(0,29)]),
([v31,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,8,9],[(0,24),(0,28),(0,30),(0,31),(0,32),(0,33),(0,34),(0,35),(0,36),(0,37),(0,38),(1,31),(1,36),(1,37)]),
([v88,v3,v1,v0,v2,v4,v5],[],[1,4,5,6,8,9],[(0,39),(0,40),(0,41),(0,42),(0,43),(0,44),(0,45),(0,46),(1,42),(1,43)]),
([v3,v1,v0,v11,v2,v4,v5],[],[0,1,4,5,6,8,9,11,17],[(0,7),(0,8),(0,14),(0,29),(0,32),(0,46),(0,47),(0,48),(0,49),(0,50),(0,51),(0,52),(0,53),(0,54),(0,55),(0,56),(0,57),(0,58),(0,59),(0,60),(0,61),(0,62),(1,56),(1,57),(1,58),(1,59),(1,60),(1,61)]),
([v171,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,8,9,15,17],[(0,9),(0,63),(0,64),(0,65),(0,66),(0,67),(0,68)]),
([v117,v3,v1,v0,v2,v4,v5],[],[1,4,5,6,8,9,10,13,18],[(0,33),(0,64),(0,67),(0,69),(0,70),(0,71),(0,72),(1,70)]),
([v92,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,8,9,11,15,17],[(0,73),(0,74),(0,76),(0,77),(0,79),(0,81),(0,83),(0,84),(1,75),(1,78),(1,80),(1,82)]),
([v3,v1,v0,v2,v12,v4,v5],[],[0,1,4,5,6,8,9,17],[(0,83),(0,85),(0,86),(0,87),(0,88),(0,89),(0,90),(0,93),(0,94),(0,95),(0,96),(0,99),(0,100),(1,91),(1,92),(1,97),(1,98),(1,101),(1,102)]),
([v129,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,9,11,15,17],[(0,103),(0,104),(0,105),(0,107),(0,108),(1,106)]),
([v53,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,7,8,9,10,17],[(0,18),(0,60),(0,109),(0,110),(0,111),(0,112),(0,113),(0,115),(1,107),(1,114),(1,116)]),
([0xaaaaaaaa00000000,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,8,9],[(0,117),(0,118),(0,119)]),
([v3,v1,v0,v2,v4,v17],[],[0,1,8,17],[(0,10),(0,47),(0,71),(0,118),(0,120),(0,121),(0,122),(0,123),(0,124),(0,125),(0,126),(0,127),(0,128),(0,129),(1,123),(1,124),(1,125),(1,129)]),
([v3,v1,v0,v2,v4,v5,v17],[],[0,1,3,4,5,6,8,9,12,17],[(0,119),(0,120),(0,130),(0,131),(0,132),(0,133),(0,134),(1,133),(1,134)]),
([0xaaaaaaaa,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,8,9],[(0,135),(0,136),(0,137)]),
([v22,v3,v1,v0,v2,v4],[],[1,4,8,17],[(0,11),(0,34),(0,48),(0,120),(0,136),(0,138),(0,139),(0,140),(0,141),(0,142),(0,143),(1,140),(1,141),(1,142)]),
([v22,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,7,8,9,14,17],[(0,120),(0,137)]),
([v3,v29,v1,v0,v2,v4,v5],[],[0,1,4,5,6,9,10,11,18],[(0,85),(0,144),(0,145),(0,146),(0,147),(0,148),(0,149),(0,150),(0,151),(0,152),(1,85),(1,147),(1,148),(1,149)]),
([v3,v1,v0,v8,v2,v4,v5],[],[0,1,2,4,5,6,9,15],[(0,12),(0,14),(0,35),(0,49),(0,50),(0,72),(0,86),(0,110),(0,121),(0,138),(0,153),(0,154),(0,155),(0,156),(0,157),(0,158),(0,159),(0,160),(0,161),(0,162),(0,163),(0,164),(0,165),(0,166),(1,86),(1,110),(1,154),(1,155),(1,156),(1,157),(1,158),(1,159),(1,166)]),
([v14,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,9],[(0,13),(0,51),(0,68),(0,84),(0,87),(0,108),(0,111),(0,139),(0,167),(0,168),(0,169),(0,170),(0,171),(0,172),(0,173),(0,174),(0,175),(1,84),(1,87),(1,108),(1,111),(1,169),(1,171),(1,172),(1,175)]),
([v43,v3,v1,v0,v2,v4,v5],[],[1,2,4,5,6,9,10,11,18],[(0,52),(0,88),(0,122),(0,168),(0,170),(0,176),(0,177),(0,178),(1,88),(1,177)]),
([v3,v23,v1,v0,v2,v4,v5],[],[0,1,3,4,5,6,9,10],[(0,56),(0,91),(0,140),(0,179),(0,180),(0,181),(0,183),(0,184),(1,113),(1,182),(1,185)]),
([v3,v1,v0,v2,v28,v4,v5],[],[0,1,2,4,5,6,9,13],[(0,181),(0,183),(0,186),(0,187),(0,188),(0,190),(0,192),(0,193),(0,195),(1,189),(1,191),(1,194)]),
([v25,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,8,9],[(0,196),(0,197),(0,198),(0,199),(0,200),(0,201),(0,202)]),
([v18,v3,v1,v0,v2,v4,v5],[],[0,1,2,3,4,5,6,7,9,13,15],[(0,18),(0,57),(0,89),(0,92),(0,112),(0,114),(0,123),(0,141),(0,159),(0,203),(0,204),(0,205),(0,206),(0,208),(0,209),(0,210),(0,211),(1,198),(1,207),(1,212)]),
([v3,v38,v1,v0,v2,v4,v5],[],[0,1,4,5,6,7,9,14,17],[(0,93),(0,213),(0,214),(0,215),(0,216),(1,93),(1,214)]),
([v3,v1,v0,v2,v4,v5,v46],[],[0,1,2,3,4,5,6,9,12,17],[(0,215),(0,217),(0,218),(0,219),(0,220),(0,221),(1,217),(1,221)]),
([v62,v3,v1,v0,v2,v4,v5],[],[0,1,3,4,5,6,9,12,17],[(0,222),(0,223),(0,224),(0,225),(0,226),(0,227),(0,228),(1,223),(1,225),(1,228)]),
([v108,v3,v1,v0,v2,v4,v5],[],[0,2,4,5,6,7,9,14,17],[(0,94),(0,224),(0,229),(1,94)]),
([v3,v1,v76,v0,v2,v4,v5],[],[1,3,4,5,6,9,13,18],[(0,36),(0,97),(0,124),(0,199),(0,230),(0,231),(0,232),(1,233)]),
([v3,v1,v0,v2,v35,v4,v5],[],[0,1,4,5,6,9],[(0,154),(0,171),(0,200),(0,209),(0,217),(0,225),(0,232),(0,234),(0,235),(0,239),(1,184),(1,188),(1,211),(1,236),(1,237),(1,238),(1,240)]),
([v56,v3,v1,v0,v2,v4,v5],[],[1,4,5,6,8,9,10,13],[(0,241),(0,243),(0,244),(0,245),(0,247),(1,201),(1,242),(1,246)]),
([v7,v3,v1,v0,v2,v4,v5],[],[0,1,3,4,5,6,9],[(0,20),(0,37),(0,58),(0,60),(0,95),(0,98),(0,115),(0,116),(0,125),(0,142),(0,155),(0,159),(0,172),(0,185),(0,186),(0,189),(0,202),(0,210),(0,212),(0,236),(0,248),(0,249),(0,250),(0,251),(0,252),(0,253),(0,254),(0,256),(0,257),(0,258),(1,247),(1,255),(1,259)]),
([v3,v1,v36,v0,v2,v4,v5],[],[0,1,4,5,6,9,10,13,17,18],[(0,99),(0,130),(0,226),(0,260),(0,261),(0,262),(0,263),(0,264),(1,99),(1,262)]),
([v3,v1,v0,v2,v4,v5,v107],[],[0,3,4,5,6,9,12,17],[(0,263),(0,265)]),
([v85,v3,v1,v0,v2,v4,v5],[],[0,1,3,4,5,6,9,12,17],[(0,266),(0,267),(0,268),(0,269),(0,270),(1,266),(1,267),(1,268)]),
([v32,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,7,9,14,17],[(0,21),(0,100),(0,131),(0,190),(0,218),(0,269),(0,271),(0,272),(0,273),(0,274),(0,275),(1,100),(1,190),(1,273),(1,275)]),
([v3,v1,v0,v6,v2,v4,v5],[],[0,1,3,4,5,6,7,8,9,10,12],[(0,22),(0,38),(0,62),(0,109),(0,128),(0,143),(0,164),(0,173),(0,205),(0,237),(0,253),(0,258),(0,276),(0,277),(0,278),(0,279),(0,280),(0,281),(0,282),(1,237),(1,258)]),
([v3,v1,v0,v2,v4,v9,v5],[],[0,1,4,5,6,9],[(0,152),(0,165),(0,174),(0,178),(0,216),(0,220),(0,227),(0,229),(0,264),(0,265),(0,270),(0,274),(0,282),(0,283),(0,284),(0,285),(0,286)]),
([v50,v3,v1,v0,v2,v4,v5],[],[0,1,3,4,5,6,7,8,9,10],[(0,166),(0,175),(0,259),(0,287),(0,288),(0,289),(0,290)]),
([v3,v1,v0,v45,v2,v4,v5],[],[0,1,3,4,5,6,9,14],[(0,23),(0,102),(0,133),(0,194),(0,228),(0,291),(0,292),(0,294),(1,293),(1,295)]),
([v3,v1,v0,v2,v4,v5,0xffffffffff00ff00],[],[0,1,4,5,6,9,12],[(0,294),(0,296),(1,239),(1,297)]),
([v102,v3,v1,v0,v2,v4,v5],[],[0,1,3,4,5,6,9,12,17],[(0,240),(0,275),(0,295),(0,298),(0,300),(1,299)]),
([0xffff00000000,v3,v1,v0,v2,v4,v5],[],[0,1,4,5,6,7,8,9],[(0,195),(0,301),(0,302),(1,300)])
]

def g6_L10 : Array W6Node := Array.mk [
([v3,v1,v0,v2,v4,v5],[],[],[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(0,22),(0,23),(0,24),(0,25),(0,26),(0,27),(0,28),(0,29),(0,30),(0,31),(0,32),(0,33),(0,34),(0,35),(0,36),(0,37),(0,38),(0,39),(0,40),(0,41),(0,42),(0,43),(0,44),(1,8),(1,9),(1,10),(1,11),(1,22),(1,23),(1,24),(1,25),(1,30),(1,31),(1,32),(1,33),(1,40),(1,41),(1,42),(1,43),(1,44)])
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_3_0 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 3 g6_L3 (Array.mk []) 0 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_3 : ∀ i < g6_L3.size, checkNodeW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 3 g6_L3 (Array.mk []) i = true := by
  intro i hi
  have hsz : g6_L3.size = 5 := by decide +kernel
  exact checkBlockW6_at g6_chk_3_0 i (Nat.zero_le _) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_4_0 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 g6_L3 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_4_1 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 g6_L3 16 12 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_4 : ∀ i < g6_L4.size, checkNodeW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 4 g6_L4 g6_L3 i = true := by
  intro i hi
  have hsz : g6_L4.size = 28 := by decide +kernel
  have hi' : i < 28 := hsz ▸ hi
  by_cases h : i < 16
  ·
    exact checkBlockW6_at g6_chk_4_0 i (by omega) (by omega)
  ·
    exact checkBlockW6_at g6_chk_4_1 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_0 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_1 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_2 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_3 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_4 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_5 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_5_6 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 96 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_5 : ∀ i < g6_L5.size, checkNodeW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 5 g6_L5 g6_L4 i = true := by
  intro i hi
  have hsz : g6_L5.size = 101 := by decide +kernel
  have hi' : i < 101 := hsz ▸ hi
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
theorem g6_chk_6_0 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_1 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_2 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_3 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_4 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_5 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_6 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_7 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_8 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_9 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_10 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_11 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_12 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_13 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_14 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_6_15 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 240 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_6 : ∀ i < g6_L6.size, checkNodeW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 6 g6_L6 g6_L5 i = true := by
  intro i hi
  have hsz : g6_L6.size = 248 := by decide +kernel
  have hi' : i < 248 := hsz ▸ hi
  by_cases h : i < 128
  ·
    by_cases h : i < 64
    ·
      by_cases h : i < 32
      ·
        by_cases h : i < 16
        ·
          exact checkBlockW6_at g6_chk_6_0 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_1 i (by omega) (by omega)
      ·
        by_cases h : i < 48
        ·
          exact checkBlockW6_at g6_chk_6_2 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_3 i (by omega) (by omega)
    ·
      by_cases h : i < 96
      ·
        by_cases h : i < 80
        ·
          exact checkBlockW6_at g6_chk_6_4 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_5 i (by omega) (by omega)
      ·
        by_cases h : i < 112
        ·
          exact checkBlockW6_at g6_chk_6_6 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_7 i (by omega) (by omega)
  ·
    by_cases h : i < 192
    ·
      by_cases h : i < 160
      ·
        by_cases h : i < 144
        ·
          exact checkBlockW6_at g6_chk_6_8 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_9 i (by omega) (by omega)
      ·
        by_cases h : i < 176
        ·
          exact checkBlockW6_at g6_chk_6_10 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_11 i (by omega) (by omega)
    ·
      by_cases h : i < 224
      ·
        by_cases h : i < 208
        ·
          exact checkBlockW6_at g6_chk_6_12 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_13 i (by omega) (by omega)
      ·
        by_cases h : i < 240
        ·
          exact checkBlockW6_at g6_chk_6_14 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_6_15 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_0 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_1 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_2 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_3 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_4 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_5 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_6 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_7 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_8 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_9 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_10 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_11 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_12 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_13 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_14 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_15 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_16 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_17 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_18 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 288 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_19 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 304 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_20 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 320 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_21 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 336 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_22 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 352 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_7_23 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 368 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_7 : ∀ i < g6_L7.size, checkNodeW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 7 g6_L7 g6_L6 i = true := by
  intro i hi
  have hsz : g6_L7.size = 378 := by decide +kernel
  have hi' : i < 378 := hsz ▸ hi
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
        by_cases h : i < 368
        ·
          by_cases h : i < 352
          ·
            exact checkBlockW6_at g6_chk_7_21 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_7_22 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_7_23 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_0 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_1 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_2 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 32 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_3 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 48 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_4 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 64 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_5 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 80 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_6 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 96 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_7 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 112 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_8 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 128 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_9 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 144 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_10 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 160 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_11 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 176 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_12 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 192 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_13 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 208 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_14 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 224 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_15 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 240 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_16 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 256 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_17 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 272 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_8_18 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 288 15 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_8 : ∀ i < g6_L8.size, checkNodeW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 8 g6_L8 g6_L7 i = true := by
  intro i hi
  have hsz : g6_L8.size = 303 := by decide +kernel
  have hi' : i < 303 := hsz ▸ hi
  by_cases h : i < 160
  ·
    by_cases h : i < 80
    ·
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
        by_cases h : i < 64
        ·
          exact checkBlockW6_at g6_chk_8_3 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_8_4 i (by omega) (by omega)
    ·
      by_cases h : i < 128
      ·
        by_cases h : i < 112
        ·
          by_cases h : i < 96
          ·
            exact checkBlockW6_at g6_chk_8_5 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_8_6 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_8_7 i (by omega) (by omega)
      ·
        by_cases h : i < 144
        ·
          exact checkBlockW6_at g6_chk_8_8 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_8_9 i (by omega) (by omega)
  ·
    by_cases h : i < 240
    ·
      by_cases h : i < 208
      ·
        by_cases h : i < 192
        ·
          by_cases h : i < 176
          ·
            exact checkBlockW6_at g6_chk_8_10 i (by omega) (by omega)
          ·
            exact checkBlockW6_at g6_chk_8_11 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_8_12 i (by omega) (by omega)
      ·
        by_cases h : i < 224
        ·
          exact checkBlockW6_at g6_chk_8_13 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_8_14 i (by omega) (by omega)
    ·
      by_cases h : i < 272
      ·
        by_cases h : i < 256
        ·
          exact checkBlockW6_at g6_chk_8_15 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_8_16 i (by omega) (by omega)
      ·
        by_cases h : i < 288
        ·
          exact checkBlockW6_at g6_chk_8_17 i (by omega) (by omega)
        ·
          exact checkBlockW6_at g6_chk_8_18 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_9_0 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 0 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_9_1 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 16 16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_9_2 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 32 13 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_9 : ∀ i < g6_L9.size, checkNodeW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 9 g6_L9 g6_L8 i = true := by
  intro i hi
  have hsz : g6_L9.size = 45 := by decide +kernel
  have hi' : i < 45 := hsz ▸ hi
  by_cases h : i < 32
  ·
    by_cases h : i < 16
    ·
      exact checkBlockW6_at g6_chk_9_0 i (by omega) (by omega)
    ·
      exact checkBlockW6_at g6_chk_9_1 i (by omega) (by omega)
  ·
    exact checkBlockW6_at g6_chk_9_2 i (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem g6_chk_10_0 : checkBlockW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 10 g6_L10 g6_L9 0 1 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem g6_chk_10 : ∀ i < g6_L10.size, checkNodeW6 goal6 2 g6_pow 19 g6_cfLBs g6_cfMasks g6_cfB0s g6_cfStocks 10 g6_L10 g6_L9 i = true := by
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
  Nat.testBit (4277071592 * 2 ^ 32 + 4008372968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  ⟨.or, [3, 4]⟩,
  ⟨.or, [2, 5]⟩,
  ⟨.and, [1, 7]⟩,
  ⟨.or, [6, 2]⟩,
  ⟨.and, [2, 5]⟩,
  ⟨.and, [3, 4]⟩,
  ⟨.or, [0, 11]⟩,
  ⟨.or, [1, 10]⟩,
  ⟨.or, [8, 0]⟩,
  ⟨.and, [12, 13]⟩,
  ⟨.and, [9, 14]⟩,
  ⟨.or, [16, 15]⟩
]

theorem wfits : Monotone2 ⟨wg, 17⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 17⟩ (List.ofFn x) = F x := by
  decide +kernel

end PEqualNP.Outside.L_meta_41520_aux

open PEqualNP.Outside.L_meta_41520_aux in
theorem PEqualNP.Outside.L_meta_41520 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071592 * 2 ^ 32 + 4008372968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071592 * 2 ^ 32 + 4008372968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
